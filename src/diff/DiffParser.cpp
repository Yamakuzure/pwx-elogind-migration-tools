/**
 * @file DiffParser.cpp
 * @brief Implementation of diff parser
 */

#include "DiffParser.h"

#include "utils/Logger.h"
#include "utils/StringUtils.h"

#include <regex>
#include <sstream>

namespace elomig {

bool DiffParser::parse( std::string const& diffOutput, std::shared_ptr< FileDiff > fileDiff ) {
	if ( diffOutput.empty() ) {
		return false;
	}

	std::istringstream         stream( diffOutput );
	std::string                line;
	std::vector< std::string > currentHunkLines;
	std::string                currentHeader;

	while ( std::getline( stream, line ) ) {
		// Remove trailing CR
		if ( !line.empty() && line.back() == '\r' ) {
			line.pop_back();
		}

		// Check for hunk header
		if ( utils::startsWith( line, "@@" ) ) {
			// Process previous hunk if any
			if ( !currentHunkLines.empty() && !currentHeader.empty() ) {
				auto hunk = std::make_shared< Hunk >();
				if ( parseHunk( currentHunkLines, hunk ) ) {
					fileDiff->addHunk( hunk );
				}
			}

			// Start new hunk
			currentHeader = line;
			currentHunkLines.clear();
			currentHunkLines.push_back( line );
		} else if ( !currentHeader.empty() ) {
			// Add to current hunk
			currentHunkLines.push_back( line );
		}
	}

	// Process last hunk
	if ( !currentHunkLines.empty() && !currentHeader.empty() ) {
		auto hunk = std::make_shared< Hunk >();
		if ( parseHunk( currentHunkLines, hunk ) ) {
			fileDiff->addHunk( hunk );
		}
	}

	return fileDiff->hunkCount() > 0;
}

bool DiffParser::parseHunk( std::vector< std::string > const& lines, std::shared_ptr< Hunk > hunk ) {
	if ( lines.empty() ) {
		return false;
	}

	// Parse header
	int srcStart = 0, tgtStart = 0;
	if ( !parseHunkHeader( lines[0], srcStart, tgtStart ) ) {
		return false;
	}

	hunk->setSourceStart( srcStart );
	hunk->setTargetStart( tgtStart );

	// Parse lines
	for ( size_t i = 1; i < lines.size(); ++i ) {
		std::string const& line = lines[i];

		if ( line.empty() ) {
			continue;
		}

		LineType    type = LineType::CONTEXT;
		std::string content;

		if ( line[0] == '+' ) {
			type    = LineType::ADDITION;
			content = line.substr( 1 );
		} else if ( line[0] == '-' ) {
			type    = LineType::REMOVAL;
			content = line.substr( 1 );
		} else if ( line[0] == ' ' || line[0] == '\\' ) {
			type    = LineType::CONTEXT;
			content = ( line.size() > 1 ) ? line.substr( 1 ) : "";
		} else {
			// Treat as context
			type    = LineType::CONTEXT;
			content = line;
		}

		HunkLine hunkLine;
		hunkLine.type       = type;
		hunkLine.content    = content;
		hunkLine.original   = line;
		hunkLine.lineNumber = static_cast< int >( hunk->lineCount() );

		hunk->addLine( hunkLine );
	}

	return true;
}

bool DiffParser::parseHunkHeader( std::string const& header, int& srcStart, int& tgtStart ) {
	// Format: @@ -<srcStart>,<srcCount> +<tgtStart>,<tgtCount> @@
	std::regex  headerRegex( R"(@@\s+-(\d+)(?:,(\d+))?\s+\+(\d+)(?:,(\d+))?\s+@@)" );
	std::smatch match;

	if ( std::regex_search( header, match, headerRegex ) ) {
		srcStart = std::stoi( match[1].str() );
		tgtStart = std::stoi( match[3].str() );
		return true;
	}

	LOG_DEBUG( "Failed to parse hunk header: %s", header.c_str() );
	return false;
}

bool DiffParser::parseLineType( std::string const& line, LineType& type, std::string& content ) {
	if ( line.empty() ) {
		return false;
	}

	char prefix = line[0];

	switch ( prefix ) {
		case '+':
			type = LineType::ADDITION;
			break;
		case '-':
			type = LineType::REMOVAL;
			break;
		case ' ':
			type = LineType::CONTEXT;
			break;
		default:
			return false;
	}

	content = line.substr( 1 );
	return true;
}

} // namespace elomig
