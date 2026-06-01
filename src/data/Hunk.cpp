/**
 * @file Hunk.cpp
 * @brief Implementation of Hunk class
 */

#include "Hunk.h"

#include "utils/StringUtils.h"

#include <sstream>

namespace elomig {

Hunk::Hunk() : m_srcStart( 0 ), m_tgtStart( 0 ), m_index( 0 ), m_useful( true ), m_maskedStart( false ), m_maskedEnd( false ), m_offset( 0 ) {}

void Hunk::addLine( HunkLine const& line ) {
	HunkLine newLine   = line;
	newLine.lineNumber = static_cast< int >( m_lines.size() );
	m_lines.push_back( newLine );
}

void Hunk::removeLine( size_t index ) {
	if ( index < m_lines.size() ) {
		m_lines.erase( m_lines.begin() + index );

		// Renumber remaining lines
		for ( size_t i = index; i < m_lines.size(); ++i ) {
			m_lines[i].lineNumber = static_cast< int >( i );
		}
	}
}

void Hunk::insertLine( size_t index, HunkLine const& line ) {
	if ( index <= m_lines.size() ) {
		HunkLine newLine   = line;
		newLine.lineNumber = static_cast< int >( index );
		m_lines.insert( m_lines.begin() + index, newLine );

		// Renumber lines after insertion point
		for ( size_t i = index + 1; i < m_lines.size(); ++i ) {
			m_lines[i].lineNumber = static_cast< int >( i );
		}
	}
}

std::string Hunk::generateHeader( int& offsetRef ) const {
	// Count source and target lines
	int srcCount = 0;
	int tgtCount = 0;

	for ( auto const& line : m_lines ) {
		if ( line.type == LineType::CONTEXT || line.type == LineType::REMOVAL ) {
			srcCount++;
		}
		if ( line.type == LineType::CONTEXT || line.type == LineType::ADDITION ) {
			tgtCount++;
		}
	}

	// Apply offset to source start
	int                adjustedSrcStart = m_srcStart + offsetRef;

	std::ostringstream oss;
	oss << "@@ -" << adjustedSrcStart << "," << srcCount << " +" << m_tgtStart << "," << tgtCount << " @@";

	// Update offset for next hunk
	offsetRef += ( tgtCount - srcCount );

	return oss.str();
}

size_t Hunk::countAdditions() const {
	size_t count = 0;
	for ( auto const& line : m_lines ) {
		if ( line.type == LineType::ADDITION && !line.done ) {
			count++;
		}
	}
	return count;
}

size_t Hunk::countRemovals() const {
	size_t count = 0;
	for ( auto const& line : m_lines ) {
		if ( line.type == LineType::REMOVAL && !line.done ) {
			count++;
		}
	}
	return count;
}

bool Hunk::hasChanges() const {
	return countAdditions() > 0 || countRemovals() > 0;
}

std::vector< std::string > Hunk::toOutput( bool includeHeader, int offsetRef ) const {
	std::vector< std::string > result;

	if ( includeHeader ) {
		result.push_back( generateHeader( offsetRef ) );
	}

	for ( auto const& line : m_lines ) {
		char prefix = ' ';
		switch ( line.type ) {
			case LineType::ADDITION:
				prefix = '+';
				break;
			case LineType::REMOVAL:
				prefix = '-';
				break;
			case LineType::CONTEXT:
				prefix = ' ';
				break;
		}

		result.push_back( std::string( 1, prefix ) + line.content );
	}

	return result;
}

} // namespace elomig
