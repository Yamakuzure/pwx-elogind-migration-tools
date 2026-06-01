/**
 * @file FileDiff.cpp
 * @brief Implementation of FileDiff class
 */

#include "FileDiff.h"

#include "utils/Logger.h"
#include "utils/StringUtils.h"

namespace elomig {

FileDiff::FileDiff() : m_isCreation( false ), m_isShell( false ), m_isXML( false ), m_isPrepared( false ) {}

FileDiff::FileDiff( std::string const& part ) : m_part( part ), m_isCreation( false ), m_isShell( false ), m_isXML( false ), m_isPrepared( false ) {}

void FileDiff::addHunk( std::shared_ptr< Hunk > hunk ) {
	if ( hunk ) {
		hunk->setIndex( static_cast< int >( m_hunks.size() ) );
		m_hunks.push_back( hunk );
	}
}

void FileDiff::removeHunk( size_t index ) {
	if ( index < m_hunks.size() ) {
		m_hunks.erase( m_hunks.begin() + index );

		// Renumber remaining hunks
		for ( size_t i = 0; i < m_hunks.size(); ++i ) {
			m_hunks[i]->setIndex( static_cast< int >( i ) );
		}
	}
}

void FileDiff::clearHunks() {
	m_hunks.clear();
}

size_t FileDiff::countUsefulHunks() const {
	size_t count = 0;
	for ( auto const& hunk : m_hunks ) {
		if ( hunk && hunk->isUseful() ) {
			count++;
		}
	}
	return count;
}

bool FileDiff::hasUsefulChanges() const {
	return countUsefulHunks() > 0;
}

bool FileDiff::buildOutput() {
	clearOutput();

	if ( !hasUsefulChanges() ) {
		return false;
	}

	// Generate patch header
	std::string header;
	if ( m_isCreation ) {
		header = "diff --git a/dev/null b/" + m_part + "\n";
	} else {
		header = "diff --git a/" + m_part + " b/" + m_part + "\n";
	}

	addOutputLine( header );
	addOutputLine( "index 0000000..1234567 100644" );
	addOutputLine( "--- /dev/null" );
	addOutputLine( "+++ b/" + m_part );

	int offset = 0;
	for ( auto const& hunk : m_hunks ) {
		if ( !hunk || !hunk->isUseful() ) {
			continue;
		}

		// Add mask markers if prepared
		if ( m_isPrepared && hunk->maskedStart() ) {
			addOutputLine( "# masked_start " + std::to_string( hunk->maskedStart() ? 1 : 0 ) );
		}

		// Add hunk
		auto lines = hunk->toOutput( true, offset );
		for ( auto const& line : lines ) {
			addOutputLine( line );
		}

		// Add mask end marker if prepared
		if ( m_isPrepared && hunk->maskedEnd() ) {
			addOutputLine( "# masked_end " + std::to_string( hunk->maskedEnd() ? 1 : 0 ) );
		}
	}

	return true;
}

std::string FileDiff::getFileKind( std::string const& path ) {
	std::string lowerPath = utils::toLower( path );

	// Shell patterns
	static std::vector< std::string > const shellPatterns = {
		".sh",         ".pl",           ".py",           ".in",         ".m4",
		".sym",        ".po",           ".pot",          "makefile",    ".gitignore",
		".gperf",      "bash/busctl",   "bash/loginctl", "pam.d/other", "pam.d/system-auth",
		"zsh/_busctl", "zsh/_loginctl", "linguas"
	};

	for ( auto const& pattern : shellPatterns ) {
		if ( utils::endsWith( lowerPath, pattern ) || lowerPath.find( pattern ) != std::string::npos ) {
			return "shell";
		}
	}

	// XML patterns
	static std::vector< std::string > const xmlPatterns = { ".xml", ".ent.in", ".policy.in" };

	for ( auto const& pattern : xmlPatterns ) {
		if ( utils::endsWith( lowerPath, pattern ) ) {
			return "xml";
		}
	}

	// C/C++ patterns
	static std::vector< std::string > const cPatterns = { ".c", ".h", ".cpp", ".hpp", ".cc" };

	for ( auto const& pattern : cPatterns ) {
		if ( utils::endsWith( lowerPath, pattern ) ) {
			return "c";
		}
	}

	return "unknown";
}

} // namespace elomig
