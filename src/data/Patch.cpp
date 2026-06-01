/**
 * @file Patch.cpp
 * @brief Implementation of Patch class
 */

#include "Patch.h"

#include <algorithm>

namespace elomig {

Patch::Patch() : m_index( 0 ), m_applied( false ) {}

Patch::Patch( std::string const& filename ) : m_filename( filename ), m_index( 0 ), m_applied( false ) {}

void Patch::addFileDiff( std::shared_ptr< FileDiff > diff ) {
	if ( diff ) {
		m_fileDiffs.push_back( diff );
		m_targetFiles.push_back( diff->part() );
	}
}

bool Patch::hasTargetFile( std::string const& file ) const {
	return std::find( m_targetFiles.begin(), m_targetFiles.end(), file ) != m_targetFiles.end();
}

} // namespace elomig
