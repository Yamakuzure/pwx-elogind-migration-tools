#ifndef ELOMIG_DEBUG_CHECKER_H
#include "data/Hunk.h"

#include <memory>
#define ELOMIG_DEBUG_CHECKER_H

namespace elomig {
class Hunk;

void checkDebug( std::shared_ptr< Hunk > hunk );

} // namespace elomig

#endif
