#ifndef ELOMIG_INCLUDE_HANDLER_H
#include "data/Hunk.h"

#include <memory>
#define ELOMIG_INCLUDE_HANDLER_H

namespace elomig {
class Hunk;
class FileDiff;

void checkIncludes( std::shared_ptr< Hunk > hunk );

} // namespace elomig

#endif
