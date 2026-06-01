#ifndef ELOMIG_MASK_CHECKER_H
#include "data/Hunk.h"

#include <memory>
#define ELOMIG_MASK_CHECKER_H

namespace elomig {
class Hunk;
class FileDiff;

void checkMasks( std::shared_ptr< Hunk > hunk, std::shared_ptr< FileDiff > fileDiff );

} // namespace elomig

#endif
