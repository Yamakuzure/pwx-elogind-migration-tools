#ifndef ELOMIG_EMPTY_MASK_CHECKER_H
#include "data/Hunk.h"

#include <memory>
#define ELOMIG_EMPTY_MASK_CHECKER_H

namespace elomig {
class Hunk;

void checkEmptyMasks( std::shared_ptr< Hunk > hunk );

} // namespace elomig

#endif
