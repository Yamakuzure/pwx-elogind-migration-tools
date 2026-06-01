#ifndef ELOMIG_COMMENT_CHECKER_H
#include "data/Hunk.h"

#include <memory>
#define ELOMIG_COMMENT_CHECKER_H

namespace elomig {
class Hunk;

void checkComments( std::shared_ptr< Hunk > hunk );

} // namespace elomig

#endif
