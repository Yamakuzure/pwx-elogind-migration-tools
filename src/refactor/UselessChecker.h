#ifndef ELOMIG_USELESS_CHECKER_H
#include "data/Hunk.h"

#include <memory>
#define ELOMIG_USELESS_CHECKER_H

namespace elomig {
class Hunk;

void checkUseless( std::shared_ptr< Hunk > hunk );

} // namespace elomig

#endif
