#ifndef ELOMIG_MUSL_CHECKER_H
#include "data/Hunk.h"

#include <memory>
#define ELOMIG_MUSL_CHECKER_H

namespace elomig {
class Hunk;

void checkMusl( std::shared_ptr< Hunk > hunk );

} // namespace elomig

#endif
