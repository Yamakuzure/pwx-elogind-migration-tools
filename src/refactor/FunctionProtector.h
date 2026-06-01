#ifndef ELOMIG_FUNCTION_PROTECTOR_H
#include "data/Hunk.h"

#include <memory>
#define ELOMIG_FUNCTION_PROTECTOR_H

namespace elomig {
class Hunk;

void checkFunctions( std::shared_ptr< Hunk > hunk );

} // namespace elomig

#endif
