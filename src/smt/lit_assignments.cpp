//
// Created by vincent on 10/11/22.
//

#include "lit_assignments.h"

auto lit_assignments::flip_last_decision() -> bool {
    // find last incomplete decision
    while(!assignments.empty() && !(assignments.back().decision && !assignments.back().complete))
        assignments.pop_back();
    // flip incomplete decision
    if (!assignments.empty()) {
        assignments.back().complete = true;
        assignments.back().lit.neg();
    }
    // return whether there was an incomplete decision
    return !assignments.empty();
};