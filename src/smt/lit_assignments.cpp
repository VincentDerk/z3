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

auto lit_assignments::get_last_decision_index() -> size_t {
    if (assignments.empty())
        return 0;
    size_t index = assignments.size() - 1;
    while(index > 0 && !(assignments[index].decision && !assignments[index].complete))
        index--;
    //assert(index == 0 || (!assignments[index].complete && assignments[index].decision));
    return index;
}