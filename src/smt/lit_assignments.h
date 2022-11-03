//
// Created by vincent on 10/11/22.
//

#ifndef Z3_LIT_ASSIGNMENTS_H
#define Z3_LIT_ASSIGNMENTS_H

#include <cassert>
#include "vector"
#include "smt/smt_literal.h"
#include "smt/smt_types.h"

class lit_assignments {

public:

    struct lit_assignment {
        smt::literal lit;
        bool decision;
        bool complete;
    };

    svector<lit_assignment> assignments;


    void decide(smt::literal lit) {
        if (assignments.empty() || assignments.back().lit.var() != lit.var())
            assignments.push_back({lit, true, false});
    };

    void propagate(smt::literal lit) {
        assignments.push_back({lit, false, false});
    };

    void pop_back(smt::bool_var v) {
        assert(!assignments.empty());
        assert(v == assignments.back().lit.var());
        assignments.pop_back();
    };
    inline void pop_back(smt::literal l) { pop_back(l.var()); };

    inline auto begin() { return assignments.begin(); };
    inline auto end() { return assignments.end(); };

    inline auto size() {
        return assignments.size();
    }

    inline auto back() {
        return assignments.back();
    }

    inline auto empty() {
        return assignments.empty();
    }

    /**
     * Flip the sign of the last incomplete decision.
     * This pops any assignments that happened in between. Therefore, after calling this method, the last assignment
     * will be either a decision that was just flipped to be complete, or no assignment is left at all (in which case
     * this method returns False).
     * @return Whether there was any incomplete decision left.
     */
    auto flip_last_decision() -> bool;

    /**
     * Shrink to the first num_lits assignments.
     * @param num_lits The number of assignments that must remain.
     */
    void shrink(size_t num_lits) {
        assert(num_lits <= assignments.size());
        assignments.shrink(num_lits);
    };

};


#endif //Z3_LIT_ASSIGNMENTS_H
