//
// Created by vincent on 10/11/22.
//

#pragma once

#include <cassert>
#include "util/vector.h"
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

    /**
     * Indicates the last performed action was a backjump.
     * The backjump removed variables, including an incomplete decision.
     * The next variable to add is either a decision (completing that decision),
     * or a propagation.
     * - When the next decision is added, it must be a 'complete' decision.
     * - When the next propagation occurs, the backjump is completed (next decision hereafter
     * is again incomplete decision).
     */
    bool must_handle_backjump = false;

    inline void clear() {
        assignments.clear();
        must_handle_backjump = false;
    };

    void decide(smt::literal lit) {
        bool is_complete_dec = must_handle_backjump;
        must_handle_backjump = false;
        // in case of start_next_model, we flip the last decision
        // and then Z3 adds the same decision but flipped afterwards.
        // we do not want to store both, so we ignore the latter addition.
        if (assignments.empty() || assignments.back().lit.var() != lit.var())
            assignments.push_back({lit, true, is_complete_dec});
    };

    void propagate(smt::literal lit) {
        must_handle_backjump = false;
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

    inline auto size() { return assignments.size(); }

    inline auto back() { return assignments.back(); }

    inline auto empty() { return assignments.empty(); }

    /**
     * Flip the sign of the last incomplete decision.
     * This pops any assignments that happened in between. Therefore, after calling this method, the last assignment
     * will be either a decision that was just flipped to be complete, or no assignment is left at all (in which case
     * this method returns False).
     * @return Whether there was any incomplete decision left.
     */
    auto flip_last_decision() -> bool;

    /**
     * TODO: delete?
     * Get the index of the last incomplete decision.
     *
     * The following conditions will hold:
     * - assignments[result] is both decision and incomplete.
     * - assignments[> result] are no decision or complete.
     * @return The index of the last incomplete decision. If no incomplete decision remains,
     * 0 is returned and one should check whether it is indeed an incomplete decision.
     */
    auto get_last_decision_index() -> size_t;

    /**
     * Perform a backjump such that only num_rem_lits literals remain on the stack.
     * @param num_rem_lits The number of remaining literals.
     */
    void backjump(size_t num_rem_lits) {
        assert(num_rem_lits < assignments.size());
        // Assume next must be an incomplete decision (not 100% sure though)
        assert(assignments[num_rem_lits+1].decision);
        assert(!assignments[num_rem_lits+1].complete);
        must_handle_backjump = true;
        assignments.shrink(num_rem_lits);
    }

    /**
     * Shrink to the first num_lits assignments.
     * @param num_lits The number of assignments that must remain.
     */
    void shrink(size_t num_lits) {
        assert(num_lits <= assignments.size());
        assignments.shrink(num_lits);
    };

};
