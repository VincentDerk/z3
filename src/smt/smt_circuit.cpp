//
// Created by vincent on 10/3/22.
//

#include "smt_circuit.h"
#include <cassert>
#include <iostream>

auto smt_circuit::decide(smt::literal l) -> circuit_ref {
    if (l.var() == prev_var)
        return null_circuit_ref;
    else
        prev_var = l.var();
    //1. add OR node: l, decision, child(0) = next circuit vector index, child(1) = 0 (fill in later)
    circuit_ref curr_index = nodes.size();
    circuit_ref next_index = curr_index + 1;
    nodes.push_back({{next_index, null_circuit_ref}, l, DECISION_NODE });
    std::cout << "Added (decide) " << l << "(" << l.var() << ")" << std::endl;
    return curr_index;
};

auto smt_circuit::propagate(smt::literal l) -> circuit_ref {
    if (l.var() == prev_var)
        return null_circuit_ref;
    else
        prev_var = l.var();
    //1. add AND node: l, propagation, child(0) = next circuit vector index, child(1) = 0 (remains 0 forever)
    circuit_ref curr_index = nodes.size();
    circuit_ref next_index = curr_index + 1;
    nodes.push_back({{next_index, null_circuit_ref}, l, PROPAGATION_NODE });
    std::cout << "Added (prop) " << l << "(" << l.var() << ")" << std::endl;
    return curr_index;
};

auto smt_circuit::next_model() -> bool {
    assert(!nodes.empty());
    //1. add TRUE NODE to complete current branch.
    nodes.push_back({{null_circuit_ref, null_circuit_ref}, sat::null_literal, TRUE_NODE});
    std::cout << "Added TRUE node" << std::endl;
    //2. find previously incomplete decision node (maybe keep track using an index?)
    size_t index; //TODO: Optimization: store found index and next time only search from there on? (update this index when adding new decision node)
    for(index = nodes.size()-2; index > 0; index--) {
        if(nodes[index].isIncompleteDecision())
            break;
    }
    circuit_node& dec_node = nodes[index];
    if (index == 0 && !dec_node.isCompleteDecision())
        return false; // no incomplete decision remains
    assert(nodes[index].isIncompleteDecision());
    //3. set its child(1) to the next circuit vector index
    // such that future nodes are added there.
    dec_node.children[1] = nodes.size();
    // Update prev_var
    prev_var = dec_node.lit.var();
    std::cout << "Set ~l branch from " << dec_node.lit << std::endl;
    return true;
};

auto smt_circuit::_backtrack(circuit_ref start_index, bool flag_prune) -> bool {
    circuit_ref node_index = start_index;
    while(node_index > 0) {
        circuit_node& node = nodes[node_index];
        node_index--;
        if (node.node_type == TRUE_NODE)
            flag_prune = true;
        else if (flag_prune && !node.isIncompleteDecision())
            nodes.pop_back();
        else if (flag_prune && node.isIncompleteDecision()) {
            // transform into propagation
            node.node_type = PROPAGATION_DUE_CONFLICT_NODE;
            node.lit.neg();
            node.children[0] = nodes.size();
            node.children[1] = null_circuit_ref;
            prev_var = node.lit.var();
            return true;
        } else if (!flag_prune && node.isIncompleteDecision()) {
            // start exploring other branch (~l decision)
            node.children[1] = nodes.size();
            prev_var = node.lit.var();
            return true;
        }
    }
    // backtrack to node_index == 0
    circuit_node& node = nodes[0];
    if (node.isIncompleteDecision()) {
        if(flag_prune) {
            // transform into propagation
            node.node_type = PROPAGATION_DUE_CONFLICT_NODE;
            node.lit.neg();
            node.children[0] = nodes.size();
            node.children[1] = null_circuit_ref;
            prev_var = node.lit.var();
        } else {
            // start exploring other branch (~l decision)
            node.children[1] = nodes.size();
            prev_var = node.lit.var();
        }
        return true;
    }
    // no decision left to backtrack to
    return false;
};

void smt_circuit::backjump(vector<sat::literal, false>::reverse_iterator unset_literals, size_t num_lits) {
    bool flag_prune = true;

    // go backwards in the circuit, pruning necessary nodes.
    // - once we encounter a TRUE node, every node above (smaller vector index) is part of a model
    // and must not be removed. Once a TRUE node is encountered, flag_prune is changed to False.
    // - when encountering a decision node, consider flipping it into a propagation node.
    //
    // we must consider following cases:
    // as long as there are literals to unset, traverse nodes in reverse order:
    // if node.literal == next_lit
    //      1. set next_lit = unset_literals.pop_back()
    //      2. if this is NOT the last processed node (!unset_literals.empty())
    //          a) case node is TRUE: flag_prune = false.
    //              No longer pop() anything because the nodes above are all part of a model.
    //          b) case node is propagation && flag_prune: pop().
    //              if !flag_prune, then a node later does rely on this node, aka it is part of a model.
    //          c) case node is IncompleteDecision: pop() if flag_prune else transform node into propagation node.
    //              Backjump indicates that ~l will lead to conflict too. So pop() this decision, unless
    //              !flag_prune because then it is part of another model already.
    //          d) case node is completeDecision: transform into propagation node if nodes.children[1] >= nodes.size()
    //              This node's left branch is part of a model. The right branch is not iff nodes.children[1] >= nodes.size()
    //              because the backjump indicates we can not find a model without backtracking even further.
    //      2. If this is our last processed node (unset_literal.empty())
    //          a) case node is incompleteDecision and pruning allowed: change to propagation ~l
    //          b) case node is incompleteDecision and pruning not allowed: start other branch: nodes.children[1] = ...
    //          c) case node is completeDecision and pruning allowed: turn into propagation l, and backtrack()
    //              we backtrack because the other branch was already explored.  Does this scenario even occur?
    //              Wouldn't backjump just jump to an earlier variable in the first place?
    //          d) case node is completeDecision and pruning not allowed: backtrack()
    //              we backtrack because both branches are already explored.  Does this scenario even occur?
    //              Wouldn't backjump just jump to an earlier variable in the first place?
    //          e) case node is propagation: pop() + backtrack() if flag_prune else only backtrack()
    //              Does this scenario even occur? Wouldn't it backjump to a previous DECISION to begin with?
    //      Invariant: When node.literal == next_lit, the node must be part of the target subcircuit because
    //          any decision l appearing in another subcircuit must appear earlier (smaller vector index) than this.
    // elseif node.literal != next_lit
    //      skip this node (assert flag_prune = false)
    std::cout << "backjmping: " << num_lits << " variables." << std::endl;
    assert(num_lits > 0);
    circuit_ref node_index = nodes.size() - 1;               // pointer upwards traversing the circuit
    sat::bool_var next_var = (*unset_literals).var();   // next var to unset
    std::cout << "node lits before backjump:";
    for (auto node : nodes)
        std::cout << node.lit << ",";
    std::cout << std::endl << nodes.back().lit.var() << " and " << next_var << std::endl;
    assert(nodes.back().lit.var() == next_var);
    // -- upwards traverse circuit till all unset_literals have been processed --
    while(num_lits > 0) {
        assert(node_index >= 0);
        next_var = (*unset_literals).var();
        circuit_node& node = nodes[node_index];
        node_index--;                                   // in next while we process next node
        // -- process node --
        if(node.lit.var() != next_var) {
            // skip. not part of the nodes we must process.
            assert(!flag_prune || node.node_type == TRUE_NODE);
            if(node.node_type == TRUE_NODE)
                flag_prune = false;                     // nodes prior to this mustn't be removed, are part of a model
        } else {
            // node.lit.var() == next_var
            unset_literals.operator++();                // next while: we process next lit
            num_lits--;
            bool is_last_unset_node = num_lits == 0;

            switch (node.node_type) {
                case TRUE_NODE:
                    // will not happen, only for node.lit.var() != next_var
                    // nodes prior to this one must not be removed, are part of a found model.
                    flag_prune = false;
                    break;
                case PROPAGATION_NODE:
                case PROPAGATION_DUE_CONFLICT_NODE:
                    if (flag_prune)
                        nodes.pop_back();
                    if (is_last_unset_node) {
                        assert(false);  //TODO: could this even happen?
                        bool success = _backtrack(node_index, flag_prune);
                        assert(success == true);
                    }
                    break;
                case DECISION_NODE:
                    if (node.isIncompleteDecision()) {
                        if(is_last_unset_node && flag_prune) {
                            node.lit.neg();                     // transform into propagation of decision.negate()
                            node.node_type = PROPAGATION_DUE_CONFLICT_NODE;
                            prev_var = node.lit.var();
                        } else if (is_last_unset_node && !flag_prune) {
                            node.children[1] = nodes.size();    // explore decision.negate() but keep original branch.
                            prev_var = node.lit.var();
                        } else if (!is_last_unset_node && flag_prune) {
                            nodes.pop_back();                               // not part of any model, pop.
                        } else {
                            node.node_type = PROPAGATION_DUE_CONFLICT_NODE; // transform into propagation
                        }
                    } else {
                        // == node.isCompleteDecision()
                        assert(!flag_prune); //bc children[0] has a model, otherwise child[1] would not have started
                        bool branch2_has_model = node.children[1] < nodes.size();
                        if (!branch2_has_model) {
                            node.children[1] = null_circuit_ref; // transform into propagation because branch2 empty
                            node.node_type = PROPAGATION_DUE_CONFLICT_NODE;
                        }
                        if (is_last_unset_node) {
                            assert(false); //TODO: Does this even occur, backjump to complete decision node?
                            bool success = _backtrack(node_index, flag_prune);
                            assert(success);
                        }
                    }
                    break;
                case DECOMPOSITION_NODE:
                case FALSE_NODE:
                    assert(false);      // Nodes are not supported yet.
                    break;
            }
        }
    }
};


void smt_circuit::print_circuit() {
    size_t node_index;
    circuit_node node;
    for(node_index = 0; node_index < nodes.size(); node_index++) {
        node = nodes[node_index];
        std::cout << node_index << ": (lit=" << node.lit << "";
        //display_literal_smt2(std::cout, node.lit);
        std::cout << ",\t children=" << node.children[0] << "," << node.children[1];
        std::cout << ",\t type=" << node.node_type << ")\n";
    }
}