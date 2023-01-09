//
// Created by vincent on 10/3/22.
//

#include "smt_circuit.h"
#include "smt_context.h"
#include <cassert>
#include <iostream>

auto smt_circuit::decide(smt::literal l) -> circuit_ref {
    if (l.var() == prev_var) {
        must_handle_backjump = false;
        return null_circuit_ref;
    }
    // Information on must_handle_backjump, see smt_circuit::propagate(l);
    // If the backjump is not of type flipped decision (i.e. after backjump it adds the opposite decision),
    // then it must be the type where it should have propagated a variable (and realised this, hence the backjump),
    // so the next variable to add is then propagate instead of decide.
    // We therefore assume must_handle_backjump to be false here.
    SASSERT(must_handle_backjump == false);

    prev_var = l.var();
    //1. add OR node: l, decision, child(0) = next circuit vector index, child(1) = 0 (fill in later)
    circuit_ref curr_index = nodes.size();
    circuit_ref next_index = curr_index + 1;
    nodes.push_back({{next_index, null_circuit_ref}, l, DECISION_NODE });
    TRACE("smt_circuit", tout << "Added (decide) " << l << "\n";);
    return curr_index;
}

auto smt_circuit::propagate(smt::literal l) -> circuit_ref {
    if (l.var() == prev_var) {
        must_handle_backjump = false;
        return null_circuit_ref;
    }

    // must_handle_backjump indicates that previous action was a backjump.
    // If must_handle_backjump is true, and we add a new variable different from prev_var,
    // i.e. the backjump produced a new propagated variable instead of a flipped decision,
    // then we should add the propagated variable and start over on that subcircuit
    //
    // hence, we remove all nodes up to and incl. prev_var, and only then
    // add the new propagated node to the end.
    if(must_handle_backjump) {
        while(nodes.back().lit.var() != prev_var) {
            TRACE("smt_circuit", tout << "backjump handling removed:" << nodes.back().lit.var() << "\n");
            nodes.pop_back();
        }
        TRACE("smt_circuit", tout << "backjump handling removed:" << nodes.back().lit.var() << "\n");
        nodes.pop_back(); // remove prev_var
        SASSERT(nodes.size() > 0);
        must_handle_backjump = false;
        // below we add the propagated node.
    }

    prev_var = l.var();
    //1. add AND node: l, propagation, child(0) = next circuit vector index, child(1) = 0 (remains 0 forever)
    circuit_ref curr_index = nodes.size();
    circuit_ref next_index = curr_index + 1;
    nodes.push_back({{next_index, null_circuit_ref}, l, PROPAGATION_NODE });
    TRACE("smt_circuit", tout << "Added (prop) " << l << "\n";);
    return curr_index;
}

auto smt_circuit::next_model() -> bool {
    SASSERT(!nodes.empty());
    SASSERT(!must_handle_backjump);
    //1. add TRUE NODE to complete current branch.
    nodes.push_back({{null_circuit_ref, null_circuit_ref}, sat::null_literal, TRUE_NODE});
    TRACE("smt_circuit", tout <<  "Added TRUE node" << "\n";);
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
    TRACE("smt_circuit", tout << "Set ~l branch from " << dec_node.lit << "\n";);
    return true;
}

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
}


void smt_circuit::backjump(sat::literal last_lit, size_t num_lits) {
    bool flag_prune = true;

    // go backwards in the circuit, pruning necessary nodes.
    // - once we encounter a TRUE node, every node above (smaller vector index) is part of a model
    // and must not be removed. Once a TRUE node is encountered, flag_prune is changed to False.
    // - when encountering a decision node, consider flipping it into a propagation node.
    //
    // we must consider following cases:
    // as long as there are literals to unset, traverse nodes in reverse order:
    // if node.is_parent_node_of(previous_node)
    //      1. set previous_node = node
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
    // elseif !node.is_parent_node_of(previous_node)
    //      skip this node (assert flag_prune = false)
    TRACE("smt_circuit", tout << "backjumping: " << num_lits << " variables." << "\n";);
    assert(num_lits > 0);
    must_handle_backjump = true;

    // -- upwards traverse circuit till all necessary literals (cf. num_lits) have been processed --
    // node_index is used to upwards traverse the circuit
    // A decision node branches into two subcircuits, each placed linearly into the nodes vector.
    // When we are traversing upwards in a right-side subcircuit, nodes[--node_index] may be of the left-subcircuit.
    // We use prev_relevant_index to track the previously processed node such that when moving upwards,
    // we can check whether the current node_index is a parent of prev_relevant_index (cf. is_parent_node).
    // if not, we must skip the node as it is a node of the left-side subcircuit.
    circuit_ref node_index = nodes.size() - 1;          // pointer, upwards traversing the circuit
    circuit_ref prev_relevant_index = null_circuit_ref; // pointer to previously processed node

    // Determine node_index:
    // Either the last added literal is indeed the last added to the circuit,
    // or an incomplete decision was flipped and caused a conflict.
    // In the latter scenario, last_lit is not nodes.back() but higher up in the circuit.
    // We should backjump from there.
    SASSERT(nodes.back().lit.var() == last_lit.var() || nodes.back().node_type == TRUE_NODE);
    if(nodes.back().node_type == TRUE_NODE) {
        // In case last node is TRUE_NODE, find node_index associated with last_lit.
        auto v = last_lit.var();
        while(node_index > 0 && nodes[node_index].lit.var() != v)
            node_index--;
        SASSERT(nodes[node_index].lit.var() == v);
        // found node_index, correcting other vars
        flag_prune = false;                                  // must no longer remove any nodes.
        prev_relevant_index = nodes[node_index].children[0]; // force is_parent_node to be true at first.
    }

    while(num_lits > 0) {
        assert(node_index >= 0);
        circuit_node& node = nodes[node_index];
        node_index--;                                   // in next while we process next node
        bool is_parent_node = node.children[0] == prev_relevant_index ||
                node.children[1] == prev_relevant_index;
        // -- process node --
        if(!is_parent_node) {
            // skip. not part of the nodes we must process.
            assert(!flag_prune || node.node_type == TRUE_NODE);
            if(node.node_type == TRUE_NODE)
                flag_prune = false;                     // nodes prior to this mustn't be removed, are part of a model
        } else {
            prev_relevant_index = node_index+1;         // next while: we process parent node of this one
            num_lits--;
            bool is_last_unset_node = num_lits == 0;

            switch (node.node_type) {
                case TRUE_NODE:
                    // will not happen, only for !is_parent_node
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

//    std::cout << "node lits after backjump:";
//    for (auto node : nodes)
//        std::cout << node.lit << ",";
//    std::cout << std::endl;
}

auto smt_circuit::as_expression(ast_manager& m, const smt::context& c) const -> expr_ref {
    //auto smt_circuit::as_expression(ast_manager& m, expr_ref (*literal2expr)(smt::literal)) const -> expr* {
    if (nodes.empty()) {
        return expr_ref(m.mk_false(), m);
    }

    if (nodes[0].node_type == TRUE_NODE) {
        assert(nodes.size() == 1);
        return expr_ref(m.mk_true(), m);
    }

    // last node must be a true node.
    // alternatively, we can increase size of results to nodes.size() + 1
    // and store a mk_true() expression at results[nodes.size()]
    SASSERT(nodes.back().node_type == TRUE_NODE);
    size_t const node_count = nodes.size();
    size_t node_index;
    expr* results[nodes.size()];
    for (size_t nb_processed_nodes = 0; nb_processed_nodes < node_count; nb_processed_nodes++) {
        node_index = node_count - nb_processed_nodes - 1;  // backwards, from last index to 0.
        const circuit_node& node = nodes[node_index];
        switch(node.node_type) {
            case TRUE_NODE: {
                results[node_index] = m.mk_true();
                break;
            }
            case PROPAGATION_NODE:
            case PROPAGATION_DUE_CONFLICT_NODE: {
                SASSERT(node.children[0] < nodes.size());
                expr_ref lit = c.literal2expr(node.lit);
                expr *branch = results[node.children[0]];
                results[node_index] = m.mk_and(lit, branch);
                break;
            }
            case DECISION_NODE: {
                SASSERT(node.isCompleteDecision());
                SASSERT(node.children[0] < nodes.size());
                SASSERT(node.children[1] < nodes.size());
                //left branch
                expr_ref left_lit = c.literal2expr(node.lit);
                expr *left_child = results[node.children[0]];
                expr *left_branch = m.mk_and(left_lit, left_child);
                // right branch
                expr_ref right_lit = c.literal2expr(~node.lit);
                expr *right_child = results[node.children[1]];
                expr *right_branch = m.mk_and(right_lit, right_child);
                // combined
                results[node_index] = m.mk_or(left_branch, right_branch);
                break;
            }
            default:{}
        }
    }
    return expr_ref(results[0], m); // root
}

void smt_circuit::finalize() {
    // Close the final model.
    // A True node denotes the closing a model.
    // True nodes are added when calling next_model()
    // To close the final model, it is important
    // this method adds a TRUE node.
    // REMARK: It could be that a circuit has 2 ending
    // TRUE nodes. e.g. when smoothing over a variable.
    assert(!nodes.empty());
    nodes.push_back({{null_circuit_ref, null_circuit_ref}, sat::null_literal, TRUE_NODE});
}

void smt_circuit::finalize_last_decision_conflict() {
    SASSERT(nodes.size() > 2);
    // Last made decision leads to unrecoverable conflict
    // (unrecoverable because all other decisions are complete)
    // 1. remove all nodes up to the last TRUE node
    while(nodes.back().node_type != TRUE_NODE)
        nodes.pop_back();
    SASSERT(nodes.size() >= 2);

    // 2. change (wrong) decision node to propagation node.
    // this would be the decision with children[1] == the now nodes.size()
    circuit_ref target_index = nodes.size();
    circuit_ref search_index = nodes.size() - 2;
    size_t size_lim = nodes.size();
    while(nodes[search_index].children[1] != target_index && search_index < size_lim) {
        // There must be a node where children[1] == target_index,
        // otherwise there is a mistake in the code. To make sure we
        // do not loop forever here due to a mistake (hard to detect?)
        // we use size_lim to detect the scenario and break.
        SASSERT(nodes[search_index].node_type != DECISION_NODE || nodes[search_index].isCompleteDecision());
        search_index--;
    }
    SASSERT(search_index < nodes.size());
    SASSERT(nodes[search_index].isCompleteDecision());
    nodes[search_index].children[1] = null_circuit_ref;
    nodes[search_index].node_type = PROPAGATION_DUE_CONFLICT_NODE;

    // 3. no need to append TRUE node because there already is one (cf first while).
}

auto smt_circuit::display(std::ostream & out) const -> std::ostream& {
    size_t node_index;
    for(node_index = 0; node_index < nodes.size(); node_index++) {
        const circuit_node& node = nodes[node_index];
        out << node_index << ": (lit=" << node.lit << "";
        out << ",\t children=" << node.children[0] << "," << node.children[1];
        out << ",\t type=" << node.node_type << ")\n";
    }
    return out;
}