//
// Created by vincent on 10/3/22.
//

#ifndef Z3_SMT_CIRCUIT_H
#define Z3_SMT_CIRCUIT_H

#include "vector"
#include "smt/smt_literal.h"

using circuit_ref = size_t;
const circuit_ref null_circuit_ref = 0;

using circuit_node_type = enum {
    FALSE_NODE = 0,
    TRUE_NODE = 1,
    DECISION_NODE,                  // OR with literal
    PROPAGATION_NODE,               // AND with literal and 1 child
    DECOMPOSITION_NODE,             // AND without literal and 2 children
    PROPAGATION_DUE_CONFLICT_NODE,  // AND with literal and 1 child
};

struct circuit_node {
    std::array<circuit_ref, 2> children{null_circuit_ref, null_circuit_ref};
    smt::literal lit{sat::null_literal}; //lit -> children(0);  not(lit) -> children(1)
    circuit_node_type node_type{FALSE_NODE};

    // Whether this node is a decision of which the 2nd child is unexplored.
    auto isIncompleteDecision() -> bool { return node_type == DECISION_NODE && children[1] == null_circuit_ref; };

    // Whether this node is a decision with both children explored.
    auto isCompleteDecision() -> bool { return node_type == DECISION_NODE && children[1] != null_circuit_ref; };

    std::ostream & operator<<(std::ostream & s) {
        s << "(type=" << node_type << ",lit=" << lit << ",children=" << children[0] << "," << children[1] << ")";
        return s;
    }

};

class smt_circuit {

    /**
     * Stores circuit_nodes in an vector.
     * - The root is at index 0.
     * - The circuit grows with increasing index, i.e. a child node always appears later in the vector.
     * - A subcircuit is 'closed' using a True node before the next subcircuit is explored (breadth first search).
     */
    svector<circuit_node> nodes;

    /**
     * This is used in the scenario of a backjump, where a decision variable must be flipped.
     * The circuit does not remove the variable but flips it. Because Z3 later calls .add(decision) again,
     * this var ensures we do not add the same decision again.
     */
    smt::bool_var prev_var{sat::null_bool_var};

public:

    /**
     * Extend the circuit with a decision node.
     * This can be interpreted as adding an OR node associated with literal l,
     * with children(0) being conditioned on l, and children(1) conditioned on ~l.
     *
     * @param l The literal that has been decided on.
     * @return The circuit reference, referencing the new decision node.
     */
    auto decide(smt::literal l) -> circuit_ref;

    /**
     * Extend the circuit with a propagation node.
     * This can be interpreted as adding an AND node associated with literal l,
     * with children(0) being conditioned on that l (and children(1) is unused).
     * @param l The literal that has been inferred to be true.
     * @return The circuit reference, referencing the new decision node.
     */
    auto propagate(smt::literal l) -> circuit_ref;

    /**
     * Prepare the circuit for the next model.
     * This means the current branch is ended by appending a TRUE node, and the last incomplete decision
     * is pointing to where the next new node will be.
     * @return Whether the circuit is ready to track the next model.
     * If no more incomplete decisions are found in the circuit, then this will return false.
     */
    auto next_model() -> bool;

    /**
     * Jump back up the circuit to a literal that must be flipped in order to find a satisfying assignment
     * (conflict clause learning related). While jumping back, the nodes that do not lead to a model are removed and
     * some decision nodes are changed to propagation nodes.
     * @param unset_literals A list of set literals that should now be unassigned, as part of the backjump.
     * The literals in this list must be chronological: the order in which they appear must correspond to
     * the reverse of their assignment order in this circuit. This list will be modified.
     * TODO: The necessaty of this list is because nodes do not store a link to their parent(s). Technically,
     * TODO: we could however refer to nodes child(0) and child(1) to find the next node in line.
     * @param num_lits The number of literals to unset from the unset_literals iterator.
     */
    void backjump(vector<sat::literal, false>::reverse_iterator unset_literals, size_t num_lits);

    /**
     * TODO: update doc
     * Jump back up the circuit to a literal that must be flipped in order to find a satisfying assignment
     * (conflict clause learning related). While jumping back, the nodes that do not lead to a model are removed and
     * some decision nodes are changed to propagation nodes.
     * @param unset_literals A list of set literals that should now be unassigned, as part of the backjump.
     * The literals in this list must be chronological: the order in which they appear must correspond to
     * the reverse of their assignment order in this circuit. This list will be modified.
     * @param num_lits The number of literals to unset.
     */
    void backjump(sat::literal last_lit, size_t num_lits);

    /**
     * Print the circuit to stdout.
     */
    void print_circuit();

private:

    /**
     * Perform a backtrack in this circuit.
     * @param start_index The index in nodes to start exploring from.
     * @return Whether the backtrack succeeded.
     * If no more backtracks are possible, False is returned.
     */
    bool _backtrack(circuit_ref start_index, bool flag_prune);
};

#endif //Z3_SMT_CIRCUIT_H
