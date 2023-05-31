from z3 import *
from Constraints import semanticConstraints_suffix, consistencyConstraints_suffix, placeholderConstraints
from helping_functions import *
import global_variables

# import values of global variables
print_output = global_variables.print_output
print_model = global_variables.print_model
maximumSize = global_variables.maximumSize
build_solution = global_variables.build_solution


def check_existence_tree_suffix(sample, sketch):
    """ Checks whether there exists a consistent substitution for the given sketch and sample.
        If build_solution is set to true it also computes and outputs such a solution.
        For both it uses the suffix heuristic.

        Parameters
        ----------
        sample : Sample
            The set of traces for which existence of a solution should be checked

        sketch : Sketch
            The sketch for which existence of a solution should be checked
    """
    sample_table, suffix_table = sample_to_tables(sample)

    s = Solver()

    semanticConstraints_suffix(s, sketch, sample_table, suffix_table, sample.letter2pos)
    consistencyConstraints_suffix(s, sketch.identifier, sample_table, sample.num_positives)
    placeholderConstraints(s, sketch, sketch.getAllNodes())

    if s.check() == z3.sat:
        print("SAT")
        if build_solution:
            build_solution_tree_suffix(sketch, sample_table, suffix_table, sample, maximumSize)
    else:
        print("UNSAT")
# ---------------------------------------------------------------------------------------------------


def build_solution_tree_suffix(sketch, sample_table, suffix_table, sample, finalSize):
    """ For the given sketch and sample it computes and outputs a consistent substitution,
        if one exists resulting in a formula of size smaller finalSize
        It uses the suffix heuristic.

        If print_model is set to true it also writes the model to a file 'solution.txt'

        Parameters
        ----------
        sample : Sample
            The set of traces for which a solution should be computed

        sketch : Sketch
            The sketch for which a solution should be computed

        finalSize : int
            An upper bound on the size of the solution

        sample_table : list (of dictionaries{id, prefix, sid, startpos})
            Together with the suffix_table this represents the sample for implementing the suffix heuristic

        suffix_table : list (of dictionaries{sid, u, v, list})
            Together with the sample_table this represents the sample for implementing the suffix heuristic
    """

    solver_1 = Solver()

    # change type0 placeholders to highest identifiers in sketch
    sketch.change_identifiers()

    # encode consistency (evaluation at the root must match the type (pos, neg) of trace)
    consistencyConstraints_suffix(solver_1, sketch.identifier, sample_table, sample.num_positives)

    # encode sketch except type0 placeholders, those are the same as the semantic constraints in the existence check
    semanticConstraints_suffix(solver_1, sketch, sample_table, suffix_table, sample.letter2pos)

    # encode same evaluation of same placeholders (1/2)
    placeholderConstraints(solver_1, sketch, sketch.getAllNodes())

    num_nodes = sketch.treeSize()
    type_0_nodes = sketch.get_type0Positions()
    additional_nodes = type_0_nodes[:-1]
    if len(type_0_nodes) > 0:
        last_node_id = type_0_nodes[-1]
    else:
        last_node_id = num_nodes - 1       # There is no type-0 placeholder
    prev_last_node_id = -1

    operators = sample.operators
    alphabet = sample.alphabet
    possible_labels = operators + alphabet
# ------------------------------
    # initialize all type-0 placeholder but the last one (will be leaf)
    # consider them as additional nodes
    for id in additional_nodes:
        # at least one label among all labels (operators + alphabet)
        solver_1.add(
            Or(
                [Bool('x_%s_%s' % (id, label)) for label in possible_labels]
            )
        )
        # at most one label among all labels
        # all Combinations of combining two atomic propositions were already added to the solver
        # Therefore, combine each operator with all atomic propositions
        solver_1.add(
            [
                And(
                    [
                        Or(
                            Not(Bool('x_%s_%s' % (id, label))),
                            Not(Bool('x_%s_%s' % (id, label2)))
                        )
                        for label2 in possible_labels[i + 1:]
                    ]
                )
                for i, label in enumerate(possible_labels[:-1])
            ]
        )
        # left child
        # at most one among all but the last node. The last one will be handled in the loop iteration
        solver_1.add(
            [
                And(
                    [
                        Or(
                            Not(Bool('l_%s_%s' % (id, pos_1))),
                            Not(Bool('l_%s_%s' % (id, pos_2)))
                        )
                        for pos_2 in range(pos_1 + 1, last_node_id)
                    ]
                )
                for pos_1 in range(id + 1, last_node_id)
            ]
        )
        # right child
        # at most one among all but the last node. The last one will be handled in the loop iteration
        solver_1.add(
            [
                And(
                    [
                        Or(
                            Not(Bool('r_%s_%s' % (id, pos_1))),
                            Not(Bool('r_%s_%s' % (id, pos_2)))
                        )
                        for pos_2 in range(pos_1 + 1, last_node_id)
                    ]
                )
                for pos_1 in range(id + 1, last_node_id)
            ]
        )
        # Constraints encoding evaluation
        # atomic propositions
        for ap in alphabet:
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    if trace[k][sample.letter2pos[ap]] == 1:
                        solver_1.add(
                            Implies(
                                Bool('x_%s_%s' % (id, ap)),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k))
                            )
                        )
                    else:
                        solver_1.add(
                            Implies(
                                Bool('x_%s_%s' % (id, ap)),  # ->
                                Not(Bool('z_%s_%s_%s' % (id, j, k)))
                            )
                        )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    if trace[k][sample.letter2pos[ap]] == 1:
                        solver_1.add(
                            Implies(
                                Bool('x_%s_%s' % (id, ap)),  # ->
                                Bool('z_%s_%s_%s' % (id, s, k))
                            )
                        )
                    else:
                        solver_1.add(
                            Implies(
                                Bool('x_%s_%s' % (id, ap)),  # ->
                                Not(Bool('z_%s_%s_%s' % (id, s, k)))
                            )
                        )

        for leftid in range(id + 1, last_node_id):
            # unary operators
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]
                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                for k in range(len(trace)):
                    # ! (Not)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '!')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                        )
                    )

                    # X
                    next_1, next_2 = suc_2(sample_entry, k)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'X')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                        )
                    )

                    # F
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'F')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                                    for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                ]
                            )
                        )
                    )

                    # G
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'G')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                                    for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                ]
                            )
                        )
                    )
            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    # ! (Not)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '!')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            Not(Bool('z_%s_%s_%s' % (leftid, s, k)))
                        )
                    )

                    # X
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'X')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, s, next))
                        )
                    )

                    # F
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'F')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, s, f))
                                    for f in range(len(suffix_entry["u"]), len(trace))
                                ]
                            )
                        )
                    )

                    # G
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'G')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, s, f))
                                    for f in range(len(suffix_entry["u"]), len(trace))
                                ]
                            )
                        )
                    )

            for rightid in range(id + 1, last_node_id):
                # binary operators
                for sample_entry in sample_table:
                    j = sample_entry["id"]
                    trace = sample_entry["prefix"]
                    startpos = sample_entry["startpos"]
                    suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                    for k in range(len(trace)):
                        # & (And)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '&')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (rightid, j, k))
                                )
                            )
                        )

                        # | (Or)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '|')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (rightid, j, k))
                                )
                            )
                        )

                        # ->
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '->')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Implies(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (rightid, j, k))
                                )
                            )
                        )

                        # U
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, 'U')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Or(
                                    [
                                        And(
                                            [Bool('z_%s_%s_%s' % (rightid, f_1, f_2))] +
                                            [
                                                Bool('z_%s_%s_%s' % (leftid, fp_1, fp_2))
                                                for fp_1, fp_2 in BET_2(j, k, f_1, f_2, startpos, len(trace))
                                            ]
                                        )
                                        for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                    ]
                                )
                            )
                        )
                for suffix_entry in suffix_table:
                    s = suffix_entry["sid"]
                    trace = suffix_entry["u"] + suffix_entry["v"]

                    for k in range(len(trace)):
                        # & (And)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '&')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, s, k)) ==
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                    Bool('z_%s_%s_%s' % (rightid, s, k))
                                )
                            )
                        )

                        # | (Or)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '|')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, s, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                    Bool('z_%s_%s_%s' % (rightid, s, k))
                                )
                            )
                        )

                        # ->
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '->')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, s, k)) ==
                                Implies(
                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                    Bool('z_%s_%s_%s' % (rightid, s, k))
                                )
                            )
                        )

                        # U
                        if k < len(suffix_entry["u"]):
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, 'U')),
                                        Bool('l_%s_%s' % (id, leftid)),
                                        Bool('r_%s_%s' % (id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, s, k)) ==
                                    Or(
                                        [
                                            And(
                                                [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                                [
                                                    Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                    for k_pp in range(k, k_p)
                                                ]
                                            )
                                            for k_p in range(k, len(trace))
                                        ]
                                    )
                                )
                            )
                        else:   # k in range(len(suffix_entry["u"]), len(trace))
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, 'U')),
                                        Bool('l_%s_%s' % (id, leftid)),
                                        Bool('r_%s_%s' % (id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, s, k)) ==
                                    Or(
                                        [
                                            And(
                                                [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                                [
                                                    Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                    for k_pp in BET_1(suffix_entry["u"], suffix_entry["v"], k, k_p)
                                                ]
                                            )
                                            for k_p in range(len(suffix_entry["u"]), len(trace))
                                        ]
                                    )
                                )
                            )
# ----------------------------------------
    # start looping
    while num_nodes < finalSize:
        if print_output:
            print('looking for formula of size', num_nodes)

        solver_2 = Solver()
        # ----------------------------------------
        # last node is leaf. Only necessary if there is at least one type-0 placeholder
        if last_node_id != num_nodes - 1:
            id = last_node_id
            # label is atomic proposition
            # at least one
            solver_2.add(
                Or(
                    [Bool('x_%s_%s' % (id, ap)) for ap in alphabet]
                )
            )
            # at most one
            solver_1.add(
                [
                    And(
                        [
                            Or(
                                Not(Bool('x_%s_%s' % (id, ap))),
                                Not(Bool('x_%s_%s' % (id, ap_2)))
                            )
                            for ap_2 in alphabet[i + 1:]
                        ]
                    )
                    for i, ap in enumerate(alphabet)
                ]
            )
            # and no operator
            solver_2.add(
                And(
                    [Not(Bool('x_%s_%s' % (id, op))) for op in operators]
                )
            )

            # evaluation for atomic proposition
            for ap in alphabet:
                for sample_entry in sample_table:
                    j = sample_entry["id"]
                    trace = sample_entry["prefix"]

                    for k in range(len(trace)):
                        if trace[k][sample.letter2pos[ap]] == 1:
                            solver_1.add(
                                Implies(
                                    Bool('x_%s_%s' % (id, ap)),  # ->
                                    Bool('z_%s_%s_%s' % (id, j, k))
                                )
                            )
                        else:
                            solver_1.add(
                                Implies(
                                    Bool('x_%s_%s' % (id, ap)),  # ->
                                    Not(Bool('z_%s_%s_%s' % (id, j, k)))
                                )
                            )

                for suffix_entry in suffix_table:
                    s = suffix_entry["sid"]
                    trace = suffix_entry["u"] + suffix_entry["v"]

                    for k in range(len(trace)):
                        if trace[k][sample.letter2pos[ap]] == 1:
                            solver_1.add(
                                Implies(
                                    Bool('x_%s_%s' % (id, ap)),  # ->
                                    Bool('z_%s_%s_%s' % (id, s, k))
                                )
                            )
                        else:
                            solver_1.add(
                                Implies(
                                    Bool('x_%s_%s' % (id, ap)),  # ->
                                    Not(Bool('z_%s_%s_%s' % (id, s, k)))
                                )
                            )
        # --------------------------
        # previously last node:
        # need to initialize all Constraints for this node:
        if prev_last_node_id != -1:
            id = prev_last_node_id
            # at least one label among all labels (operators + alphabet)
            solver_1.add(
                Or(
                    [Bool('x_%s_%s' % (id, label)) for label in possible_labels]
                )
            )
            # at most one label among all labels
            # all Combinations of combining two atomic propositions were already added to the solver
            # Therefore, combine each operator with all atomic propositions
            solver_1.add(
                [
                    And(
                        [
                            Or(
                                Not(Bool('x_%s_%s' % (id, op))),
                                Not(Bool('x_%s_%s' % (id, ap)))
                            )
                            for ap in alphabet
                        ]
                    )
                    for op in operators
                ]
            )
            # additionally, consider each pair of operators
            solver_1.add(
                [
                    And(
                        [
                            Or(
                                Not(Bool('x_%s_%s' % (id, op_1))),
                                Not(Bool('x_%s_%s' % (id, op_2)))
                            )
                            for op_2 in operators[i+1:]
                        ]
                    )
                    for i, op_1 in enumerate(operators)
                ]
            )

            # left child
            # there is only one valid option (requires higher index)
            solver_2.add(
                Bool('l_%s_%s' % (id, last_node_id))
            )

            # right child
            # at least one (with higher index)
            solver_2.add(
                Bool('r_%s_%s' % (id, last_node_id))
            )
            # Constraints encoding evaluation, atomic proposition were already added
            leftid = last_node_id
            rightid = last_node_id

            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]
                startpos = sample_entry["startpos"]
                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                for k in range(len(trace)):
                    # ! (Not)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '!')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                        )
                    )

                    # X
                    next_1, next_2 = suc_2(sample_entry, k)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'X')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                        )
                    )

                    # F
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'F')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                                    for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                ]
                            )
                        )
                    )

                    # G
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'G')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                                    for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                ]
                            )
                        )
                    )
                    # & (And)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '&')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, rightid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )

                    # | (Or)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '|')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, rightid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )

                    # ->
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '->')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, rightid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Implies(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )

                    # U
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'U')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, rightid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Or(
                                [
                                    And(
                                        [Bool('z_%s_%s_%s' % (rightid, f_1, f_2))] +
                                        [
                                            Bool('z_%s_%s_%s' % (leftid, fp_1, fp_2))
                                            for fp_1, fp_2 in BET_2(j, k, f_1, f_2, startpos, len(trace))
                                        ]
                                    )
                                    for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                ]
                            )
                        )
                    )
            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    # ! (Not)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '!')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            Not(Bool('z_%s_%s_%s' % (leftid, s, k)))
                        )
                    )

                    # X
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'X')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, s, next))
                        )
                    )

                    # F
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'F')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, s, f))
                                    for f in range(len(suffix_entry["u"]), len(trace))
                                ]
                            )
                        )
                    )

                    # G
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'G')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, s, f))
                                    for f in range(len(suffix_entry["u"]), len(trace))
                                ]
                            )
                        )
                    )
                    # & (And)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '&')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, rightid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (rightid, s, k))
                            )
                        )
                    )

                    # | (Or)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '|')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, rightid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (rightid, s, k))
                            )
                        )
                    )

                    # ->
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '->')),
                                Bool('l_%s_%s' % (id, leftid)),
                                Bool('r_%s_%s' % (id, rightid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            Implies(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (rightid, s, k))
                            )
                        )
                    )

                    # U
                    if k < len(suffix_entry["u"]):
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, 'U')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, s, k)) ==
                                Or(
                                    [
                                        And(
                                            [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                            [
                                                Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                for k_pp in range(k, k_p)
                                            ]
                                        )
                                        for k_p in range(k, len(trace))
                                    ]
                                )
                            )
                        )
                    else:  # k in range(len(suffix_entry["u"]), len(trace))
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, 'U')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, rightid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, s, k)) ==
                                Or(
                                    [
                                        And(
                                            [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                            [
                                                Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                for k_pp in BET_1(suffix_entry["u"], suffix_entry["v"], k, k_p)
                                            ]
                                        )
                                        for k_p in range(len(suffix_entry["u"]), len(trace))
                                    ]
                                )
                            )
                        )
# --------------------------------------
        # all other nodes
        # it suffices to add:
        # - the at least one Constraints on the children to solver_2,
        # - the at most one containing the new last node to solver_1
        # - and the evaluation with the new last node as one of the children also to solver_1
        for id in additional_nodes:
            # left child
            # at least one (with higher index)
            solver_2.add(
                Or(
                    [Bool('l_%s_%s' % (id, pos)) for pos in range(id + 1, last_node_id + 1)]
                )
            )
            # at most one
            solver_1.add(
                And(
                    [
                        Or(
                            Not(Bool('l_%s_%s' % (id, last_node_id))),
                            Not(Bool('l_%s_%s' % (id, pos)))
                        )
                        for pos in range(id + 1, last_node_id)
                    ]
                )
            )
            # right child
            # at least one (with higher index)
            solver_2.add(
                Or(
                    [Bool('r_%s_%s' % (id, pos)) for pos in range(id + 1, last_node_id + 1)]
                )
            )
            # at most one
            solver_1.add(
                And(
                    [
                        Or(
                            Not(Bool('r_%s_%s' % (id, last_node_id))),
                            Not(Bool('r_%s_%s' % (id, pos)))
                        )
                        for pos in range(id + 1, last_node_id)
                    ]
                )
            )

            # Constraints encoding evaluation
            # unary operators
            leftid = last_node_id
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]
                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                for k in range(len(trace)):
                    # ! (Not)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '!')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                        )
                    )

                    # X
                    next_1, next_2 = suc_2(sample_entry, k)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'X')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                        )
                    )

                    # F
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'F')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                                    for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                ]
                            )
                        )
                    )

                    # G
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'G')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, j, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                                    for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                ]
                            )
                        )
                    )
            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    # ! (Not)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, '!')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            Not(Bool('z_%s_%s_%s' % (leftid, s, k)))
                        )
                    )

                    # X
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'X')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, s, next))
                        )
                    )

                    # F
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'F')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, s, f))
                                    for f in range(len(suffix_entry["u"]), len(trace))
                                ]
                            )
                        )
                    )

                    # G
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (id, 'G')),
                                Bool('l_%s_%s' % (id, leftid))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (id, s, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, s, f))
                                    for f in range(len(suffix_entry["u"]), len(trace))
                                ]
                            )
                        )
                    )
            # binary operators
            for other_id in range(id+1, last_node_id + 1):
                leftid = last_node_id
                for sample_entry in sample_table:
                    j = sample_entry["id"]
                    trace = sample_entry["prefix"]
                    startpos = sample_entry["startpos"]
                    suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                    for k in range(len(trace)):
                        # & (And)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '&')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                )
                            )
                        )

                        # | (Or)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '|')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                )
                            )
                        )

                        # ->
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '->')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Implies(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                )
                            )
                        )

                        # U
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, 'U')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, j, k)) ==
                                Or(
                                    [
                                        And(
                                            [Bool('z_%s_%s_%s' % (other_id, f_1, f_2))] +
                                            [
                                                Bool('z_%s_%s_%s' % (leftid, fp_1, fp_2))
                                                for fp_1, fp_2 in BET_2(j, k, f_1, f_2, startpos, len(trace))
                                            ]
                                        )
                                        for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                    ]
                                )
                            )
                        )
                for suffix_entry in suffix_table:
                    s = suffix_entry["sid"]
                    trace = suffix_entry["u"] + suffix_entry["v"]

                    for k in range(len(trace)):
                        # & (And)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '&')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, s, k)) ==
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                )
                            )
                        )

                        # | (Or)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '|')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, s, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                )
                            )
                        )

                        # ->
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (id, '->')),
                                    Bool('l_%s_%s' % (id, leftid)),
                                    Bool('r_%s_%s' % (id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (id, s, k)) ==
                                Implies(
                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                )
                            )
                        )

                        # U
                        if k < len(suffix_entry["u"]):
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, 'U')),
                                        Bool('l_%s_%s' % (id, leftid)),
                                        Bool('r_%s_%s' % (id, other_id))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, s, k)) ==
                                    Or(
                                        [
                                            And(
                                                [Bool('z_%s_%s_%s' % (other_id, s, k_p))] +
                                                [
                                                    Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                    for k_pp in range(k, k_p)
                                                ]
                                            )
                                            for k_p in range(k, len(trace))
                                        ]
                                    )
                                )
                            )
                        else:  # k in range(len(suffix_entry["u"]), len(trace))
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, 'U')),
                                        Bool('l_%s_%s' % (id, leftid)),
                                        Bool('r_%s_%s' % (id, other_id))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, s, k)) ==
                                    Or(
                                        [
                                            And(
                                                [Bool('z_%s_%s_%s' % (other_id, s, k_p))] +
                                                [
                                                    Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                    for k_pp in BET_1(suffix_entry["u"], suffix_entry["v"], k, k_p)
                                                ]
                                            )
                                            for k_p in range(len(suffix_entry["u"]), len(trace))
                                        ]
                                    )
                                )
                            )
                # ----------
                # new node as right child
                rightid = last_node_id
                if other_id != rightid:
                    for sample_entry in sample_table:
                        j = sample_entry["id"]
                        trace = sample_entry["prefix"]
                        startpos = sample_entry["startpos"]
                        suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                        for k in range(len(trace)):
                            # & (And)
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, '&')),
                                        Bool('l_%s_%s' % (id, other_id)),
                                        Bool('r_%s_%s' % (id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, j, k)) ==
                                    And(
                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                        Bool('z_%s_%s_%s' % (rightid, j, k))
                                    )
                                )
                            )

                            # | (Or)
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, '|')),
                                        Bool('l_%s_%s' % (id, other_id)),
                                        Bool('r_%s_%s' % (id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, j, k)) ==
                                    Or(
                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                        Bool('z_%s_%s_%s' % (rightid, j, k))
                                    )
                                )
                            )

                            # ->
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, '->')),
                                        Bool('l_%s_%s' % (id, other_id)),
                                        Bool('r_%s_%s' % (id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, j, k)) ==
                                    Implies(
                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                        Bool('z_%s_%s_%s' % (rightid, j, k))
                                    )
                                )
                            )

                            # U
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, 'U')),
                                        Bool('l_%s_%s' % (id, other_id)),
                                        Bool('r_%s_%s' % (id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, j, k)) ==
                                    Or(
                                        [
                                            And(
                                                [Bool('z_%s_%s_%s' % (rightid, f_1, f_2))] +
                                                [
                                                    Bool('z_%s_%s_%s' % (other_id, fp_1, fp_2))
                                                    for fp_1, fp_2 in BET_2(j, k, f_1, f_2, startpos, len(trace))
                                                ]
                                            )
                                            for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                        ]
                                    )
                                )
                            )
                    for suffix_entry in suffix_table:
                        s = suffix_entry["sid"]
                        trace = suffix_entry["u"] + suffix_entry["v"]

                        for k in range(len(trace)):
                            # & (And)
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, '&')),
                                        Bool('l_%s_%s' % (id, other_id)),
                                        Bool('r_%s_%s' % (id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, s, k)) ==
                                    And(
                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                        Bool('z_%s_%s_%s' % (rightid, s, k))
                                    )
                                )
                            )

                            # | (Or)
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, '|')),
                                        Bool('l_%s_%s' % (id, other_id)),
                                        Bool('r_%s_%s' % (id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, s, k)) ==
                                    Or(
                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                        Bool('z_%s_%s_%s' % (rightid, s, k))
                                    )
                                )
                            )

                            # ->
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (id, '->')),
                                        Bool('l_%s_%s' % (id, other_id)),
                                        Bool('r_%s_%s' % (id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (id, s, k)) ==
                                    Implies(
                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                        Bool('z_%s_%s_%s' % (rightid, s, k))
                                    )
                                )
                            )

                            # U
                            if k < len(suffix_entry["u"]):
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_%s' % (id, 'U')),
                                            Bool('l_%s_%s' % (id, other_id)),
                                            Bool('r_%s_%s' % (id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (id, s, k)) ==
                                        Or(
                                            [
                                                And(
                                                    [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                                    [
                                                        Bool('z_%s_%s_%s' % (other_id, s, k_pp))
                                                        for k_pp in range(k, k_p)
                                                    ]
                                                )
                                                for k_p in range(k, len(trace))
                                            ]
                                        )
                                    )
                                )
                            else:   # k in range(len(suffix_entry["u"]), len(trace))
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_%s' % (id, 'U')),
                                            Bool('l_%s_%s' % (id, other_id)),
                                            Bool('r_%s_%s' % (id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (id, s, k)) ==
                                        Or(
                                            [
                                                And(
                                                    [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                                    [
                                                        Bool('z_%s_%s_%s' % (other_id, s, k_pp))
                                                        for k_pp in BET_1(suffix_entry["u"], suffix_entry["v"], k, k_p)
                                                    ]
                                                )
                                                for k_p in range(len(suffix_entry["u"]), len(trace))
                                            ]
                                        )
                                    )
                                )
# -------------------------------
        # Construct solver s = s1 + s2
        solver = Solver()
        solver.add(solver_1.assertions())
        solver.add(solver_2.assertions())

        if solver.check() == z3.sat:
            # construct substitutions from model
            m = solver.model()

            if print_model:
                file = 'solution.txt'
                f = open(file, 'w')
                for e in m:
                    f.write(str(e) + ', ' + str(is_true(m[e])) + '\n')
                f.close()

            typ0_ids = sketch.get_type0Positions()
            typ1_ids = sketch.get_type1Positions()
            typ2_ids = sketch.get_type2Positions()

            # type 1 and 2 can be applied directly by chancing the label
            substitutions = []
            for id in typ1_ids:
                sub = (id, [op for op in ['!', 'X', 'G', 'F'] if z3.is_true(m[z3.Bool('x_%s_%s' % (id, op))])][0])
                substitutions.append(sub)

            for id in typ2_ids:
                sub = (id, [op for op in ['&', '|', '->', 'U'] if z3.is_true(m[z3.Bool('x_%s_%s' % (id, op))])][0])
                substitutions.append(sub)

            LTL = sketch.substitute_sketch_type_1_2(substitutions)

            # for type 0 placeholders a new sketch has to be constructed which replaces the placeholder-node
            substitutions = []

            for id in typ0_ids:
                sub = (id, construct_Sketch_from_Model(m, alphabet, id, last_node_id + 1))
                substitutions.append(sub)

            cLTL = LTL.substitute_sketch_type_0(substitutions)
            cLTL.reduce()

            if print_output:
                print(cLTL.prettyPrint(True))
                print(sample.isFormulaConsistent(cLTL))

            break
        else:
            if prev_last_node_id != -1:
                additional_nodes.append(prev_last_node_id)
            if last_node_id != num_nodes - 1:
                prev_last_node_id = last_node_id
                last_node_id += 1
                num_nodes += 1

        if num_nodes == finalSize:
            if print_output:
                print('No solution found up to size', finalSize)
# ---------------------------------------------------------------------------------------------------
