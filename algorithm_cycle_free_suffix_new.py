from Constraints import semanticConstraints_suffix, consistencyConstraints_suffix, placeholderConstraints, \
     semanticConstraints_cycle_free_suffix, structureConstraints_cycle_free, \
     initial_cycleConstraints, loop_cycleConstraints
from helping_functions import *
import global_variables
from pytictoc import TicToc

# import values of global variables
print_output = global_variables.print_output
maximumSize = global_variables.maximumSize
build_solution = global_variables.build_solution
print_model = global_variables.print_model
print_tables = global_variables.print_tables
timing = global_variables.timing


def check_existence_cycle_free_suffix(sample, sketch):
    t = TicToc()
    t.tic()
    s = Solver()
    sample_table, suffix_table = sample_to_tables(sample)

    if print_tables:
        pretty_print_dic_list(sample_table)
        pretty_print_dic_list(suffix_table)

    semanticConstraints_suffix(s, sketch, sample_table, suffix_table, sample.letter2pos)
    consistencyConstraints_suffix(s, sketch.identifier, sample_table, sample.num_positives)
    placeholderConstraints(s, sketch, sketch.getAllNodes())

    if s.check() == z3.sat:
        print("SAT")
        if timing:
            print('existence', t.tocvalue())
        if build_solution:
            build_solution_cycle_free_suffix(sketch, sample_table, suffix_table, sample, maximumSize)
        if timing:
            print('total', t.tocvalue())
    else:
        print("UNSAT")
# --------------------------------------------------------------------------------------------------- TODO


def build_solution_cycle_free_suffix(sketch, sample_table, suffix_table, sample, finalSize):
    t = TicToc()
    t.tic()
    operators = sample.operators
    alphabet = sample.alphabet
    possible_labels = operators + alphabet

    solver_1 = Solver()

    # encode consistency (evaluation at the root must match the type (pos, neg) of trace)
    consistencyConstraints_suffix(solver_1, sketch.identifier, sample_table, sample.num_positives)

    parent_nodes = []       # parent of a type-0 placeholder
    sketch_nodes = []       # nodes of the sketch which are neither parent_nodes nor type-0 placeholder

    # parse sketch to fill parent- and sketch_nodes
    for node in sketch.getAllNodes():
        if node._isLeaf() and '?' not in node.label:
            # node is not type-0 placeholder and has no children
            sketch_nodes.append(node)

        if node._isUnary():
            if '?' in node.left.label and not ('?u' in node.left.label or '?b' in node.left.label):
                # child is type-0 placeholder
                parent_nodes.append(node)
            else:
                sketch_nodes.append(node)

        if node._isBinary():
            if '?' in node.left.label and not ('?u' in node.left.label or '?b' in node.left.label) or \
               '?' in node.right.label and not ('?u' in node.right.label or '?b' in node.right.label):
                # at least one child is type-0 placeholder
                parent_nodes.append(node)
            else:
                sketch_nodes.append(node)

    # encode semantics of sketch except parent nodes
    semanticConstraints_cycle_free_suffix(solver_1, sketch_nodes, sample_table, suffix_table, sample.letter2pos)

    # encode structure-Constraints, defining the structure of the fixed (non type-0) part of the sketch
    structureConstraints_cycle_free(solver_1, sketch_nodes, parent_nodes, possible_labels)

    # encode same evaluation of same placeholders (1/2)
    placeholderConstraints(solver_1, sketch, sketch.getAllNodes())

    # list of ids considered to be in the completed sketch
    identifier_list = [node.identifier for node in sketch_nodes + parent_nodes]
    # id of node added in this iteration, -1 in first iteration
    new_node_id = -1
    # list of former new_nodes, together they replace type-0 placeholder
    additional_node_list = []

    if identifier_list == []:       # sketch is single type-0 placeholder
        identifier_list = [0]
        new_node_id = 0
        additional_node_list = []

    current_size = len(identifier_list)

    # ----------------------- TODO
    # encode semantics of parent nodes for initial loop iteration:
    for node in parent_nodes:
        node_id = node.identifier
        # The children can not have id 0 (root) or the one of the node itself (would form loop)
        pos_child_id = [id for id in identifier_list if id != 0 and id != node_id]
        if node._isUnary():
            # Structure (unary): the node has precisely one left child.
            # Only encode 'at most' over the initial nodes, then add Constraints for new_node in each iteration.
            # At least has to be encoded in each iteration (disjunction over all possible ids)
            solver_1.add(
                [
                    And(
                        [
                            Or(
                                Not(Bool('l_%s_%s' % (node_id, pos_1))),
                                Not(Bool('l_%s_%s' % (node_id, pos_2)))
                            )
                            for pos_2 in identifier_list[i + 1:]
                        ]
                    )
                    for i, pos_1 in enumerate(identifier_list[:-1])
                ]
            )
            # ----------------------------------- TODO
            # Evaluation (unary): the evaluation (z-variables) has to follow the semantics of LTL.
            # Again only encode semantics with initial nodes as left child and add Constraints in each iteration later
            for leftid in pos_child_id:
                # ! (Not)
                if node.label == '!':
                    for sample_entry in sample_table:
                        j = sample_entry["id"]
                        trace = sample_entry["prefix"]

                        for k in range(len(trace)):
                            solver_1.add(
                                Implies(
                                    Bool('l_%s_%s' % (node_id, leftid)),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                    Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                                )
                            )
                    for suffix_entry in suffix_table:
                        s = suffix_entry["sid"]
                        trace = suffix_entry["u"] + suffix_entry["v"]

                        for k in range(len(trace)):
                            solver_1.add(
                                Implies(
                                    Bool('l_%s_%s' % (node_id, leftid)),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    Not(Bool('z_%s_%s_%s' % (leftid, s, k)))
                                )
                            )
                # X
                elif node.label == 'X':
                    for sample_entry in sample_table:
                        j = sample_entry["id"]
                        trace = sample_entry["prefix"]

                        for k in range(len(trace)):
                            next_1, next_2 = suc_2(sample_entry, k)

                            solver_1.add(
                                Implies(
                                    Bool('l_%s_%s' % (node_id, leftid)),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                    Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                                )
                            )

                    for suffix_entry in suffix_table:
                        s = suffix_entry["sid"]
                        trace = suffix_entry["u"] + suffix_entry["v"]

                        for k in range(len(trace)):
                            next = suc_1(suffix_entry["u"], suffix_entry["v"], k)

                            solver_1.add(
                                Implies(
                                    Bool('l_%s_%s' % (node_id, leftid)),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    Bool('z_%s_%s_%s' % (leftid, s, next))
                                )
                            )
                # F
                elif node.label == 'F':
                    for sample_entry in sample_table:
                        j = sample_entry["id"]
                        trace = sample_entry["prefix"]
                        suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                        for k in range(len(trace)):
                            solver_1.add(
                                Implies(
                                    Bool('l_%s_%s' % (node_id, leftid)),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                    Or(
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
                            solver_1.add(
                                Implies(
                                    Bool('l_%s_%s' % (node_id, leftid)),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    Or(
                                        [
                                            Bool('z_%s_%s_%s' % (leftid, s, f))
                                            for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                        ]
                                    )
                                )
                            )
                # G
                elif node.label == 'G':
                    for sample_entry in sample_table:
                        j = sample_entry["id"]
                        trace = sample_entry["prefix"]
                        suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                        for k in range(len(trace)):
                            solver_1.add(
                                Implies(
                                    Bool('l_%s_%s' % (node_id, leftid)),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
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
                            solver_1.add(
                                Implies(
                                    Bool('l_%s_%s' % (node_id, leftid)),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    And(
                                        [
                                            Bool('z_%s_%s_%s' % (leftid, s, f))
                                            for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                        ]
                                    )
                                )
                            )
                # ?u
                elif '?u' in node.label:
                    # finite prefix in sample-table
                    for sample_entry in sample_table:
                        j = sample_entry["id"]
                        trace = sample_entry["prefix"]
                        suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                        for k in range(len(trace)):
                            # placeholder is !
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_!' % node_id),
                                        Bool('l_%s_%s' % (node_id, leftid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                    Not(
                                        Bool('z_%s_%s_%s' % (leftid, j, k))
                                    )
                                )
                            )
                            # placeholder is X
                            next_1, next_2 = suc_2(sample_entry, k)
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_X' % node_id),
                                        Bool('l_%s_%s' % (node_id, leftid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                    Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                                )
                            )
                            # placeholder is F
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_F' % node_id),
                                        Bool('l_%s_%s' % (node_id, leftid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                    Or(
                                        [
                                            Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                                            for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                        ]
                                    )
                                )
                            )
                            # placeholder is G
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_G' % node_id),
                                        Bool('l_%s_%s' % (node_id, leftid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                    And(
                                        [
                                            Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                                            for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                        ]
                                    )
                                )
                            )

                    # suffixes in suffix-table
                    for suffix_entry in suffix_table:
                        s = suffix_entry["sid"]
                        trace = suffix_entry["u"] + suffix_entry["v"]

                        for k in range(len(trace)):
                            # placeholder is !
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_!' % node_id),
                                        Bool('l_%s_%s' % (node_id, leftid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    Not(
                                        Bool('z_%s_%s_%s' % (leftid, s, k))
                                    )
                                )
                            )
                            # placeholder is X
                            next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_X' % node_id),
                                        Bool('l_%s_%s' % (node_id, leftid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    Bool('z_%s_%s_%s' % (leftid, s, next))
                                )
                            )
                            # placeholder is F
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_F' % node_id),
                                        Bool('l_%s_%s' % (node_id, leftid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    Or(
                                        [
                                            Bool('z_%s_%s_%s' % (leftid, s, f))
                                            for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                        ]
                                    )
                                )
                            )
                            # placeholder is G
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_G' % node_id),
                                        Bool('l_%s_%s' % (node_id, leftid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    And(
                                        [
                                            Bool('z_%s_%s_%s' % (leftid, s, f))
                                            for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                        ]
                                    )
                                )
                            )
        # ----------------------------------- TODO
        else:  # node._isBinary()
            left_is_type_0 = False
            right_is_type_0 = False

            # Structure (binary): Check which child is type-0 placeholder, structure Constraints already encode
            # the non type-0 placeholder
            if '?' in node.left.label and not ('?u' in node.left.label or '?b' in node.left.label):
                # left child is type-0 placeholder
                left_is_type_0 = True

                # Only encode 'at most' over the initial nodes, then add Constraints for new_node in each iteration.
                # At least has to be encoded in each iteration (disjunction over all possible ids)
                solver_1.add(
                    [
                        And(
                            [
                                Or(
                                    Not(Bool('l_%s_%s' % (node_id, pos_1))),
                                    Not(Bool('l_%s_%s' % (node_id, pos_2)))
                                )
                                for pos_2 in identifier_list[i + 1:]
                            ]
                        )
                        for i, pos_1 in enumerate(identifier_list[:-1])
                    ]
                )
            # ----------------------------------- TODO
            if '?' in node.right.label and not ('?u' in node.right.label or '?b' in node.right.label):
                # right child is type-0 placeholder
                right_is_type_0 = True

                # Only encode 'at most' over the initial nodes, then add Constraints for new_node in each iteration.
                # At least has to be encoded in each iteration (disjunction over all possible ids)
                solver_1.add(
                    [
                        And(
                            [
                                Or(
                                    Not(Bool('r_%s_%s' % (node_id, pos_1))),
                                    Not(Bool('r_%s_%s' % (node_id, pos_2)))
                                )
                                for pos_2 in identifier_list[i + 1:]
                            ]
                        )
                        for i, pos_1 in enumerate(identifier_list[:-1])
                    ]
                )
            # ----------------------------------- TODO
            # Evaluation (binary): the evaluation (z-variables) has to follow the semantics of LTL.
            # Again only encode semantics with initial nodes as children and add Constraints in each iteration later
            if left_is_type_0:
                for leftid in pos_child_id:
                    if right_is_type_0:
                        for rightid in pos_child_id:
                            # & (And)
                            if node.label == '&':
                                for sample_entry in sample_table:
                                    j = sample_entry["id"]
                                    trace = sample_entry["prefix"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                And(
                                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, j, k))
                                                )
                                            )
                                        )

                                for suffix_entry in suffix_table:
                                    s = suffix_entry["sid"]
                                    trace = suffix_entry["u"] + suffix_entry["v"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                And(
                                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, s, k))
                                                )
                                            )
                                        )
                            # | (Or)
                            elif node.label == '|':
                                for sample_entry in sample_table:
                                    j = sample_entry["id"]
                                    trace = sample_entry["prefix"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Or(
                                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, j, k))
                                                )
                                            )
                                        )

                                for suffix_entry in suffix_table:
                                    s = suffix_entry["sid"]
                                    trace = suffix_entry["u"] + suffix_entry["v"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Or(
                                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, s, k))
                                                )
                                            )
                                        )
                            # ->
                            elif node.label == '->':
                                for sample_entry in sample_table:
                                    j = sample_entry["id"]
                                    trace = sample_entry["prefix"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Implies(
                                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, j, k))
                                                )
                                            )
                                        )

                                for suffix_entry in suffix_table:
                                    s = suffix_entry["sid"]
                                    trace = suffix_entry["u"] + suffix_entry["v"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Implies(
                                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, s, k))
                                                )
                                            )
                                        )
                            # U
                            elif node.label == 'U':
                                for sample_entry in sample_table:
                                    j = sample_entry["id"]
                                    startpos = sample_entry["startpos"]
                                    trace = sample_entry["prefix"]
                                    suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Or(
                                                    [
                                                        And(
                                                            [Bool('z_%s_%s_%s' % (rightid, f_1, f_2))] +
                                                            [
                                                                Bool('z_%s_%s_%s' % (leftid, fp_1, fp_2))
                                                                for fp_1, fp_2 in
                                                                BET_2(j, k, f_1, f_2, startpos, len(trace))
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

                                    for k in range(len(suffix_entry["u"])):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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
                                    for k in range(len(suffix_entry["u"]), len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Or(
                                                    [
                                                        And(
                                                            [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                                            [
                                                                Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                                for k_pp in
                                                                BET_1(suffix_entry["u"], suffix_entry["v"], k, k_p)
                                                            ]
                                                        )
                                                        for k_p in range(len(suffix_entry["u"]), len(trace))
                                                    ]
                                                )
                                            )
                                        )
                            # ?b
                            elif '?b' in node.label:
                                # finite prefix in sample-table
                                for sample_entry in sample_table:
                                    j = sample_entry["id"]
                                    startpos = sample_entry["startpos"]
                                    trace = sample_entry["prefix"]
                                    suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                                    for k in range(len(trace)):
                                        # placeholder is &
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '&')),
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                And(
                                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, j, k))
                                                )
                                            )
                                        )
                                        # placeholder is |
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '|')),
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Or(
                                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, j, k))
                                                )
                                            )
                                        )
                                        # placeholder is ->
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '->')),
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Implies(
                                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, j, k))
                                                )
                                            )
                                        )
                                        # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, 'U')),
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Or(
                                                    [
                                                        And(
                                                            [Bool('z_%s_%s_%s' % (rightid, f_1, f_2))] +
                                                            [
                                                                Bool('z_%s_%s_%s' % (leftid, fp_1, fp_2))
                                                                for fp_1, fp_2 in
                                                                BET_2(j, k, f_1, f_2, startpos, len(trace))
                                                            ]
                                                        )
                                                        for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                                    ]
                                                )
                                            )
                                        )

                                # suffixes in suffix-table
                                for suffix_entry in suffix_table:
                                    s = suffix_entry["sid"]
                                    trace = suffix_entry["u"] + suffix_entry["v"]

                                    for k in range(len(trace)):
                                        # placeholder is &
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '&')),
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                And(
                                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, s, k))
                                                )
                                            )
                                        )
                                        # placeholder is |
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '|')),
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Or(
                                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, s, k))
                                                )
                                            )
                                        )
                                        # placeholder is ->
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '->')),
                                                    Bool('l_%s_%s' % (node_id, leftid)),
                                                    Bool('r_%s_%s' % (node_id, rightid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Implies(
                                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                    Bool('z_%s_%s_%s' % (rightid, s, k))
                                                )
                                            )
                                        )
                                        # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                                        if k in range(len(suffix_entry["u"])):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('x_%s_%s' % (node_id, 'U')),
                                                        Bool('l_%s_%s' % (node_id, leftid)),
                                                        Bool('r_%s_%s' % (node_id, rightid))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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
                                        else:  # k in range(len(suffix_entry["u"]), len(trace)):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('x_%s_%s' % (node_id, 'U')),
                                                        Bool('l_%s_%s' % (node_id, leftid)),
                                                        Bool('r_%s_%s' % (node_id, rightid))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                    Or(
                                                        [
                                                            And(
                                                                [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                                                [
                                                                    Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                                    for k_pp in
                                                                    BET_1(suffix_entry["u"], suffix_entry["v"], k,
                                                                          k_p)
                                                                ]
                                                            )
                                                            for k_p in range(len(suffix_entry["u"]), len(trace))
                                                        ]
                                                    )
                                                )
                                            )
                    # ----------------------------------- TODO
                    else:
                        rightid = node.right.identifier
                        # & (And)
                        if node.label == '&':
                            for sample_entry in sample_table:
                                j = sample_entry["id"]
                                trace = sample_entry["prefix"]

                                for k in range(len(trace)):
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                            And(
                                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                Bool('z_%s_%s_%s' % (rightid, j, k))
                                            )
                                        )
                                    )

                            for suffix_entry in suffix_table:
                                s = suffix_entry["sid"]
                                trace = suffix_entry["u"] + suffix_entry["v"]

                                for k in range(len(trace)):
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                            And(
                                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                Bool('z_%s_%s_%s' % (rightid, s, k))
                                            )
                                        )
                                    )
                        # | (Or)
                        elif node.label == '|':
                            for sample_entry in sample_table:
                                j = sample_entry["id"]
                                trace = sample_entry["prefix"]

                                for k in range(len(trace)):
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                            Or(
                                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                Bool('z_%s_%s_%s' % (rightid, j, k))
                                            )
                                        )
                                    )

                            for suffix_entry in suffix_table:
                                s = suffix_entry["sid"]
                                trace = suffix_entry["u"] + suffix_entry["v"]

                                for k in range(len(trace)):
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                            Or(
                                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                Bool('z_%s_%s_%s' % (rightid, s, k))
                                            )
                                        )
                                    )
                        # ->
                        elif node.label == '->':
                            for sample_entry in sample_table:
                                j = sample_entry["id"]
                                trace = sample_entry["prefix"]

                                for k in range(len(trace)):
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                            Implies(
                                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                Bool('z_%s_%s_%s' % (rightid, j, k))
                                            )
                                        )
                                    )

                            for suffix_entry in suffix_table:
                                s = suffix_entry["sid"]
                                trace = suffix_entry["u"] + suffix_entry["v"]

                                for k in range(len(trace)):
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                            Implies(
                                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                Bool('z_%s_%s_%s' % (rightid, s, k))
                                            )
                                        )
                                    )
                        # U
                        elif node.label == 'U':
                            for sample_entry in sample_table:
                                j = sample_entry["id"]
                                startpos = sample_entry["startpos"]
                                trace = sample_entry["prefix"]
                                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                                for k in range(len(trace)):
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                            Or(
                                                [
                                                    And(
                                                        [Bool('z_%s_%s_%s' % (rightid, f_1, f_2))] +
                                                        [
                                                            Bool('z_%s_%s_%s' % (leftid, fp_1, fp_2))
                                                            for fp_1, fp_2 in
                                                            BET_2(j, k, f_1, f_2, startpos, len(trace))
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

                                for k in range(len(suffix_entry["u"])):
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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
                                for k in range(len(suffix_entry["u"]), len(trace)):
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                            Or(
                                                [
                                                    And(
                                                        [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                                        [
                                                            Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                            for k_pp in
                                                            BET_1(suffix_entry["u"], suffix_entry["v"], k, k_p)
                                                        ]
                                                    )
                                                    for k_p in range(len(suffix_entry["u"]), len(trace))
                                                ]
                                            )
                                        )
                                    )
                        # ?b
                        elif '?b' in node.label:
                            # finite prefix in sample-table
                            for sample_entry in sample_table:
                                j = sample_entry["id"]
                                startpos = sample_entry["startpos"]
                                trace = sample_entry["prefix"]
                                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                                for k in range(len(trace)):
                                    # placeholder is &
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('x_%s_%s' % (node_id, '&')),
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                            And(
                                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                Bool('z_%s_%s_%s' % (rightid, j, k))
                                            )
                                        )
                                    )
                                    # placeholder is |
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('x_%s_%s' % (node_id, '|')),
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                            Or(
                                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                Bool('z_%s_%s_%s' % (rightid, j, k))
                                            )
                                        )
                                    )
                                    # placeholder is ->
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('x_%s_%s' % (node_id, '->')),
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                            Implies(
                                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                                Bool('z_%s_%s_%s' % (rightid, j, k))
                                            )
                                        )
                                    )
                                    # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('x_%s_%s' % (node_id, 'U')),
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                            Or(
                                                [
                                                    And(
                                                        [Bool('z_%s_%s_%s' % (rightid, f_1, f_2))] +
                                                        [
                                                            Bool('z_%s_%s_%s' % (leftid, fp_1, fp_2))
                                                            for fp_1, fp_2 in
                                                            BET_2(j, k, f_1, f_2, startpos, len(trace))
                                                        ]
                                                    )
                                                    for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                                ]
                                            )
                                        )
                                    )

                            # suffixes in suffix-table
                            for suffix_entry in suffix_table:
                                s = suffix_entry["sid"]
                                trace = suffix_entry["u"] + suffix_entry["v"]

                                for k in range(len(trace)):
                                    # placeholder is &
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('x_%s_%s' % (node_id, '&')),
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                            And(
                                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                Bool('z_%s_%s_%s' % (rightid, s, k))
                                            )
                                        )
                                    )
                                    # placeholder is |
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('x_%s_%s' % (node_id, '|')),
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                            Or(
                                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                Bool('z_%s_%s_%s' % (rightid, s, k))
                                            )
                                        )
                                    )
                                    # placeholder is ->
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('x_%s_%s' % (node_id, '->')),
                                                Bool('l_%s_%s' % (node_id, leftid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                            Implies(
                                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                                Bool('z_%s_%s_%s' % (rightid, s, k))
                                            )
                                        )
                                    )
                                    # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                                    if k in range(len(suffix_entry["u"])):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, 'U')),
                                                    Bool('l_%s_%s' % (node_id, leftid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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
                                    else:  # k in range(len(suffix_entry["u"]), len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, 'U')),
                                                    Bool('l_%s_%s' % (node_id, leftid))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Or(
                                                    [
                                                        And(
                                                            [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                                            [
                                                                Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                                for k_pp in
                                                                BET_1(suffix_entry["u"], suffix_entry["v"], k,
                                                                      k_p)
                                                            ]
                                                        )
                                                        for k_p in range(len(suffix_entry["u"]), len(trace))
                                                    ]
                                                )
                                            )
                                        )

            # ----------------------------------- TODO
            else:  # left_is_type_0 == False
                leftid = node.left.identifier
                for rightid in pos_child_id:
                    # & (And)
                    if node.label == '&':
                        for sample_entry in sample_table:
                            j = sample_entry["id"]
                            trace = sample_entry["prefix"]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        And(
                                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                                            Bool('z_%s_%s_%s' % (rightid, j, k))
                                        )
                                    )
                                )

                        for suffix_entry in suffix_table:
                            s = suffix_entry["sid"]
                            trace = suffix_entry["u"] + suffix_entry["v"]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        And(
                                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                                            Bool('z_%s_%s_%s' % (rightid, s, k))
                                        )
                                    )
                                )
                    # | (Or)
                    elif node.label == '|':
                        for sample_entry in sample_table:
                            j = sample_entry["id"]
                            trace = sample_entry["prefix"]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Or(
                                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                                            Bool('z_%s_%s_%s' % (rightid, j, k))
                                        )
                                    )
                                )

                        for suffix_entry in suffix_table:
                            s = suffix_entry["sid"]
                            trace = suffix_entry["u"] + suffix_entry["v"]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Or(
                                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                                            Bool('z_%s_%s_%s' % (rightid, s, k))
                                        )
                                    )
                                )
                    # ->
                    elif node.label == '->':
                        for sample_entry in sample_table:
                            j = sample_entry["id"]
                            trace = sample_entry["prefix"]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Implies(
                                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                                            Bool('z_%s_%s_%s' % (rightid, j, k))
                                        )
                                    )
                                )

                        for suffix_entry in suffix_table:
                            s = suffix_entry["sid"]
                            trace = suffix_entry["u"] + suffix_entry["v"]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Implies(
                                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                                            Bool('z_%s_%s_%s' % (rightid, s, k))
                                        )
                                    )
                                )
                    # U
                    elif node.label == 'U':
                        for sample_entry in sample_table:
                            j = sample_entry["id"]
                            startpos = sample_entry["startpos"]
                            trace = sample_entry["prefix"]
                            suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Or(
                                            [
                                                And(
                                                    [Bool('z_%s_%s_%s' % (rightid, f_1, f_2))] +
                                                    [
                                                        Bool('z_%s_%s_%s' % (leftid, fp_1, fp_2))
                                                        for fp_1, fp_2 in
                                                        BET_2(j, k, f_1, f_2, startpos, len(trace))
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

                            for k in range(len(suffix_entry["u"])):
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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
                            for k in range(len(suffix_entry["u"]), len(trace)):
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Or(
                                            [
                                                And(
                                                    [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                                    [
                                                        Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                        for k_pp in
                                                        BET_1(suffix_entry["u"], suffix_entry["v"], k, k_p)
                                                    ]
                                                )
                                                for k_p in range(len(suffix_entry["u"]), len(trace))
                                            ]
                                        )
                                    )
                                )
                    # ?b
                    elif '?b' in node.label:
                        # finite prefix in sample-table
                        for sample_entry in sample_table:
                            j = sample_entry["id"]
                            startpos = sample_entry["startpos"]
                            trace = sample_entry["prefix"]
                            suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                            for k in range(len(trace)):
                                # placeholder is &
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_%s' % (node_id, '&')),
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        And(
                                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                                            Bool('z_%s_%s_%s' % (rightid, j, k))
                                        )
                                    )
                                )
                                # placeholder is |
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_%s' % (node_id, '|')),
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Or(
                                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                                            Bool('z_%s_%s_%s' % (rightid, j, k))
                                        )
                                    )
                                )
                                # placeholder is ->
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_%s' % (node_id, '->')),
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Implies(
                                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                                            Bool('z_%s_%s_%s' % (rightid, j, k))
                                        )
                                    )
                                )
                                # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_%s' % (node_id, 'U')),
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Or(
                                            [
                                                And(
                                                    [Bool('z_%s_%s_%s' % (rightid, f_1, f_2))] +
                                                    [
                                                        Bool('z_%s_%s_%s' % (leftid, fp_1, fp_2))
                                                        for fp_1, fp_2 in
                                                        BET_2(j, k, f_1, f_2, startpos, len(trace))
                                                    ]
                                                )
                                                for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                            ]
                                        )
                                    )
                                )

                        # suffixes in suffix-table
                        for suffix_entry in suffix_table:
                            s = suffix_entry["sid"]
                            trace = suffix_entry["u"] + suffix_entry["v"]

                            for k in range(len(trace)):
                                # placeholder is &
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_%s' % (node_id, '&')),
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        And(
                                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                                            Bool('z_%s_%s_%s' % (rightid, s, k))
                                        )
                                    )
                                )
                                # placeholder is |
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_%s' % (node_id, '|')),
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Or(
                                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                                            Bool('z_%s_%s_%s' % (rightid, s, k))
                                        )
                                    )
                                )
                                # placeholder is ->
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_%s' % (node_id, '->')),
                                            Bool('r_%s_%s' % (node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Implies(
                                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                                            Bool('z_%s_%s_%s' % (rightid, s, k))
                                        )
                                    )
                                )
                                # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                                if k in range(len(suffix_entry["u"])):
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('x_%s_%s' % (node_id, 'U')),
                                                Bool('r_%s_%s' % (node_id, rightid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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
                                else:  # k in range(len(suffix_entry["u"]), len(trace)):
                                    solver_1.add(
                                        Implies(
                                            And(
                                                Bool('x_%s_%s' % (node_id, 'U')),
                                                Bool('r_%s_%s' % (node_id, rightid))
                                            ),  # ->
                                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                            Or(
                                                [
                                                    And(
                                                        [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                                        [
                                                            Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                            for k_pp in
                                                            BET_1(suffix_entry["u"], suffix_entry["v"], k,
                                                                  k_p)
                                                        ]
                                                    )
                                                    for k_p in range(len(suffix_entry["u"]), len(trace))
                                                ]
                                            )
                                        )
                                    )
# ----------------------------------- TODO
    # initial cycle-Constraints for sketch
    initial_cycleConstraints(solver_1, sketch_nodes, parent_nodes, alphabet)

    if timing:
        print('initial setup', t.tocvalue())
        t.tic()

    # build SAT-formula, check satisfiability, loop until solution found or maximal size reached
    while current_size <= finalSize:
        if print_output:
            print('looking for formula of size', current_size)

        solver_2 = Solver()

        # add new cycle-Constraints in each but the first iteration
        if new_node_id != -1:
            loop_cycleConstraints(solver_1, parent_nodes, additional_node_list, new_node_id, identifier_list,
                                  alphabet)
# ----------------------------------- TODO
        # parent nodes:
        for node in parent_nodes:
            node_id = node.identifier
            # child can not have id 0 (root) or the one of the node itself (would form loop)
            pos_child_id = [id for id in identifier_list if id != 0 and id != node_id]
            if node._isUnary():
                # Structure (unary)
                # at least one left child
                solver_2.add(
                    Or(
                        [Bool('l_%s_%s' % (node_id, pos)) for pos in pos_child_id]
                    )
                )

                # in first iteration new_node_id == -1, so initial Constraints are already complete for this iteration
                # otherwise add new Constraints ensuring at most one left child
                if new_node_id != -1:
                    solver_1.add(
                        [
                            Or(
                                Not(Bool('l_%s_%s' % (node_id, pos))),
                                Not(Bool('l_%s_%s' % (node_id, new_node_id)))
                            )
                            for pos in [id for id in identifier_list if id != new_node_id]
                        ]
                    )
# ----------------------------------- TODO
                # Evaluation (unary):
                # in first iteration new_node_id == -1, so initial Constraints are already complete for this iteration
                # otherwise add new Constraints ensuring correct evaluation if new_node is left child
                if new_node_id != -1:
                    # ! (Not)
                    if node.label == '!':
                        for sample_entry in sample_table:
                            j = sample_entry["id"]
                            trace = sample_entry["prefix"]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        Bool('l_%s_%s' % (node_id, new_node_id)),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Not(Bool('z_%s_%s_%s' % (new_node_id, j, k)))
                                    )
                                )
                        for suffix_entry in suffix_table:
                            s = suffix_entry["sid"]
                            trace = suffix_entry["u"] + suffix_entry["v"]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        Bool('l_%s_%s' % (node_id, new_node_id)),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Not(Bool('z_%s_%s_%s' % (new_node_id, s, k)))
                                    )
                                )
                    # X
                    elif node.label == 'X':
                        for sample_entry in sample_table:
                            j = sample_entry["id"]
                            trace = sample_entry["prefix"]

                            for k in range(len(trace)):
                                next_1, next_2 = suc_2(sample_entry, k)

                                solver_1.add(
                                    Implies(
                                        Bool('l_%s_%s' % (node_id, new_node_id)),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Bool('z_%s_%s_%s' % (new_node_id, next_1, next_2))
                                    )
                                )

                        for suffix_entry in suffix_table:
                            s = suffix_entry["sid"]
                            trace = suffix_entry["u"] + suffix_entry["v"]

                            for k in range(len(trace)):
                                next = suc_1(suffix_entry["u"], suffix_entry["v"], k)

                                solver_1.add(
                                    Implies(
                                        Bool('l_%s_%s' % (node_id, new_node_id)),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Bool('z_%s_%s_%s' % (new_node_id, s, next))
                                    )
                                )
                    # F
                    elif node.label == 'F':
                        for sample_entry in sample_table:
                            j = sample_entry["id"]
                            trace = sample_entry["prefix"]
                            suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        Bool('l_%s_%s' % (node_id, new_node_id)),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Or(
                                            [
                                                Bool('z_%s_%s_%s' % (new_node_id, f_1, f_2))
                                                for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                            ]
                                        )
                                    )
                                )

                        for suffix_entry in suffix_table:
                            s = suffix_entry["sid"]
                            trace = suffix_entry["u"] + suffix_entry["v"]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        Bool('l_%s_%s' % (node_id, new_node_id)),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Or(
                                            [
                                                Bool('z_%s_%s_%s' % (new_node_id, s, f))
                                                for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                            ]
                                        )
                                    )
                                )
                    # G
                    elif node.label == 'G':
                        for sample_entry in sample_table:
                            j = sample_entry["id"]
                            trace = sample_entry["prefix"]
                            suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        Bool('l_%s_%s' % (node_id, new_node_id)),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        And(
                                            [
                                                Bool('z_%s_%s_%s' % (new_node_id, f_1, f_2))
                                                for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                            ]
                                        )
                                    )
                                )

                        for suffix_entry in suffix_table:
                            s = suffix_entry["sid"]
                            trace = suffix_entry["u"] + suffix_entry["v"]

                            for k in range(len(trace)):
                                solver_1.add(
                                    Implies(
                                        Bool('l_%s_%s' % (node_id, new_node_id)),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        And(
                                            [
                                                Bool('z_%s_%s_%s' % (new_node_id, s, f))
                                                for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                            ]
                                        )
                                    )
                                )
                    # ?u
                    elif '?u' in node.label:
                        # finite prefix in sample-table
                        for sample_entry in sample_table:
                            j = sample_entry["id"]
                            trace = sample_entry["prefix"]
                            suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                            for k in range(len(trace)):
                                # placeholder is !
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_!' % node_id),
                                            Bool('l_%s_%s' % (node_id, new_node_id))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Not(
                                            Bool('z_%s_%s_%s' % (new_node_id, j, k))
                                        )
                                    )
                                )
                                # placeholder is X
                                next_1, next_2 = suc_2(sample_entry, k)
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_X' % node_id),
                                            Bool('l_%s_%s' % (node_id, new_node_id))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Bool('z_%s_%s_%s' % (new_node_id, next_1, next_2))
                                    )
                                )
                                # placeholder is F
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_F' % node_id),
                                            Bool('l_%s_%s' % (node_id, new_node_id))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        Or(
                                            [
                                                Bool('z_%s_%s_%s' % (new_node_id, f_1, f_2))
                                                for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                            ]
                                        )
                                    )
                                )
                                # placeholder is G
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_G' % node_id),
                                            Bool('l_%s_%s' % (node_id, new_node_id))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                        And(
                                            [
                                                Bool('z_%s_%s_%s' % (new_node_id, f_1, f_2))
                                                for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                            ]
                                        )
                                    )
                                )

                        # suffixes in suffix-table
                        for suffix_entry in suffix_table:
                            s = suffix_entry["sid"]
                            trace = suffix_entry["u"] + suffix_entry["v"]

                            for k in range(len(trace)):
                                # placeholder is !
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_!' % node_id),
                                            Bool('l_%s_%s' % (node_id, new_node_id))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Not(
                                            Bool('z_%s_%s_%s' % (new_node_id, s, k))
                                        )
                                    )
                                )
                                # placeholder is X
                                next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_X' % node_id),
                                            Bool('l_%s_%s' % (node_id, new_node_id))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Bool('z_%s_%s_%s' % (new_node_id, s, next))
                                    )
                                )
                                # placeholder is F
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_F' % node_id),
                                            Bool('l_%s_%s' % (node_id, new_node_id))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Or(
                                            [
                                                Bool('z_%s_%s_%s' % (new_node_id, s, f))
                                                for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                            ]
                                        )
                                    )
                                )
                                # placeholder is G
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_G' % node_id),
                                            Bool('l_%s_%s' % (node_id, new_node_id))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        And(
                                            [
                                                Bool('z_%s_%s_%s' % (new_node_id, s, f))
                                                for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                            ]
                                        )
                                    )
                                )
            # ----------------------------------- TODO
            else:   # node._isBinary()
                left_is_type_0 = False
                right_is_type_0 = False

                # Structure (binary)
                if '?' in node.left.label and not ('?u' in node.left.label or '?b' in node.left.label):
                    # left child is type-0 placeholder
                    left_is_type_0 = True
                    # at least one
                    solver_2.add(
                        Or(
                            [Bool('l_%s_%s' % (node_id, pos)) for pos in pos_child_id]
                        )
                    )
                    # in first iteration new_node_id == -1, so initial Constraints are already complete
                    # otherwise add new Constraints ensuring at most one left child
                    if new_node_id != -1:
                        solver_1.add(
                            [
                                Or(
                                    Not(Bool('l_%s_%s' % (node_id, pos))),
                                    Not(Bool('l_%s_%s' % (node_id, new_node_id)))
                                )
                                for pos in [id for id in identifier_list if id != new_node_id]
                            ]
                        )
                # ----------------------------------- TODO
                if '?' in node.right.label and not ('?u' in node.right.label or '?b' in node.right.label):
                    # right child is type-0 placeholder
                    right_is_type_0 = True
                    # at least one
                    solver_2.add(
                        Or(
                            [Bool('r_%s_%s' % (node_id, pos)) for pos in pos_child_id]
                        )
                    )
                    # in first iteration new_node_id == -1, so initial Constraints are already complete
                    # otherwise add new Constraints ensuring at most one left child
                    if new_node_id != -1:
                        solver_1.add(
                            [
                                Or(
                                    Not(Bool('r_%s_%s' % (node_id, pos))),
                                    Not(Bool('r_%s_%s' % (node_id, new_node_id)))
                                )
                                for pos in [id for id in identifier_list if id != new_node_id]
                            ]
                        )
                # ----------------------------------- TODO
                # Evaluation (binary)
                # in first iteration new_node_id == -1, so initial Constraints are already complete for this iteration
                # otherwise add new Constraints ensuring correct evaluation if new_node is one (or both) of the children
                if new_node_id != -1:
                    if left_is_type_0:
                        # loop over all possible ids
                        for other_id in pos_child_id:
                            # & (And)
                            if node.label == '&':
                                for sample_entry in sample_table:
                                    j = sample_entry["id"]
                                    trace = sample_entry["prefix"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                And(
                                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                                )
                                            )
                                        )

                                for suffix_entry in suffix_table:
                                    s = suffix_entry["sid"]
                                    trace = suffix_entry["u"] + suffix_entry["v"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                And(
                                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                                )
                                            )
                                        )
                            # | (Or)
                            elif node.label == '|':
                                for sample_entry in sample_table:
                                    j = sample_entry["id"]
                                    trace = sample_entry["prefix"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Or(
                                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                                )
                                            )
                                        )

                                for suffix_entry in suffix_table:
                                    s = suffix_entry["sid"]
                                    trace = suffix_entry["u"] + suffix_entry["v"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Or(
                                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                                )
                                            )
                                        )
                            # ->
                            elif node.label == '->':
                                for sample_entry in sample_table:
                                    j = sample_entry["id"]
                                    trace = sample_entry["prefix"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Implies(
                                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                                )
                                            )
                                        )

                                for suffix_entry in suffix_table:
                                    s = suffix_entry["sid"]
                                    trace = suffix_entry["u"] + suffix_entry["v"]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Implies(
                                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                                )
                                            )
                                        )
                            # U
                            elif node.label == 'U':
                                for sample_entry in sample_table:
                                    j = sample_entry["id"]
                                    startpos = sample_entry["startpos"]
                                    trace = sample_entry["prefix"]
                                    suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                                    for k in range(len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Or(
                                                    [
                                                        And(
                                                            [Bool('z_%s_%s_%s' % (other_id, f_1, f_2))] +
                                                            [
                                                                Bool('z_%s_%s_%s' % (new_node_id, fp_1, fp_2))
                                                                for fp_1, fp_2 in
                                                                BET_2(j, k, f_1, f_2, startpos, len(trace))
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

                                    for k in range(len(suffix_entry["u"])):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Or(
                                                    [
                                                        And(
                                                            [Bool('z_%s_%s_%s' % (other_id, s, k_p))] +
                                                            [
                                                                Bool('z_%s_%s_%s' % (new_node_id, s, k_pp))
                                                                for k_pp in range(k, k_p)
                                                            ]
                                                        )
                                                        for k_p in range(k, len(trace))
                                                    ]
                                                )
                                            )
                                        )
                                    for k in range(len(suffix_entry["u"]), len(trace)):
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Or(
                                                    [
                                                        And(
                                                            [Bool('z_%s_%s_%s' % (other_id, s, k_p))] +
                                                            [
                                                                Bool('z_%s_%s_%s' % (new_node_id, s, k_pp))
                                                                for k_pp in
                                                                BET_1(suffix_entry["u"], suffix_entry["v"], k, k_p)
                                                            ]
                                                        )
                                                        for k_p in range(len(suffix_entry["u"]), len(trace))
                                                    ]
                                                )
                                            )
                                        )
                            # ?b
                            elif '?b' in node.label:
                                # finite prefix in sample-table
                                for sample_entry in sample_table:
                                    j = sample_entry["id"]
                                    startpos = sample_entry["startpos"]
                                    trace = sample_entry["prefix"]
                                    suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                                    for k in range(len(trace)):
                                        # placeholder is &
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '&')),
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                And(
                                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                                )
                                            )
                                        )
                                        # placeholder is |
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '|')),
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Or(
                                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                                )
                                            )
                                        )
                                        # placeholder is ->
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '->')),
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Implies(
                                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                                )
                                            )
                                        )
                                        # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, 'U')),
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                Or(
                                                    [
                                                        And(
                                                            [Bool('z_%s_%s_%s' % (other_id, f_1, f_2))] +
                                                            [
                                                                Bool('z_%s_%s_%s' % (new_node_id, fp_1, fp_2))
                                                                for fp_1, fp_2 in
                                                                BET_2(j, k, f_1, f_2, startpos, len(trace))
                                                            ]
                                                        )
                                                        for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                                    ]
                                                )
                                            )
                                        )

                                # suffixes in suffix-table
                                for suffix_entry in suffix_table:
                                    s = suffix_entry["sid"]
                                    trace = suffix_entry["u"] + suffix_entry["v"]

                                    for k in range(len(trace)):
                                        # placeholder is &
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '&')),
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                And(
                                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                                )
                                            )
                                        )
                                        # placeholder is |
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '|')),
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Or(
                                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                                )
                                            )
                                        )
                                        # placeholder is ->
                                        solver_1.add(
                                            Implies(
                                                And(
                                                    Bool('x_%s_%s' % (node_id, '->')),
                                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                                    Bool('r_%s_%s' % (node_id, other_id))
                                                ),  # ->
                                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                Implies(
                                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)),
                                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                                )
                                            )
                                        )
                                        # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                                        if k in range(len(suffix_entry["u"])):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('x_%s_%s' % (node_id, 'U')),
                                                        Bool('l_%s_%s' % (node_id, new_node_id)),
                                                        Bool('r_%s_%s' % (node_id, other_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                    Or(
                                                        [
                                                            And(
                                                                [Bool('z_%s_%s_%s' % (other_id, s, k_p))] +
                                                                [
                                                                    Bool('z_%s_%s_%s' % (new_node_id, s, k_pp))
                                                                    for k_pp in range(k, k_p)
                                                                ]
                                                            )
                                                            for k_p in range(k, len(trace))
                                                        ]
                                                    )
                                                )
                                            )
                                        else:  # k in range(len(suffix_entry["u"]), len(trace)):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('x_%s_%s' % (node_id, 'U')),
                                                        Bool('l_%s_%s' % (node_id, new_node_id)),
                                                        Bool('r_%s_%s' % (node_id, other_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                    Or(
                                                        [
                                                            And(
                                                                [Bool('z_%s_%s_%s' % (other_id, s, k_p))] +
                                                                [
                                                                    Bool('z_%s_%s_%s' % (new_node_id, s, k_pp))
                                                                    for k_pp in
                                                                    BET_1(suffix_entry["u"], suffix_entry["v"], k,
                                                                          k_p)
                                                                ]
                                                            )
                                                            for k_p in range(len(suffix_entry["u"]), len(trace))
                                                        ]
                                                    )
                                                )
                                            )
                    if right_is_type_0:
                        # loop over all possible ids
                        for other_id in pos_child_id:
                            # if also left child is type-0, the case in which new node is both left and
                            # right child is already covered above, so don't repeat it
                            if not left_is_type_0 or other_id != new_node_id:
                                # & (And)
                                if node.label == '&':
                                    for sample_entry in sample_table:
                                        j = sample_entry["id"]
                                        trace = sample_entry["prefix"]

                                        for k in range(len(trace)):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                    And(
                                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, j, k))
                                                    )
                                                )
                                            )

                                    for suffix_entry in suffix_table:
                                        s = suffix_entry["sid"]
                                        trace = suffix_entry["u"] + suffix_entry["v"]

                                        for k in range(len(trace)):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                    And(
                                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, s, k))
                                                    )
                                                )
                                            )
                                # | (Or)
                                elif node.label == '|':
                                    for sample_entry in sample_table:
                                        j = sample_entry["id"]
                                        trace = sample_entry["prefix"]

                                        for k in range(len(trace)):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                    Or(
                                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, j, k))
                                                    )
                                                )
                                            )

                                    for suffix_entry in suffix_table:
                                        s = suffix_entry["sid"]
                                        trace = suffix_entry["u"] + suffix_entry["v"]

                                        for k in range(len(trace)):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                    Or(
                                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, s, k))
                                                    )
                                                )
                                            )
                                # ->
                                elif node.label == '->':
                                    for sample_entry in sample_table:
                                        j = sample_entry["id"]
                                        trace = sample_entry["prefix"]

                                        for k in range(len(trace)):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                    Implies(
                                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, j, k))
                                                    )
                                                )
                                            )

                                    for suffix_entry in suffix_table:
                                        s = suffix_entry["sid"]
                                        trace = suffix_entry["u"] + suffix_entry["v"]

                                        for k in range(len(trace)):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                    Implies(
                                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, s, k))
                                                    )
                                                )
                                            )
                                # U
                                elif node.label == 'U':
                                    for sample_entry in sample_table:
                                        j = sample_entry["id"]
                                        startpos = sample_entry["startpos"]
                                        trace = sample_entry["prefix"]
                                        suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                                        for k in range(len(trace)):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                    Or(
                                                        [
                                                            And(
                                                                [Bool('z_%s_%s_%s' % (new_node_id, f_1, f_2))] +
                                                                [
                                                                    Bool('z_%s_%s_%s' % (other_id, fp_1, fp_2))
                                                                    for fp_1, fp_2 in
                                                                    BET_2(j, k, f_1, f_2, startpos, len(trace))
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

                                        for k in range(len(suffix_entry["u"])):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                    Or(
                                                        [
                                                            And(
                                                                [Bool('z_%s_%s_%s' % (new_node_id, s, k_p))] +
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
                                        for k in range(len(suffix_entry["u"]), len(trace)):
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                    Or(
                                                        [
                                                            And(
                                                                [Bool('z_%s_%s_%s' % (new_node_id, s, k_p))] +
                                                                [
                                                                    Bool('z_%s_%s_%s' % (other_id, s, k_pp))
                                                                    for k_pp in
                                                                    BET_1(suffix_entry["u"], suffix_entry["v"], k, k_p)
                                                                ]
                                                            )
                                                            for k_p in range(len(suffix_entry["u"]), len(trace))
                                                        ]
                                                    )
                                                )
                                            )
                                # ?b
                                elif '?b' in node.label:
                                    # finite prefix in sample-table
                                    for sample_entry in sample_table:
                                        j = sample_entry["id"]
                                        startpos = sample_entry["startpos"]
                                        trace = sample_entry["prefix"]
                                        suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                                        for k in range(len(trace)):
                                            # placeholder is &
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('x_%s_%s' % (node_id, '&')),
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                    And(
                                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, j, k))
                                                    )
                                                )
                                            )
                                            # placeholder is |
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('x_%s_%s' % (node_id, '|')),
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                    Or(
                                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, j, k))
                                                    )
                                                )
                                            )
                                            # placeholder is ->
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('x_%s_%s' % (node_id, '->')),
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                    Implies(
                                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, j, k))
                                                    )
                                                )
                                            )
                                            # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('x_%s_%s' % (node_id, 'U')),
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                                    Or(
                                                        [
                                                            And(
                                                                [Bool('z_%s_%s_%s' % (new_node_id, f_1, f_2))] +
                                                                [
                                                                    Bool('z_%s_%s_%s' % (other_id, fp_1, fp_2))
                                                                    for fp_1, fp_2 in
                                                                    BET_2(j, k, f_1, f_2, startpos, len(trace))
                                                                ]
                                                            )
                                                            for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                                        ]
                                                    )
                                                )
                                            )

                                    # suffixes in suffix-table
                                    for suffix_entry in suffix_table:
                                        s = suffix_entry["sid"]
                                        trace = suffix_entry["u"] + suffix_entry["v"]

                                        for k in range(len(trace)):
                                            # placeholder is &
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('x_%s_%s' % (node_id, '&')),
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                    And(
                                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, s, k))
                                                    )
                                                )
                                            )
                                            # placeholder is |
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('x_%s_%s' % (node_id, '|')),
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                    Or(
                                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, s, k))
                                                    )
                                                )
                                            )
                                            # placeholder is ->
                                            solver_1.add(
                                                Implies(
                                                    And(
                                                        Bool('x_%s_%s' % (node_id, '->')),
                                                        Bool('l_%s_%s' % (node_id, other_id)),
                                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                                    ),  # ->
                                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                    Implies(
                                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                                        Bool('z_%s_%s_%s' % (new_node_id, s, k))
                                                    )
                                                )
                                            )
                                            # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                                            if k in range(len(suffix_entry["u"])):
                                                solver_1.add(
                                                    Implies(
                                                        And(
                                                            Bool('x_%s_%s' % (node_id, 'U')),
                                                            Bool('l_%s_%s' % (node_id, other_id)),
                                                            Bool('r_%s_%s' % (node_id, new_node_id))
                                                        ),  # ->
                                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                        Or(
                                                            [
                                                                And(
                                                                    [Bool('z_%s_%s_%s' % (new_node_id, s, k_p))] +
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
                                            else:  # k in range(len(suffix_entry["u"]), len(trace)):
                                                solver_1.add(
                                                    Implies(
                                                        And(
                                                            Bool('x_%s_%s' % (node_id, 'U')),
                                                            Bool('l_%s_%s' % (node_id, other_id)),
                                                            Bool('r_%s_%s' % (node_id, new_node_id))
                                                        ),  # ->
                                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                                        Or(
                                                            [
                                                                And(
                                                                    [Bool('z_%s_%s_%s' % (new_node_id, s, k_p))] +
                                                                    [
                                                                        Bool('z_%s_%s_%s' % (other_id, s, k_pp))
                                                                        for k_pp in
                                                                        BET_1(suffix_entry["u"], suffix_entry["v"], k,
                                                                              k_p)
                                                                    ]
                                                                )
                                                                for k_p in range(len(suffix_entry["u"]), len(trace))
                                                            ]
                                                        )
                                                    )
                                                )
        # ----------------------------------- TODO
        # additional nodes: nodes with are not contained in original sketch but also are not the new_node
        for node_id in additional_node_list:
            # left child
            # at least one
            solver_2.add(
                Or(
                    [Bool('l_%s_%s' % (node_id, pos)) for pos in identifier_list]
                )
            )
            # at most one, for new_node as left child only, other already in previous iteration
            solver_1.add(
                [
                    Or(
                        Not(Bool('l_%s_%s' % (node_id, pos))),
                        Not(Bool('l_%s_%s' % (node_id, new_node_id)))
                    )
                    for pos in [id for id in identifier_list if id != new_node_id]
                ]
            )
            # right child
            # at least one
            solver_2.add(
                Or(
                    [Bool('r_%s_%s' % (node_id, pos)) for pos in identifier_list]
                )
            )
            # at most one, for new_node as left child only, other already in previous iteration
            solver_1.add(
                [
                    Or(
                        Not(Bool('r_%s_%s' % (node_id, pos))),
                        Not(Bool('r_%s_%s' % (node_id, new_node_id)))
                    )
                    for pos in [id for id in identifier_list if id != new_node_id]
                ]
            )

            # Constraints encoding evaluation
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]
                startpos = sample_entry["startpos"]
                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                for k in range(len(trace)):
                    # unary operators: , for new_node as left child only, other already in previous iteration
                    # ! (Not)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (node_id, '!')),
                                Bool('l_%s_%s' % (node_id, new_node_id))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Not(Bool('z_%s_%s_%s' % (new_node_id, j, k)))
                        )
                    )

                    # X
                    next_1, next_2 = suc_2(sample_entry, k)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (node_id, 'X')),
                                Bool('l_%s_%s' % (node_id, new_node_id))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Bool('z_%s_%s_%s' % (new_node_id, next_1, next_2))
                        )
                    )

                    # F
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (node_id, 'F')),
                                Bool('l_%s_%s' % (node_id, new_node_id))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (new_node_id, f_1, f_2))
                                    for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                ]
                            )
                        )
                    )

                    # G
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (node_id, 'G')),
                                Bool('l_%s_%s' % (node_id, new_node_id))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (new_node_id, f_1, f_2))
                                    for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                ]
                            )
                        )
                    )
                    # binary operators: only for new_node being left or right child, other already in previous iteration
                    for other_id in [id for id in identifier_list if id != 0 and id != node_id]:
                        # & (And)
                        # new node is left child
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (node_id, '&')),
                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                    Bool('r_%s_%s' % (node_id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                And(
                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)),
                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                )
                            )
                        )
                        # new node is right child
                        # Case where new_node is both left and right child is already covered above
                        if other_id != new_node_id:
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (node_id, '&')),
                                        Bool('l_%s_%s' % (node_id, other_id)),
                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                    And(
                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                        Bool('z_%s_%s_%s' % (new_node_id, j, k))
                                    )
                                )
                            )

                        # | (Or)
                        # new node is left child
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (node_id, '|')),
                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                    Bool('r_%s_%s' % (node_id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)),
                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                )
                            )
                        )
                        # new node is right child
                        # Case where new_node is both left and right child is already covered above
                        if other_id != new_node_id:
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (node_id, '|')),
                                        Bool('l_%s_%s' % (node_id, other_id)),
                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                    Or(
                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                        Bool('z_%s_%s_%s' % (new_node_id, j, k))
                                    )
                                )
                            )

                        # ->
                        # new node is left child
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (node_id, '->')),
                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                    Bool('r_%s_%s' % (node_id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                Implies(
                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)),
                                    Bool('z_%s_%s_%s' % (other_id, j, k))
                                )
                            )
                        )
                        # new node is right child
                        # Case where new_node is both left and right child is already covered above
                        if other_id != new_node_id:
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (node_id, '->')),
                                        Bool('l_%s_%s' % (node_id, other_id)),
                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                    Implies(
                                        Bool('z_%s_%s_%s' % (other_id, j, k)),
                                        Bool('z_%s_%s_%s' % (new_node_id, j, k))
                                    )
                                )
                            )

                        # U
                        # new node is left child
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (node_id, 'U')),
                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                    Bool('r_%s_%s' % (node_id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                Or(
                                    [
                                        And(
                                            [Bool('z_%s_%s_%s' % (other_id, f_1, f_2))] +
                                            [
                                                Bool('z_%s_%s_%s' % (new_node_id, fp_1, fp_2))
                                                for fp_1, fp_2 in
                                                BET_2(j, k, f_1, f_2, startpos, len(trace))
                                            ]
                                        )
                                        for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                    ]
                                )
                            )
                        )
                        # new node is right child
                        # Case where new_node is both left and right child is already covered above
                        if other_id != new_node_id:
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (node_id, 'U')),
                                        Bool('l_%s_%s' % (node_id, other_id)),
                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                    Or(
                                        [
                                            And(
                                                [Bool('z_%s_%s_%s' % (new_node_id, f_1, f_2))] +
                                                [
                                                    Bool('z_%s_%s_%s' % (other_id, fp_1, fp_2))
                                                    for fp_1, fp_2 in
                                                    BET_2(j, k, f_1, f_2, startpos, len(trace))
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
                    # unary operators: , for new_node as left child only, other already in previous iteration
                    # ! (Not)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (node_id, '!')),
                                Bool('l_%s_%s' % (node_id, new_node_id))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Not(Bool('z_%s_%s_%s' % (new_node_id, s, k)))
                        )
                    )

                    # X
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (node_id, 'X')),
                                Bool('l_%s_%s' % (node_id, new_node_id))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Bool('z_%s_%s_%s' % (new_node_id, s, next))
                        )
                    )

                    # F
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (node_id, 'F')),
                                Bool('l_%s_%s' % (node_id, new_node_id))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (new_node_id, s, f))
                                    for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                ]
                            )
                        )
                    )
                    # G
                    solver_1.add(
                        Implies(
                            And(
                                Bool('x_%s_%s' % (node_id, 'G')),
                                Bool('l_%s_%s' % (node_id, new_node_id))
                            ),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (new_node_id, s, f))
                                    for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                ]
                            )
                        )
                    )
                    # binary operators: only for new_node being left or right child, other already in previous iteration
                    for other_id in [id for id in identifier_list if id != 0 and id != node_id]:
                        # & (And)
                        # new node is left child
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (node_id, '&')),
                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                    Bool('r_%s_%s' % (node_id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                And(
                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)),
                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                )
                            )
                        )
                        # new node is right child
                        # Case where new_node is both left and right child is already covered above
                        if other_id != new_node_id:
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (node_id, '&')),
                                        Bool('l_%s_%s' % (node_id, other_id)),
                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    And(
                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                        Bool('z_%s_%s_%s' % (new_node_id, s, k))
                                    )
                                )
                            )

                        # | (Or)
                        # new node is left child
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (node_id, '|')),
                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                    Bool('r_%s_%s' % (node_id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)),
                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                )
                            )
                        )
                        # new node is right child
                        # Case where new_node is both left and right child is already covered above
                        if other_id != new_node_id:
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (node_id, '|')),
                                        Bool('l_%s_%s' % (node_id, other_id)),
                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    Or(
                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                        Bool('z_%s_%s_%s' % (new_node_id, s, k))
                                    )
                                )
                            )

                        # ->
                        # new node is left child
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (node_id, '->')),
                                    Bool('l_%s_%s' % (node_id, new_node_id)),
                                    Bool('r_%s_%s' % (node_id, other_id))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                Implies(
                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)),
                                    Bool('z_%s_%s_%s' % (other_id, s, k))
                                )
                            )
                        )
                        # new node is right child
                        # Case where new_node is both left and right child is already covered above
                        if other_id != new_node_id:
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (node_id, '->')),
                                        Bool('l_%s_%s' % (node_id, other_id)),
                                        Bool('r_%s_%s' % (node_id, new_node_id))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    Implies(
                                        Bool('z_%s_%s_%s' % (other_id, s, k)),
                                        Bool('z_%s_%s_%s' % (new_node_id, s, k))
                                    )
                                )
                            )

                        # U
                        # new node is left child
                        if k < len(suffix_entry["u"]):
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (node_id, 'U')),
                                        Bool('l_%s_%s' % (node_id, new_node_id)),
                                        Bool('r_%s_%s' % (node_id, other_id))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    Or(
                                        [
                                            And(
                                                [Bool('z_%s_%s_%s' % (other_id, s, k_p))] +
                                                [
                                                    Bool('z_%s_%s_%s' % (new_node_id, s, k_pp))
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
                                        Bool('x_%s_%s' % (node_id, 'U')),
                                        Bool('l_%s_%s' % (node_id, new_node_id)),
                                        Bool('r_%s_%s' % (node_id, other_id))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                    Or(
                                        [
                                            And(
                                                [Bool('z_%s_%s_%s' % (other_id, s, k_p))] +
                                                [
                                                    Bool('z_%s_%s_%s' % (new_node_id, s, k_pp))
                                                    for k_pp in
                                                    BET_1(suffix_entry["u"], suffix_entry["v"], k,
                                                          k_p)
                                                ]
                                            )
                                            for k_p in range(len(suffix_entry["u"]), len(trace))
                                        ]
                                    )
                                )
                            )
                        # new node is right child
                        # Case where new_node is both left and right child is already covered above
                        if other_id != new_node_id:
                            if k < len(suffix_entry["u"]):
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_%s' % (node_id, 'U')),
                                            Bool('l_%s_%s' % (node_id, other_id)),
                                            Bool('r_%s_%s' % (node_id, new_node_id))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Or(
                                            [
                                                And(
                                                    [Bool('z_%s_%s_%s' % (new_node_id, s, k_p))] +
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
                            else:  # k in range(len(suffix_entry["u"]), len(trace))
                                solver_1.add(
                                    Implies(
                                        And(
                                            Bool('x_%s_%s' % (node_id, 'U')),
                                            Bool('l_%s_%s' % (node_id, other_id)),
                                            Bool('r_%s_%s' % (node_id, new_node_id))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                        Or(
                                            [
                                                And(
                                                    [Bool('z_%s_%s_%s' % (new_node_id, s, k_p))] +
                                                    [
                                                        Bool('z_%s_%s_%s' % (other_id, s, k_pp))
                                                        for k_pp in
                                                        BET_1(suffix_entry["u"], suffix_entry["v"], k,
                                                              k_p)
                                                    ]
                                                )
                                                for k_p in range(len(suffix_entry["u"]), len(trace))
                                            ]
                                        )
                                    )
                                )
        # ----------------------------------- TODO
        # new node: added in this iteration. In initial iteration new_node_id == -1
        if new_node_id != -1:
            # children cannot have id 0 (root) or the one of the node itself (loop)
            pos_child_id = [id for id in identifier_list if id != 0 and id != new_node_id]
            # except when the node has to be a leaf and therefore the children can be ignored
            if len(pos_child_id) == 0:
                pos_child_id = [new_node_id]

            # at least one label among all labels (operators + alphabet)
            solver_1.add(
                Or(
                    [Bool('x_%s_%s' % (new_node_id, label)) for label in possible_labels]
                )
            )
            # at most one label among all labels
            solver_1.add(
                [
                    And(
                        [
                            Or(
                                Not(Bool('x_%s_%s' % (new_node_id, label))),
                                Not(Bool('x_%s_%s' % (new_node_id, label2)))
                            )
                            for label2 in possible_labels[i+1:]
                        ]
                    )
                    for i, label in enumerate(possible_labels[:-1])
                ]
            )

            # left child
            # at least one
            solver_2.add(
                Or(
                    [Bool('l_%s_%s' % (new_node_id, pos)) for pos in pos_child_id]
                )
            )
            # at most one
            solver_1.add(
                [
                    And(
                        [
                            Or(
                                Not(Bool('l_%s_%s' % (new_node_id, pos_1))),
                                Not(Bool('l_%s_%s' % (new_node_id, pos_2)))
                            )
                            for pos_2 in identifier_list[i+1:]
                        ]
                    )
                    for i, pos_1 in enumerate(identifier_list[:-1])
                ]
            )
            # right child
            # at least one
            solver_2.add(
                Or(
                    [Bool('r_%s_%s' % (new_node_id, pos)) for pos in pos_child_id]
                )
            )
            # at most one
            solver_1.add(
                [
                    And(
                        [
                            Or(
                                Not(Bool('r_%s_%s' % (new_node_id, pos_1))),
                                Not(Bool('r_%s_%s' % (new_node_id, pos_2)))
                            )
                            for pos_2 in identifier_list[i+1:]
                        ]
                    )
                    for i, pos_1 in enumerate(identifier_list[:-1])
                ]
            )

            # Constraints encoding evaluation
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]
                startpos = sample_entry["startpos"]
                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                for k in range(len(trace)):
                    # atomic proposition
                    for ap in alphabet:
                        if trace[k][sample.letter2pos[ap]] == 1:
                            solver_1.add(
                                Implies(
                                    Bool('x_%s_%s' % (new_node_id, ap)),  # ->
                                    Bool('z_%s_%s_%s' % (new_node_id, j, k))
                                )
                            )
                        else:
                            solver_1.add(
                                Implies(
                                    Bool('x_%s_%s' % (new_node_id, ap)),  # ->
                                    Not(Bool('z_%s_%s_%s' % (new_node_id, j, k)))
                                )
                            )

                    for leftid in pos_child_id:
                        # unary operators
                        # ! (Not)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (new_node_id, '!')),
                                    Bool('l_%s_%s' % (new_node_id, leftid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (new_node_id, j, k)) ==
                                Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                            )
                        )

                        # X
                        next_1, next_2 = suc_2(sample_entry, k)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (new_node_id, 'X')),
                                    Bool('l_%s_%s' % (new_node_id, leftid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (new_node_id, j, k)) ==
                                Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                            )
                        )

                        # F
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (new_node_id, 'F')),
                                    Bool('l_%s_%s' % (new_node_id, leftid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (new_node_id, j, k)) ==
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
                                    Bool('x_%s_%s' % (new_node_id, 'G')),
                                    Bool('l_%s_%s' % (new_node_id, leftid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (new_node_id, j, k)) ==
                                And(
                                    [
                                        Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                                        for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                                    ]
                                )
                            )
                        )

                        for rightid in pos_child_id:
                            # binary operators
                            # & (And)
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (new_node_id, '&')),
                                        Bool('l_%s_%s' % (new_node_id, leftid)),
                                        Bool('r_%s_%s' % (new_node_id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)) ==
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
                                        Bool('x_%s_%s' % (new_node_id, '|')),
                                        Bool('l_%s_%s' % (new_node_id, leftid)),
                                        Bool('r_%s_%s' % (new_node_id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)) ==
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
                                        Bool('x_%s_%s' % (new_node_id, '->')),
                                        Bool('l_%s_%s' % (new_node_id, leftid)),
                                        Bool('r_%s_%s' % (new_node_id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)) ==
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
                                        Bool('x_%s_%s' % (new_node_id, 'U')),
                                        Bool('l_%s_%s' % (new_node_id, leftid)),
                                        Bool('r_%s_%s' % (new_node_id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (new_node_id, j, k)) ==
                                    Or(
                                        [
                                            And(
                                                [Bool('z_%s_%s_%s' % (rightid, f_1, f_2))] +
                                                [
                                                    Bool('z_%s_%s_%s' % (leftid, fp_1, fp_2))
                                                    for fp_1, fp_2 in
                                                    BET_2(j, k, f_1, f_2, startpos, len(trace))
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
                    # atomic proposition
                    for ap in alphabet:
                        if trace[k][sample.letter2pos[ap]] == 1:
                            solver_1.add(
                                Implies(
                                    Bool('x_%s_%s' % (new_node_id, ap)),  # ->
                                    Bool('z_%s_%s_%s' % (new_node_id, s, k))
                                )
                            )
                        else:
                            solver_1.add(
                                Implies(
                                    Bool('x_%s_%s' % (new_node_id, ap)),  # ->
                                    Not(Bool('z_%s_%s_%s' % (new_node_id, s, k)))
                                )
                            )

                    for leftid in pos_child_id:
                        # unary operators
                        # ! (Not)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (new_node_id, '!')),
                                    Bool('l_%s_%s' % (new_node_id, leftid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (new_node_id, s, k)) ==
                                Not(Bool('z_%s_%s_%s' % (leftid, s, k)))
                            )
                        )

                        # X
                        next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (new_node_id, 'X')),
                                    Bool('l_%s_%s' % (new_node_id, leftid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (new_node_id, s, k)) ==
                                Bool('z_%s_%s_%s' % (leftid, s, next))
                            )
                        )

                        # F
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (new_node_id, 'F')),
                                    Bool('l_%s_%s' % (new_node_id, leftid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (new_node_id, s, k)) ==
                                Or(
                                    [
                                        Bool('z_%s_%s_%s' % (leftid, s, f))
                                        for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                    ]
                                )
                            )
                        )

                        # G
                        solver_1.add(
                            Implies(
                                And(
                                    Bool('x_%s_%s' % (new_node_id, 'G')),
                                    Bool('l_%s_%s' % (new_node_id, leftid))
                                ),  # ->
                                Bool('z_%s_%s_%s' % (new_node_id, s, k)) ==
                                And(
                                    [
                                        Bool('z_%s_%s_%s' % (leftid, s, f))
                                        for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                    ]
                                )
                            )
                        )

                        for rightid in pos_child_id:
                            # binary operators
                            # & (And)
                            solver_1.add(
                                Implies(
                                    And(
                                        Bool('x_%s_%s' % (new_node_id, '&')),
                                        Bool('l_%s_%s' % (new_node_id, leftid)),
                                        Bool('r_%s_%s' % (new_node_id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)) ==
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
                                        Bool('x_%s_%s' % (new_node_id, '|')),
                                        Bool('l_%s_%s' % (new_node_id, leftid)),
                                        Bool('r_%s_%s' % (new_node_id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)) ==
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
                                        Bool('x_%s_%s' % (new_node_id, '->')),
                                        Bool('l_%s_%s' % (new_node_id, leftid)),
                                        Bool('r_%s_%s' % (new_node_id, rightid))
                                    ),  # ->
                                    Bool('z_%s_%s_%s' % (new_node_id, s, k)) ==
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
                                            Bool('x_%s_%s' % (new_node_id, 'U')),
                                            Bool('l_%s_%s' % (new_node_id, leftid)),
                                            Bool('r_%s_%s' % (new_node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (new_node_id, s, k)) ==
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
                                            Bool('x_%s_%s' % (new_node_id, 'U')),
                                            Bool('l_%s_%s' % (new_node_id, leftid)),
                                            Bool('r_%s_%s' % (new_node_id, rightid))
                                        ),  # ->
                                        Bool('z_%s_%s_%s' % (new_node_id, s, k)) ==
                                        Or(
                                            [
                                                And(
                                                    [Bool('z_%s_%s_%s' % (rightid, s, k_p))] +
                                                    [
                                                        Bool('z_%s_%s_%s' % (leftid, s, k_pp))
                                                        for k_pp in
                                                        BET_1(suffix_entry["u"], suffix_entry["v"], k,
                                                              k_p)
                                                    ]
                                                )
                                                for k_p in range(len(suffix_entry["u"]), len(trace))
                                            ]
                                        )
                                    )
                                )
# ------------------------------ TODO
        # Construct solver s = s1 + s2
        solver = Solver()
        solver.add(solver_1.assertions())
        solver.add(solver_2.assertions())
        if timing:
            print('iteration - setup', t.tocvalue())
            t.tic()

        if solver.check() == z3.sat:
            if timing:
                print('solving', t.tocvalue())
                t.tic()

            if print_output:
                print("building solution")

            # construct substitutions from model
            m = solver.model()

            if print_model:
                filename = "z3test.smt2"
                with open(filename, mode='w') as f:
                    f.write(solver.to_smt2())

                file = 'solution.txt'
                f = open(file, 'w')
                for e in m:
                    f.write(str(e) + ', ' + str(is_true(m[e])) + '\n')
                f.close()

            LTL = construct_Sketch_from_Model_cycle_free(0, m, sample.alphabet, identifier_list)
            LTL.reduce()

            if print_output:
                print(LTL.prettyPrint(True))
                print(sample.isFormulaConsistent(LTL))

            break

        else:
            if timing:
                print('solving', t.tocvalue())
                t.tic()

            if new_node_id != -1:
                additional_node_list.append(new_node_id)
            new_node_id = max(identifier_list) + 1
            identifier_list.append(new_node_id)
            current_size += 1

        if current_size > finalSize:
            if print_output:
                print('No solution found up to size', finalSize)
# ---------------------------------------------------------------------------------------------------
