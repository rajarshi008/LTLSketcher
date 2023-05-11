from helping_functions import *


def semanticConstraints(solver, sketch, sample):
    label = sketch.getLabel()
    node_id = sketch.identifier
    traces = sample.positive + sample.negative

    try:
        leftid = sketch.left.identifier
    except:
        leftid = None
        pass
    try:
        rightid = sketch.right.identifier
    except:
        rightid = None
        pass

    for j, trace in enumerate(traces):
        for k in range(trace.length):
            if sketch._isLeaf() and '?' not in label:
                tracePosition = sample.letter2pos[label]
                if trace.vector[k][tracePosition] == 1:
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k))
                    )
                else:
                    solver.add(
                        Not(Bool('z_%s_%s_%s' % (node_id, j, k)))
                    )

            elif label == '!':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                )

            elif label == '&':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    And(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

            elif label == '|':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Or(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

            elif label == '->':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Implies(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

            elif label == 'X':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Bool('z_%s_%s_%s' % (leftid, j, trace.nextPos(k)))
                )

            elif label == 'F':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Or(
                        [
                            Bool('z_%s_%s_%s' % (leftid, j, f))
                            for f in trace.futurePos(k)
                        ]
                    )
                )

            elif label == 'G':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    And(
                        [
                            Bool('z_%s_%s_%s' % (leftid, j, f))
                            for f in trace.futurePos(k)
                        ]
                    )
                )

            elif label == 'U':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Or(
                        [
                            And(
                                [Bool('z_%s_%s_%s' % (rightid, j, k_p))] +
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, k_pp))
                                    for k_pp in trace.auxiliaryPos(k, k_p)
                                ]
                            )
                            for k_p in trace.futurePos(k)
                        ]
                    )
                )

            elif '?u' in label:
                # placeholder is !
                solver.add(
                    Implies(
                        Bool('x_%s_!' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Not(
                            Bool('z_%s_%s_%s' % (leftid, j, k))
                        )
                    )
                )
                # placeholder is X
                solver.add(
                    Implies(
                        Bool('x_%s_X' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, j, trace.nextPos(k)))
                    )
                )
                # placeholder is F
                solver.add(
                    Implies(
                        Bool('x_%s_F' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            [
                                Bool('z_%s_%s_%s' % (leftid, j, f))
                                for f in trace.futurePos(k)
                            ]
                        )
                    )
                )
                # placeholder is G
                solver.add(
                    Implies(
                        Bool('x_%s_G' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            [
                                Bool('z_%s_%s_%s' % (leftid, j, f))
                                for f in trace.futurePos(k)
                            ]
                        )
                    )
                )

            elif '?b' in label:
                # placeholder is &
                solver.add(
                    Implies(
                        Bool('x_%s_&' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is |
                solver.add(
                    Implies(
                        Bool('x_%s_|' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is ->
                solver.add(
                    Implies(
                        Bool('x_%s_->' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                solver.add(
                    Implies(
                        Bool('x_%s_U' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            [
                                And(
                                    [Bool('z_%s_%s_%s' % (rightid, j, k_p))] +
                                    [
                                        Bool('z_%s_%s_%s' % (leftid, j, k_pp))
                                        for k_pp in trace.auxiliaryPos(k, k_p)
                                    ]
                                )
                                for k_p in trace.futurePos(k)
                            ]
                        )
                    )
                )

    if '?u' in label:
        X = [Bool('x_%s_%s' % (node_id, op)) for op in ['!', 'X', 'F', 'G']]

        # at least one operator and at most one
        solver.add(
            Or(X),
            And(
                [Or(
                    Not(a), Not(b)
                ) for i, a in enumerate(X) for b in (X[(i + 1):])]
            )
        )

    elif '?b' in label:
        X = [Bool('x_%s_%s' % (node_id, op)) for op in ['&', '|', '->', 'U']]

        # at least one operator and at most one
        solver.add(
            Or(X),
            And(
                [Or(
                    Not(a), Not(b)
                ) for i, a in enumerate(X) for b in (X[(i + 1):])]
            )
        )

    if sketch._isUnary():
        semanticConstraints(solver, sketch.left, sample)
    if sketch._isBinary():
        semanticConstraints(solver, sketch.left, sample)
        semanticConstraints(solver, sketch.right, sample)
# --------------------------------------------------------------------------------------------------- TODO


def semanticConstraints_BMC(solver, sketch, sample):
    label = sketch.getLabel()
    node_id = sketch.identifier
    traces = sample.positive + sample.negative

    try:
        leftid = sketch.left.identifier
    except:
        leftid = None
        pass
    try:
        rightid = sketch.right.identifier
    except:
        rightid = None
        pass

    for j, trace in enumerate(traces):
        for k in range(trace.length):
            if sketch._isLeaf() and '?' not in label:
                tracePosition = sample.letter2pos[label]
                if trace.vector[k][tracePosition] == 1:
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k))
                    )
                else:
                    solver.add(
                        Not(Bool('z_%s_%s_%s' % (node_id, j, k)))
                    )

            elif label == '!':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                )

            elif label == '&':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    And(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

            elif label == '|':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Or(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

            elif label == '->':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Implies(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

            elif label == 'X':
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Bool('z_%s_%s_%s' % (leftid, j, trace.nextPos(k)))
                )

            elif label == 'F':
                if k < trace.length - 1:
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (node_id, j, k+1))
                        )
                    )
                else:   # k == trace.length-1
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            [
                                Bool('z_%s_%s_%s' % (leftid, j, f))
                                for f in range(trace.lasso_start, trace.length)
                            ]
                        )
                    )

            elif label == 'G':
                if k < trace.length - 1:
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (node_id, j, k+1))
                        )
                    )
                else:   # k == trace.length-1
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            [
                                Bool('z_%s_%s_%s' % (leftid, j, f))
                                for f in range(trace.lasso_start, trace.length)
                            ]
                        )
                    )

            elif label == 'U':
                if k < trace.length - 1:
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (rightid, j, k)),
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (node_id, j, k+1))
                            )
                        )
                    )
                else:  # k == trace.length-1
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            [
                                And(
                                    [Bool('z_%s_%s_%s' % (rightid, j, k_p))] +
                                    [
                                        Bool('z_%s_%s_%s' % (leftid, j, k_pp))
                                        for k_pp in trace.auxiliaryPos(k, k_p)
                                    ]
                                )
                                for k_p in range(trace.lasso_start, trace.length)
                            ]
                        )
                    )

            elif '?u' in label:
                # placeholder is !
                solver.add(
                    Implies(
                        Bool('x_%s_!' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Not(
                            Bool('z_%s_%s_%s' % (leftid, j, k))
                        )
                    )
                )
                # placeholder is X
                solver.add(
                    Implies(
                        Bool('x_%s_X' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, j, trace.nextPos(k)))
                    )
                )
                # placeholder is F
                if k < trace.length - 1:
                    solver.add(
                        Implies(
                            Bool('x_%s_F' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (node_id, j, k + 1))
                            )
                        )
                    )
                else:  # k == trace.length-1
                    solver.add(
                        Implies(
                            Bool('x_%s_F' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in range(trace.lasso_start, trace.length)
                                ]
                            )
                        )
                    )
                # placeholder is G
                if k < trace.length - 1:
                    solver.add(
                        Implies(
                            Bool('x_%s_G' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (node_id, j, k + 1))
                            )
                        )
                    )
                else:  # k == trace.length-1
                    solver.add(
                        Implies(
                            Bool('x_%s_G' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in range(trace.lasso_start, trace.length)
                                ]
                            )
                        )
                    )
            elif '?b' in label:
                # placeholder is &
                solver.add(
                    Implies(
                        Bool('x_%s_&' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is |
                solver.add(
                    Implies(
                        Bool('x_%s_|' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is ->
                solver.add(
                    Implies(
                        Bool('x_%s_->' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                if k < trace.length-1:
                    solver.add(
                        Implies(
                            Bool('x_%s_U' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (rightid, j, k)),
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (node_id, j, k+1))
                                )
                            )
                        )
                    )
                else:
                    solver.add(
                        Implies(
                            Bool('x_%s_U' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                [
                                    And(
                                        [Bool('z_%s_%s_%s' % (rightid, j, k_p))] +
                                        [
                                            Bool('z_%s_%s_%s' % (leftid, j, k_pp))
                                            for k_pp in trace.auxiliaryPos(k, k_p)
                                        ]
                                    )
                                    for k_p in range(trace.lasso_start, trace.length)
                                ]
                            )
                        )
                    )

    if '?u' in label:
        X = [Bool('x_%s_%s' % (node_id, op)) for op in ['!', 'X', 'F', 'G']]

        # at least one operator and at most one
        solver.add(
            Or(X),
            And(
                [Or(
                    Not(a), Not(b)
                ) for i, a in enumerate(X) for b in (X[(i + 1):])]
            )
        )

    elif '?b' in label:
        X = [Bool('x_%s_%s' % (node_id, op)) for op in ['&', '|', '->', 'U']]

        # at least one operator and at most one
        solver.add(
            Or(X),
            And(
                [Or(
                    Not(a), Not(b)
                ) for i, a in enumerate(X) for b in (X[(i + 1):])]
            )
        )

    if sketch._isUnary():
        semanticConstraints_BMC(solver, sketch.left, sample)
    if sketch._isBinary():
        semanticConstraints_BMC(solver, sketch.left, sample)
        semanticConstraints_BMC(solver, sketch.right, sample)
# --------------------------------------------------------------------------------------------------- TODO


def semanticConstraints_suffix(solver, sketch, sample_table, suffix_table, letter2pos):
    label = sketch.getLabel()
    node_id = sketch.identifier

    if sketch._isLeaf() and '?' not in label:
        tracePosition = letter2pos[label]

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                if trace[k][tracePosition] == 1:
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k))
                    )
                else:
                    solver.add(
                        Not(Bool('z_%s_%s_%s' % (node_id, j, k)))
                    )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                if trace[k][tracePosition] == 1:
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k))
                    )
                else:
                    solver.add(
                        Not(Bool('z_%s_%s_%s' % (node_id, s, k)))
                    )

    elif label == '!':
        leftid = sketch.left.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Not(Bool('z_%s_%s_%s' % (leftid, s, k)))
                )

    elif label == '&':
        leftid = sketch.left.identifier
        rightid = sketch.right.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    And(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    And(
                        Bool('z_%s_%s_%s' % (leftid, s, k)),
                        Bool('z_%s_%s_%s' % (rightid, s, k))
                    )
                )

    elif label == '|':
        leftid = sketch.left.identifier
        rightid = sketch.right.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Or(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Or(
                        Bool('z_%s_%s_%s' % (leftid, s, k)),
                        Bool('z_%s_%s_%s' % (rightid, s, k))
                    )
                )

    elif label == '->':
        leftid = sketch.left.identifier
        rightid = sketch.right.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Implies(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Implies(
                        Bool('z_%s_%s_%s' % (leftid, s, k)),
                        Bool('z_%s_%s_%s' % (rightid, s, k))
                    )
                )

    elif label == 'X':
        leftid = sketch.left.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                next_1, next_2 = suc_2(sample_entry, k)

                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                next = suc_1(suffix_entry["u"], suffix_entry["v"], k)

                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Bool('z_%s_%s_%s' % (leftid, s, next))
                )

    elif label == 'F':
        leftid = sketch.left.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]
            suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Or(
                        [
                            Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                            for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                        ]
                    )
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Or(
                        [
                            Bool('z_%s_%s_%s' % (leftid, s, f))
                            for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                        ]
                    )
                )

    elif label == 'G':
        leftid = sketch.left.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]
            suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    And(
                        [
                            Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                            for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                        ]
                    )
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    And(
                        [
                            Bool('z_%s_%s_%s' % (leftid, s, f))
                            for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                        ]
                    )
                )

    elif label == 'U':
        leftid = sketch.left.identifier
        rightid = sketch.right.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            startpos = sample_entry["startpos"]
            trace = sample_entry["prefix"]
            suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
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

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(suffix_entry["u"])):
                solver.add(
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
            for k in range(len(suffix_entry["u"]), len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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

    elif '?u' in label:
        X = [Bool('x_%s_%s' % (node_id, op)) for op in ['!', 'X', 'F', 'G']]

        # at least one operator and at most one
        solver.add(
            Or(X),
            And(
                [Or(
                    Not(a), Not(b)
                ) for i, a in enumerate(X) for b in (X[(i + 1):])]
            )
        )

        # semantics for placeholder
        leftid = sketch.left.identifier

        # finite prefix in sample-table
        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]
            suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

            for k in range(len(trace)):
                # placeholder is !
                solver.add(
                    Implies(
                        Bool('x_%s_!' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Not(
                            Bool('z_%s_%s_%s' % (leftid, j, k))
                        )
                    )
                )
                # placeholder is X
                next_1, next_2 = suc_2(sample_entry, k)
                solver.add(
                    Implies(
                        Bool('x_%s_X' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                    )
                )
                # placeholder is F
                solver.add(
                    Implies(
                        Bool('x_%s_F' % node_id),  # ->
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
                solver.add(
                    Implies(
                        Bool('x_%s_G' % node_id),  # ->
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
                solver.add(
                    Implies(
                        Bool('x_%s_!' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Not(
                            Bool('z_%s_%s_%s' % (leftid, s, k))
                        )
                    )
                )
                # placeholder is X
                next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                solver.add(
                    Implies(
                        Bool('x_%s_X' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, s, next))
                    )
                )
                # placeholder is F
                solver.add(
                    Implies(
                        Bool('x_%s_F' % node_id),  # ->
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
                solver.add(
                    Implies(
                        Bool('x_%s_G' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        And(
                            [
                                Bool('z_%s_%s_%s' % (leftid, s, f))
                                for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                            ]
                        )
                    )
                )

    elif '?b' in label:
        X = [Bool('x_%s_%s' % (node_id, op)) for op in ['&', '|', '->', 'U']]

        # at least one operator and at most one
        solver.add(
            Or(X),
            And(
                [Or(
                    Not(a), Not(b)
                ) for i, a in enumerate(X) for b in (X[(i + 1):])]
            )
        )

        # semantics for placeholder
        leftid = sketch.left.identifier
        rightid = sketch.right.identifier

        # finite prefix in sample-table
        for sample_entry in sample_table:
            j = sample_entry["id"]
            startpos = sample_entry["startpos"]
            trace = sample_entry["prefix"]
            suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

            for k in range(len(trace)):
                # placeholder is &
                solver.add(
                    Implies(
                        Bool('x_%s_&' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is |
                solver.add(
                    Implies(
                        Bool('x_%s_|' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is ->
                solver.add(
                    Implies(
                        Bool('x_%s_->' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                solver.add(
                    Implies(
                        Bool('x_%s_U' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
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

        # suffixes in suffix-table
        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                # placeholder is &
                solver.add(
                    Implies(
                        Bool('x_%s_&' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )
                )
                # placeholder is |
                solver.add(
                    Implies(
                        Bool('x_%s_|' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )
                )
                # placeholder is ->
                solver.add(
                    Implies(
                        Bool('x_%s_->' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )
                )
                # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                if k in range(len(suffix_entry["u"])):
                    solver.add(
                        Implies(
                            Bool('x_%s_U' % node_id),  # ->
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
                else:   # k in range(len(suffix_entry["u"]), len(trace)):
                    solver.add(
                        Implies(
                            Bool('x_%s_U' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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

    if sketch._isUnary():
        semanticConstraints_suffix(solver, sketch.left, sample_table, suffix_table, letter2pos)
    if sketch._isBinary():
        semanticConstraints_suffix(solver, sketch.left, sample_table, suffix_table, letter2pos)
        semanticConstraints_suffix(solver, sketch.right, sample_table, suffix_table, letter2pos)
# --------------------------------------------------------------------------------------------------- TODO


def semanticConstraints_suffix_BMC(solver, sketch, sample_table, suffix_table, letter2pos):
    label = sketch.getLabel()
    node_id = sketch.identifier

    if sketch._isLeaf() and '?' not in label:
        tracePosition = letter2pos[label]

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                if trace[k][tracePosition] == 1:
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k))
                    )
                else:
                    solver.add(
                        Not(Bool('z_%s_%s_%s' % (node_id, j, k)))
                    )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                if trace[k][tracePosition] == 1:
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k))
                    )
                else:
                    solver.add(
                        Not(Bool('z_%s_%s_%s' % (node_id, s, k)))
                    )

    elif label == '!':
        leftid = sketch.left.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Not(Bool('z_%s_%s_%s' % (leftid, s, k)))
                )

    elif label == '&':
        leftid = sketch.left.identifier
        rightid = sketch.right.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    And(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    And(
                        Bool('z_%s_%s_%s' % (leftid, s, k)),
                        Bool('z_%s_%s_%s' % (rightid, s, k))
                    )
                )

    elif label == '|':
        leftid = sketch.left.identifier
        rightid = sketch.right.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Or(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Or(
                        Bool('z_%s_%s_%s' % (leftid, s, k)),
                        Bool('z_%s_%s_%s' % (rightid, s, k))
                    )
                )

    elif label == '->':
        leftid = sketch.left.identifier
        rightid = sketch.right.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Implies(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (rightid, j, k))
                    )
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Implies(
                        Bool('z_%s_%s_%s' % (leftid, s, k)),
                        Bool('z_%s_%s_%s' % (rightid, s, k))
                    )
                )

    elif label == 'X':
        leftid = sketch.left.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                next_1, next_2 = suc_2(sample_entry, k)

                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                next = suc_1(suffix_entry["u"], suffix_entry["v"], k)

                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Bool('z_%s_%s_%s' % (leftid, s, next))
                )

    elif label == 'F':
        leftid = sketch.left.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                next_1, next_2 = suc_2(sample_entry, k)
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Or(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                    )
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)-1):
                next = suc_1(suffix_entry["u"], suffix_entry["v"], k)

                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Or(
                        Bool('z_%s_%s_%s' % (leftid, s, k)),
                        Bool('z_%s_%s_%s' % (node_id, s, next))
                    )
                )

            k = len(trace)-1
            solver.add(
                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                Or(
                    [
                        Bool('z_%s_%s_%s' % (leftid, s, f))
                        for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                    ]
                )
            )

    elif label == 'G':
        leftid = sketch.left.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                next_1, next_2 = suc_2(sample_entry, k)
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    And(
                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                        Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                    )
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)-1):
                next = suc_1(suffix_entry["u"], suffix_entry["v"], k)

                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    And(
                        Bool('z_%s_%s_%s' % (leftid, s, k)),
                        Bool('z_%s_%s_%s' % (node_id, s, next))
                    )
                )

            k = len(trace)-1
            solver.add(
                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                And(
                    [
                        Bool('z_%s_%s_%s' % (leftid, s, f))
                        for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                    ]
                )
            )

    elif label == 'U':
        leftid = sketch.left.identifier
        rightid = sketch.right.identifier

        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                next_1, next_2 = suc_2(sample_entry, k)
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                    Or(
                        Bool('z_%s_%s_%s' % (rightid, j, k)),
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                        )
                    )
                )

        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)-1):
                next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Or(
                        Bool('z_%s_%s_%s' % (rightid, s, k)),
                        And(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (node_id, s, next))
                        )
                    )
                )
            k = len(trace)-1
            solver.add(
                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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

    elif '?u' in label:
        X = [Bool('x_%s_%s' % (node_id, op)) for op in ['!', 'X', 'F', 'G']]

        # at least one operator and at most one
        solver.add(
            Or(X),
            And(
                [Or(
                    Not(a), Not(b)
                ) for i, a in enumerate(X) for b in (X[(i + 1):])]
            )
        )

        # semantics for placeholder
        leftid = sketch.left.identifier

        # finite prefix in sample-table
        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                # placeholder is !
                solver.add(
                    Implies(
                        Bool('x_%s_!' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Not(
                            Bool('z_%s_%s_%s' % (leftid, j, k))
                        )
                    )
                )
                # placeholder is X
                next_1, next_2 = suc_2(sample_entry, k)
                solver.add(
                    Implies(
                        Bool('x_%s_X' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                    )
                )
                # placeholder is F
                solver.add(
                    Implies(
                        Bool('x_%s_F' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                        )
                    )
                )
                # placeholder is G
                solver.add(
                    Implies(
                        Bool('x_%s_G' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                        )
                    )
                )

        # suffixes in suffix-table
        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                # placeholder is !
                solver.add(
                    Implies(
                        Bool('x_%s_!' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Not(
                            Bool('z_%s_%s_%s' % (leftid, s, k))
                        )
                    )
                )
                # placeholder is X
                next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                solver.add(
                    Implies(
                        Bool('x_%s_X' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, s, next))
                    )
                )
                # placeholder is F
                if k == len(trace)-1:
                    solver.add(
                        Implies(
                            Bool('x_%s_F' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, s, f))
                                    for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                ]
                            )
                        )
                    )
                else:   # k in range(len(trace)-1)
                    solver.add(
                        Implies(
                            Bool('x_%s_F' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (node_id, s, next))
                            )
                        )
                    )

                # placeholder is G
                if k == len(trace)-1:
                    solver.add(
                        Implies(
                            Bool('x_%s_G' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, s, f))
                                    for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                ]
                            )
                        )
                    )
                else:   # k in range(len(trace)-1)
                    solver.add(
                        Implies(
                            Bool('x_%s_G' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (node_id, s, next))
                            )
                        )
                    )

    elif '?b' in label:
        X = [Bool('x_%s_%s' % (node_id, op)) for op in ['&', '|', '->', 'U']]

        # at least one operator and at most one
        solver.add(
            Or(X),
            And(
                [Or(
                    Not(a), Not(b)
                ) for i, a in enumerate(X) for b in (X[(i + 1):])]
            )
        )

        # semantics for placeholder
        leftid = sketch.left.identifier
        rightid = sketch.right.identifier

        # finite prefix in sample-table
        for sample_entry in sample_table:
            j = sample_entry["id"]
            trace = sample_entry["prefix"]

            for k in range(len(trace)):
                # placeholder is &
                solver.add(
                    Implies(
                        Bool('x_%s_&' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is |
                solver.add(
                    Implies(
                        Bool('x_%s_|' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is ->
                solver.add(
                    Implies(
                        Bool('x_%s_->' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )
                )
                # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                next_1, next_2 = suc_2(sample_entry, k)
                solver.add(
                    Implies(
                        Bool('x_%s_U' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (rightid, j, k)),
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                            )
                        )
                    )
                )

        # suffixes in suffix-table
        for suffix_entry in suffix_table:
            s = suffix_entry["sid"]
            trace = suffix_entry["u"] + suffix_entry["v"]

            for k in range(len(trace)):
                # placeholder is &
                solver.add(
                    Implies(
                        Bool('x_%s_&' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )
                )
                # placeholder is |
                solver.add(
                    Implies(
                        Bool('x_%s_|' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )
                )
                # placeholder is ->
                solver.add(
                    Implies(
                        Bool('x_%s_->' % node_id),  # ->
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )
                )
                # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                if k in range(len(trace)-1):
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                    solver.add(
                        Implies(
                            Bool('x_%s_U' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (rightid, s, k)),
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                    Bool('z_%s_%s_%s' % (node_id, s, next))
                                )
                            )
                        )
                    )
                else:   # k = len(trace)-1
                    solver.add(
                        Implies(
                            Bool('x_%s_U' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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

    if sketch._isUnary():
        semanticConstraints_suffix_BMC(solver, sketch.left, sample_table, suffix_table, letter2pos)
    if sketch._isBinary():
        semanticConstraints_suffix_BMC(solver, sketch.left, sample_table, suffix_table, letter2pos)
        semanticConstraints_suffix_BMC(solver, sketch.right, sample_table, suffix_table, letter2pos)
# --------------------------------------------------------------------------------------------------- TODO


def semanticConstraints_cycle_free(solver, node_list, sample):
    traces = sample.positive + sample.negative

    for node in node_list:
        label = node.getLabel()
        node_id = node.identifier

        try:
            leftid = node.left.identifier
        except:
            leftid = None
            pass
        try:
            rightid = node.right.identifier
        except:
            rightid = None
            pass

        for j, trace in enumerate(traces):
            for k in range(trace.length):
                if node._isLeaf() and '?' not in label:
                    tracePosition = sample.letter2pos[label]
                    if trace.vector[k][tracePosition] == 1:
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, j, k))
                        )
                    else:
                        solver.add(
                            Not(Bool('z_%s_%s_%s' % (node_id, j, k)))
                        )

                elif label == '!':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                    )

                elif label == '&':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

                elif label == '|':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

                elif label == '->':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

                elif label == 'X':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, j, trace.nextPos(k)))
                    )

                elif label == 'F':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            [
                                Bool('z_%s_%s_%s' % (leftid, j, f))
                                for f in trace.futurePos(k)
                            ]
                        )
                    )

                elif label == 'G':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            [
                                Bool('z_%s_%s_%s' % (leftid, j, f))
                                for f in trace.futurePos(k)
                            ]
                        )
                    )

                elif label == 'U':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            [
                                And(
                                    [Bool('z_%s_%s_%s' % (rightid, j, k_p))] +
                                    [
                                        Bool('z_%s_%s_%s' % (leftid, j, k_pp))
                                        for k_pp in trace.auxiliaryPos(k, k_p)
                                    ]
                                )
                                for k_p in trace.futurePos(k)
                            ]
                        )
                    )

                elif '?u' in label:
                    # placeholder is !
                    solver.add(
                        Implies(
                            Bool('x_%s_!' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Not(
                                Bool('z_%s_%s_%s' % (leftid, j, k))
                            )
                        )
                    )
                    # placeholder is X
                    solver.add(
                        Implies(
                            Bool('x_%s_X' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, j, trace.nextPos(k)))
                        )
                    )
                    # placeholder is F
                    solver.add(
                        Implies(
                            Bool('x_%s_F' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in trace.futurePos(k)
                                ]
                            )
                        )
                    )
                    # placeholder is G
                    solver.add(
                        Implies(
                            Bool('x_%s_G' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in trace.futurePos(k)
                                ]
                            )
                        )
                    )

                elif '?b' in label:
                    # placeholder is &
                    solver.add(
                        Implies(
                            Bool('x_%s_&' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is |
                    solver.add(
                        Implies(
                            Bool('x_%s_|' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is ->
                    solver.add(
                        Implies(
                            Bool('x_%s_->' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Implies(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                    solver.add(
                        Implies(
                            Bool('x_%s_U' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                [
                                    And(
                                        [Bool('z_%s_%s_%s' % (rightid, j, k_p))] +
                                        [
                                            Bool('z_%s_%s_%s' % (leftid, j, k_pp))
                                            for k_pp in trace.auxiliaryPos(k, k_p)
                                        ]
                                    )
                                    for k_p in trace.futurePos(k)
                                ]
                            )
                        )
                    )
# --------------------------------------------------------------------------------------------------- TODO


def semanticConstraints_cycle_free_suffix(solver, node_list, sample_table, suffix_table, letter2pos):
    for node in node_list:
        label = node.getLabel()
        node_id = node.identifier

        if node._isLeaf() and '?' not in label:
            tracePosition = letter2pos[label]

            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    if trace[k][tracePosition] == 1:
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, j, k))
                        )
                    else:
                        solver.add(
                            Not(Bool('z_%s_%s_%s' % (node_id, j, k)))
                        )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    if trace[k][tracePosition] == 1:
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, s, k))
                        )
                    else:
                        solver.add(
                            Not(Bool('z_%s_%s_%s' % (node_id, s, k)))
                        )

        elif label == '!':
            leftid = node.left.identifier
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Not(Bool('z_%s_%s_%s' % (leftid, s, k)))
                    )

        elif label == '&':
            leftid = node.left.identifier
            rightid = node.right.identifier
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )

        elif label == '|':
            leftid = node.left.identifier
            rightid = node.right.identifier
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )

        elif label == '->':
            leftid = node.left.identifier
            rightid = node.right.identifier
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )

        elif label == 'X':
            leftid = node.left.identifier
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    next_1, next_2 = suc_2(sample_entry, k)

                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)

                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, s, next))
                    )

        elif label == 'F':
            leftid = node.left.identifier
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]
                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            [
                                Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                                for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                            ]
                        )
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Or(
                            [
                                Bool('z_%s_%s_%s' % (leftid, s, f))
                                for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                            ]
                        )
                    )

        elif label == 'G':
            leftid = node.left.identifier
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]
                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            [
                                Bool('z_%s_%s_%s' % (leftid, f_1, f_2))
                                for f_1, f_2 in FUT_2(sample_entry, k, suffix_entry)
                            ]
                        )
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        And(
                            [
                                Bool('z_%s_%s_%s' % (leftid, s, f))
                                for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                            ]
                        )
                    )

        elif label == 'U':
            leftid = node.left.identifier
            rightid = node.right.identifier
            for sample_entry in sample_table:
                j = sample_entry["id"]
                startpos = sample_entry["startpos"]
                trace = sample_entry["prefix"]
                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
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

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(suffix_entry["u"])):
                    solver.add(
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
                for k in range(len(suffix_entry["u"]), len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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

        elif '?u' in label:
            leftid = node.left.identifier
            # finite prefix in sample-table
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]
                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                for k in range(len(trace)):
                    # placeholder is !
                    solver.add(
                        Implies(
                            Bool('x_%s_!' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Not(
                                Bool('z_%s_%s_%s' % (leftid, j, k))
                            )
                        )
                    )
                    # placeholder is X
                    next_1, next_2 = suc_2(sample_entry, k)
                    solver.add(
                        Implies(
                            Bool('x_%s_X' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                        )
                    )
                    # placeholder is F
                    solver.add(
                        Implies(
                            Bool('x_%s_F' % node_id),  # ->
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
                    solver.add(
                        Implies(
                            Bool('x_%s_G' % node_id),  # ->
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
                    solver.add(
                        Implies(
                            Bool('x_%s_!' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Not(
                                Bool('z_%s_%s_%s' % (leftid, s, k))
                            )
                        )
                    )
                    # placeholder is X
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                    solver.add(
                        Implies(
                            Bool('x_%s_X' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, s, next))
                        )
                    )
                    # placeholder is F
                    solver.add(
                        Implies(
                            Bool('x_%s_F' % node_id),  # ->
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
                    solver.add(
                        Implies(
                            Bool('x_%s_G' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, s, f))
                                    for f in FUT_1(suffix_entry["u"], suffix_entry["v"], k)
                                ]
                            )
                        )
                    )

        elif '?b' in label:
            leftid = node.left.identifier
            rightid = node.right.identifier
            # finite prefix in sample-table
            for sample_entry in sample_table:
                j = sample_entry["id"]
                startpos = sample_entry["startpos"]
                trace = sample_entry["prefix"]
                suffix_entry = suffix_table[int(sample_entry["sid"][1:])]

                for k in range(len(trace)):
                    # placeholder is &
                    solver.add(
                        Implies(
                            Bool('x_%s_&' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is |
                    solver.add(
                        Implies(
                            Bool('x_%s_|' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is ->
                    solver.add(
                        Implies(
                            Bool('x_%s_->' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Implies(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                    solver.add(
                        Implies(
                            Bool('x_%s_U' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
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

            # suffixes in suffix-table
            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    # placeholder is &
                    solver.add(
                        Implies(
                            Bool('x_%s_&' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (rightid, s, k))
                            )
                        )
                    )
                    # placeholder is |
                    solver.add(
                        Implies(
                            Bool('x_%s_|' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (rightid, s, k))
                            )
                        )
                    )
                    # placeholder is ->
                    solver.add(
                        Implies(
                            Bool('x_%s_->' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Implies(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (rightid, s, k))
                            )
                        )
                    )
                    # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                    if k in range(len(suffix_entry["u"])):
                        solver.add(
                            Implies(
                                Bool('x_%s_U' % node_id),  # ->
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
                    else:   # k in range(len(suffix_entry["u"]), len(trace)):
                        solver.add(
                            Implies(
                                Bool('x_%s_U' % node_id),  # ->
                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
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
# --------------------------------------------------------------------------------------------------- TODO


def semanticConstraints_cycle_free_BMC(solver, node_list, sample):
    traces = sample.positive + sample.negative

    for node in node_list:
        label = node.getLabel()
        node_id = node.identifier

        try:
            leftid = node.left.identifier
        except:
            leftid = None
            pass
        try:
            rightid = node.right.identifier
        except:
            rightid = None
            pass

        for j, trace in enumerate(traces):
            for k in range(trace.length):
                if node._isLeaf() and '?' not in label:
                    tracePosition = sample.letter2pos[label]
                    if trace.vector[k][tracePosition] == 1:
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, j, k))
                        )
                    else:
                        solver.add(
                            Not(Bool('z_%s_%s_%s' % (node_id, j, k)))
                        )

                elif label == '!':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                    )

                elif label == '&':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

                elif label == '|':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

                elif label == '->':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

                elif label == 'X':
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, j, trace.nextPos(k)))
                    )

                elif label == 'F':
                    if k < trace.length - 1:
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (node_id, j, trace.nextPos(k)))
                            )
                        )
                    else:  # k == trace.length-1
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in range(trace.lasso_start, trace.length)
                                ]
                            )
                        )

                elif label == 'G':
                    if k < trace.length - 1:
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (node_id, j, trace.nextPos(k)))
                            )
                        )
                    else:  # k == trace.length-1
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            And(
                                [
                                    Bool('z_%s_%s_%s' % (leftid, j, f))
                                    for f in range(trace.lasso_start, trace.length)
                                ]
                            )
                        )

                elif label == 'U':
                    if k < trace.length - 1:
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (rightid, j, k)),
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (node_id, j, trace.nextPos(k)))
                                )
                            )
                        )
                    else:  # k == trace.length -1
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                [
                                    And(
                                        [Bool('z_%s_%s_%s' % (rightid, j, k_p))] +
                                        [
                                            Bool('z_%s_%s_%s' % (leftid, j, k_pp))
                                            for k_pp in trace.auxiliaryPos(k, k_p)
                                        ]
                                    )
                                    for k_p in range(trace.lasso_start, trace.length)
                                ]
                            )
                        )

                elif '?u' in label:
                    # placeholder is !
                    solver.add(
                        Implies(
                            Bool('x_%s_!' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Not(
                                Bool('z_%s_%s_%s' % (leftid, j, k))
                            )
                        )
                    )
                    # placeholder is X
                    solver.add(
                        Implies(
                            Bool('x_%s_X' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, j, trace.nextPos(k)))
                        )
                    )
                    # placeholder is F
                    if k < trace.length - 1:
                        solver.add(
                            Implies(
                                Bool('x_%s_F' % node_id),  # ->
                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (node_id, j, trace.nextPos(k)))
                                )
                            )
                        )
                    else:  # k == trace.length-1
                        solver.add(
                            Implies(
                                Bool('x_%s_F' % node_id),  # ->
                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                Or(
                                    [
                                        Bool('z_%s_%s_%s' % (leftid, j, f))
                                        for f in range(trace.lasso_start, trace.length)
                                    ]
                                )
                            )
                        )
                    # placeholder is G
                    if k < trace.length - 1:
                        solver.add(
                            Implies(
                                Bool('x_%s_G' % node_id),  # ->
                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (node_id, j, trace.nextPos(k)))
                                )
                            )
                        )
                    else:  # k == trace.length-1
                        solver.add(
                            Implies(
                                Bool('x_%s_G' % node_id),  # ->
                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                And(
                                    [
                                        Bool('z_%s_%s_%s' % (leftid, j, f))
                                        for f in range(trace.lasso_start, trace.length)
                                    ]
                                )
                            )
                        )

                elif '?b' in label:
                    # placeholder is &
                    solver.add(
                        Implies(
                            Bool('x_%s_&' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is |
                    solver.add(
                        Implies(
                            Bool('x_%s_|' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is ->
                    solver.add(
                        Implies(
                            Bool('x_%s_->' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Implies(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                    if k < trace.length - 1:
                        solver.add(
                            Implies(
                                Bool('x_%s_%s' % (node_id, 'U')),  # ->
                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (rightid, j, k)),
                                    And(
                                        Bool('z_%s_%s_%s' % (leftid, j, k)),
                                        Bool('z_%s_%s_%s' % (node_id, j, trace.nextPos(k)))
                                    )
                                )
                            )
                        )
                    else:  # k == trace.length -1
                        solver.add(
                            Implies(
                                Bool('x_%s_%s' % (node_id, 'U')),  # ->
                                Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                                Or(
                                    [
                                        And(
                                            [Bool('z_%s_%s_%s' % (rightid, j, k_p))] +
                                            [
                                                Bool('z_%s_%s_%s' % (leftid, j, k_pp))
                                                for k_pp in trace.auxiliaryPos(k, k_p)
                                            ]
                                        )
                                        for k_p in range(trace.lasso_start, trace.length)
                                    ]
                                )
                            )
                        )
# --------------------------------------------------------------------------------------------------- TODO


def consistencyConstraints(solver, root_id, sample):
    """
	Adds consistency constraints for given sample to solver
	"""
    s = solver
    for number in range(sample.num_positives):
        s.add(
            Bool('z_%s_%s_0' % (root_id, number)) == True
        )
    for number in range(sample.num_negatives):
        s.add(
            Bool('z_%s_%s_0' % (root_id, sample.num_positives + number)) == False
        )
# --------------------------------------------------------------------------------------------------- TODO


def consistencyConstraints_suffix(s, root_id, sample_table, num_positive):
    for example in sample_table:
        if len(example["prefix"]) == 0:
            id = example["sid"]
            pos = example["startpos"]
        else:
            id = example["id"]
            pos = 0

        if example["id"] < num_positive:
            # word is positive
            s.add(
                Bool('z_%s_%s_%s' % (root_id, id, pos))
            )
        else:
            # word is negative
            s.add(
                Not(Bool('z_%s_%s_%s' % (root_id, id, pos)))
            )
# --------------------------------------------------------------------------------------------------- TODO


def semanticConstraints_cycle_free_suffix_BMC(solver, node_list, sample_table, suffix_table, letter2pos):
    for node in node_list:
        label = node.getLabel()
        node_id = node.identifier

        try:
            leftid = node.left.identifier
        except:
            leftid = None
            pass
        try:
            rightid = node.right.identifier
        except:
            rightid = None
            pass

        if node._isLeaf() and '?' not in label:
            tracePosition = letter2pos[label]

            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    if trace[k][tracePosition] == 1:
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, j, k))
                        )
                    else:
                        solver.add(
                            Not(Bool('z_%s_%s_%s' % (node_id, j, k)))
                        )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    if trace[k][tracePosition] == 1:
                        solver.add(
                            Bool('z_%s_%s_%s' % (node_id, s, k))
                        )
                    else:
                        solver.add(
                            Not(Bool('z_%s_%s_%s' % (node_id, s, k)))
                        )

        elif label == '!':
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Not(Bool('z_%s_%s_%s' % (leftid, j, k)))
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Not(Bool('z_%s_%s_%s' % (leftid, s, k)))
                    )

        elif label == '&':
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )

        elif label == '|':
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )

        elif label == '->':
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (rightid, j, k))
                        )
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Implies(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (rightid, s, k))
                        )
                    )

        elif label == 'X':
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    next_1, next_2 = suc_2(sample_entry, k)

                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)

                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Bool('z_%s_%s_%s' % (leftid, s, next))
                    )

        elif label == 'F':
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    next_1, next_2 = suc_2(sample_entry, k)
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                        )

                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace) - 1):
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (node_id, s, next))
                        )
                    )
                k = len(trace) - 1
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    Or(
                        [
                            Bool('z_%s_%s_%s' % (leftid, s, f))
                            for f in range(len(suffix_entry["u"]), len(trace))
                        ]
                    )
                )

        elif label == 'G':
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    next_1, next_2 = suc_2(sample_entry, k)
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, j, k)),
                            Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                        )

                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace) - 1):
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        And(
                            Bool('z_%s_%s_%s' % (leftid, s, k)),
                            Bool('z_%s_%s_%s' % (node_id, s, next))
                        )
                    )
                k = len(trace) - 1
                solver.add(
                    Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                    And(
                        [
                            Bool('z_%s_%s_%s' % (leftid, s, f))
                            for f in range(len(suffix_entry["u"]), len(trace))
                        ]
                    )
                )

        elif label == 'U':
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    next_1, next_2 = suc_2(sample_entry, k)
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (rightid, j, k)),
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                            )
                        )
                    )

            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace) - 1):
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                    solver.add(
                        Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                        Or(
                            Bool('z_%s_%s_%s' % (rightid, s, k)),
                            And(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (node_id, s, next))
                            )
                        )
                    )
                k = len(trace) - 1
                solver.add(
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

        elif '?u' in label:
            # finite prefix in sample-table
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    # placeholder is !
                    solver.add(
                        Implies(
                            Bool('x_%s_!' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Not(
                                Bool('z_%s_%s_%s' % (leftid, j, k))
                            )
                        )
                    )
                    # placeholder is X
                    next_1, next_2 = suc_2(sample_entry, k)
                    solver.add(
                        Implies(
                            Bool('x_%s_X' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, next_1, next_2))
                        )
                    )
                    # placeholder is F
                    solver.add(
                        Implies(
                            Bool('x_%s_F' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                            )
                        )
                    )
                    # placeholder is G
                    solver.add(
                        Implies(
                            Bool('x_%s_G' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                            )
                        )
                    )

            # suffixes in suffix-table
            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    # placeholder is !
                    solver.add(
                        Implies(
                            Bool('x_%s_!' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Not(
                                Bool('z_%s_%s_%s' % (leftid, s, k))
                            )
                        )
                    )
                    # placeholder is X
                    next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                    solver.add(
                        Implies(
                            Bool('x_%s_X' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Bool('z_%s_%s_%s' % (leftid, s, next))
                        )
                    )
                    # placeholder is F
                    if k < len(trace) - 1:
                        solver.add(
                            Implies(
                                Bool('x_%s_F' % node_id),  # ->
                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                    Bool('z_%s_%s_%s' % (node_id, s, next))
                                )
                            )
                        )
                    else:  # k == len(trace) - 1
                        solver.add(
                            Implies(
                                Bool('x_%s_F' % node_id),  # ->
                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                Or(
                                    [
                                        Bool('z_%s_%s_%s' % (leftid, s, f))
                                        for f in range(len(suffix_entry["u"]), len(trace))
                                    ]
                                )
                            )
                        )
                    # placeholder is G
                    if k < len(trace) - 1:
                        solver.add(
                            Implies(
                                Bool('x_%s_G' % node_id),  # ->
                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, s, k)),
                                    Bool('z_%s_%s_%s' % (node_id, s, next))
                                )
                            )
                        )
                    else:  # k == len(trace) - 1
                        solver.add(
                            Implies(
                                Bool('x_%s_G' % node_id),  # ->
                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                And(
                                    [
                                        Bool('z_%s_%s_%s' % (leftid, s, f))
                                        for f in range(len(suffix_entry["u"]), len(trace))
                                    ]
                                )
                            )
                        )

        elif '?b' in label:
            # finite prefix in sample-table
            for sample_entry in sample_table:
                j = sample_entry["id"]
                trace = sample_entry["prefix"]

                for k in range(len(trace)):
                    # placeholder is &
                    solver.add(
                        Implies(
                            Bool('x_%s_&' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is |
                    solver.add(
                        Implies(
                            Bool('x_%s_|' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is ->
                    solver.add(
                        Implies(
                            Bool('x_%s_->' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Implies(
                                Bool('z_%s_%s_%s' % (leftid, j, k)),
                                Bool('z_%s_%s_%s' % (rightid, j, k))
                            )
                        )
                    )
                    # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                    next_1, next_2 = suc_2(sample_entry, k)
                    solver.add(
                        Implies(
                            Bool('x_%s_%s' % (node_id, 'U')),  # ->
                            Bool('z_%s_%s_%s' % (node_id, j, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (rightid, j, k)),
                                And(
                                    Bool('z_%s_%s_%s' % (leftid, j, k)),
                                    Bool('z_%s_%s_%s' % (node_id, next_1, next_2))
                                )
                            )
                        )
                    )

            # suffixes in suffix-table
            for suffix_entry in suffix_table:
                s = suffix_entry["sid"]
                trace = suffix_entry["u"] + suffix_entry["v"]

                for k in range(len(trace)):
                    # placeholder is &
                    solver.add(
                        Implies(
                            Bool('x_%s_&' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            And(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (rightid, s, k))
                            )
                        )
                    )
                    # placeholder is |
                    solver.add(
                        Implies(
                            Bool('x_%s_|' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Or(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (rightid, s, k))
                            )
                        )
                    )
                    # placeholder is ->
                    solver.add(
                        Implies(
                            Bool('x_%s_->' % node_id),  # ->
                            Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                            Implies(
                                Bool('z_%s_%s_%s' % (leftid, s, k)),
                                Bool('z_%s_%s_%s' % (rightid, s, k))
                            )
                        )
                    )
                    # placeholder is U, uses [a -> (b & c)] == [(a -> b) & (a -> c)]
                    if k < len(trace) - 1:
                        next = suc_1(suffix_entry["u"], suffix_entry["v"], k)
                        solver.add(
                            Implies(
                                Bool('x_%s_%s' % (node_id, 'U')),  # ->
                                Bool('z_%s_%s_%s' % (node_id, s, k)) ==
                                Or(
                                    Bool('z_%s_%s_%s' % (rightid, s, k)),
                                    And(
                                        Bool('z_%s_%s_%s' % (leftid, s, k)),
                                        Bool('z_%s_%s_%s' % (node_id, s, next))
                                    )
                                )
                            )
                        )
                    else:  # k = len(trace) - 1
                        solver.add(
                            Implies(
                                Bool('x_%s_%s' % (node_id, 'U')),  # ->
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
# --------------------------------------------------------------------------------------------------- TODO


def placeholderConstraints(solver, sketch, nodes):
    """
	Adds constraints to solver which ensure that type-1/-2 placeholders are substituted with the same operator
	"""
    s = solver

    placeholder = sketch.label
    id = sketch.identifier

    if '?u' in placeholder:
        for node in nodes:
            if node.label == placeholder and node.identifier != id:
                s.add(
                    And(
                        [
                            Bool('x_%s_%s' % (id, op)) ==
                            Bool('x_%s_%s' % (node.identifier, op))
                            for op in ['!', 'X', 'G', 'F']
                        ]
                    )
                )

    elif '?b' in placeholder:
        for node in nodes:
            if node.label == placeholder and node.identifier != id:
                s.add(
                    And(
                        [
                            Bool('x_%s_%s' % (id, op)) ==
                            Bool('x_%s_%s' % (node.identifier, op))
                            for op in ['&', '|', '->', 'U']
                        ]
                    )
                )

    if sketch._isUnary():
        placeholderConstraints(s, sketch.left, nodes)
    if sketch._isBinary():
        placeholderConstraints(s, sketch.left, nodes)
        placeholderConstraints(s, sketch.right, nodes)
# --------------------------------------------------------------------------------------------------- TODO


def suffixConstraints(solver, sketch, sample):
    """
    Adds constraints to solver which ensure that equal suffixes have to evaluate the same in the placeholder-0-nodes
    """
    placeholderPositions = sketch.get_type0Positions()

    if len(placeholderPositions) > 0:
        traces = sample.positive + sample.negative

        for j, trace_1 in enumerate(traces):
            for offset, trace_2 in enumerate(traces[j+1:]):
                for pos_1 in range(trace_1.length):
                    suffix_1 = build_suffix(trace_1, pos_1)
                    for pos_2 in range(trace_2.length):
                        suffix_2 = build_suffix(trace_2, pos_2)
                        if equal(suffix_1, suffix_2):
                            solver.add(
                                And(
                                    [
                                        Bool('z_%s_%s_%s' % (i, j, pos_1)) ==
                                        Bool('z_%s_%s_%s' % (i, j + 1 + offset, pos_2))
                                        for i in placeholderPositions
                                    ]
                                )
                            )
# --------------------------------------------------------------------------------------------------- TODO


def structureConstraints(solver, sketch):
    label = sketch.getLabel()
    node_id = sketch.identifier

    if '?' not in label:
        solver.add(
            Bool('x_%s_%s' % (node_id, label))
        )

    if sketch._isUnary() and (not '?' in sketch.left.label or '?u' in sketch.left.label or '?b' in sketch.left.label):
        solver.add(
            Bool('l_%s_%s' % (node_id, sketch.left.identifier))
        )
        structureConstraints(solver, sketch.left)

    if sketch._isBinary():
        if not '?' in sketch.left.label or '?u' in sketch.left.label or '?b' in sketch.left.label:
            solver.add(
                Bool('l_%s_%s' % (node_id, sketch.left.identifier))
            )
            structureConstraints(solver, sketch.left)
        if not'?' in sketch.right.label or '?u' in sketch.right.label or '?b' in sketch.right.label:
            solver.add(
                Bool('r_%s_%s' % (node_id, sketch.right.identifier))
            )
            structureConstraints(solver, sketch.right)
# --------------------------------------------------------------------------------------------------- TODO


def structureConstraints_cycle_free(solver, sketch_nodes, parent_nodes, possible_labels):
    nodes = sketch_nodes + parent_nodes
    id_list = [node.identifier for node in nodes]
    for node in sketch_nodes:
        node_id = node.identifier
        if '?' not in node.label:
            solver.add(
                Bool('x_%s_%s' % (node_id, node.label))
            )
            solver.add(
                [
                    Not(Bool('x_%s_%s' % (node_id, label)))
                    for label in possible_labels if label != node.label
                ]
            )
        elif '?u' in node.label:
            X = [Bool('x_%s_%s' % (node_id, op)) for op in ['!', 'X', 'F', 'G']]

            # at least one operator and at most one
            solver.add(
                Or(X),
                And(
                    [Or(
                        Not(a), Not(b)
                    ) for i, a in enumerate(X) for b in (X[(i + 1):])]
                )
            )
            solver.add(
                [
                    Not(Bool('x_%s_%s' % (node_id, label)))
                    for label in possible_labels if label not in ['!', 'X', 'F', 'G']
                ]
            )

        elif '?b' in node.label:
            X = [Bool('x_%s_%s' % (node_id, op)) for op in ['&', '|', '->', 'U']]

            # at least one operator and at most one
            solver.add(
                Or(X),
                And(
                    [Or(
                        Not(a), Not(b)
                    ) for i, a in enumerate(X) for b in (X[(i + 1):])]
                )
            )
            solver.add(
                [
                    Not(Bool('x_%s_%s' % (node_id, label)))
                    for label in possible_labels if label not in ['&', '|', '->', 'U']
                ]
            )

        if node._isUnary():
            solver.add(
                Bool('l_%s_%s' % (node_id, node.left.identifier))
            )
        elif node._isBinary():
            solver.add(
                Bool('l_%s_%s' % (node_id, node.left.identifier)),
                Bool('r_%s_%s' % (node_id, node.right.identifier))
            )

    for node in parent_nodes:
        node_id = node.identifier
        Y = [Bool('x_%s_%s' % (node_id, op)) for op in possible_labels]

        if '?' not in node.label:
            solver.add(
                Bool('x_%s_%s' % (node_id, node.label))
            )
            solver.add(
                [
                    Not(Bool('x_%s_%s' % (node_id, label)))
                    for label in possible_labels if label != node.label
                ]
            )
        elif '?u' in node.label:
            X = [Bool('x_%s_%s' % (node_id, op)) for op in ['!', 'X', 'F', 'G']]

            # at least one operator and at most one
            solver.add(
                Or(X)
            )
            solver.add(
                [
                    And(
                        [
                            Or(
                                Not(a),
                                Not(b)
                            )
                            for b in (Y[(i + 1):])
                        ]
                    )
                    for i, a in enumerate(Y)
                ]
            )

        elif '?b' in node.label:
            X = [Bool('x_%s_%s' % (node_id, op)) for op in ['&', '|', '->', 'U']]

            # at least one operator and at most one
            solver.add(
                Or(X)
            )
            solver.add(
                [
                    And(
                        [
                            Or(
                                Not(a),
                                Not(b)
                            )
                            for b in (Y[(i + 1):])
                        ]
                    )
                    for i, a in enumerate(Y)
                ]
            )

        if node._isBinary():
            # left child is not type-0
            if not '?' in node.left.label or '?u' in node.left.label or '?b' in node.left.label:
                solver.add(
                    Bool('l_%s_%s' % (node_id, node.left.identifier))
                )
                solver.add(
                    [
                        Not(Bool('l_%s_%s' % (node_id, leftid)))
                        for leftid in id_list if leftid != node.left.identifier
                    ]
                )
            # right child is not type-0
            if not '?' in node.right.label or '?u' in node.right.label or '?b' in node.right.label:
                solver.add(
                    Bool('r_%s_%s' % (node_id, node.right.identifier))
                )
                solver.add(
                    [
                        Not(Bool('r_%s_%s' % (node_id, rightid)))
                        for rightid in id_list if rightid != node.right.identifier
                    ]
                )
# --------------------------------------------------------------------------------------------------- TODO


def cycleConstraints(solver, identifier_list, alphabet):
    """
    Adds constraints to the solver, which ensure that the sketch corresponding to a satisfying model does not contain a
    cycle. The idea is to use a set of path variables p_i_j which indicate that there is a path from i to j in the sense
    that j is in (one of) the subtree(s) of i. Then p_i_i has to be False for all i.
    """

    unary = ['!', 'X', 'G', 'F']
    binary = ['&', '|', '->', 'U']

    # leaves
    solver.add(
        And(
            [
                Implies(
                    Or(
                        [Bool('x_%s_%s' % (id, ap)) for ap in alphabet]
                    ),
                    And(
                        [Not(Bool('p_%s_%s' % (id, target))) for target in identifier_list]
                    )
                )
                for id in identifier_list
            ]
        )
    )

    # unary operators
    solver.add(
        And(
            [
                Implies(
                    Or(
                        [Bool('x_%s_%s' % (id, op)) for op in unary]
                    ),
                    And(
                        [
                            Implies(
                                Bool('l_%s_%s' % (id, leftid)),
                                And(
                                    [Bool('p_%s_%s' % (id, leftid))] +
                                    [
                                        Bool('p_%s_%s' % (id, target)) ==
                                        Bool('p_%s_%s' % (leftid, target))
                                        for target in identifier_list if target != leftid
                                    ]
                                )

                            )
                            for leftid in identifier_list
                        ]
                    )
                )
                for id in identifier_list
            ]
        )
    )

    # binary operators
    solver.add(
        And(
            [
                Implies(
                    Or(
                        [Bool('x_%s_%s' % (id, op)) for op in binary]
                    ),
                    And(
                        [
                            And(
                                [
                                    Implies(
                                        And(
                                            Bool('l_%s_%s' % (id, leftid)),
                                            Bool('r_%s_%s' % (id, rightid))
                                        ),
                                        And(
                                            [Bool('p_%s_%s' % (id, leftid))] +
                                            [Bool('p_%s_%s' % (id, rightid))] +
                                            [
                                                Bool('p_%s_%s' % (id, target)) ==
                                                Or(
                                                    Bool('p_%s_%s' % (leftid, target)),
                                                    Bool('p_%s_%s' % (rightid, target))
                                                )
                                                for target in identifier_list if target != leftid and target != rightid
                                            ]
                                        )
                                    )
                                    for rightid in identifier_list
                                ]
                            )
                            for leftid in identifier_list
                        ]
                    )
                )
                for id in identifier_list
            ]
        )
    )

    # no cycle Constraint
    solver.add(
        And(
            [Not(Bool('p_%s_%s' % (id, id))) for id in identifier_list]
        )
    )
# --------------------------------------------------------------------------------------------------- TODO


def initial_cycleConstraints(solver, sketch_nodes, parent_nodes, alphabet):
    """
    Adds constraints to the solver, which ensure that the sketch corresponding to a satisfying model does not contain a
    cycle. The idea is to use a set of path variables p_i_j which indicate that there is a path from i to j in the sense,
    that j is in (one of) the subtree(s) of i. Then p_i_i has to be False for all i.
    """
    identifier_list = [node.identifier for node in sketch_nodes] + [node.identifier for node in parent_nodes]

    unary = ['!', 'X', 'G', 'F']
    binary = ['&', '|', '->', 'U']

    for node in sketch_nodes:
        label = node.label
        node_id = node.identifier

        if label in alphabet:
            solver.add(
                And(
                    [Not(Bool('p_%s_%s' % (node_id, target))) for target in identifier_list]
                )
            )
        elif label in unary or '?u' in label:
            leftid = node.left.identifier
            solver.add(
                And(
                    [Bool('p_%s_%s' % (node_id, leftid))] +
                    [
                        Bool('p_%s_%s' % (node_id, target)) ==
                        Bool('p_%s_%s' % (leftid, target))
                        for target in identifier_list if target != leftid
                    ]
                )
            )
        elif label in binary or '?b' in label:
            leftid = node.left.identifier
            rightid = node.right.identifier
            solver.add(
                And(
                    [Bool('p_%s_%s' % (node_id, leftid))] +
                    [Bool('p_%s_%s' % (node_id, rightid))] +
                    [
                        Bool('p_%s_%s' % (node_id, target)) ==
                        Or(
                            Bool('p_%s_%s' % (leftid, target)),
                            Bool('p_%s_%s' % (rightid, target))
                        )
                        for target in identifier_list if target != leftid and target != rightid
                    ]
                )
            )

    for node in parent_nodes:
        node_id = node.identifier

        if node._isUnary():
            solver.add(
                And(
                    [
                        Implies(
                            Bool('l_%s_%s' % (node_id, leftid)),    # ->
                            And(
                                [Bool('p_%s_%s' % (node_id, leftid))] +
                                [
                                    Bool('p_%s_%s' % (node_id, target)) ==
                                    Bool('p_%s_%s' % (leftid, target))
                                    for target in identifier_list if target != leftid
                                ]
                            )
                        )
                        for leftid in identifier_list
                    ]
                )
            )
        elif node._isBinary():
            solver.add(
                And(
                    [
                        And(
                            [
                                Implies(
                                    And(
                                        Bool('l_%s_%s' % (node_id, leftid)),
                                        Bool('r_%s_%s' % (node_id, rightid))
                                    ),
                                    And(
                                        [Bool('p_%s_%s' % (node_id, leftid))] +
                                        [Bool('p_%s_%s' % (node_id, rightid))] +
                                        [
                                            Bool('p_%s_%s' % (node_id, target)) ==
                                            Or(
                                                Bool('p_%s_%s' % (leftid, target)),
                                                Bool('p_%s_%s' % (rightid, target))
                                            )
                                            for target in identifier_list if target != leftid and target != rightid
                                        ]
                                    )
                                )
                                for rightid in identifier_list
                            ]
                        )
                        for leftid in identifier_list
                    ]
                )
            )

    # no cycle Constraint
    solver.add(
        And(
            [Not(Bool('p_%s_%s' % (id, id))) for id in identifier_list]
        )
    )
# --------------------------------------------------------------------------------------------------- TODO


def loop_cycleConstraints(solver, parent_nodes, additional_node_ids, new_node_id, identifier_list, alphabet):
    """
    Adds constraints to the solver, which ensure that the sketch corresponding to a satisfying model does not contain a
    cycle. The idea is to use a set of path variables p_i_j which indicate that there is a path from i to j in the sense,
    that j is in (one of) the subtree(s) of i. Then p_i_i has to be False for all i.
    """
    unary = ['!', 'X', 'G', 'F']
    binary = ['&', '|', '->', 'U']

    for node in parent_nodes:
        node_id = node.identifier

        if node._isUnary():
            solver.add(
                Implies(
                    Bool('l_%s_%s' % (node_id, new_node_id)),  # ->
                    And(
                        [Bool('p_%s_%s' % (node_id, new_node_id))] +
                        [
                            Bool('p_%s_%s' % (node_id, target)) ==
                            Bool('p_%s_%s' % (new_node_id, target))
                            for target in identifier_list if target != new_node_id
                        ]
                    )
                )
            )
        elif node._isBinary():
            # new node as left child (and both)
            solver.add(
                And(
                    [
                        Implies(
                            And(
                                Bool('l_%s_%s' % (node_id, new_node_id)),
                                Bool('r_%s_%s' % (node_id, rightid))
                            ),
                            And(
                                [Bool('p_%s_%s' % (node_id, new_node_id))] +
                                [Bool('p_%s_%s' % (node_id, rightid))] +
                                [
                                    Bool('p_%s_%s' % (node_id, target)) ==
                                    Or(
                                        Bool('p_%s_%s' % (new_node_id, target)),
                                        Bool('p_%s_%s' % (rightid, target))
                                    )
                                    for target in identifier_list if target != new_node_id and target != rightid
                                ]
                            )
                        )
                        for rightid in identifier_list
                    ]
                )
            )
            # new node as right child
            solver.add(
                And(
                    [
                        Implies(
                            And(
                                Bool('l_%s_%s' % (node_id, leftid)),
                                Bool('r_%s_%s' % (node_id, new_node_id))
                            ),
                            And(
                                [Bool('p_%s_%s' % (node_id, leftid))] +
                                [Bool('p_%s_%s' % (node_id, new_node_id))] +
                                [
                                    Bool('p_%s_%s' % (node_id, target)) ==
                                    Or(
                                        Bool('p_%s_%s' % (leftid, target)),
                                        Bool('p_%s_%s' % (new_node_id, target))
                                    )
                                    for target in identifier_list if target != leftid and target != new_node_id
                                ]
                            )
                        )
                        for leftid in identifier_list if leftid != new_node_id
                    ]
                )
            )

    # additional nodes: label unclear so add another implication.
    # Only Consider cases with new_node as one of the children.
    for node_id in additional_node_ids:
        # unary operators
        solver.add(
            Implies(
                Or(
                    [Bool('x_%s_%s' % (node_id, op)) for op in unary]
                ),
                Implies(
                    Bool('l_%s_%s' % (node_id, new_node_id)),
                    And(
                        [Bool('p_%s_%s' % (node_id, new_node_id))] +
                        [
                            Bool('p_%s_%s' % (node_id, target)) ==
                            Bool('p_%s_%s' % (new_node_id, target))
                            for target in identifier_list if target != new_node_id
                        ]
                    )
                )
            )
        )

        # binary operators
        # new node as left child (or both)
        solver.add(
            Implies(
                Or(
                    [Bool('x_%s_%s' % (node_id, op)) for op in binary]
                ),
                And(
                    [
                        Implies(
                            And(
                                Bool('l_%s_%s' % (node_id, new_node_id)),
                                Bool('r_%s_%s' % (node_id, rightid))
                            ),
                            And(
                                [Bool('p_%s_%s' % (node_id, new_node_id))] +
                                [Bool('p_%s_%s' % (node_id, rightid))] +
                                [
                                    Bool('p_%s_%s' % (node_id, target)) ==
                                    Or(
                                        Bool('p_%s_%s' % (new_node_id, target)),
                                        Bool('p_%s_%s' % (rightid, target))
                                    )
                                    for target in identifier_list if
                                    target != new_node_id and target != rightid
                                ]
                            )
                        )
                        for rightid in identifier_list
                    ]
                )
            )
        )
        # new node as right child
        solver.add(
            Implies(
                Or(
                    [Bool('x_%s_%s' % (node_id, op)) for op in binary]
                ),
                And(
                    [
                        Implies(
                            And(
                                Bool('l_%s_%s' % (node_id, leftid)),
                                Bool('r_%s_%s' % (node_id, new_node_id))
                            ),
                            And(
                                [Bool('p_%s_%s' % (node_id, leftid))] +
                                [Bool('p_%s_%s' % (node_id, new_node_id))] +
                                [
                                    Bool('p_%s_%s' % (node_id, target)) ==
                                    Or(
                                        Bool('p_%s_%s' % (leftid, target)),
                                        Bool('p_%s_%s' % (new_node_id, target))
                                    )
                                    for target in identifier_list if
                                    target != leftid and target != new_node_id
                                ]
                            )
                        )
                        for leftid in identifier_list if leftid != new_node_id
                    ]
                )
            )
        )

    # new node - no cycle Constraint
    solver.add(
        Not(Bool('p_%s_%s' % (new_node_id, new_node_id)))
    )
    # new node as leaf
    solver.add(
        Implies(
            Or(
                [Bool('x_%s_%s' % (new_node_id, ap)) for ap in alphabet]
            ),  # ->
            And(
                [
                    Not(Bool('p_%s_%s' % (new_node_id, target)))
                    for target in identifier_list if target != new_node_id
                ]
            )
        )
    )

    # new node as unary operator
    solver.add(
        Implies(
            Or(
                [Bool('x_%s_%s' % (new_node_id, op)) for op in unary]
            ),
            And(
                [
                    Implies(
                        Bool('l_%s_%s' % (new_node_id, leftid)),
                        And(
                            [Bool('p_%s_%s' % (new_node_id, leftid))] +
                            [
                                Bool('p_%s_%s' % (new_node_id, target)) ==
                                Bool('p_%s_%s' % (leftid, target))
                                for target in identifier_list if target != leftid
                            ]
                        )
                    )
                    for leftid in identifier_list
                ]
            )
        )
    )

    # new node as binary operator
    solver.add(
        Implies(
            Or(
                [Bool('x_%s_%s' % (new_node_id, op)) for op in binary]
            ),
            And(
                [
                    And(
                        [
                            Implies(
                                And(
                                    Bool('l_%s_%s' % (new_node_id, leftid)),
                                    Bool('r_%s_%s' % (new_node_id, rightid))
                                ),
                                And(
                                    [Bool('p_%s_%s' % (new_node_id, leftid))] +
                                    [Bool('p_%s_%s' % (new_node_id, rightid))] +
                                    [
                                        Bool('p_%s_%s' % (new_node_id, target)) ==
                                        Or(
                                            Bool('p_%s_%s' % (leftid, target)),
                                            Bool('p_%s_%s' % (rightid, target))
                                        )
                                        for target in identifier_list if
                                        target != leftid and target != rightid
                                    ]
                                )
                            )
                            for rightid in identifier_list
                        ]
                    )
                    for leftid in identifier_list
                ]
            )
        )
    )
# ---------------------------------------------------------------------------------------------------
