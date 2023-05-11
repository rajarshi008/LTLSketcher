from sample import Trace
from sketch import Sketch
from z3 import *


def pretty_print_dic_list(dic_list):
    for dic in dic_list:
        print(dic)
# ---------------------------------------------------------------------------------------------------


def pretty_print_sample(sample):
    for p in sample.positive:
        print(p)
    print('----------')
    for n in sample.negative:
        print(n)
# ---------------------------------------------------------------------------------------------------


def build_suffix(word, pos):
    if pos <= word.lasso_start:
        suffix = Trace(word.vector[pos:], word.lasso_start-pos)
    else:
        lasso = word.vector[pos:] + word.vector[word.lasso_start:pos]
        suffix = Trace(lasso, 0)

    return suffix
# ---------------------------------------------------------------------------------------------------


def equal(word_1, word_2):
    if word_2.lasso_start > word_1.lasso_start:     # u_2 > u_1
        return equal(word_2, word_1)

    else:
        abs_u1 = word_1.lasso_start
        abs_v2 = len(word_2.lasso)
        lcm = leastCommonMultiple(len(word_1.lasso), len(word_2.lasso))
        size = abs_u1 + abs_v2 + lcm

        if unroll(word_1.prefix, word_1.lasso, size) == unroll(word_2.prefix, word_2.lasso, size):
            return True
        else:
            return False
# ---------------------------------------------------------------------------------------------------


def is_true_suffix_of(word_1, word_2):
    for i in range(1, word_2.length):
        if equal(word_1, build_suffix(word_2, i)):
            return True, i

    return False, -1
# ---------------------------------------------------------------------------------------------------


def unroll(finitePart, lassoPart, length):
    """
    unrolls a ultimately periodic word up to the given length
    """
    result = copy.copy(finitePart)
    while len(result) < length:
        result += lassoPart
    return result[:length]
# ---------------------------------------------------------------------------------------------------


def leastCommonMultiple(a, b):
    """
    calculates the least common multiple of a and b
    """
    return abs(a * b) // math.gcd(a, b)
# ---------------------------------------------------------------------------------------------------


def reduce_sample(sample):
    traces = sample.positive + sample.negative

    for idx, trace in enumerate(traces):
        # reduce lasso (remove multiple loops)
        for loop_length in range(1, int(trace.lasso_length/2)+1):
            if trace.lasso_length % loop_length == 0:       # length is dividable by l
                multiple = True
                for j in range(loop_length, trace.lasso_length):
                    i = j % loop_length

                    if trace.lasso[i] != trace.lasso[j]:
                        multiple = False
                        break
                if multiple:
                    trace.lasso = trace.lasso[:loop_length]
                    trace.lasso_length = loop_length
                    trace.vector = trace.prefix + trace.lasso
                    trace.length = trace.prefix_length + trace.lasso_length
                    break

        # reduce prefix (shift lasso if possible)
        prefix_pos = trace.prefix_length-1
        while prefix_pos >= 0:
            if trace.prefix[-1] == trace.lasso[-1]:
                trace.lasso = [trace.lasso[-1]] + trace.lasso[:-1]
                trace.lasso_start -= 1
                trace.prefix = trace.prefix[:-1]
                trace.prefix_length -= 1
                trace.vector = trace.prefix + trace.lasso
                trace.length = trace.prefix_length + trace.lasso_length
                prefix_pos -= 1
            else:
                break

    # for debugging
    # pretty_print_sample(sample)
# ---------------------------------------------------------------------------------------------------


def suc_1(prefix, lasso, pos):
    word = Trace(prefix + lasso, len(prefix))
    return word.nextPos(pos)
# ---------------------------------------------------------------------------------------------------


def suc_2(sample_entry, pos):
    if pos < len(sample_entry["prefix"]) -1:
        return sample_entry["id"], pos+1
    else:
        return sample_entry["sid"], sample_entry["startpos"]
# ---------------------------------------------------------------------------------------------------


def FUT_1(prefix, lasso, pos):
    word = Trace(prefix + lasso, len(prefix))
    return word.futurePos(pos)
# ---------------------------------------------------------------------------------------------------


def FUT_2(sample_entry, pos, suffix_entry):
    future_positions = []

    for pos_p in range(pos, len(sample_entry["prefix"])):
        future_positions.append((sample_entry["id"], pos_p))

    for f in FUT_1(suffix_entry["u"], suffix_entry["v"], sample_entry["startpos"]):
        future_positions.append((suffix_entry["sid"], f))

    return future_positions
# ---------------------------------------------------------------------------------------------------


def BET_1(prefix, lasso, pos_1, pos_2):
    word = Trace(prefix + lasso, len(prefix))
    return word.auxiliaryPos(pos_1, pos_2)
# ---------------------------------------------------------------------------------------------------


def BET_2(id_1, pos_1, id_2, pos_2, start_pos, prefix_length):
    between_positions = []

    if str(id_1) == str(id_2):
        for k in range(pos_1, pos_2):
            between_positions.append((id_1, k))

    else:
        for k in range(pos_1, prefix_length):
            between_positions.append((id_1, k))

        for k in range(start_pos, pos_2):
            between_positions.append((id_2, k))

    return between_positions
# ---------------------------------------------------------------------------------------------------


def sample_to_tables(sample):
    size = sample.num_positives + sample.num_negatives
    traces = sample.positive + sample.negative

    # initialize variables
    sample_table = []  # table of dictionaries{id,prefix,sid,startpos}
    suffix_table = []  # table of dictionaries{sid,u,v,list}

    reference_table = [None] * size  # maps id of example to entry in sample_table
    suffix_counter = 0  # keeps track of the number of suffixes in suffix_table (to get new sid)
    sample_counter = 0  # keeps track of the number of samples in sample_table (to set reference table)

    for xid, x in enumerate(traces):
        has_suffix_at_all = False

        for offset, y in enumerate(traces[xid + 1:]):
            yid = xid + 1 + offset
            has_common_suffix = False
            common_suffix = None
            x_suffix_start = -1
            y_suffix_start = -1

            # search for common suffix
            for i in range(x.length):
                suffix_1 = build_suffix(x, i)
                for j in range(y.length):
                    suffix_2 = build_suffix(y, j)

                    if equal(suffix_1, suffix_2):
                        has_common_suffix = True
                        common_suffix = suffix_1
                        x_suffix_start = i
                        y_suffix_start = j
                        break

                if has_common_suffix:
                    break

            # Common suffix was found, check reference-table to see in which case we are
            if has_common_suffix:
                has_suffix_at_all = True

                # case 1:
                if reference_table[xid] is None and reference_table[yid] is None:
                    sample_entry_x = {
                        "id": xid,
                        "prefix": x.vector[:x_suffix_start],
                        "sid": 's' + str(suffix_counter),
                        "startpos": 0
                    }
                    sample_table.append(sample_entry_x)
                    reference_table[xid] = sample_counter
                    sample_counter += 1

                    sample_entry_y = {
                        "id": yid,
                        "prefix": y.vector[:y_suffix_start],
                        "sid": 's' + str(suffix_counter),
                        "startpos": 0
                    }
                    sample_table.append(sample_entry_y)
                    reference_table[yid] = sample_counter
                    sample_counter += 1

                    suffix_entry = {
                        "sid": 's' + str(suffix_counter),
                        "u": common_suffix.prefix,
                        "v": common_suffix.lasso,
                        "list": [xid, yid]
                    }
                    suffix_table.append(suffix_entry)
                    suffix_counter += 1

                # case 2:
                elif reference_table[xid] is not None and reference_table[yid] is None:
                    u = suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["u"]
                    v = suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["v"]
                    entry = Trace(u + v, len(u))

                    # case 2.1
                    if equal(common_suffix, entry):
                        sample_entry_y = {
                            "id": yid,
                            "prefix": y.vector[:y_suffix_start],
                            "sid": sample_table[reference_table[xid]]["sid"],
                            "startpos": 0
                        }
                        sample_table.append(sample_entry_y)
                        reference_table[yid] = sample_counter
                        sample_counter += 1

                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["list"].append(yid)

                    # case 2.2
                    c_suffix_of_e, pos = is_true_suffix_of(common_suffix, entry)
                    if c_suffix_of_e:
                        sample_entry_y = {
                            "id": yid,
                            "prefix": y.vector[:y_suffix_start],
                            "sid": sample_table[reference_table[xid]]["sid"],
                            "startpos": pos
                        }
                        sample_table.append(sample_entry_y)
                        reference_table[yid] = sample_counter
                        sample_counter += 1

                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["list"].append(yid)

                    # case 2.3
                    e_suffix_of_c, pos = is_true_suffix_of(entry, common_suffix)
                    if e_suffix_of_c:
                        additional_size = pos
                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["u"] = common_suffix.prefix
                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["v"] = common_suffix.lasso

                        for lid in suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["list"]:
                            sample_table[reference_table[lid]]["startpos"] += additional_size

                        sample_table[reference_table[xid]]["pre"] = x.vector[:x_suffix_start]
                        sample_table[reference_table[xid]]["startpos"] = 0

                        sample_entry_y = {
                            "id": yid,
                            "prefix": y.vector[:y_suffix_start],
                            "sid": sample_table[reference_table[xid]]["sid"],
                            "startpos": 0
                        }
                        sample_table.append(sample_entry_y)
                        reference_table[yid] = sample_counter
                        sample_counter += 1

                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["list"].append(yid)

                # case 3:
                elif reference_table[xid] is None and reference_table[yid] is not None:
                    print('ERROR')
                    exit(1)

                # case 4:
                elif reference_table[xid] is not None and reference_table[yid] is not None:
                    u = suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["u"]
                    v = suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["v"]
                    entry = Trace(u + v, len(u))

                    # Compare entry 1 and common_suffix
                    e_suffix_of_c, pos = is_true_suffix_of(entry, common_suffix)

                    if e_suffix_of_c:
                        additional_size = pos
                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["u"] = common_suffix.prefix
                        suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["v"] = common_suffix.lasso

                        for lid in suffix_table[int(sample_table[reference_table[xid]]["sid"][1:])]["list"]:
                            sample_table[reference_table[lid]]["startpos"] += additional_size

                        sample_table[reference_table[xid]]["prefix"] = x.vector[:x_suffix_start]
                        sample_table[reference_table[xid]]["startpos"] = 0

                        sample_table[reference_table[yid]]["prefix"] = y.vector[:y_suffix_start]
                        sample_table[reference_table[yid]]["startpos"] = 0

        # case 5
        if not has_suffix_at_all and reference_table[xid] is None:
            sample_entry = {
                "id": xid,
                "prefix": [],
                "sid": 's' + str(suffix_counter),
                "startpos": 0
            }
            sample_table.append(sample_entry)
            reference_table[xid] = sample_counter
            sample_counter += 1

            suffix_entry = {
                "sid": 's' + str(suffix_counter),
                "u": x.prefix,
                "v": x.lasso,
                "list": [xid]
            }
            suffix_table.append(suffix_entry)
            suffix_counter += 1

    # Postprocessing of the Construction of the 2 tables
    for zid, z in enumerate(sample_table):
        u = suffix_table[int(z["sid"][1:])]["u"]
        v = suffix_table[int(z["sid"][1:])]["v"]
        entry = Trace(u + v, len(u))

        for i in range(len(z["prefix"])):
            u_i = z["prefix"][i:] + u
            v_i = v
            word_i = Trace(u_i + v_i, len(u_i))

            z_from_i_suffix_of_entry, pos = is_true_suffix_of(word_i, entry)
            if z_from_i_suffix_of_entry:
                z["prefix"] = z["prefix"][:i]
                z["startpos"] = pos

    return sample_table, suffix_table
# --------------------------------------------------------------------------------------------------- TODO


def construct_Sketch_from_Model(model, alphabet, id, number_of_nodes):
    """
    recursively constructs a Sketch induced by the given model
    """
    sketch = Sketch()
    sketch.identifier = id

    leaf = [ap for ap in alphabet if z3.is_true(model[z3.Bool('x_%s_%s' % (id, ap))])]
    unary = [op for op in ['!', 'X', 'G', 'F'] if z3.is_true(model[z3.Bool('x_%s_%s' % (id, op))])]
    binary = [op for op in ['&', '|', '->', 'U'] if z3.is_true(model[z3.Bool('x_%s_%s' % (id, op))])]

    if len(leaf) > 0:
        ap = leaf[0]
        sketch.label = ap
        sketch.left = None
        sketch.right = None

    elif len(unary) > 0:
        op = unary[0]
        sketch.label = op

        lchild = [lid for lid in range(id + 1, number_of_nodes) if z3.is_true(model[z3.Bool('l_%s_%s' % (id, lid))])][0]
        sketch.left = construct_Sketch_from_Model(model, alphabet, lchild, number_of_nodes)

        sketch.right = None

    elif len(binary) > 0:
        op = binary[0]
        sketch.label = op

        lchild = [lid for lid in range(id + 1, number_of_nodes) if z3.is_true(model[z3.Bool('l_%s_%s' % (id, lid))])][0]
        sketch.left = construct_Sketch_from_Model(model, alphabet, lchild, number_of_nodes)

        rchild = [rid for rid in range(id + 1, number_of_nodes) if z3.is_true(model[z3.Bool('r_%s_%s' % (id, rid))])][0]
        sketch.right = construct_Sketch_from_Model(model, alphabet, rchild, number_of_nodes)

    return sketch
# --------------------------------------------------------------------------------------------------- TODO


def construct_Sketch_from_Model_cycle_free(rootid, model, alphabet, identifier_list):
    """
    recursively constructs a Sketch induced by the given model.
    If node already exists this one is used instead
    """

    sketch_list = []
    labels = alphabet + ['!', 'X', 'G', 'F', '&', '|', '->', 'U']

    for id in identifier_list:
        label = [label for label in labels if is_true(model[Bool('x_%s_%s' % (id, label))])][0]

        sketch = Sketch()
        sketch.identifier = id
        sketch.label = label

        sketch_list.append(sketch)

    for sketch in sketch_list:
        id = sketch.identifier

        if sketch.label in ['!', 'X', 'G', 'F']:
            left = [pos for pos in identifier_list if is_true(model[Bool('l_%s_%s' % (id, pos))])][0]
            sketch.left = sketch_list[identifier_list.index(left)]

        elif sketch.label in ['&', '|', '->', 'U']:
            left = [pos for pos in identifier_list if is_true(model[Bool('l_%s_%s' % (id, pos))])][0]
            sketch.left = sketch_list[identifier_list.index(left)]

            right = [pos for pos in identifier_list if is_true(model[Bool('r_%s_%s' % (id, pos))])][0]
            sketch.right = sketch_list[identifier_list.index(right)]

    return sketch_list[identifier_list.index(rootid)]
# ---------------------------------------------------------------------------------------------------

