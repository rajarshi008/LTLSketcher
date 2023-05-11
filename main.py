import argparse, json
from pytictoc import TicToc
from sample import Sample
from sketch import Sketch
from helping_functions import reduce_sample
from algorithm_tree_new import check_existence_tree
from algorithm_tree_suffix_new import check_existence_tree_suffix
from algorithm_tree_bmc_new import check_existence_tree_bmc
from algorithm_tree_suffix_bmc_new import check_existence_tree_suffix_bmc
from algorithm_cycle_free_new import check_existence_cycle_free
from algorithm_cycle_free_bmc_new import check_existence_cycle_free_bmc
from algorithm_cycle_free_suffix_new import check_existence_cycle_free_suffix
from algorithm_cycle_free_suffix_bmc_new import check_existence_cycle_free_suffix_bmc


# Variables to enable different prints and the creation of log-files
solver_log_file = True
print_output = True


def main():
    """
	Check whether there exists a set of substitutions for the given sketch, such that the resulting completed sketch
	is consistent with the given sample. If such a set exists, compute the substitutions resulting in the smallest
	completed sketch, apply them and check consistency with the sample.
	"""
    # arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--input_file', '-i', dest='input_file', default='example.trace')
    parser.add_argument('--sketch', '-s', dest='sketch', default='G(?1)')
    parser.add_argument('--mode', '-m', dest='mode', default='tree', choices=['tree'])
    parser.add_argument('--suffix', '-suf', dest='suffix_optimization', default=False, action='store_true')
    parser.add_argument('--bmc', '-bmc', dest='bmc_optimization', default=False, action='store_true')

    args, unknown = parser.parse_known_args()

    input_file = args.input_file
    sketch = args.sketch
    mode = args.mode
    suffix_optimization = args.suffix_optimization
    bmc_optimization = args.bmc_optimization


    s = Sample()
    s.readFromFile(input_file)
    reduce_sample(s)

    
    f = Sketch.convertTextToSketch(sketch)
    starting_id = 0
    f.assign_identifiers(starting_id)
    f.reduce()
    run_solver(s, f, mode, suffix_optimization, bmc_optimization)

# -----------------------------------------------------------------------------------------------------
def run_solver(s, f, algo, suffix_optimization, bmc_optimization):
    try:
        if algo == 'tree':
            if suffix_optimization and bmc_optimization:
                if print_output:
                    print('tree algorithm - with suffix- and bmc-optimization')
                check_existence_tree_suffix_bmc(s, f)
            elif suffix_optimization:
                if print_output:
                    print('tree algorithm - with suffix-optimization')
                check_existence_tree_suffix(s, f)
            elif bmc_optimization:
                if print_output:
                    print('tree algorithm - with bmc-optimization')
                check_existence_tree_bmc(s, f)
            else:
                if print_output:
                    print('tree algorithm - without optimizations')
                check_existence_tree(s, f)
        elif algo == 'cycle-free':
            if suffix_optimization and bmc_optimization:
                if print_output:
                    print('cycle-free algorithm - with suffix- and bmc-optimization')
                check_existence_cycle_free_suffix_bmc(s, f)

            elif suffix_optimization:
                if print_output:
                    print('cycle-free algorithm - with suffix-optimization')
                check_existence_cycle_free_suffix(s, f)
            elif bmc_optimization:
                if print_output:
                    print('cycle-free algorithm - with bmc-optimization')
                check_existence_cycle_free_bmc(s, f)
            else:
                if print_output:
                    print('cycle-free algorithm - without optimizations')
                check_existence_cycle_free(s, f)
        else:
            raise TypeError("Invalid mode")

        if print_output:
            print('Complete LTL formula:', f)
        return 0

    except TypeError as terr:
        print(terr)
        return 1
    except:
        return 1

# -----------------------------------------------------------------------------------------------------
if __name__ == "__main__":
    main()



############ For experiments ############
def log_results(trace_file, sketch_str, timeout, mode, output_file_name): # mode is outputfilename
    '''
    A function to run note the results
    '''
    print("-----------LTL sketching on %s using %s-----------"%(trace_file, mode))

    s = Sample(positive = [], negative=[], original_formula=None, alphabet=[])
    s.readFromFile(trace_file)
    reduce_sample(s)
    f = Sketch.convertTextToSketch(sketch_str)

    starting_id = 0
    f.assign_identifiers(starting_id)
    f.reduce()

    mode_split = mode.split('-')
    algo = mode_split[0]
    parameters = mode_split[1:]
    bmc = True if 'bmc' in parameters else False
    suf = True if 'suf' in parameters else False
    # Header: algorithm-type, running time, sample-file, sketch, number of positive words, number of positive words,
    # completed sketch, final size

    
    sketch_str = str(f)
    original_formula_str = str(s.original_formula)
    ver = 'NA'

    info_dict = {"File name":trace_file,\
                 "Algo type":mode,\
                 "Original Formula":original_formula_str,\
                 "Sketch": sketch_str,\
                 "Total time":timeout,
                 "Completed sketch":'',\
                 "Final size":0,\
                 "Verified":ver}

    print(output_file_name)
    with open(output_file_name, 'w') as file:
        json.dump(info_dict, file)

    t = TicToc()
    t.tic()
    run_solver(s, f, algo, suf, bmc)
    complete_sketch_str = str(f)
    time_passed = t.tocvalue()
    
    try:
        ver = s.isFormulaConsistent(f)
    except:
        ver = 'NA'

    info_dict.update({"Total time":time_passed,
                 "Completed sketch":complete_sketch_str,\
                 "Final size":f.treeSize(),\
                 "Verified": ver\
                    })
    
    with open(output_file_name, 'w') as file:
        json.dump(info_dict, file)

#log_results('experiment_results/generated_files/final_benchmark/f:03-nw:100-ml:10-0.trace', '?u1(->(q,?u1(!(p))))', 300, 'tree-bmc', 'check.json')


