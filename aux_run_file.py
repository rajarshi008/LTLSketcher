import csv
from pytictoc import TicToc
from main import run_solver
from sample import *
from sketch import Sketch
from helping_functions import reduce_sample
import shutil

solver_log_file = False
print_output = False


def results_sketcher(trace_file, timeout, mode, suf_op, bmc_op):		# mode is output-filename
	"""
	An auxiliary function to run the code
	"""
	print("#####RUNNING SKETCHER on {}#####".format(trace_file))

	s, sketch_str, original_f_str = readFromFile(trace_file)
	reduce_sample(s)

	f = Sketch.convertTextToSketch(sketch_str)
	starting_id = 1
	f.assign_identifiers(starting_id)
	f.reduce()

	# Header: sample-file, number of positive words, number of negative words, algorithm-type, running time, sketch,
	# completed sketch, final size, status

	print(trace_file)
	output_file_name = trace_file.split('.trace')[0]+'-' + mode
	alg_type = mode
	if suf_op:
		output_file_name += '-suf'
		alg_type += '-suf'
	if bmc_op:
		output_file_name += '-bmc'
		alg_type += '-bmc'

	output_file_name += '.csv'
	print(output_file_name)


	with open(output_file_name, 'w') as file:
		
		writer = csv.writer(file)
		time_passed = timeout
		csvInfo = [trace_file, str(s.num_positives), str(s.num_negatives), mode, str(time_passed), sketch_str, "",
				   original_f_str, 'Timeout']
		writer.writerow(csvInfo)

	t = TicToc()
	t.tic()
	
	exit_code = run_solver(s, f, mode, suf_op, bmc_op)
	complete_sketch_str = str(f) 
	time_passed = t.tocvalue()

	if exit_code == 1:
		status = 'Error'
	else:
		status = str(s.isFormulaConsistent(f))
	
	with open(output_file_name, 'w') as file:
		writer = csv.writer(file)
		csvInfo = [trace_file, str(s.num_positives), str(s.num_negatives), mode, str(round(time_passed, 2)), sketch_str,
				   complete_sketch_str, original_f_str, str(len(f.getUniqueNodes())), status]
		writer.writerow(csvInfo)


# ----------------------------------------------------------------------------
def readFromFile(filename):
	positives = []
	negatives = []

	with open(filename, 'r') as file:
		mode = 0

		while True:
			line = file.readline()
			if line == '':
				break

			if line == '---\n':
				mode += 1
				continue

			if mode == 0:
				trace_vector, lasso_start = lineToTrace(line)
				trace = Trace(vector=trace_vector, lasso_start=lasso_start)
				positives.append(trace)

			if mode == 1:
				trace_vector, lasso_start = lineToTrace(line)
				trace = Trace(vector=trace_vector, lasso_start=lasso_start)
				negatives.append(trace)

			if mode == 2:
				sketch = line.strip()

			if mode == 3:
				original = line.strip()

	alphabet = [chr(ord('p') + i) for i in range(len(positives[0].vector[0]))]
	s = Sample(positive=positives, negative=negatives, alphabet=alphabet)

	s.letter2pos = {s.alphabet[i]: i for i in range(len(s.alphabet))}

	return s, sketch, original


results_sketcher('../dummy/2.trace', 100, 'tree', False, False)
