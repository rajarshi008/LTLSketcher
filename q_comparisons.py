from rq import Queue, Worker, Connection
from redis import Redis
from random import seed
from random import random
import csv, json
import os
import glob
import argparse
from main import log_results
import datetime
from sample import Sample


class multiprocess:
	'''
	Class that handles the multiprocessing (requires redis installation)
	'''

	def __init__(self, benchmark_folder, sketch_dict, modes, timeout):
		
		self.benchmark_folder = benchmark_folder
		self.timeout = timeout
		self.modes = modes
		self.sketch_dict = sketch_dict
		self.tracelist = glob.glob(self.benchmark_folder+'/**/*.trace', recursive = True)	
		self.compiled_file = 'tool-runs.csv'

	def populate_queue(self):
		'''
		Creates the work queue with different experiments
		'''
		redis_conn= Redis()
		q = Queue('Sketching-experiments', connection=redis_conn)
		q.empty()
		
		for file in self.tracelist:
			s=Sample()
			s.readFromFile(file)
			formula = s.original_formula
			print(formula, self.sketch_dict[formula])
			for mode in self.modes:
				#log_results(trace_file, timeout, mode)
				for i, sketch in enumerate(self.sketch_dict[formula]):
					output_file_name = file.split('.trace')[0]+'-' + mode + '-' + str(i) + '.json'
					#print(output_file_name)	
					q.enqueue(log_results, args=(file, sketch,\
													self.timeout,mode,\
													output_file_name),\
								job_timeout=self.timeout)

			
		print('Length of queue', len(q))

	
	def compile_results(self):
		"""
		Compiles the results from different experiments
		"""
		jsonFileList = []
		# Reading all the json files
		for root, dirs, files in os.walk(self.benchmark_folder):
			for file in files:
				if file.endswith('.json'):
					jsonFileList.append(str(os.path.join(root, file)))
		
		print(jsonFileList)
		#Getting the json keys
		with open(jsonFileList[0], 'r') as file:
			info_dict = json.load(file)
			csv_keys = info_dict.keys()

		#Writing the header
		csv_file = open(self.compiled_file, 'w')
		dict_writer = csv.DictWriter(csv_file, csv_keys)
		dict_writer.writeheader()

		#Writing the entries
		for json_file in jsonFileList:
			with open(json_file, 'r') as file:
				csv_info = json.load(file)
			dict_writer.writerow(csv_info)

		csv_file.close()


	def clean_files(self):
		'''
		Cleans up the intermediate csv/json files
		'''

		csvFileList = []
		

		for root, dirs, files in os.walk(self.benchmark_folder):
			for file in files:
				if file.endswith('.csv'):
					csvFileList.append(str(os.path.join(root, file)))
		for file in csvFileList:

			if file != self.compiled_file:
				os.remove(file)


		

def main():
	parser = argparse.ArgumentParser()
	parser.add_argument('--benchmark_folder', dest='benchmark_folder', default='experiment_results/generated_files/example')
	parser.add_argument('--sketch_file', dest='sketch_file', default='experiment_results/generated_files/sketches.txt')
	parser.add_argument('--modes', dest='modes', default=['tree', 'tree-suf', 'tree-bmc', 'tree-suf-bmc'], nargs='+', type=list)
	parser.add_argument('--compile', dest='compile_results', action='store_true', default=False)
	parser.add_argument('--timeout', dest='timeout', default=600)

	args,unknown = parser.parse_known_args()

	benchmark_folder = args.benchmark_folder
	timeout = int(args.timeout)
	modes = list(args.modes)
	compile_results = bool(args.compile_results)
	sketch_file = args.sketch_file

	sketch_dict = {}
	with open(sketch_file, 'r') as file:

		while True:
			line = file.readline()
			if line == '':
				break
			formula, sketches = line.strip().split(':')
			sketch_dict[formula] = sketches.split(';')

	m = multiprocess(benchmark_folder, sketch_dict, modes, timeout)

	if compile_results:
		m.compile_results()
		#m.clean_files()
	else:
		m.populate_queue()



if __name__ == '__main__':
    main() 
