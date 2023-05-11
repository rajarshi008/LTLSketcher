from ce_sample_gen import CEGSampleGenerator, ce_sample_gen
from sketch import Sketch
from rq import Queue
from redis import Redis
import os, json, csv
import glob
import argparse
import datetime


class multiprocess:
	"""
	Class that handles the multiprocessing (requires redis installation)
	"""

	def __init__(self, pairs, reps, output_folder, timeout):
		
		self.timeout = timeout
		self.pairs = pairs
		self.reps = reps
		self.output_folder = output_folder
		self.compiled_file = self.output_folder + '/compiled_info.csv'

	def populate_queue(self):
		"""
		Creates the work queue with different experiments
		"""
		redis_conn = Redis()
		q = Queue('Sample-experiments', connection=redis_conn)
		q.empty()

		for i,pair in enumerate(self.pairs):

			original_formula = pair[0]
			sketch = pair[1]
			alphabet = pair[2]
			sample_name = self.output_folder + '/aux'+str(i)+'.trace'
			output_name = self.output_folder + '/aux'+str(i)+'.json'
			q.enqueue(ce_sample_gen, args=(original_formula, \
											sketch, alphabet,\
											self.reps, sample_name,\
											output_name),
					job_timeout=self.timeout)

			
		print('Length of queue', len(q))

	def compile_results(self):
		"""
		Compiles the results from different experiments
		"""
		jsonFileList = []
		# Reading all the json files
		for root, dirs, files in os.walk(self.output_folder):
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
		"""
		Cleans up the intermediate csv/json files
		"""

		jsonFileList = []

		for root, dirs, files in os.walk(self.output_folder):
			for file in files:
				if file.endswith('.json'):
					jsonFileList.append(str(os.path.join(root, file)))
		
		for file in jsonFileList:
			if file != self.compiled_file:
				os.remove(file)


def run_tests():
	parser = argparse.ArgumentParser()
	parser.add_argument('--output_folder', dest='output_folder', default='experiment_results/sample_info')
	parser.add_argument('--pairs_file', dest='pairs_file', default='sketch_pairs.txt')
	parser.add_argument('--reps', dest='reps', default=10)
	parser.add_argument('--compile', dest='compile_results', action='store_true', default=False)
	parser.add_argument('--timeout', dest='timeout', default=900)

	args, unknown = parser.parse_known_args()

	output_folder = args.output_folder
	pairs_file = output_folder + '/' + args.pairs_file
	reps = int(args.reps)
	timeout = int(args.timeout)
	compile_results = bool(args.compile_results)

	with open(pairs_file, 'r') as file:

		pairs = []
		while True:
			line = file.readline()
			if line == '':
				break
			
			original_formula, sketches, alphabet = line.split(':')
			sketches = sketches.split(';')
			alphabet = alphabet.strip().split(',')

			pairs.extend([(original_formula, sketch, alphabet) for sketch in sketches])

	
	m = multiprocess(pairs, reps, output_folder, timeout)

	if compile_results:
		m.compile_results()
		#m.clean_files()
	else:
		m.populate_queue()


if __name__ == '__main__':
	run_tests()
