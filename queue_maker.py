from rq import Queue
from redis import Redis
import os
import glob
import argparse
from aux_run_file import *
import datetime


class multiprocess:
	"""
	Class that handles the multiprocessing (requires redis installation)
	"""

	def __init__(self, benchmark_folder, modes, timeout):
		
		self.benchmark_folder = benchmark_folder
		self.timeout = timeout
		self.modes = modes
		self.tracelist = glob.glob(self.benchmark_folder+'/**/*.trace', recursive=True)
		self.compiled_file = 'tool-runs.csv'

	def populate_queue(self):
		"""
		Creates the work queue with different experiments
		"""
		redis_conn = Redis()
		q = Queue('Sketching-experiments', connection=redis_conn)
		q.empty()
		
		for file in self.tracelist:
			if 'tree' in self.modes:
				q.enqueue(results_sketcher, args=(file,
										self.timeout, 
										'tree',
										False,
										False),
						job_timeout=self.timeout)

			if 'tree-suf' in self.modes:
				q.enqueue(results_sketcher, args=(file,
										self.timeout,
										'tree',
										True,
										False),
						job_timeout=self.timeout)

			if 'tree-bmc' in self.modes:
				q.enqueue(results_sketcher, args=(file,
										self.timeout,
										'tree',
										False,
										True),
						job_timeout=self.timeout)

			if 'tree-suf-bmc' in self.modes:
				q.enqueue(results_sketcher, args=(file,
										self.timeout,
										'tree',
										True,
										True),
						job_timeout=self.timeout)

			if 'cycle-free' in self.modes:
			
				q.enqueue(results_sketcher, args=(file,
												self.timeout,
												'cycle-free',
												False,
												False),
							job_timeout=self.timeout)
			if 'cycle-free-suf' in self.modes:
				q.enqueue(results_sketcher, args=(file,
												  self.timeout,
												  'cycle-free',
												True,
												False),
						  job_timeout=self.timeout)
			if 'cycle-free-bmc' in self.modes:
				q.enqueue(results_sketcher, args=(file,
												  self.timeout,
												  'cycle-free',
												False,
												True),
						  job_timeout=self.timeout)
			if 'cycle-free-suf-bmc' in self.modes:
				q.enqueue(results_sketcher, args=(file,
												  self.timeout,
												  'cycle-free',
												True,
												True),
						  job_timeout=self.timeout)
			
		print('Length of queue', len(q))

	def compile_results(self):
		"""
		Compiles the results from different experiments
		"""
		csvInfo = []
		csvFileList = []
		# Reading all the csv files in the folder
		for root, dirs, files in os.walk(self.benchmark_folder):
			for file in files:
				if file.endswith('.csv'):
					csvFileList.append(str(os.path.join(root, file)))
			
		for csvFile in csvFileList:
			
			with open(csvFile, 'r') as file2:
				reader = csv.reader(file2)
				for row in reader:
					csvInfo.append(row)

		with open(self.compiled_file, 'w') as file1:
			writer = csv.writer(file1)

			header = ["Sample file", "Num positive words", "Num of negative words", "Algorithm-type", "Running time",
					  "Sketch", "Completed Sketch", "Starting formula", "Final Size", "Status"]
				
			csvInfo = [header] + csvInfo

			writer.writerows(csvInfo)

			# for file in csvFileList:
			# 	os.remove(file)

	def clean_files(self):
		"""
		Cleans up the intermediate csv/json files
		"""

		csvFileList = []

		for root, dirs, files in os.walk(self.benchmark_folder):
			for file in files:
				if file.endswith('.csv'):
					csvFileList.append(str(os.path.join(root, file)))
		for file in csvFileList:

			if file != self.compiled_file:
				os.remove(file)


def run_tests():
	parser = argparse.ArgumentParser()
	parser.add_argument('--benchmark_folder', dest='benchmark_folder', default='Tests-dummy/')
	parser.add_argument('--modes', dest='modes', default=['tree', 'tree-suf', 'tree-bmc', 'tree-suf-bmc'], nargs='+', type=list)
	parser.add_argument('--compile', dest='compile_results', action='store_true', default=False)
	parser.add_argument('--timeout', dest='timeout', default=200)

	args, unknown = parser.parse_known_args()

	benchmark_folder = args.benchmark_folder
	timeout = int(args.timeout)
	modes = list(args.modes)
	compile_results = bool(args.compile_results)

	print(benchmark_folder)
	m = multiprocess(benchmark_folder, modes, timeout)

	if compile_results:
		m.compile_results()
		#m.clean_files()
	else:
		m.populate_queue()


if __name__ == '__main__':
	run_tests()
