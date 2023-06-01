import argparse
import os, shutil, glob, csv
import datetime
from sample import Sample, Trace
from sketch import Sketch

class GenerateBatch:
	'''
	sample generator class
	'''
	def __init__(self,
				formula_file = './formulas.txt',
				sample_sizes = [(10,10),(50,50)],
				trace_lengths = [(6,6)],
				output_folder = 'experiment_results/generated_files/' + datetime.datetime.now().strftime('%Y-%m-%d_%H-%M-%S'),
				total_num = 1,
				gen_method = 'buchi_method'):


		self.formula_file = formula_file
		self.sample_sizes = sample_sizes
		self.trace_lengths = trace_lengths
		self.output_folder = output_folder
		self.total_num = total_num
		self.gen_method = gen_method
		
		if os.path.exists(self.output_folder):
			shutil.rmtree(self.output_folder)

		os.makedirs(output_folder)
		formula_file_name = self.formula_file.split('/')[-1]

		shutil.copyfile(self.formula_file, output_folder+'/'+formula_file_name)
		self.sample_sizes.sort()
		self.max_size = sample_sizes[-1]
		

	def generateFromLargeSample(self):
		
		generated_files = self.generate(gen_from_large_sample=True)
		#generating small benchmarks from large ones
		self.generateSmallBenchmarks(generated_files, self.sample_sizes[:-1])



	def generate(self, gen_from_large_sample=False):

		if gen_from_large_sample:
			sample_sizes = [self.max_size]
		else:	
			sample_sizes = self.sample_sizes

		traces_folder = self.output_folder+'/TracesFiles/' 
		os.makedirs(traces_folder)

		generated_files = []
		
		with open(self.formula_file, 'r') as file:
			formula_num=0
			for line in file:
				
				formula_text, alphabet = line.split(';')
				alphabet = alphabet.strip().split(',')
				
				#trace_lengths = lengths.split(',')
				#trace_lengths = [(int(i),int(i)) for i in trace_lengths]

				formula = Sketch.convertTextToSketch(formula_text)
		
				formula_num+=1
				print('---------------Generating Benchmarks for formula %s---------------'%formula.prettyPrint())
				
				for size in sample_sizes:
					for length_range in self.trace_lengths:
						for num in range(self.total_num):
							length_mean = (length_range[0]+length_range[1])//2
							sample=Sample(positive=[], negative=[])

							trace_file = traces_folder+'f:'+str(formula_num).zfill(2)+'-'+'nw:'+str((size[0]+size[1])//2).zfill(3)+'-'+'ml:'+str(length_mean).zfill(2)+'-'+str(num)+'.trace'
							generated_files.append(trace_file)

							if self.gen_method=='buchi_method':

								sample.generator_via_buchi(formula=formula,
											                  filename=trace_file,
											                  num_traces=size,
											                  length_traces=length_range,
											                  alphabet=alphabet,
											                  length_range=length_range,
											                  write=True)

							if not sample.isFormulaConsistent(formula):
								raise Exception("Formula %s is not consistent with sample"%formula.prettyPrint())


		return generated_files


	def generateSmallBenchmarks(self, generated_files, sizes):
		
		for filename in generated_files:
			
			s = Sample(positive=[],negative=[])
			s.readFromFile(filename)
			
			for (i,j) in sizes:
				
				new_filename = filename.replace("nw:"+str((self.max_size[0]+self.max_size[1])//2).zfill(3), "nw:"+str(i).zfill(3))
				new_positive = s.positive[:i]
				new_negative = s.negative[:j]
				new_s = Sample(positive=new_positive, \
								negative=new_negative, \
								original_formula=s.original_formula, \
								alphabet=s.alphabet)

				new_s.writeToFile(new_filename)



#Data type for parser
def tupleList(s):
	try:
		return tuple(map(int , s.split(',')))
	except:
		print("Wrong format; provide comma separated values")

def main():

	parser = argparse.ArgumentParser()
	parser.add_argument('--formula_file', dest='formula_file', default = 'experiment_results/formulas.txt')
	parser.add_argument('--size', dest='sample_sizes', default=[(10,10),(25,25),(50,50),(100,100),(200,200),(400,400)], nargs='+', type=tupleList)
	parser.add_argument('--lengths', dest='trace_lengths', default=[(4,8),(8,12),(12,16)], nargs='+', type=tupleList)
	parser.add_argument('--total_num', dest='total_num', default=1, type=int)
	parser.add_argument('--output_folder', dest='output_folder', default = 'experiment_results/generated_files/' + datetime.datetime.now().strftime('%Y-%m-%d_%H-%M-%S'))
	parser.add_argument('--generation_method', dest='gen_method', default='buchi_method')

	args,unknown = parser.parse_known_args()
	formula_file = args.formula_file
	sample_sizes = list(args.sample_sizes)
	trace_lengths = list(args.trace_lengths)
	output_folder = args.output_folder
	total_num = int(args.total_num)
	gen_method = args.gen_method

	generator = GenerateBatch(formula_file=formula_file,
				sample_sizes=sample_sizes,
				trace_lengths=trace_lengths,
				output_folder=output_folder,
				total_num=total_num,
				gen_method=gen_method)

	generator.generateFromLargeSample() 



#main()
def sample_stats(folder_name):

	all_files = glob.glob(folder_name+'/**/*.trace', recursive = True)
	
	info_dict = {'Name':'',\
					'Original Formula':'',\
					'Num positive':0,\
					'Num negative':0,\
					'Total size':0,\
					'Average trace len':0.0\
					}

	csv_file = open(folder_name+'sample_stats.csv', 'w')
	dict_writer = csv.DictWriter(csv_file, info_dict.keys())
	dict_writer.writeheader()
	

	for file in all_files:
		s = Sample(positive=[], negative=[], alphabet=[], original_formula=None)
		s.readFromFile(file)
		info_dict.update({'Name':file,\
					'Original Formula':s.original_formula,\
					'Num positive':len(s.positive),\
					'Num negative':len(s.negative),\
					'Total size':len(s),\
					'Average trace len':len(s)/(len(s.positive)+len(s.negative))\
					})
		dict_writer.writerow(info_dict)

	csv_file.close()

sample_stats('experiment_results/generated_files/')
