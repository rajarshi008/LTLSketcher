import spot
import logging, time, json, os, random
from sample import Sample, Trace
from algorithm_tree_bmc_new import check_existence_tree_bmc
from main import run_solver, main
from sketch import Sketch
from ltl2aut import LTL2NFA
from nfa import NFA
from graphviz import Source


logging.basicConfig(format='%(levelname)s:%(message)s', level=logging.INFO)


class CEGSampleGenerator:
	'''
	class for counterexample guided sample generation
	'''
	def __init__(self, original_formula, sketch_str, sample_name, alphabet):

		self.original_formula = original_formula
		self.current_formula = Sketch.convertTextToSketch('true')
		self.sketch_str = sketch_str
		self.lcc = spot.language_containment_checker()
		self.alphabet = alphabet

		self.spot_original_formula = spot.formula(self.original_formula.prettyPrint()) 
		self.spot_current_formula = spot.formula(self.current_formula.prettyPrint())
		self.lcc = spot.language_containment_checker()
		
		#for a fresh sample
		if os.path.isfile(sample_name):
			os.remove(sample_name)

		self.sample = Sample(positive=[], negative=[])
		self.sample.alphabet = alphabet
		self.sample.letter2pos = {self.alphabet[i]:i for i in range(len(self.alphabet))}
		self.sample_name = sample_name
		
		#initiating sample
		self.sample.positive = self.generateSmallCounterexample(self.original_formula)
		self.sample.negative = self.generateSmallCounterexample(Sketch(['!', self.original_formula]))
 
		self.sample.writeToFile(self.sample_name)
		
		self.run_info = {'Original Formula': original_formula.prettyPrint(),\
						'Sketch': sketch_str,\
						'Final Formula': '',\
						'Sample name': self.sample_name,\
						'Num positives negatives': (1,1),\
						'CEG loops': 0,\
						'Total time': 0.00,\
						'Learning time': 0.00,\
						'CE Gen time': 0.00,\
						'Sample size': 0,\
						}
		print('Intial sample size:',len(self.sample))
	
	def generateSmallCounterexample(self, formula):

		letter2pos = {self.alphabet[i]:i for i in range(len(self.alphabet))}
		ltl2nfa = LTL2NFA(formula, letter2pos)
		
		prefix_nfa = ltl2nfa.generateAutomata()

		prefix = prefix_nfa.generate_smallest_word()
		
		end_state = random.choice([state for state in prefix_nfa.reachable_states(prefix)\
								 if state in prefix_nfa.final_states])

		lasso_nfa = NFA([end_state],[end_state],prefix_nfa.transitions,prefix_nfa.alphabet)
		lasso = lasso_nfa.generate_smallest_word()

		trace = Trace(vector=[[int(digit) for digit in letter] for letter in prefix + lasso]\
														   ,lasso_start=len(prefix))

		return [trace]
		
	def genPositiveWords(self, number):

		if self.lcc.contains(self.spot_current_formula, self.spot_original_formula):
			return None
		else:
			#generation of positive words using buchi automaton
			conj_formula = Sketch(['&', self.original_formula, Sketch(['!', self.current_formula])])
			new_positives = self.generateSmallCounterexample(conj_formula)
			'''
			#aux_sample = Sample(positive=[],negative=[])
			#to compute the length range use the size of the nfa and set an upperbound of -1
			print('Generating examples for %s'%conj_formula)
			new_positives, _ = aux_sample.generator_via_buchi(formula=conj_formula,\
															num_traces=(number,0),\
															length_range=(0,-1),\
															alphabet=self.alphabet,\
															write=False)
			
			'''
			return new_positives
			

	def genNegativeWords(self, number):

		#print('Checking for negative counterexamples')
		
		if self.lcc.contains(self.spot_original_formula, self.spot_current_formula):
			return None
		else:
			conj_formula = Sketch(['&', self.current_formula, Sketch(['!', self.original_formula])])
			new_positives = self.generateSmallCounterexample(conj_formula)
			'''
			aux_sample = Sample(positive=[],negative=[])
			print('Generating examples for %s'%conj_formula)
			new_positives, _ = aux_sample.generator_via_buchi(formula=conj_formula,\
															num_traces=(number,0),\
															length_range=(0,-1),\
															alphabet=self.alphabet,\
															write=False)
			'''
			return new_positives

	def cegis_loop(self, additions=1):
		#main loop
		iteration = 0

		logging.info('Original Formula: %s'%self.original_formula.prettyPrint())
		
		start_time = time.time()
		learning_time = 0
		ce_gen_time = 0
		while True:

			iteration += 1
			logging.info('****** Iteration number %d ******'%iteration)
			logging.info('Current Formula: %s'%self.current_formula.prettyPrint())
			logging.info('Sample Size: (%d,%d)'%(len(self.sample.positive), len(self.sample.negative)))

			######## Learning Algorithm ########
			
			aux_sample = Sample(positive=[], negative=[], original_formula=None, alphabet=[])
			aux_sample.readFromFile(self.sample_name)
			print('Auxiliary sample size', len(aux_sample))

			sketch = Sketch.convertTextToSketch(self.sketch_str)
			
			start_learn = time.time()
			starting_id=0	
			sketch.assign_identifiers(starting_id)
			sketch.reduce()
			run_solver(aux_sample, sketch, 'tree', False, True)#supposedly the best learning algorithm
			end_learn = time.time()

			self.current_formula = sketch
			self.spot_current_formula = spot.formula(self.current_formula.prettyPrint())
			####################################
			learning_time += end_learn - start_learn

			if self.lcc.are_equivalent(self.spot_original_formula, self.spot_current_formula):
				logging.info('!!!Learned the same formula!!!')
				break
			
			########## CE generation ############
			start_gen = time.time()
			positive_words = self.genPositiveWords(number=additions)
			if positive_words != None:
				self.sample.positive+=positive_words
				self.sample.num_positives += len(positive_words)

			negative_words = self.genNegativeWords(number=additions)
			if negative_words != None:
				self.sample.negative+=negative_words
				self.sample.num_negatives+= len(negative_words)

			if positive_words == None and negative_words == None:
				break
			end_gen = time.time()

			self.sample.writeToFile(self.sample_name)
			####################################
			ce_gen_time += end_gen - start_gen

		end_time = time.time()
		logging.info('---Final Formula %s'%(self.current_formula.prettyPrint()))
		logging.info('---Final Sample Size %d (%d postives, %d negatives)'%(len(self.sample), len(self.sample.positive), len(self.sample.negative)))
		logging.info('---Time taken %.2f'%(end_time-start_time))

		print('CE gen time', ce_gen_time)
		self.run_info.update({'Final Formula': self.current_formula.prettyPrint(),\
						'CEG loops': iteration,\
						'Total time': round(end_time-start_time,10),\
						'Learning time': round(learning_time,10),\
						'CE Gen time': round(ce_gen_time,10),\
						'Num positives negatives': (len(self.sample.positive), len(self.sample.negative)),\
						'Sample size': len(self.sample)\
						})


def ce_sample_gen(original_formula_str, sketch_str, alphabet, reps, sample_name='test.trace', output_file=None):
	

	for i in range(reps):

		original_formula = Sketch.convertTextToSketch(original_formula_str)
		gen = CEGSampleGenerator(original_formula, sketch_str, sample_name, alphabet)
		
		#preprinting 
		if output_file != None:
			if not os.path.isfile(output_file):
				curr_info = gen.run_info
				curr_info.update({'Repetitions': 0})
				with open(output_file, 'w') as file:
					json.dump(curr_info, file)


		gen.cegis_loop()
		
		#postprinting
		if output_file != None:
			with open(output_file, 'r') as file:
				curr_info = json.load(file)
			
			curr_info['CEG loops'] = (i*curr_info['CEG loops'] + gen.run_info['CEG loops'])/(i+1)
			
			curr_info['Total time'] = (i*curr_info['Total time'] + gen.run_info['Total time'])/(i+1)
			curr_info['Learning time'] = (i*curr_info['Learning time'] + gen.run_info['Learning time'])/(i+1)
			curr_info['CE Gen time'] = (i*curr_info['CE Gen time'] + gen.run_info['CE Gen time'])/(i+1)

			curr_info['Num positives negatives'] = ((i*curr_info['Num positives negatives'][0] \
										+ gen.run_info['Num positives negatives'][0])/(i+1),\
										(i*curr_info['Num positives negatives'][1] \
										+ gen.run_info['Num positives negatives'][1])/(i+1))
			curr_info['Sample size'] = (i*curr_info['Sample size'] + gen.run_info['Sample size'])/(i+1)
			curr_info['Repetitions'] += 1
		
			with open(output_file, 'w') as file:
				json.dump(curr_info, file)



ce_sample_gen('->(F(q),U(!(p),q))','?1',['p','q'], 2,'test.trace','test.json')
	
