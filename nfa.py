from IPython.display import display
import spot
from spot.jupyter import display_inline
from graphviz import Source
import random
#from ltlf2dfa.parser.ltlf import LTLfParser
from sketch import Sketch

class NFA:

	def __init__(self, init_states, final_states, transitions, alphabet):
		self.final_states = final_states
		self.init_states = init_states
		self.transitions = transitions
		self.states = transitions.keys()
		self.alphabet = alphabet
		#self.current_state = self.init_state

		# Calculating number of words of length 0 accepted of length 0 from a state
		self.number_of_words = {(state, 0):int(state in self.final_states) for state in self.states}
		self.calculated_till = 0

	def __len__(self):
		return len(self.states)

	def __str__(self):
		'''
		prints the dfas in a readable format
		'''
		output_str = ''
		output_str += 'Init: '+','.join(list(map(str,self.init_states))) + '\n'
		output_str += 'States: '+','.join(list(map(str, self.states))) + '\n'
		output_str += 'Transitions:\n'
		for state in self.transitions:
			for letter in self.alphabet:
				for next_state in self.transitions[state][letter]:
					output_str += str(state)+ '-'+str(letter)+'->'+str(next_state)+','
					output_str += '\n'
		output_str += 'Final states: '+','.join(list(map(str,self.final_states)))
		return output_str

	def reachable_states(self, word):

		reachable_state = self.init_states
		
		for letter in word:
			
			new_reachable_state = []
			for state in reachable_state:
				for next_state in self.transitions[state][letter]:
					new_reachable_state.append(next_state)

			reachable_state = new_reachable_state

		return reachable_state

	def is_word_in(self, word):
		'''
		checks if a word belongs to the language of the DFA
		'''
		reachable_states = self.reachable_states(word)
		
		for state in reachable_states:
			if state in self.final_states:
				return True

		return False

	
	def generate_dot_str(self):

		dot_str =  "digraph g {\n"
		dot_str += 'label="[NFA]"\n' 
		dot_str += ('__start0 [label="start" shape="none"]\n')

		for state in self.states:
			if state in self.final_states:
				shape = "doublecircle"
			else:
				shape = "circle"
			dot_str += ('{} [shape="{}" label="{}"]\n'.format(state, shape, state))

		for init_state in self.init_states:	
			dot_str += ('__start0 -> {}\n'.format(init_state))


		for state in self.transitions.keys():
			tran = self.transitions[state]
			for letter in tran.keys():
				for next_state in self.transitions[state][letter]:
					dot_str += ('{} -> {}[label="{}"]\n'.format(state, next_state, letter))
		dot_str += ("}\n")

		return dot_str

	
	def show(self, filename="test.gv"):
		'''
		Produces an image of the DFA
		'''	
		dot_str = self.generate_dot_str()
		s = Source(dot_str, filename=filename, format="png")
		s.view()
		

	def save(self, filename):
		
		dot_str = self.generate_dot_str()
		with open(filename + ".dot", "w") as file:
			file.write(dot_str)


	def is_total(self):

		for state in self.states:
			if len(list(self.transitions[state].keys())) != len(self.alphabet):
				return False
		return True
	
	def is_det(self):

		for state in self.states:
			for letter in self.alphabet:
				if len(self.transitions[state][letter])>1:
					return False

		return True


	def generate_all_accepting_words(self):
		'''
		returns all words that are accepted by NFA
		'''
		return self.generate_accepting_words(self.init_states)


	def generate_accepting_words(self, state):
		'''
		returns all words that are accepted by a DFA from a given state 
		'''		
		all_words = []
		if state in self.final_states:
			all_words += ['']

		for letter in self.alphabet:
			successor_states = self.transitions[state][letter]

			for next_state in successor_states:
				all_words += [letter+word for word in self.generate_accepting_words(next_state)]

		return all_words

	def generate_num_accepting_words(self, length):
		'''
		returns the number of words that are accepted of a particular length
		'''
		if self.calculated_till > length:
			return
		else:
			for i in range(self.calculated_till+1,length+1):
				self.number_of_words.update({(state, i):0 for state in self.states})
				for state in self.states:
					for letter in self.alphabet:
						successor_states = self.transitions[state][letter]
						for next_state in successor_states:
							self.number_of_words[(state, i)] += self.number_of_words[(next_state, i-1)]



	def generate_random_word(self):
		'''
		returns any random word that is accepted
		'''
		random_length = random.randint(0,100)
		return self.generate_random_word_length(random_length)


	def generate_smallest_word(self):
		'''
		returns a random word of the smallest length (greater than zero)
		'''
		nfa_size = len(self)
		if self.calculated_till < nfa_size:
			self.generate_num_accepting_words(nfa_size)


		smallest_length = None
		for l in range(1,nfa_size+1):
			for init_state in self.init_states:
				#print(init_state)
				#print(self.number_of_words)

				if self.number_of_words[(init_state,l)] != 0:
					smallest_length = l
					break
			else:
				continue
			break

		if smallest_length == None:
			return None
		else:
			return self.generate_random_word_length(smallest_length)


	# Algorithm taken from https://link.springer.com/article/10.1007/s00453-010-9446-5
	def generate_random_word_length(self, length):
		'''
		returns a random word of a particular length that is accepted
		'''
		if self.calculated_till < length:
			self.generate_num_accepting_words(length)

		rand_word = tuple()
		state = random.choice(self.init_states)

		for i in range(1,length+1):
			
			transition_list = []
			prob_list = []
			
			for letter in self.alphabet:
				for next_state in self.transitions[state][letter]:
					transition_list.append((letter, next_state))
					prob_list.append(self.number_of_words[(next_state, length-i)]/self.number_of_words[(state, length-i+1)])

			next_transition = random.choices(transition_list, weights=prob_list)[0]
			state = next_transition[1]
			
			rand_word+=(next_transition[0],)	
		
		return rand_word


	def generate_random_words_in_batch(self, length_range, batch_size):
		'''
		Generates random words in a batch with a factor of variation
		'''
		epsilon = 0.01
		
		if self.calculated_till < length_range[1]:
			self.generate_num_accepting_words(length_range[1])

		word_list = []
		last_path = []
		prob_dict = {}
		length_list = list(range(length_range[0], length_range[1]+1))
		valid_length = {}
		
		for l in length_list:
			for init_state in self.init_states:
				if self.number_of_words[(init_state,l)] != 0:
					try:
						valid_length[init_state].append(l)
					except:
						valid_length[init_state] = [l]


		if valid_length == {}:

			self.show()
			if self.size() < length_range[1]:
				raise Exception('Max Length of trace %d is smaller that DFA size %d'%(length_range[1], self.size()))
			else:	
				raise Exception('No accepting traces for this DFA') 

		transition_count = {}

		num=0
		for num in range(batch_size):
			
			rand_word = tuple()
			state = random.choice(list(valid_length.keys()))
			length = random.choice(valid_length[state])
			
			for i in range(1,length+1):
				non_sink_transitions = [] #letters which lead to some accepting states
				prob_list = []
				count_list = []

				for letter in self.alphabet:
					for next_state in self.transitions[state][letter]:
					
						if (state, letter, next_state) not in transition_count:
							transition_count[(state, letter, next_state)] = 0
						
						#print(next_state, self.number_of_words[(next_state, length-i)], length-i)
						if self.number_of_words[(next_state, length-i)] != 0:
							non_sink_transitions.append((state, letter, next_state))
							

						count_list.append(transition_count[(state, letter, next_state)])


				num_accepted_trans = len(non_sink_transitions)
				total_count = sum(count_list)
				
				for j in range(len(self.alphabet)):
					
					for next_state in self.transitions[state][self.alphabet[j]]:
						if self.number_of_words[(next_state, length-i)] != 0:
							if num_accepted_trans == 1:
								transition_prob = 1
							elif total_count == 0:
								transition_prob = (1/num_accepted_trans)
							else:
								transition_prob = (1/num_accepted_trans)*(1-(count_list[j]/total_count))
						
							prob_list.append(transition_prob)
					
				
				
				prob_list = [(i/sum(prob_list)) for i in prob_list]
	
				next_transition = random.choices(non_sink_transitions, weights=prob_list)[0]
				transition_count[next_transition] += 1
				#print("Count", transition_count)
				state = next_transition[2]
				rand_word+=(next_transition[1],)
			
			word_list.append(rand_word)	

		return word_list


	'''
	def complement(self):
		
		#returns a complement of the self object
		
		comp_final_states = [state for state in self.states if state not in self.final_states]
		d = DFA(self.init_state, comp_final_states, dict(self.transitions))
		return d
	
	'''