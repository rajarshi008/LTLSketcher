from sketch import Sketch
from nfa import NFA
import spot
from graphviz import Source


unary_operators = ['G', 'F', '!', 'X']
binary_operators = ['&', '|', 'U', '->']


class LTL2NFA:

	def __init__(self, formula, letter2pos):

		self.formula = formula
		self.spot_formula = self.formula.prettyPrint()
		self.letter2pos = letter2pos
		self.propositions = list(self.letter2pos.keys())
		self.letter_list = [(0,),(1,)]
		for i in range(len(self.propositions)-1):
			self.letter_list = [l+(0,) for l in self.letter_list] + [l+(1,) for l in self.letter_list]


	def generateAutomata(self):
		'''
		Generates the automaton equivalent of the formulas
		'''
		self.equiv_buchi = spot.translate(self.spot_formula, 'Buchi', 'state-based', 'complete')
		self.buchi_dot_string = self.equiv_buchi.to_str('dot')
		#print(dot_string)
		#s = Source(self.buchi_dot_string, format="png")
		#s.view()

		#print(self.buchi_dot_string)
		self.equiv_nfa = self.buchiDot2NFA(self.buchi_dot_string)
		#self.equiv_nfa.show()
		#print('Is the NFA total', self.equiv_nfa.is_total())
		#self.equiv_nfa.show()
		#self.equiv_nfa.show()

		return self.equiv_nfa
		

	def buchiDot2NFA(self, dot_string):
		'''
		Generates NFA with same structure as Buchi
		'''
		automaton_info = dot_string.split('\n')
		final_states = []
		transitions = {}

		for line in automaton_info:
			
			if line == '}':
				break

			#finding intial state
			if 'I' in line:
				if '->' not in line:
					continue
				else:
					init_state = line.split('->')[1].strip()
					continue
		
			#for final state
			if line[2].isnumeric():
				if 'peripheries' in line:
					final_states.append(line[2])
					continue

			#for transitions
			if '->' in line:
				#line = line.replace(' ', '')
				edge, label_info = line.split('[')
				
				edge = edge.replace(' ', '')
				first_state, second_state = edge.split('->')
				#print(first_state, second_state)

				label = label_info.split('\"')[1]
				#print(label)
				atom = self.SpotFormula2Formula(label)
				letters = self.atom2letters(atom)

			

				for letter in letters:
					try:
						transitions[first_state][letter].append(second_state)
					except:
						try:
							transitions[first_state][letter] = [second_state]
						except:
							transitions[first_state] = {letter:[second_state]}


				#print(first_state, second_state, letters)	

		alphabet = list(map(lambda x: ''.join([str(i) for i in x]), self.letter_list))
		nfa = NFA(init_state, final_states, transitions, alphabet)
		
		return nfa


	def SpotFormula2Formula(self, spot_formula):
		'''
		converts spot formula to Formula class
		'''
		infix_formula = spot.formula(spot_formula).to_str('lbt')
		#print('Before edit', infix_formula)
		infix_formula = infix_formula.replace('\"','').replace(' ','')
		#print(spot_formula, infix_formula)
		stack = []
		
		for i in range(len(infix_formula)-1,-1,-1):
			op = infix_formula[i]
			f = Sketch()
			f.label = op
			if op in unary_operators:

				f.left = stack.pop() 
				f.right = None
				stack.append(f)

			elif op in binary_operators:

				p = stack.pop()
				f.left = p
				f.right = stack.pop()
				stack.append(f)

			else:

				f.left = None
				f.right = None
				stack.append(f)

		return stack[0]

	#quite non-optimized but works! :D
	def atom2letters(self, atom):

		sat_letters = []
		#print('ina2l', atom)
		for letter in self.letter_list:
			
			if self.checkSat(letter, atom):
				sat_letters.append(''.join([str(i) for i in letter]))

		return sat_letters


	def checkSat(self, letter, atom):

		op = atom.label
		#print('this is the op', op)
		if op == '&':
			return self.checkSat(letter, atom.left) and self.checkSat(letter, atom.right)
		elif op == '|':
			return self.checkSat(letter, atom.left) or self.checkSat(letter, atom.right)
		elif op == '!':
			return not self.checkSat(letter, atom.left)
		elif op == 't':
			return True
		elif op in self.propositions:
			return letter[self.letter2pos[op]] == 1
		else:
			print('Atom cannot be parsed properly')
			return



	
#f = LTL2NFA('&(F(p),G(q))', {'p':0, 'q':1})
#f.generateAutomata()
