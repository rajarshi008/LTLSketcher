from sketch import Sketch
import random
import sys
#from ltl2aut import LTL2NFA
#from nfa import NFA
from graphviz import Source

def lineToTrace(line):
    
    lasso_start = None
    try:
        traceData, lasso_start = line.split('::')
    except:
        traceData = line

    trace_vector = [tuple([int(varValue) for varValue in varsInTimestep.split(',')]) for varsInTimestep in
                    traceData.split(';')]

    return (trace_vector, lasso_start)


def findRandLength(length_list, rand_length, length_range):

    all_possible_lengths = set(range(length_range[0]-rand_length,length_range[1]-rand_length))
    possible_lengths = all_possible_lengths.intersection(set(length_list))
    
    try:
        rand_length = random.choice(list(possible_lengths))
        return rand_length
    except:
        return None

class Trace:
    """
    defines a sequences of letters, which could be a subset of propositions
    """

    def __init__(self, vector, lasso_start=None):

        self.vector = vector
        self.length = len(vector)
        self.lasso_start = lasso_start
        if self.lasso_start == None:
            self.is_finite = True

        if lasso_start != None:
            
            self.is_finite = False
            self.lasso_start = int(lasso_start)
            if self.lasso_start >= self.length:
                raise Exception(
                    "lasso start = %s is greater than any value in trace (trace length = %s) -- must be smaller" % (
                        self.lasso_start, self.length))

            self.lasso_length = self.length - self.lasso_start
            self.prefix_length = self.length - self.lasso_length

            self.lasso = self.vector[self.lasso_start:self.length]
            self.prefix = self.vector[:self.lasso_start]

    def nextPos(self, currentPos):
        """
        returns the next position in the trace
        """
        if currentPos == self.length - 1:
            return self.lasso_start
        else:
            return currentPos + 1

    def auxiliaryPos(self, startPos, endPos):
        """
        returns the positions of the auxiliary function
        """
        if startPos < endPos:
            return [i for i in range(startPos, endPos)]
        elif startPos == endPos:
            return []
        else:
            return [i for i in range(self.prefix_length, endPos)] + [j for j in range(startPos, self.length)]

    def futurePos(self, currentPos):
        """
        returns all the relevant future positions
        """
        if currentPos < self.lasso_start:
            return range(currentPos, self.length)
        else:
            return range(self.lasso_start, self.length)

    def evaluateFormula(self, formula, letter2pos):
        """
        evalutates formula on trace
        """
        nodes = list(set(formula.getAllNodes()))
        self.truthAssignmentTable = {node: [None for _ in range(self.length)] for node in nodes}
        
        return self.truthValue(formula, 0, letter2pos)

    def truthValue(self, formula, timestep, letter2pos):
        """
        evaluates formula on trace starting from timestep
        """
        futureTracePositions = self.futurePos(timestep)
        tableValue = self.truthAssignmentTable[formula][timestep]
        if tableValue != None:
            return tableValue
        else:
            label = formula.label
            if label == 'true':
                val = True
            elif label == 'false':
                val = False
            elif label == '&':
                val = self.truthValue(formula.left, timestep, letter2pos) and self.truthValue(formula.right, timestep,
                                                                                              letter2pos)
            elif label == '|':
                val = self.truthValue(formula.left, timestep, letter2pos) or self.truthValue(formula.right, timestep,
                                                                                             letter2pos)
            elif label == '!':
                val = not self.truthValue(formula.left, timestep, letter2pos)
            elif label == '->':
                val = not self.truthValue(formula.left, timestep, letter2pos) or self.truthValue(formula.right,
                                                                                                 timestep, letter2pos)
            elif label == 'F':
                val = max([self.truthValue(formula.left, futureTimestep, letter2pos) for futureTimestep in
                           futureTracePositions])
            elif label == 'G':
                val = min([self.truthValue(formula.left, futureTimestep, letter2pos) for futureTimestep in
                           futureTracePositions])
            elif label == 'U':
                val = max(
                    [self.truthValue(formula.right, futureTimestep, letter2pos) for futureTimestep in
                     futureTracePositions]) == True \
                      and ( \
                                  self.truthValue(formula.right, timestep, letter2pos) \
                                  or \
                                  (self.truthValue(formula.left, timestep, letter2pos) and self.truthValue(formula,
                                                                                                           self.nextPos(
                                                                                                               timestep),
                                                                                                           letter2pos)) \
                          )
            elif label == 'X':
                    val = self.truthValue(formula.left, self.nextPos(timestep), letter2pos)
            else:
                val = bool(self.vector[timestep][letter2pos[label]])
            self.truthAssignmentTable[formula][timestep] = val
            return val

    def __str__(self):
        vector_str = [list(map(lambda x: str(int(x)), letter)) for letter in self.vector]
        if self.is_finite:
            return str(';'.join([','.join(letter) for letter in vector_str]))
        else:
            return str(';'.join([','.join(letter) for letter in vector_str])) + '::' + str(self.lasso_start)

    def __len__(self):
        return self.length


# noinspection PyDefaultArgument,PySimplifyBooleanCheck
class Sample:
    '''
	contains the sample of postive and negative examples
	'''

    def __init__(self, positive=[], negative=[], alphabet=[], original_formula=None):

        self.positive = positive
        self.negative = negative
        self.alphabet = alphabet
        self.num_positives = len(self.positive)
        self.num_negatives = len(self.negative)
        self.operators = ['G', 'F', '!', 'X', '&', '|', 'U', '->']
        self.original_formula = original_formula


    def __len__(self):

        return sum([len(trace) for trace in self.positive+self.negative])


    def readFromFile(self, filename):
        """
        reads .trace files to extract sample from it
        """
        with open(filename, 'r') as file:
            mode = 0
            count = 0
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
                    self.positive.append(trace)
                    self.num_positives += 1

                if mode == 1:
                    trace_vector, lasso_start = lineToTrace(line)
                    trace = Trace(vector=trace_vector, lasso_start=lasso_start)
                    self.negative.append(trace)
                    self.num_negatives += 1

                if mode == 2:
                    #self.operators = list(line.strip().split(','))
                    self.original_formula = str(line.strip())

                if mode == 3:
                    self.alphabet = list(line.split(','))

        if mode != 3:
            self.alphabet = [chr(ord('p') + i) for i in range(len(self.positive[0].vector[0]))]

        self.letter2pos = {self.alphabet[i]: i for i in range(len(self.alphabet))}

    def isFormulaConsistent(self, formula):
        """
		checks if the sample is consistent with given formula
		"""
        if formula == None:
            return True
        for trace in self.positive:
            if trace.evaluateFormula(formula, self.letter2pos) == False:
                #print('positive-example',trace)
                return False

        for trace in self.negative:
            if trace.evaluateFormula(formula, self.letter2pos) == True:
                #print('negative-example',trace)
                return False
        return True

    def random_trace(self,
                     alphabet=['p', 'q', 'r'],
                     length=5):
        """
		generates random traces from a given formula
		"""
        trace_vector = [[random.randint(0, 1) for _ in range(len(alphabet))] for _ in range(length)]
        return Trace(trace_vector)

    def random_trace_up(self,
                         alphabet=['p', 'q', 'r'],
                         length=5):
        """
    	generates random traces from a given formula
    	"""
        trace_vector = [[random.randint(0, 1) for _ in range(len(alphabet))] for _ in range(length)]
        return Trace(trace_vector, random.randint(0, length-1))

    def generator_random(self,
                  formula=None,
                  filename='generated.words',
                  num_traces=(5, 5),
                  length_traces=None,
                  alphabet=['p', 'q', 'r'],
                  length_range=(5, 15)):
        '''
		generates a random sample consistent with a given LTL formula
		'''
        num_positives = 0
        num_positives = num_traces[0]
        num_negatives = 0
        num_negatives = num_traces[1]
        ver = True
        letter2pos = {alphabet[i]: i for i in range(len(alphabet))}
        self.original_formula = str(formula)
        

        while num_positives < total_num_positives or num_negatives < total_num_negatives:
            if length_traces is None:
                length = random.randint(length_range[0], length_range[1])
            else:
                length = length_traces

            final_trace = self.random_trace_up(alphabet, length)

            # check
            if formula != None:
                ver = final_trace.evaluateFormula(formula, letter2pos)

            if num_positives < total_num_positives:
                if ver == True or formula == None:
                    self.positive.append(final_trace)
                    num_positives += 1
                    continue

            if num_negatives < total_num_negatives:
                if ver == False or formula == None:
                    self.negative.append(final_trace)
                    num_negatives += 1

        self.operators = operators
        self.writeToFile(filename)

    def generator_via_buchi(self,
                  formula=None,
                  filename='generated.trace',
                  num_traces=(5, 5),
                  length_traces=None,
                  alphabet=['p', 'q', 'r'],
                  length_range=(4, 16),
                  write=True):
        
        '''
        generates a sample consistent with a given LTL formula by intermediate conversion to Buchi automata
        '''

        #print('To generate %d positive and %d negative'%(num_traces[0], num_traces[1]))
        num_positives = num_traces[0]
        num_negatives = num_traces[1]
        
        ver = True
        self.alphabet = alphabet
        letter2pos = {self.alphabet[i]: i for i in range(len(alphabet))}
        self.letter2pos = letter2pos
        self.original_formula = str(formula)
        
        #For positive examples
        #print('---------Generating positive examples------------')
        


        ltl2nfa = LTL2NFA(formula, letter2pos)
        nfa = ltl2nfa.generateAutomata()

        #nfa.show()

        nfa_pairs = [] #for generating up words

        #now only considering paths from 1 intial states, plan to add more in future
        for i in range(len(nfa.final_states)):

            #can add checks to ensure that there is atleast one path from inital to final state
            nfa_prefix = NFA([nfa.init_states[0]], [nfa.final_states[i]], nfa.transitions, nfa.alphabet)
            nfa_lasso = NFA([nfa.final_states[i]], [nfa.final_states[i]], nfa.transitions, nfa.alphabet)
            nfa_pairs.append((nfa_prefix,nfa_lasso))



        #Perform an n way split
        num_pairs = len(nfa_pairs)
        num_splits = [int(num_positives/num_pairs)]*num_pairs
        #Making sure the split add up to the num of positives
        while sum(num_splits) < num_positives:

            i = random.randint(0,num_pairs-1)
            num_splits[i]+=1

        #print(num_splits)
        #Generating examples from each nfa pair
        
        if length_range[1] != -1:
            prefix_length_range = (int(length_range[0]/2), int(length_range[1]/2))
            lasso_length_range = (int(length_range[0]/2), int(length_range[1]/2))
        else:
            prefix_length_range = (1,len(nfa))
            lasso_length_range = (1,len(nfa))

        #print(prefix_length_range, lasso_length_range)

        #print('Positive splits', num_splits)
        #print(num_splits)

        for i in range(num_pairs):

            #Generating prefixes
            prefix_list =  nfa_pairs[i][0].generate_random_words_in_batch(prefix_length_range, num_splits[i])
            prefix_dict = {}
            for prefix in prefix_list:
                try:
                    prefix_dict[len(prefix)].append(prefix)
                except:
                    prefix_dict[len(prefix)] = [prefix]
            prefix_lengths = list(prefix_dict.keys())

            #Generating lassos
            lasso_list =  nfa_pairs[i][1].generate_random_words_in_batch(lasso_length_range,num_splits[i])
            lasso_dict = {}
            for lasso in lasso_list:
                try:
                    lasso_dict[len(lasso)].append(lasso)
                except:
                    lasso_dict[len(lasso)] = [lasso]
            lasso_lengths = list(lasso_dict.keys())
            
            #Combining prefix and lassos
            combined_set = set()
            attempt = 0
            while len(combined_set) < num_splits[i] and attempt < 1000: 
                attempt+=1
                rand_prefix = random.choice(prefix_list)
                rand_prefix_length = len(rand_prefix)
                #print(rand_prefix)
                #if strict_len:
                    #if there is strict requirement on the lasso lengths
                #    rand_lasso_length = findRandLength(lasso_lengths, rand_prefix_length, length_range)
                #    if rand_lasso_length == None:
                #        continue
                #    else:
                #        rand_lasso = random.choice(lasso_dict[rand_lasso_length])
                #else:
                    #if there is no strict requirement on the lasso lengths
                rand_lasso_length = random.choice(lasso_lengths)
                rand_lasso = random.choice(lasso_dict[rand_lasso_length])

                assert(rand_lasso_length>0 and rand_prefix_length>0)

                rand_trace = Trace(vector=[[int(digit) for digit in letter] for letter in rand_prefix + rand_lasso]\
                                                            ,lasso_start=rand_prefix_length)
                
                #assert(rand_trace.evaluateFormula(formula, letter2pos))
                combined_set.add(rand_trace)



            self.positive += list(combined_set)

        #For negative examples
        #print('---------Generating negative examples------------')
        neg_formula = Sketch(['!', formula])
        ltl2nfa = LTL2NFA(neg_formula, letter2pos)
        nfa = ltl2nfa.generateAutomata()

        nfa_pairs = [] #for generating up words
        for i in range(len(nfa.final_states)):

            #can add checks to ensure that there is atleast one path from inital to final state
            nfa_prefix = NFA([nfa.init_states[0]], [nfa.final_states[i]], nfa.transitions, nfa.alphabet)
            nfa_lasso = NFA([nfa.final_states[i]], [nfa.final_states[i]], nfa.transitions, nfa.alphabet)
            nfa_pairs.append((nfa_prefix,nfa_lasso))

        
        #Perform an n way split
        num_pairs = len(nfa_pairs)
        num_splits = [int(num_negatives/num_pairs)]*num_pairs
        #Making sure the split add up to the num of negatives
        while sum(num_splits) < num_negatives:

            i = random.randint(0,num_pairs-1)
            num_splits[i]+=1

        #print('Negative splits', num_splits)
        #Generating examples from each nfa pair
        for i in range(num_pairs):

            #Generating prefixes
            prefix_list =  nfa_pairs[i][0].generate_random_words_in_batch(prefix_length_range,num_splits[i])
            prefix_dict = {}
            for prefix in prefix_list:
                try:
                    prefix_dict[len(prefix)].append(prefix)
                except:
                    prefix_dict[len(prefix)] = [prefix]
            prefix_lengths = list(prefix_dict.keys())

            #Generating lassos
            lasso_list =  nfa_pairs[i][1].generate_random_words_in_batch(lasso_length_range,num_splits[i])
            lasso_dict = {}
            for lasso in lasso_list:
                try:
                    lasso_dict[len(lasso)].append(lasso)
                except:
                    lasso_dict[len(lasso)] = [lasso]
            lasso_lengths = list(lasso_dict.keys())
            
            #Combining prefix and lassos
            combined_set = set()
            attempt = 0
            while len(combined_set) < num_splits[i] and attempt < 1000: 
                attempt+=1
                rand_prefix = random.choice(prefix_list)
                rand_prefix_length = len(rand_prefix)
                
                # if strict_len:
                #     #if there is strict requirement on the lasso lengths
                #     rand_lasso_length = findRandLength(lasso_lengths, rand_prefix_length, length_range)
                #     if rand_lasso_length == None:
                #         continue
                #     else:
                #         rand_lasso = random.choice(lasso_dict[rand_lasso_length])
                # else:
                    #if there is no strict requirement on the lasso lengths
                rand_lasso_length = random.choice(lasso_lengths)
                rand_lasso = random.choice(lasso_dict[rand_lasso_length])


                rand_trace = Trace(vector=[[int(digit) for digit in letter] for letter in rand_prefix + rand_lasso]\
                                                            ,lasso_start=rand_prefix_length)
                

                assert(not rand_trace.evaluateFormula(formula, letter2pos))
                combined_set.add(rand_trace)


            #print('Len of combined set', len(combined_set), 'and number of attempts', attempt)

            self.negative += list(combined_set)

        #print('Generated %d positive and %d negative'%(len(self.positive), len(self.negative)))
        if write:
            self.writeToFile(filename)
        else:
            return (self.positive, self.negative)
    

    def writeToFile(self, filename):
        """
        writes a sample to the given file
        """
       # print(self.original_formula)
        with open(filename, 'w') as file:
            for trace in self.positive:
                file.write(str(trace) + '\n')
            file.write('---\n')

            for trace in self.negative:
                file.write(str(trace) + '\n')

            if self.original_formula != None:
                file.write('---\n')
                file.write(self.original_formula+'\n')

            if self.alphabet != []:
                file.write('---\n')
                file.write(','.join(self.alphabet))


'''
s = Sample(positive=[], negative=[])
f = Sketch.convertTextToSketch('G(->(q, G(!(p))))')
s.generator_via_buchi(formula=f, alphabet=['p','q'], num_traces=(20,20), filename='first-example.trace')
print(s.isFormulaConsistent(f))
'''