from lark import Lark, Transformer
from graphviz import Source

unary_operators = ['G', 'F', '!', 'X'] + ['?u' + str(i) for i in range(0, 100, 1)]
binary_operators = ['&', '|', 'U', '->'] + ['?b' + str(i) for i in range(0, 100, 1)]


class SimpleTree:
    def __init__(self, label="dummy"):
        self.left = None
        self.right = None
        self.label = label

    def __hash__(self):
        # return hash((self.label, self.left, self.right))
        return hash(self.label) + id(self.left) + id(self.right)

    def __eq__(self, other):
        if other == None:
            return False
        else:
            return self.label == other.label and self.left == other.left and self.right == other.right

    def __ne__(self, other):
        return not self == other

    def _isLeaf(self):
        return self.right == None and self.left == None

    def _isUnary(self):
        return self.left != None and self.right == None

    def _isBinary(self):
        return self.left != None and self.right != None

    def _isPlaceholder(self):
        return '?' in self.label

    def _addLeftChild(self, child):
        if child == None:
            return
        if type(child) is str:
            child = SimpleTree(child)
        self.left = child

    def _addRightChild(self, child):
        if type(child) is str:
            child = SimpleTree(child)
        self.right = child

    def addChildren(self, leftChild=None, rightChild=None):
        self._addLeftChild(leftChild)
        self._addRightChild(rightChild)

    def addChild(self, child):
        self._addLeftChild(child)

    def getAllNodes(self):
        leftNodes = []
        rightNodes = []

        if self.left != None:
            leftNodes = self.left.getAllNodes()
        if self.right != None:
            rightNodes = self.right.getAllNodes()
        return [self] + leftNodes + rightNodes

    def getAllLabels(self):
        if self.left != None:
            leftLabels = self.left.getAllLabels()
        else:
            leftLabels = []

        if self.right != None:
            rightLabels = self.right.getAllLabels()
        else:
            rightLabels = []
        return [self.label] + leftLabels + rightLabels


    def getLabel(self):
        return self.label

    def replace(self,  replacement):
        self.label = replacement.label
        self.left = replacement.left
        self.right = replacement.right

    def __repr__(self):
        if self.left == None and self.right == None:
            return self.label

        # the (not enforced assumption) is that if a node has only one child, that is the left one
        elif self.left != None and self.right == None:
            return self.label + '(' + self.left.__repr__() + ')'

        elif self.left != None and self.right != None:
            return self.label + '(' + self.left.__repr__() + ',' + self.right.__repr__() + ')'


'''
A class for encoding syntax Trees and syntax DAGs of LTL formulas
'''


class Sketch(SimpleTree):

    def __init__(self, formulaArg="dummyF"):
        self.size = None
        if not isinstance(formulaArg, str):
            self.label = formulaArg[0]
            self.left = formulaArg[1]
            try:
                self.right = formulaArg[2]
            except:
                self.right = None
            self.identifier = None
        else:
            super().__init__(formulaArg)

    def prettyPrint(self, top=False):
        '''
		prints sketch in infix notation
		'''
        if top is True:
            lb = ""
            rb = ""
        else:
            lb = "("
            rb = ")"
        if self._isLeaf():
            return self.label
        if self.label in unary_operators:
            return lb + self.label + " " + self.left.prettyPrint() + rb
        if self.label in binary_operators:
            return lb + self.left.prettyPrint() + " " + self.label + " " + self.right.prettyPrint() + rb

    def getUniqueNodes(self):
        nodes = self.getAllNodes()
        identifiers = [node.identifier for node in nodes]
        return [node for i, node in enumerate(nodes) if node.identifier not in identifiers[i+1:]]

    def reduce(self):
        repeat = False
        subformulas = [(repr(node), node) for node in self.getUniqueNodes()]
        subformulas = sorted(subformulas,key = lambda i: len(i[0]),reverse=True)
        for pos,formula in enumerate(subformulas):
            subformula = formula[0]
            node = formula[1]

            occurances = [tuple for tuple in subformulas[pos:] if tuple[0] == subformula]
            if len(occurances) > 1:
                for n in self.getUniqueNodes():
                    if repr(n.left) == subformula:
                        n.left = node
                    if repr(n.right) == subformula:
                        n.right = node
                repeat = True
                break
        if repeat:
            self.reduce()

    def get_placeholders(self):
        '''
		returns the set of placeholders from the functions
		'''
        leftTree = []
        rightTree = []

        if self.left != None:
            leftTree = self.left.get_placeholders()

        if self.right != None:
            rightTree = self.right.get_placeholders()

        if '?' in self.label:
            return [self.label] + leftTree + rightTree
        else:
            return leftTree + rightTree

    def get_type0Positions(self):
        """
		returns list of identifier of all type 0 placeholders
		"""
        leftTree = []
        rightTree = []

        if self.left != None:
            leftTree = self.left.get_type0Positions()

        if self.right != None:
            rightTree = self.right.get_type0Positions()

        if '?' in self.label and '?u' not in self.label and '?b' not in self.label:
            return [self.identifier] + leftTree + rightTree
        else:
            return leftTree + rightTree

    def get_type1Positions(self):
        """
    	returns list of identifier of all type 1 placeholders
		"""
        leftTree = []
        rightTree = []

        if self.left != None:
            leftTree = self.left.get_type1Positions()

        if self.right != None:
            rightTree = self.right.get_type1Positions()

        if '?u' in self.label:
            return [self.identifier] + leftTree + rightTree
        else:
            return leftTree + rightTree

    def get_type2Positions(self):
        """
        returns list of identifier of all type 2 placeholders
    	"""
        leftTree = []
        rightTree = []

        if self.left != None:
            leftTree = self.left.get_type2Positions()

        if self.right != None:
            rightTree = self.right.get_type2Positions()

        if '?b' in self.label:
            return [self.identifier] + leftTree + rightTree
        else:
            return leftTree + rightTree

    def assign_identifiers(self, i):
        '''
		assigns identifiers to each node of the syntax tree
		'''

        for node in self.getAllNodes():
            node.identifier = i
            i += 1

    def change_identifiers(self):
        """
        assigns new Identifiers to type0 placeholders which are larger than the size of the sketch
        """
        size = self.treeSize()
        ids = self.get_type0Positions()
        i = 0

        for node in self.getAllNodes():
            if node.identifier in ids:
                node.identifier = size + i
                i += 1

    def getAllIdentifier(self):
        if self.left != None:
            leftids = self.left.getAllIdentifier()
        else:
            leftids = []

        if self.right != None:
            rightids = self.right.getAllIdentifier()
        else:
            rightids = []
        return [self.identifier] + leftids + rightids

    def getDepth(self):
        if self.left == None and self.right == None:
            return 1
        leftValue = 0
        rightValue = 0
        if self.left != None:
            leftValue = self.left.getDepth()
        if self.right != None:
            rightValue = self.right.getDepth()
        return 1 + max(leftValue, rightValue)

    def getNumberOfSubformulas(self):
        return len(self.getSetOfSubformulas())

    def getSetOfSubformulas(self):
        if self.left == None and self.right == None:
            return [repr(self)]
        leftValue = []
        rightValue = []
        if self.left != None:
            leftValue = self.left.getSetOfSubformulas()
        if self.right != None:
            rightValue = self.right.getSetOfSubformulas()
        return list(set([repr(self)] + leftValue + rightValue))

    def getListOfSubformulas(self):
        if self.left == None and self.right == None:
            return [repr(self)]
        leftValue = []
        rightValue = []
        if self.left != None:
            leftValue = self.left.getListOfSubformulas()
        if self.right != None:
            rightValue = self.right.getListOfSubformulas()
        return [repr(self)] + leftValue + rightValue

    def treeSize(self):
        if self.size == None:
            if self.left == None and self.right == None:
                return 1
            leftSize = 0
            rightSize = 0
            if self.left != None:
                leftSize = self.left.treeSize()
            if self.right != None:
                rightSize = self.right.treeSize()
            self.size = 1 + leftSize + rightSize

        return self.size

    def substitute_sketch_type_1_2(self, substitutions):
        ids_to_sub = [sub[0] for sub in substitutions]

        for node in self.getAllNodes():
            if node.identifier in ids_to_sub:
                node.label = substitutions[ids_to_sub.index(node.identifier)][1]

        return self

    def substitute_sketch_type_0(self, substitutions):
        ids_to_sub = [sub[0] for sub in substitutions]

        for node in self.getAllNodes():
            if node.identifier in ids_to_sub:
                node.replace(substitutions[ids_to_sub.index(node.identifier)][1])

        return self

    @classmethod
    def convertTextToSketch(cls, sketchText):

        f = Sketch()
        try:
            sketch_parser = Lark(r"""
				?sketch: _binary_expression
						|_unary_expression
						| constant
						| variable
				!constant: "true"
						| "false"
				_binary_expression: binary_operator "(" sketch "," sketch ")" | bplaceholder "(" sketch "," sketch ")" 
				_unary_expression: unary_operator "(" sketch ")" | uplaceholder "(" sketch ")"
				
				!bplaceholder: /\?b/SIGNED_NUMBER
				!uplaceholder: /\?u/SIGNED_NUMBER
				!placeholder: "?"SIGNED_NUMBER
				variable: /[a-z]/ | placeholder
				!binary_operator: "&" | "|" | "->" | "U"
				!unary_operator: "F" | "G" | "!" | "X"
				
				%import common.SIGNED_NUMBER    
				%import common.WS
				%ignore WS 
			 """, start='sketch')

            tree = sketch_parser.parse(sketchText)

        except Exception as e:
            print("can't parse sketch %s" % sketchText)
            print("error: %s" % e)

        f = TreeToFormula().transform(tree)
        return f


# noinspection PyTypeChecker
class TreeToFormula(Transformer):
    def sketch(self, sketchArgs):

        return Sketch(sketchArgs)

    def bplaceholder(self, args):
        # print(args)
        return str(args[0]) + str(args[1])

    def uplaceholder(self, args):
        # print(args)
        return str(args[0]) + str(args[1])

    def placeholder(self, args):
        # print(args)
        return str(args[0]) + str(args[1])

    def variable(self, varName):
        # print(varName)
        return Sketch([str(varName[0]), None, None])

    def constant(self, arg):
        if str(arg[0]) == "true":
            connector = "|"
        elif str(arg[0]) == "false":
            connector = "&"
        return Sketch([connector, Sketch(["p", None, None]), Sketch(["!", Sketch(["p", None, None]), None])])

    def binary_operator(self, args):
        return str(args[0])

    def unary_operator(self, args):
        return str(args[0])


def display(formula):
    # get the nodes and the edge realtion

    # node_dict = {formula: identifier}
    # edges = {identifier}

    formula_queue = []
    formula_id = {formula: 1}
    edges = []

    if formula.left != None:
        formula_queue.append(formula.left)
        formula_id[formula.left] = 2 * formula_id[formula]
        edges.append((formula_id[formula], formula_id[formula.left]))
    if formula.right != None:
        formula_queue.append(formula.right)
        formula_id[formula.right] = 2 * formula_id[formula] + 1
        edges.append((formula_id[formula], formula_id[formula.right]))

    while formula_queue != []:
        curr_formula = formula_queue.pop()
        if curr_formula.left != None:
            if curr_formula.left not in formula_id:
                formula_queue.append(curr_formula.left)
                formula_id[curr_formula.left] = 2 * formula_id[curr_formula]
            edges.append((formula_id[curr_formula], formula_id[curr_formula.left]))
        if curr_formula.right != None:
            if curr_formula.right not in formula_id:
                formula_queue.append(curr_formula.right)
                formula_id[curr_formula.right] = 2 * formula_id[curr_formula] + 1
            edges.append((formula_id[curr_formula], formula_id[curr_formula.right]))

    print(formula_id)
    dot_str = "digraph g {\n"

    for formula in formula_id:
        dot_str += ('{} [label="{}"]\n'.format(formula_id[formula], formula.label))
    for edge in edges:
        dot_str += ('{} -> {}\n'.format(edge[0], edge[1]))

    dot_str += ("}\n")
    print(dot_str)
    s = Source(dot_str, filename="test.gv", format="png")
    s.view()
