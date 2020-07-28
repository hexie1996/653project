import ast
import astor
import graphviz as gv

def invert(node): # to get the opposite condition so that we can get the exitcase
	inverse = {ast.Eq: ast.NotEq,
			   ast.NotEq: ast.Eq,
			   ast.Lt: ast.GtE,
			   ast.LtE: ast.Gt,
			   ast.Gt: ast.LtE,
			   ast.GtE: ast.Lt,
			   ast.Is: ast.IsNot,
			   ast.IsNot: ast.Is,
			   ast.In: ast.NotIn,
			   ast.NotIn: ast.In}
	if type(node) == ast.Compare:
		op = type(node.ops[0])
		inverse_node = ast.Compare(left=node.left, ops=[inverse[op]()],
								   comparators=node.comparators)
	elif type(node) == ast.BinOp and type(node.op) in inverse:
		op = type(node.op)
		inverse_node = ast.BinOp(node.left, inverse[op](), node.right)
	elif type(node) == ast.NameConstant and node.value in [True, False]:
		inverse_node = ast.NameConstant(value=not node.value)
	else:
		inverse_node = ast.UnaryOp(op=ast.Not(), operand=node)

	return inverse_node

def merge_exitcases(exit1, exit2):
	if exit1:
		if exit2:
			return ast.BoolOp(ast.And(), values=[exit1, exit2])
		return exit1
	return exit2
# objects: block link cfg
class Block(object):
	def __init__(self, id):
		self.id = id
		self.labels = [] #statemens of the block
		self.functions = [] # if the functions are called
		self.predecessors = []
		self.exits = []

	def is_empty(self):
		#to see if the block has no label
		return len(self.labels) == 0
	def get_source(self):
		#convert ast tree into python statement
		src = ''
		for label in self.labels:
			if type(label) in [ast.If, ast.For, ast.While,ast.FunctionDef]:
				src += (astor.to_source(label)).split('\n')[0] + "\n"
			else:
				src += astor.to_source(label)
		return src
	def get_calls(self):
		txt = ""
		for func_name in self.functions:
			txt += func_name + '\n'
		return txt

class Link(object):
	def __init__(self, source, target, exitcase=None):
		self.source = source
		self.target = target
		self.exitcase = exitcase
	def get_exitcase(self):
		if self.exitcase:
			return astor.to_source(self.exitcase)
		else:
			return ""
class CFG(object):
	def __init__(self, name):
		self.name = name
		self.entryblock = None
		self.functioncfgs = {}
	def _visit_blocks(self, graph, block, visited=[]):
		if block.id in visited:
			return
		nodelabel = block.get_source()
		graph.node(str(block.id), label=nodelabel)
		visited.append(block.id)

		if block.functions:
			calls_node = str(block.id)+"_calls"
			calls_label = block.get_calls().strip()
			#style of call node and edges
			graph.node(calls_node, label=calls_label,_attributes={'shape': 'box'})
			graph.edge(str(block.id), calls_node, label="calls",_attributes={'style': 'dashed'})

		# visit the rest of the blocks
		for exit in block.exits:
			self._visit_blocks(graph, exit.target, visited)
			edgelabel = exit.get_exitcase().strip()
			graph.edge(str(block.id), str(exit.target.id), label=edgelabel)
	
	def build_visual(self, filepath, format):
		graph = self._build_visual(format)
		graph.render(filepath, view=True)

	def _build_visual(self, format='png'):
		graph = gv.Digraph(name='cluster'+self.name, format=format,
						   graph_attr={'label': self.name})
		self._visit_blocks(graph, self.entryblock, visited=[])

		for subcfg in self.functioncfgs:
			subgraph = self.functioncfgs[subcfg]._build_visual(format=format)
			graph.subgraph(subgraph)

		return graph
class CFGBuilder(ast.NodeVisitor):
	def __init__(self):
		super().__init__()
		self.after_loop_block_stack = []
		self.curr_loop_guard_stack = []

	def build(self, name, tree, entry_id=0):
		self.cfg = CFG(name)
		self.current_id = entry_id
		self.current_block = self.new_block()
		self.cfg.entryblock = self.current_block
		self.visit(tree)
		self.clean_cfg(self.cfg.entryblock)
		return self.cfg

	def build_from_file(self, name, filepath):
		with open(filepath, 'r') as src_file:
			src = src_file.read()
		tree = ast.parse(src, mode='exec')
		return self.build(name, tree)

	def new_block(self):
		self.current_id += 1
		return Block(self.current_id)

	def add_statement(self, block, label):
		block.labels.append(label)

	def add_exit(self, block, nextblock, exitcase=None):
		newlink = Link(block, nextblock, exitcase)
		block.exits.append(newlink)
		nextblock.predecessors.append(newlink)

	def new_loopguard(self):
		if self.current_block.is_empty() and len(self.current_block.exits) == 0:
			 loopguard = self.current_block
		else:
			loopguard = self.new_block()
			self.add_exit(self.current_block, loopguard)
		return loopguard

	def new_functionCFG(self, node):
		self.current_id += 1
		func_body = ast.Module(body=node.body)
		func_builder = CFGBuilder()
		self.cfg.functioncfgs[node.name] = func_builder.build(node.name,func_body,self.current_id)
		self.current_id = func_builder.current_id + 1

	def clean_cfg(self, block, visited=[]):
		if block in visited:
			return
		visited.append(block)
		if block.is_empty():
			for pred in block.predecessors:
				for exit in block.exits:
					self.add_exit(pred.source, exit.target,merge_exitcases(pred.exitcase,exit.exitcase))
					if exit in exit.target.predecessors:
						exit.target.predecessors.remove(exit)
				if pred in pred.source.exits:
					pred.source.exits.remove(pred)
			block.predecessors = []
			for exit in block.exits[:]:
				self.clean_cfg(exit.target, visited)
			block.exits = []
		else:
			for exit in block.exits[:]:
				self.clean_cfg(exit.target, visited)
	#visit methods
	def visit_Expr(self, node):
		self.add_statement(self.current_block, node)
		self.generic_visit(node)

	def visit_Call(self, node):
		def visit_func(node):
			if type(node) == ast.Name:
				return node.id
			elif type(node) == ast.Attribute:
				func_name = visit_func(node.value)
				func_name += "." + node.attr
				return func_name
			elif type(node) == ast.Str:
				return node.s
			elif type(node) == ast.Subscript:
				return node.value.id
		func = node.func
		func_name = visit_func(func)
		self.current_block.functions.append(func_name)
	def visit_Assign(self, node):
		self.add_statement(self.current_block, node)
		self.generic_visit(node)
	def visit_AnnAssign(self, node):
		self.add_statement(self.current_block, node)
		self.generic_visit(node)
	def visit_AugAssign(self, node):
		self.add_statement(self.current_block, node)
		self.generic_visit(node)
	def visit_Assert(self, node):
		self.add_statement(self.current_block, node)
		failblock = self.new_block()
		self.add_exit(self.current_block, failblock, invert(node.test))
		successblock = self.new_block()
		self.add_exit(self.current_block, successblock, node.test)
		self.current_block = successblock
		self.generic_visit(node)

	def visit_If(self, node):
		self.add_statement(self.current_block, node)
		if_block = self.new_block()
		self.add_exit(self.current_block, if_block, node.test)
		afterif_block = self.new_block()
		#consider about else condition
		if len(node.orelse) != 0:
			else_block = self.new_block()
			self.add_exit(self.current_block, else_block, invert(node.test))
			self.current_block = else_block
			# each else if condition is seen as a new if statement
			for child in node.orelse:
				self.visit(child)
			if not self.current_block.exits:
				self.add_exit(self.current_block, afterif_block)
		else:
			self.add_exit(self.current_block, afterif_block, invert(node.test))
		self.current_block = if_block
		for child in node.body:
			self.visit(child)
		if not self.current_block.exits:
			self.add_exit(self.current_block, afterif_block)
		self.current_block = afterif_block

	def visit_While(self, node):
		loop_guard = self.new_loopguard()
		self.current_block = loop_guard
		self.add_statement(self.current_block, node)
		self.curr_loop_guard_stack.append(loop_guard)
		while_block = self.new_block()
		self.add_exit(self.current_block, while_block, node.test)
		afterwhile_block = self.new_block()
		self.after_loop_block_stack.append(afterwhile_block)
		self.current_block = while_block
		for child in node.body:
			self.visit(child)
		if not self.current_block.exits:
			self.add_exit(self.current_block, loop_guard)
		self.current_block = afterwhile_block
		self.after_loop_block_stack.pop()
		self.curr_loop_guard_stack.pop()

	def visit_For(self, node):
		loop_guard = self.new_loopguard()
		self.current_block = loop_guard
		self.add_statement(self.current_block, node)
		self.curr_loop_guard_stack.append(loop_guard)
		for_block = self.new_block()
		self.add_exit(self.current_block, for_block, node.iter)
		afterfor_block = self.new_block()
		self.add_exit(self.current_block, afterfor_block)
		self.after_loop_block_stack.append(afterfor_block)
		self.current_block = for_block
		for child in node.body:
			self.visit(child)
		if not self.current_block.exits:
			self.add_exit(self.current_block, loop_guard)
		self.current_block = afterfor_block
		self.after_loop_block_stack.pop()
		self.curr_loop_guard_stack.pop()
	def visit_Break(self, node):
		assert len(self.after_loop_block_stack), "Found break not inside loop"
		self.add_exit(self.current_block, self.after_loop_block_stack[-1])
	def visit_Continue(self, node):
		assert len(self.curr_loop_guard_stack), "Found continue outside loop"
		self.add_exit(self.current_block,self.curr_loop_guard_stack[-1])  
	def visit_Import(self, node):
		self.add_statement(self.current_block, node)
	def visit_ImportFrom(self, node):
		self.add_statement(self.current_block, node)
	def visit_FunctionDef(self, node):
		self.add_statement(self.current_block, node)
		self.new_functionCFG(node)
	def visit_Await(self, node):
		afterawait_block = self.new_block()
		self.add_exit(self.current_block, afterawait_block)
		self.generic_visit(node)
		self.current_block = afterawait_block
	def visit_Return(self, node):
		self.add_statement(self.current_block, node)
		self.current_block = self.new_block()
	def visit_Yield(self, node):
		afteryield_block = self.new_block()
		self.add_exit(self.current_block, afteryield_block)
		self.current_block = afteryield_block