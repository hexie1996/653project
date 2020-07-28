from cfg_generator import *

cfg = CFGBuilder().build_from_file('example.py', './example.py')
cfg.build_visual('exampleCFG', 'png')