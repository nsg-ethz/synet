#!/usr/bin/python

import glob, os, numpy

LOGS='results'

data = {}

for result_file in glob.glob(os.path.join(LOGS, '*.txt')):
	basename = os.path.basename(result_file).strip('.txt')
	topology = basename.split('-')[0]
	mode = basename.split('-')[1]
	run_id = basename.split('-')[2]
	if topology not in data.keys():
		data[topology] = {}
	if mode not in data[topology].keys():
		data[topology][mode] = []
	last_line = open(result_file, 'r').readlines()[-1].strip()
	if not last_line.startswith('Synthesis time:'):
		continue
	synthesis_time = float(last_line.split(': ')[1])
	data[topology][mode].append(synthesis_time)

for topo in data.keys():
	for mode in data[topo].keys():
		times = data[topo][mode]
		if len(times) == 0:
			continue
		print topo, mode, numpy.average(times), numpy.std(times)
