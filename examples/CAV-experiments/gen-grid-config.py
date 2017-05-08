#!/usr/bin/python

import sys

assert len(sys.argv) == 3

n=int(sys.argv[1])
mode=sys.argv[2]

inputs_file = open('grid{}-{}.logic'.format(n, mode), 'w')
req_file = open('grid{}-{}-req.logic'.format(n, mode), 'w')

print 'Genearing config for grid of size', n, 'in mode', mode

for x in range(1, n+1):
	for y in range(1, n+1):
		inputs_file.write('+SetNode("R{}{}").\n'.format(x, y))

for x in range(1, n+1):
	for y in range(1, n+1):
		num_ifaces = (1 if x in [1, n] else 2) + (1 if y in [1, n] else 2)
		for i in range(1, num_ifaces+1):
			inputs_file.write('+SetInterface("R{}{}","I{}{}_{}").\n'.format(x, y, x, y, i))

for y in range(1, n+1):
	for x in range(1, n+1):
		# add left link
		if x < n:
			cur_iface = 1
			opposite_iface = 1 + (1 if (x + 1) < n else 0) + (1 if y < n else 0)
			inputs_file.write('+SetLink("I{}{}_{}", "I{}{}_{}").\n'.format(y, x, cur_iface, y, x+1, opposite_iface))
		# add down link
		if y < n:
			cur_iface = 1 + (1 if x < n else 0)
			opposite_iface = 1 + (1 if x < n else 0) + (1 if (y + 1) < n else 0) + (1 if x > 1 else 0)
			inputs_file.write('+SetLink("I{}{}_{}", "I{}{}_{}").\n'.format(y, x, cur_iface, y+1, x, opposite_iface))

for x in range(1, n+1):
	for y in range(1, n+1):
		inputs_file.write('+SetAdminDist("R{}{}","static",1).\n'.format(x, y))
		inputs_file.write('+SetAdminDist("R{}{}","bgp",2).\n'.format(x, y))
		inputs_file.write('+SetAdminDist("R{}{}","ospf",3).\n'.format(x, y))


inputs_file.write('+SetNetwork("R{}{}","N{}{}_1").\n'.format(n,n,n,n))

if mode == 'bgp':
	inputs_file.write('+SetNetwork("R{}1","N{}1_BGP").\n'.format(n,n))
	inputs_file.write('+SetBGPAnnouncement("R{}1","N{}1_BGP", "GOOGLE", "1;2;3", 3).\n'.format(n,n))


for y in range(1, n+1):
	for x in range(1, n+1):
		if x < n:
			req_file.write('+Fwd("N{}{}_1", "R{}{}", "R{}{}", "{}").\n'.format(n, n, y, x, y, x+1, 'static' if mode == 'static' else 'ospf'))
		elif y < n:
			req_file.write('+Fwd("N{}{}_1", "R{}{}", "R{}{}", "{}").\n'.format(n, n, y, x, y+1, x, 'static' if mode == 'static' else 'ospf'))

if mode == 'bgp':
	for x in range(1, n+1):
		for y in range(1, n+1):
			print x, y
			if y < n:
				req_file.write('+Fwd("N{}1_BGP", "R{}{}", "R{}{}", "{}").\n'.format(n, y, x, y+1, x, 'static' if mode == 'static' else 'ospf'))
				print '+Fwd("N{}1_BGP", "R{}{}", "R{}{}", "{}").\n'.format(n, y, x, y+1, x, 'static' if mode == 'static' else 'ospf')
			elif x > 1:
				req_file.write('+Fwd("N{}1_BGP", "R{}{}", "R{}{}", "{}").\n'.format(n, y, x, y, x-1, 'static' if mode == 'static' else 'ospf'))
				print '+Fwd("N{}1_BGP", "R{}{}", "R{}{}", "{}").\n'.format(n, y, x, y, x-1, 'static' if mode == 'static' else 'ospf')

if mode == 'bgp':
	for x in range(2, n+1):
		req_file.write('+Fwd("GOOGLE", "R{}{}", "R{}{}", "bgp").\n'.format(n, x, n, x-1))

inputs_file.close()
req_file.close()
