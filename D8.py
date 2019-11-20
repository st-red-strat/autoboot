# -*- coding: utf-8 -*-
from __future__ import print_function
import sage.cboot as cb
from sage.misc.cachefunc import cached_function
import os.path
import sys
from sage.rings.rational import Rational
from sage.all import pi, e, euler_gamma, catalan, khinchin, glaisher, sin, cos, tan, sec, csc, cot, sinh, cosh, tanh, sech, csch, coth, asin, acos, atan, asec, acsc, acot, asinh, acosh, atanh, asech, acsch, acoth, sqrt, log, exp, I

context = cb.context_for_scalar(epsilon=0.5, Lambda=11)
spins = list(range(22))
secs = {("rep[1]", 0): 1, ("rep[2]", 0): 1, ("rep[3]", 0): 1, ("rep[4]", 1): 1, ("rep[5]", 0): 1, ("rep[5]", 1): 1}
scalarnum = 1
nu_max = 8
mygap = {}
def gaps(deltas):
	return mygap

save_dir = "."

def get_path(path):
	return os.path.join(save_dir, path)

@cached_function
def prepare_g(spin, Delta_12, Delta_34):
	return context.approx_cb(nu_max, spin, Delta_1_2=Delta_12, Delta_3_4=Delta_34)

def get_shift(gaps, sector, spin):
	if (sector, spin) in gaps: return context(gaps[(sector, spin)])
	elif spin == 0: return context.epsilon
	else: return 2 * context.epsilon + spin

val = [((context("1") / context("2")) * pow(context("2"), (context("-1") / context("2")))), (context("1") / context("2"))]
one = context(1)

def make_F_range(delta, sector, num, spin):
	shift = get_shift(gaps(delta), sector, spin)
	sign = one if spin % 2 == 0 else -one
	F = lambda d1, d2, d3, d4: sign * context.dot(context.F_minus_matrix((d2 + d3) / 2), prepare_g(spin, d1 - d2, d3 - d4).shift(shift))
	H = lambda d1, d2, d3, d4: sign * context.dot(context.F_plus_matrix((d2 + d3) / 2), prepare_g(spin, d1 - d2, d3 - d4).shift(shift))
	get = lambda fh, d1, d2, d3, d4: fh(delta[d1], delta[d2], delta[d3], delta[d4])
	if sector == "rep[1]" and spin % 2 == 0 and num == 0:
		bl = [get(F, "e", "e", "e", "e"), get(F, "e", "e", "v", "v"), get(F, "v", "v", "v", "v"), get(H, "e", "e", "v", "v"), get(H, "v", "v", "v", "v")]
		return [[[bl[0], 0], [0, 0]], [[0, val[0] * bl[1]], [val[0] * bl[1], 0]], [[0, 0], [0, 0]], [[0, 0], [0, 0]], [[0, 0], [0, val[1] * bl[2]]], [[0, val[0] * bl[3]], [val[0] * bl[3], 0]], [[0, 0], [0, val[1] * bl[4]]], [[0, 0], [0, 0]]]
	if sector == "rep[2]" and spin % 2 == 0 and num == 0:
		bl = [get(F, "v", "v", "v", "v"), get(H, "v", "v", "v", "v")]
		return [0, 0, 0, bl[0], 0, 0, -val[1] * bl[1], 0]
	if sector == "rep[3]" and spin % 2 == 0 and num == 0:
		bl = [get(F, "v", "v", "v", "v"), get(H, "v", "v", "v", "v")]
		return [0, 0, bl[0], 0, 0, 0, -val[1] * bl[1], 0]
	if sector == "rep[4]" and spin % 2 == 1 and num == 0:
		bl = [get(F, "v", "v", "v", "v"), get(H, "v", "v", "v", "v")]
		return [0, 0, bl[0], bl[0], -val[1] * bl[0], 0, val[1] * bl[1], 0]
	if sector == "rep[5]" and spin % 2 == 0 and num == 0:
		bl = [get(F, "e", "v", "v", "e"), get(H, "e", "v", "v", "e"), get(F, "e", "v", "e", "v")]
		return [0, val[1] * bl[0], 0, 0, 0, -val[1] * bl[1], 0, bl[2]]
	if sector == "rep[5]" and spin % 2 == 1 and num == 0:
		bl = [get(F, "e", "v", "v", "e"), get(H, "e", "v", "v", "e"), get(F, "e", "v", "e", "v")]
		return [0, -val[1] * bl[0], 0, 0, 0, val[1] * bl[1], 0, bl[2]]
	raise RuntimeError("unknown sector name")

def make_F_scalar(delta, num):
	F = lambda d1, d2, d3, d4, d: context.dot(context.F_minus_matrix((d2 + d3) / 2), context.gBlock(0, d, d1 - d2, d3 - d4))
	H = lambda d1, d2, d3, d4, d: context.dot(context.F_plus_matrix((d2 + d3) / 2), context.gBlock(0, d, d1 - d2, d3 - d4))
	get = lambda fh, d1, d2, d3, d4, d: fh(delta[d1], delta[d2], delta[d3], delta[d4], delta[d])
	if num == 0:
		bl = [get(F, "e", "e", "e", "e", "e"), get(F, "e", "e", "v", "v", "e"), get(F, "e", "v", "v", "e", "v"), get(F, "v", "v", "v", "v", "e"), get(H, "e", "e", "v", "v", "e"), get(H, "e", "v", "v", "e", "v"), get(H, "v", "v", "v", "v", "e"), get(F, "e", "v", "e", "v", "v")]
		return [[[bl[0], 0], [0, 0]], [[0, val[0] * bl[1]], [val[0] * bl[1], val[1] * bl[2]]], [[0, 0], [0, 0]], [[0, 0], [0, 0]], [[0, 0], [0, val[1] * bl[3]]], [[0, val[0] * bl[4]], [val[0] * bl[4], -val[1] * bl[5]]], [[0, 0], [0, val[1] * bl[6]]], [[0, 0], [0, bl[7]]]]
	raise RuntimeError("unknown sector number")

def make_F_unit(delta):
	F = lambda d1, d2, d3, d4: context.dot(context.F_minus_matrix((d2 + d3) / 2), context.gBlock(0, 0, d1 - d2, d3 - d4))
	H = lambda d1, d2, d3, d4: context.dot(context.F_plus_matrix((d2 + d3) / 2), context.gBlock(0, 0, d1 - d2, d3 - d4))
	get = lambda fh, d1, d2, d3, d4: fh(delta[d1], delta[d2], delta[d3], delta[d4])
	bl = [get(F, "e", "e", "e", "e"), get(F, "e", "e", "v", "v"), get(F, "v", "v", "v", "v"), get(H, "e", "e", "v", "v"), get(H, "v", "v", "v", "v")]
	return [bl[0], bl[1], 0, 0, bl[2], bl[3], bl[4], 0]

def make_SDP(delta):
	cdel = dict()
	for k in delta: cdel[k] = context(delta[k])
	pvms = []
	for sec in secs:
		for spin in spins:
			if spin % 2 == sec[1]:
				for num in range(secs[sec]): pvms.append(make_F_range(cdel, sec[0], num, spin))
	for num in range(scalarnum): pvms.append(make_F_scalar(cdel, num))
	norm = make_F_unit(cdel)
	obj = 0
	return context.sumrule_to_SDP(norm, obj, pvms)

def name(deltas):
	return "sdp-{0[e]}-{0[v]}".format(deltas).replace("/", "#")

def has_done(deltas):
	return os.path.exists(get_path(name(deltas) + ".xml"))

def writefl(mes):
	print(mes, end="")
	sys.stdout.flush()

def write_SDP(deltas):
	prob = get_path(name(deltas) + ".xml")
	if not has_done(deltas): make_SDP(deltas).write(prob)
