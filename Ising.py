# -*- coding: utf-8 -*-
from __future__ import print_function
import sage.cboot as cb
from sage.misc.cachefunc import cached_function
import os.path
import sys
from sage.rings.rational import Rational
from sage.all import pi, e, euler_gamma, catalan, khinchin, glaisher, sin, cos, tan, sec, csc, cot, sinh, cosh, tanh, sech, csch, coth, asin, acos, atan, asec, acsc, acot, asinh, acosh, atanh, asech, acsch, acoth, sqrt, log, exp, I

# <-- edit from here
context = cb.context_for_scalar(epsilon=0.5, Lambda=15, Prec=800)
spins = list(range(27)) + [49, 50]
nu_max = 14
# {(r, s): d, ...} means operators in irrep r and spin s must have Delta >= d.
mygap = {}
def gaps(deltas):
	return mygap

save_dir = "."

def name(deltas):
	return "sdp-{0[e]}-{0[a]}".format(deltas).replace("/", "#")

# edit to here -->

# do not edit from here
secs = {("rep[1]", 0): 1, ("rep[2]", 0): 1, ("rep[2]", 1): 1}
scalarnum = 1

@cached_function
def prepare_g(spin, Delta_12, Delta_34):
	return context.approx_cb(nu_max, spin, Delta_1_2=Delta_12, Delta_3_4=Delta_34)

def get_shift(gaps, sector, spin):
	if (sector, spin) in gaps: return context(gaps[(sector, spin)])
	elif spin == 0: return context.epsilon
	else: return 2 * context.epsilon + spin

val = [(context("1") / context("2"))]
one = context(1)

def make_F_range(delta, sector, num, spin):
	shift = get_shift(gaps(delta), sector, spin)
	sign = one if spin % 2 == 0 else -one
	F = lambda d1, d2, d3, d4: sign * context.dot(context.F_minus_matrix((d2 + d3) / 2), prepare_g(spin, d1 - d2, d3 - d4).shift(shift))
	H = lambda d1, d2, d3, d4: sign * context.dot(context.F_plus_matrix((d2 + d3) / 2), prepare_g(spin, d1 - d2, d3 - d4).shift(shift))
	get = lambda fh, d1, d2, d3, d4: fh(delta[d1], delta[d2], delta[d3], delta[d4])
	if sector == "rep[1]" and spin % 2 == 0 and num == 0:
		bl = [get(F, "a", "a", "a", "a"), get(F, "e", "e", "a", "a"), get(F, "e", "e", "e", "e"), get(H, "e", "e", "a", "a")]
		return [[[bl[0], 0], [0, 0]], [[0, val[0] * bl[1]], [val[0] * bl[1], 0]], [[0, 0], [0, bl[2]]], [[0, val[0] * bl[3]], [val[0] * bl[3], 0]], [[0, 0], [0, 0]]]
	if sector == "rep[2]" and spin % 2 == 0 and num == 0:
		bl = [get(F, "e", "a", "a", "e"), get(H, "e", "a", "a", "e"), get(F, "e", "a", "e", "a")]
		return [0, bl[0], 0, -bl[1], bl[2]]
	if sector == "rep[2]" and spin % 2 == 1 and num == 0:
		bl = [get(F, "e", "a", "a", "e"), get(H, "e", "a", "a", "e"), get(F, "e", "a", "e", "a")]
		return [0, -bl[0], 0, bl[1], bl[2]]
	raise RuntimeError("unknown sector name")

def make_F_scalar(delta, num):
	F = lambda d1, d2, d3, d4, d: context.dot(context.F_minus_matrix((d2 + d3) / 2), context.gBlock(0, d, d1 - d2, d3 - d4))
	H = lambda d1, d2, d3, d4, d: context.dot(context.F_plus_matrix((d2 + d3) / 2), context.gBlock(0, d, d1 - d2, d3 - d4))
	get = lambda fh, d1, d2, d3, d4, d: fh(delta[d1], delta[d2], delta[d3], delta[d4], delta[d])
	if num == 0:
		bl = [get(F, "a", "a", "a", "a", "e"), get(F, "e", "a", "a", "e", "a"), get(F, "e", "e", "a", "a", "e"), get(F, "e", "e", "e", "e", "e"), get(H, "e", "a", "a", "e", "a"), get(H, "e", "e", "a", "a", "e"), get(F, "e", "a", "e", "a", "a")]
		return [[[bl[0], 0], [0, 0]], [[bl[1], val[0] * bl[2]], [val[0] * bl[2], 0]], [[0, 0], [0, bl[3]]], [[-bl[4], val[0] * bl[5]], [val[0] * bl[5], 0]], [[bl[6], 0], [0, 0]]]
	raise RuntimeError("unknown sector number")

def make_F_unit(delta):
	F = lambda d1, d2, d3, d4: context.dot(context.F_minus_matrix((d2 + d3) / 2), context.gBlock(0, 0, d1 - d2, d3 - d4))
	H = lambda d1, d2, d3, d4: context.dot(context.F_plus_matrix((d2 + d3) / 2), context.gBlock(0, 0, d1 - d2, d3 - d4))
	get = lambda fh, d1, d2, d3, d4: fh(delta[d1], delta[d2], delta[d3], delta[d4])
	bl = [get(F, "a", "a", "a", "a"), get(F, "e", "e", "a", "a"), get(F, "e", "e", "e", "e"), get(H, "e", "e", "a", "a")]
	return [bl[0], bl[1], bl[2], bl[3], 0]

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

def write_SDP(deltas, dir=None, file=None, overwrite=False):
	if dir is None: dir = save_dir
	if file is None: file = name(deltas) + ".xml"
	path = os.path.join(dir, file)
	if overwrite or not os.path.exists(path): make_SDP(deltas).write(path)
	return path
