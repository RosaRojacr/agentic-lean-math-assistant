#!/usr/bin/env python3
"""Untrusted predictors; acceptance is recomputed by check_atlas.py.

Each band uses exactly 64 closed rational subslabs. The default reproduces the
two retained pilot bands; ``--campaign target`` produces the exact thirteen-band
manifest through delta = 1/1000. Centers and inverse Jacobians use 65-digit
mpmath then round to 100-bit dyadic rationals. Endpoint predictor defects set
initial radii; failed face radii double at most 12 times. No sampled value can
accept a slab. No subdivision beyond the cap is allowed.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
from fractions import Fraction as Q
import json
from pathlib import Path
from types import FunctionType
import time

import mpmath as mp
import check_atlas as check
import expressions

mp.mp.dps = 65


def numeric_rem(x,k):
    value = mp.mpf(0)
    for j in reversed(range(64)):
        value = value*x*x + mp.mpf((-1)**(k+j))/(2*(k+j)+1)
    return value


numeric_evaluate = FunctionType(expressions.evaluate.__code__,
    {'rat':lambda n,d:mp.mpf(n)/d,'rem':numeric_rem})


def real(q):
    return mp.mpf(q.numerator)/q.denominator


def rationalize(x):
    return Q(int(mp.nint(x*2**100)),2**100)


def rows(scale,mu,x):
    tau,u,v,w = x
    values = numeric_evaluate(scale*tau,mp.pi,u,v,w)
    return mp.matrix(values[:3]+[tau**3*values[4]-mu])


@lru_cache(maxsize=1)
def seed():
    return mp.findroot(lambda u,v,w:tuple(numeric_evaluate(0,mp.pi,u,v,w)[:3]),
                       (50,50,-750))


@lru_cache(maxsize=None)
def root_at(scale,mu):
    guess = [(real(mu)/(4*mp.pi))**(mp.mpf(1)/3)]+list(seed())
    return mp.findroot(lambda *x:rows(real(scale),real(mu),x),guess,
                       tol=mp.mpf('1e-52'))


def make_cell(scale,lo,hi):
    mid = (lo+hi)/2
    center = root_at(scale,mid)
    jac = mp.matrix(mp.calculus.optimization.jacobian(
        mp,lambda *x:rows(real(scale),real(mid),x),center))
    inv = jac**-1
    slope = inv[:,3]
    radii = []
    for j in range(4):
        error = max(abs(root_at(scale,end)[j]-center[j]-slope[j]*real(end-mid))
                    for end in [lo,hi])
        radii.append(rationalize(3*error+mp.mpf(['1e-7','1e-4','1e-4','1e-2'][j])))
    return {'scale':scale,'mu':[lo,hi],'center':list(map(rationalize,center)),
            'slope':list(map(rationalize,slope)),'radii':radii,
            'preconditioner':[[rationalize(inv[i,j]) for j in range(4)] for i in range(4)]}


def tune(cell):
    for attempt in range(13):
        result = check.check_cell(cell)
        if result['status']=='ENCLOSURES_PASS':
            return result,attempt
        failed = [int(k) for k,f in result['faces'].items()
                  if Q(f['low'][1])>=0 or Q(f['high'][0])<=0]
        if not failed or attempt==12:
            return result,attempt
        for j in failed:
            cell['radii'][j] *= 2
    raise AssertionError('unreachable')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--receipt',type=Path,required=True)
    parser.add_argument('--campaign',choices=['pilot','target'],default='pilot')
    args = parser.parse_args()
    start = time.monotonic()
    schema = check.TARGET_SCHEMA if args.campaign == 'target' else check.PILOT_SCHEMA
    targets = check.expected_bands(schema)
    bands,attempts = [],[]
    for scale,lo,hi in targets:
        cells,log = [],[]
        for j in range(64):
            cell = make_cell(scale,(lo+(hi-lo)*j/64)/scale**3,
                             (lo+(hi-lo)*(j+1)/64)/scale**3)
            result,steps = tune(cell)
            cells.append(cell)
            log.append({'index':j,'doublings':steps,'status':result['status']})
        bands.append({'delta':[lo,hi],'cells':cells})
        attempts.append(log)
        print(f"band {lo} .. {hi}: {sum(x['status']=='ENCLOSURES_PASS' for x in log)}/64",
              flush=True)
    args.output.write_text(json.dumps({'schema':schema,'bands':bands},
                                     default=str,indent=2)+'\n')
    receipt = {'status':'PRODUCER_ONLY','campaign':args.campaign,'schema':schema,
               'bands':len(bands),'cells':sum(len(band['cells']) for band in bands),
               'precision_decimal_digits':65,'predictor_dyadic_bits':100,
               'predictor_remainder_terms':64,
               'elapsed_seconds':time.monotonic()-start,'attempts':attempts}
    args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='attempts'}))


if __name__=='__main__':
    main()
