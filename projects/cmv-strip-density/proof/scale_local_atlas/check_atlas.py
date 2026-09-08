#!/usr/bin/env python3
"""Scale-local numerical pilot, NOT a Lean proof or candidate-exclusion theorem.

Mean-value enclosure follows face_bridge_pilot/check_bridge.py:330-337.
Endpoints are integers times 2^-160; every arithmetic operation rounds outward.
R_k(x)=(-1)^k integral_0^1 t^(2k)/(1+x²t²) dt is evaluated with
20 exact geometric-series terms and an absolute integral remainder bound.
The derivative remainder uses |R_m'| <= 2|x|/(2m+3).
Floating point is used only by the separate producer, never for acceptance.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
import json
from pathlib import Path
import sys

import expressions

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'face_bridge_pilot'))
from check_bridge import PI as EXACT_PI, load_json, parse_q

BITS = 160
SCALE = 1 << BITS
TERMS = 20
NVAR = 5  # centered density parameter followed by four box displacements
NAMES = ['fold','cosine','third','gap','density_cube',
         's_pos','s_lt_one','y_pos','y_lt_one','w_pos','w_lt_one','v_pos','v_lt_one',
         'y_gt_s','v_gt_w','density_den','angle_den_four','angle_den_three',
         'atan_guard_four','atan_guard_three','height_order','A_pos','gap_den']
if json.loads(Path(__file__).with_name('expression_names.json').read_text()) != NAMES:
    raise ValueError('generated output contract mismatch')

PILOT_SCHEMA = 'cmv-scale-local-pilot-v1'
TARGET_SCHEMA = 'cmv-scale-local-target-manifest-v1'
SUPPORTED_SCHEMAS = {PILOT_SCHEMA, TARGET_SCHEMA}


def expected_bands(schema):
    """Exact scale and density bands accepted for each campaign."""
    delta0 = Q(251,20)*Q(1,126334)**3
    if schema == PILOT_SCHEMA:
        return [(Q(1,126334),delta0,8*delta0),
                (Q(1,25),Q(1,1000),Q(1,500))]
    if schema == TARGET_SCHEMA:
        target = Q(1,1000)
        bands = [(Q(2**j,126334),8**j*delta0,
                  min(8**(j+1)*delta0,target)) for j in range(13)]
        if (bands[0][1] != delta0 or bands[-1][2] != target or
                any(lo >= hi for _,lo,hi in bands) or
                any(left[2] != right[1] for left,right in zip(bands,bands[1:]))):
            raise AssertionError('invalid built-in target manifest')
        return bands
    raise ValueError('unsupported atlas schema')


def floor(q):
    q = Q(q) * SCALE
    return q.numerator // q.denominator


def ceil(q):
    return -floor(-Q(q))


@dataclass(frozen=True, slots=True)
class I:
    lo: int
    hi: int

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError('reversed interval')

    @staticmethod
    def bounds(lo, hi):
        return I(floor(lo), ceil(hi))

    @staticmethod
    def point(x):
        return I.bounds(x, x)

    def __add__(self, other):
        if isinstance(other, D):
            return NotImplemented
        o = as_i(other)
        return I(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        if isinstance(other, D):
            return NotImplemented
        return self + -as_i(other)

    def __rsub__(self, other):
        return as_i(other) + -self

    def __mul__(self, other):
        if isinstance(other, D):
            return NotImplemented
        o = as_i(other)
        products = (self.lo*o.lo, self.lo*o.hi, self.hi*o.lo, self.hi*o.hi)
        return I(min(products)//SCALE, -((-max(products))//SCALE))

    __rmul__ = __mul__

    def reciprocal(self):
        if self.lo <= 0 <= self.hi:
            raise ValueError('denominator contains zero')
        return I.bounds(Q(SCALE, self.hi), Q(SCALE, self.lo))

    def __truediv__(self, other):
        if isinstance(other, D):
            return NotImplemented
        return self * as_i(other).reciprocal()

    def __rtruediv__(self, other):
        return as_i(other) * self.reciprocal()

    def __pow__(self, n):
        if type(n) is not int:
            raise ValueError('only integer powers are supported')
        if n < 0:
            return self.reciprocal() ** -n
        if n == 0:
            return I.point(1)
        if n % 2 == 0:
            ends = (Q(self.lo, SCALE)**n, Q(self.hi, SCALE)**n)
            return I.bounds(0 if self.lo <= 0 <= self.hi else min(ends), max(ends))
        return I.bounds(Q(self.lo, SCALE)**n, Q(self.hi, SCALE)**n)

    def exact(self):
        return [str(Q(self.lo, SCALE)), str(Q(self.hi, SCALE))]


def as_i(x):
    return x if isinstance(x, I) else I.point(x)


ZERO = I.point(0)
ONE = I.point(1)
PI = I.bounds(EXACT_PI.lo, EXACT_PI.hi)


@dataclass(frozen=True, slots=True)
class D:
    v: I
    d: tuple[I, ...]

    @staticmethod
    def constant(x):
        return D(as_i(x), (ZERO,)*NVAR)

    def __add__(self, other):
        o = as_d(other)
        return D(self.v+o.v, tuple(a+b for a,b in zip(self.d,o.d)))

    __radd__ = __add__

    def __neg__(self):
        return D(-self.v, tuple(-a for a in self.d))

    def __sub__(self, other):
        return self + -as_d(other)

    def __rsub__(self, other):
        return as_d(other) + -self

    def __mul__(self, other):
        o = as_d(other)
        return D(self.v*o.v, tuple(a*o.v+self.v*b for a,b in zip(self.d,o.d)))

    __rmul__ = __mul__

    def reciprocal(self):
        inv = self.v.reciprocal()
        factor = -(inv**2)
        return D(inv, tuple(a*factor for a in self.d))

    def __truediv__(self, other):
        return self * as_d(other).reciprocal()

    def __rtruediv__(self, other):
        return as_d(other) * self.reciprocal()

    def __pow__(self, n):
        if type(n) is not int:
            raise ValueError('only integer powers are supported')
        if n == 0:
            return D.constant(1)
        factor = n*self.v**(n-1)
        return D(self.v**n, tuple(factor*a for a in self.d))


def as_d(x):
    return x if isinstance(x, D) else D.constant(x)


def rem_interval(x, k):
    """Finite geometric identity, valid without an alternating-series oracle."""
    if type(k) is not int or k < 0:
        raise ValueError('remainder index must be a nonnegative integer')
    bound = Q(max(abs(x.lo), abs(x.hi)), SCALE)
    if bound > Q(1,2):
        raise ValueError('remainder evaluation guard |x| <= 1/2 failed')
    square = x**2
    value, derivative = ZERO, ZERO
    for j in reversed(range(TERMS)):
        coefficient = Q((-1)**(k+j), 2*(k+j)+1)
        value = value*square + coefficient
        if j:
            derivative = derivative*square + 2*j*coefficient
    derivative = x*derivative
    m = k+TERMS
    error = bound**(2*TERMS)/Q(2*m+1)
    derivative_error = (2*TERMS*bound**(2*TERMS-1)/Q(2*m+1) +
                        2*bound**(2*TERMS+1)/Q(2*m+3))
    return (value+I.bounds(-error,error),
            derivative+I.bounds(-derivative_error,derivative_error))


def rem(x,k):
    if isinstance(x,D):
        value, derivative = rem_interval(x.v,k)
        return D(value, tuple(derivative*a for a in x.d))
    return rem_interval(as_i(x),k)[0]


expressions.rat = Q
expressions.rem = rem


def matrix_vector(matrix, vector):
    return [sum((a*b for a,b in zip(row,vector)), 0) for row in matrix]


def model_inputs(cell, whole):
    """Construct the five centered atlas variables and physical model inputs."""
    radius = (cell['mu'][1]-cell['mu'][0])/2
    bounds = [I.bounds(-radius,radius)] + [I.bounds(-r,r) for r in cell['radii']]
    if not whole:
        bounds = [ZERO]*NVAR
    variables = [D(b,tuple(ONE if i==j else ZERO for j in range(NVAR)))
                 for i,b in enumerate(bounds)]
    theta, *displacements = variables
    tau,u,v,w = [c+m*theta+d
                 for c,m,d in zip(cell['center'],cell['slope'],displacements)]
    return theta, tau, (cell['scale']*tau, PI, u, v, w), bounds


def model(cell, whole):
    mid = sum(cell['mu'])/2
    theta, tau, inputs, bounds = model_inputs(cell, whole)
    values = expressions.evaluate(*inputs)
    if len(values) != len(NAMES) or any(
            not isinstance(x,D) or len(x.d) != NVAR for x in values):
        raise ValueError('incomplete generated value or derivative vector')
    residuals = values[:3] + [tau**3*values[4]-(mid+theta)]
    return matrix_vector(cell['preconditioner'],residuals), values, bounds


def mean_value(value, center, bounds):
    return center.v + sum((a*b for a,b in zip(value.d,bounds)),ZERO)


def centered_record(value, point):
    """Retain the exact data needed by a centered-difference Lean instance."""
    if not isinstance(value, D) or not isinstance(point, D):
        raise ValueError('centered record requires dual interval values')
    if len(value.d) != NVAR or len(point.d) != NVAR:
        raise ValueError('centered record has wrong coordinate count')
    return {
        'center': point.v.exact(),
        'whole': value.v.exact(),
        'coefficients': [entry.exact() for entry in value.d],
    }


def check_cell(cell, include_centered=False):
    """Check one cell; optionally retain raw output centered coefficients."""
    full, values, bounds = model(cell,True)
    center, points, _ = model(cell,False)
    faces = {}
    accepted = True
    for i,row in enumerate(full):
        other = center[i].v + sum((a*b for j,(a,b) in enumerate(zip(row.d,bounds))
                                   if j != i+1),ZERO)
        low = other - cell['radii'][i]*row.d[i+1]
        high = other + cell['radii'][i]*row.d[i+1]
        faces[str(i)] = {'low':low.exact(),'high':high.exact()}
        accepted &= low.hi < 0 and high.lo > 0
    guards = {}
    for name,value,point in zip(NAMES[5:],values[5:],points[5:]):
        enclosure = mean_value(value,point,bounds)
        # Intersect two independently sound enclosures to reduce dependency.
        enclosure = I(max(enclosure.lo,value.v.lo),min(enclosure.hi,value.v.hi))
        guards[name] = enclosure.exact()
        accepted &= enclosure.lo > 0
    gap = mean_value(values[3],points[3],bounds)
    accepted &= gap.hi < 0
    result = {'status':'ENCLOSURES_PASS' if accepted else 'ENCLOSURES_FAIL',
              'faces':faces,'guards':guards,'gap':gap.exact(),
              'center_residuals':[x.v.exact() for x in center]}
    if include_centered:
        result['centered_bounds'] = [bound.exact() for bound in bounds]
        result['raw_outputs'] = {
            name: centered_record(value, point)
            for name, value, point in zip(NAMES, values, points)
        }
    return result


def parse_cell(raw):
    def q(x):
        return parse_q(x,'cell')
    cell = {k: q(raw[k]) for k in ['scale']}
    for k in ['mu','radii','center','slope']:
        cell[k] = [q(x) for x in raw[k]]
    cell['preconditioner'] = [[q(x) for x in row] for row in raw['preconditioner']]
    if set(raw) != set(cell):
        raise ValueError('unexpected cell keys')
    if not (cell['scale']>0 and len(cell['mu'])==2 and 0<cell['mu'][0]<cell['mu'][1]
            and all(len(cell[k])==4 for k in ['radii','center','slope'])
            and all(r>0 for r in cell['radii'])
            and len(cell['preconditioner'])==4
            and all(len(row)==4 for row in cell['preconditioner'])):
        raise ValueError('invalid cell shape or positive domain')
    # Exact invertibility; row preconditioning must preserve the zero set.
    matrix = [row[:] for row in cell['preconditioner']]
    for i in range(4):
        pivot = next((j for j in range(i,4) if matrix[j][i]),None)
        if pivot is None:
            raise ValueError('singular preconditioner')
        matrix[i],matrix[pivot] = matrix[pivot],matrix[i]
        for j in range(i+1,4):
            factor = matrix[j][i]/matrix[i][i]
            matrix[j] = [a-factor*b for a,b in zip(matrix[j],matrix[i])]
    return cell


def check(path):
    raw = load_json(path)
    if set(raw) != {'schema','bands'} or raw['schema'] not in SUPPORTED_SCHEMAS:
        raise ValueError('invalid atlas schema')
    expected = expected_bands(raw['schema'])
    if len(raw['bands']) != len(expected):
        raise ValueError('required atlas bands missing')
    results = []
    for band,(scale,target_lo,target_hi) in zip(raw['bands'],expected):
        if set(band) != {'delta','cells'}:
            raise ValueError('unexpected band keys')
        endpoints = [parse_q(x,'band endpoint') for x in band['delta']]
        if endpoints != [target_lo,target_hi] or not 0<len(band['cells'])<=64:
            raise ValueError('wrong band or subdivision cap exceeded')
        cursor = target_lo
        rows = []
        for data in band['cells']:
            cell = parse_cell(data)
            if cell['scale'] != scale:
                raise ValueError('wrong prescribed band scale')
            lower,upper = [cell['scale']**3*x for x in cell['mu']]
            if lower != cursor:
                raise ValueError('density seam mismatch')
            cursor = upper
            try:
                rows.append(check_cell(cell))
            except ValueError as exc:
                rows.append({'status':'ENCLOSURES_FAIL','error':str(exc)})
        if cursor != target_hi:
            raise ValueError('band coverage incomplete')
        results.append({'delta':band['delta'],'scale':str(scale),'cells':rows,
                        'accepted':sum(x['status']=='ENCLOSURES_PASS' for x in rows)})
    passed = all(b['accepted']==len(b['cells']) for b in results)
    campaign = 'TARGET_MANIFEST' if raw['schema'] == TARGET_SCHEMA else 'PILOT'
    return {'status':f'{campaign}_ENCLOSURES_PASS' if passed else
                     f'{campaign}_ENCLOSURES_FAIL',
            'proof_status':'NOT_KERNEL_REPLAYED','schema':raw['schema'],
            'bits':BITS,'remainder_terms':TERMS,'bands':results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    result = check(args.certificate)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'bands'}))
    for band in result['bands']:
        print(f"accepted {band['accepted']}/{len(band['cells'])} on {band['delta']}")
    return 0 if result['status'].endswith('_ENCLOSURES_PASS') else 1


if __name__ == '__main__':
    raise SystemExit(main())
