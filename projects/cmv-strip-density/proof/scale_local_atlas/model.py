#!/usr/bin/env python3
"""Exact local model producer; symbolic identities are NOT Lean proof receipts.

Jet coefficients are exact polynomials in pi and local coordinates. Tails are
exact expressions, not truncations. Arctangent integral remainders stay explicit.
Definitions mirror NearOneNormalizedFlow, NearOneAnalyticSystem,
NearOneRegularizedThirdRow and NearOneFirstCellGap.
"""
from __future__ import annotations

from functools import lru_cache
import sympy as S
from sympy.printing.pycode import PythonCodePrinter

s, p, u, v, w = S.symbols('s p u v w')
REM = S.Function('rem')


def simp(x):
    return S.factor(S.expand(x))


class Jet:
    """f(s) = sum(c[k]*s**k, k<N) + s**N*tail, exactly."""
    def __init__(self, c, tail=0, value=None):
        self.c = tuple(map(S.sympify, c))
        self.n = len(c)
        self.tail = S.sympify(tail)
        self.value = (sum(a*s**k for k, a in enumerate(self.c)) +
                      s**self.n*self.tail) if value is None else value

    @classmethod
    def const(cls, x, n=4):
        return cls([x]+[0]*(n-1))

    def lift(self, x):
        if isinstance(x, Jet):
            assert x.n == self.n
            return x
        return Jet.const(x, self.n)

    def __add__(self, other):
        o = self.lift(other)
        return Jet([simp(a+b) for a,b in zip(self.c,o.c)],
                   self.tail+o.tail, self.value+o.value)
    __radd__ = __add__

    def __neg__(self):
        return Jet([-a for a in self.c], -self.tail, -self.value)

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) + -self

    def __mul__(self, other):
        o = self.lift(other)
        n = self.n
        c = [simp(sum(self.c[i]*o.c[k-i] for i in range(k+1)))
             for k in range(n)]
        high = sum(self.c[i]*o.c[j]*s**(i+j-n)
                   for i in range(n) for j in range(n) if i+j >= n)
        a = sum(x*s**i for i,x in enumerate(self.c))
        b = sum(x*s**i for i,x in enumerate(o.c))
        tail = high + self.tail*b + o.tail*a + s**n*self.tail*o.tail
        return Jet(c, tail, self.value*o.value)
    __rmul__ = __mul__

    def inverse(self):
        assert self.c[0] != 0
        c = [1/self.c[0]]
        for k in range(1,self.n):
            c.append(simp(-sum(self.c[i]*c[k-i] for i in range(1,k+1))/self.c[0]))
        product = self * Jet(c)
        return Jet(c, -product.tail/self.value, 1/self.value)

    def __truediv__(self, other):
        return self * self.lift(other).inverse()

    def __rtruediv__(self, other):
        return self.lift(other) * self.inverse()

    def __pow__(self, k):
        assert isinstance(k, int) and k >= 0
        out = Jet.const(1, self.n)
        for _ in range(k):
            out = out*self
        return out

    def truncate(self, n):
        if type(n) is not int or not 0 <= n <= self.n:
            raise ValueError('invalid truncation order')
        assert n <= self.n
        tail = sum(self.c[k]*s**(k-n) for k in range(n,self.n)) + s**(self.n-n)*self.tail
        return Jet(self.c[:n], tail, self.value)

    def divide_s(self, k):
        if type(k) is not int or not 0 <= k <= self.n:
            raise ValueError('division exceeds retained jet order')
        assert all(x == 0 for x in self.c[:k]), self.c[:k]
        return Jet(self.c[k:], self.tail)


def remainder(x, k):
    """R_k(x)=(-1)^k integral_0^1 t^(2k)/(1+x²t²) dt.

    R_k(x)=(-1)^k/(2k+1)+x² R_(k+1)(x). Since x(0)=0,
    its N-jet uses N/2 exact steps, with a retained analytic tail.
    """
    assert x.c[0] == 0 and x.n % 2 == 0
    power = Jet.const(1, x.n)
    out = Jet.const(0, x.n)
    for j in range(x.n//2):
        out += power*S.Rational((-1)**(k+j), 2*(k+j)+1)
        power *= x*x
    assert all(c == 0 for c in power.c)
    return Jet(out.c, out.tail + power.tail*REM(x.value,k+x.n//2),
               REM(x.value,k))


def aq(x):
    return 1 + x*x*remainder(x,1)


@lru_cache(maxsize=1)
def expressions():
    t = Jet([0,1,0,0])
    z = Jet([p,p*p,u,0])
    a = Jet([5*p/12,(43*p*p+1056)/144,v,0])
    b = Jet([-44+19*p*p/24,p*(295*p*p-14256)/216,w,0])
    A, R = 1+t*z, 2+t*a
    e = 6*a-2*z+t*b
    E, B = 2*e, 2*R+2*t*e
    Y, W, V = t*A, t*R, t*(R+t*e)
    K = 2*R**2-4+t**2*(R**4-4*R**2)+2*t**4*(R**2-R**4)+t**6*R**4
    U = (1-t**2)**2*(1+t**2*A**2)
    WW = (1+t**2*R**2)**2*(4+t**2*B**2)
    X = (3+t**2*R**2)*(2-t**2*R*B)
    Z = (1-t**2)*(1-t**2*A)
    L = (1+t**2*A**2)*(4+t**2*B**2)*K
    fn = z*(1-t**2)*(1-t**2*A)-p*A*(1+t**2)
    cn = (4*E*R-8*z+t*(E**2-4*z**2)+
          t**4*(-4*E*R+8*R**4*z)+
          t**5*(-E**2+8*E*R**3*z-8*E*R*z+4*R**4*z**2)+
          t**6*(2*E**2*R**2*z-2*E**2*z+4*E*R**3*z**2-4*E*R*z**2)+
          t**7*(E**2*R**2*z**2-E**2*z**2))
    an = p*L+(E-4*z)*U*WW+2*E*U*X-4*z*(4+t**2*B**2)*Z
    third = an-2*cn+16*fn+t*((4*a-(2*z+p)/3)*cn-S.Rational(8,3)*z*fn)
    polynomial = third.divide_s(2)
    hc = lambda x: (1-x*x)/(1+x*x)
    C = 2*z*(2+t*z)/((1+t*t)*(1-Y*Y))
    density = hc(t)/hc(Y)
    d4, d3 = 1+t*Y, 1+W*V
    q4, q3 = t*t*z/d4, t*t*e/d3
    inc4 = 2*z/d4*aq(q4)
    bar4 = 2*t*t*C*aq(t)+density*inc4
    inc42 = 2*z/d4*(t*t*z*z/(d4*d4)*remainder(q4,1)-A)
    inc32 = 2*e/d3*(t*t*e*e/(d3*d3)*remainder(q3,1)-R*(R+t*e))
    bar42 = 2*C*aq(t)+density*inc42+2*t*z*C
    bar32 = 2*C*R*aq(W)+density*inc32+2*t*e*C
    fd = 2*(1+t*t)**2*(1+Y*Y)
    sine_product = 4*A/((1+t*t)*(1+Y*Y))
    fc = -fd*sine_product*bar4
    area_d = 2*(1+t*t)**2*(1+W*W)**2*(1+Y*Y)*(1+V*V)
    pi_weight = 2*K/((1+t*t)**2*(1+W*W)**2)
    ac = area_d*(2*hc(t)**2*bar32-(1+hc(W))**2*bar42+4*z*pi_weight)
    full_third = polynomial+ac.truncate(2)+((4-2*z*t/3)*fc).truncate(2)
    full_fold = (4*fn+t*t*fc).truncate(2)
    gap = ((2-R**2+t*t*R**2)*z*(1-t*t*A)*(1+Y*Y)*(1+V*V)+
           4*z*(1-t*t*A)*A*(1+V*V)-
           4*e*(1-V*W)*A*(1-t*t)*(1+Y*Y))
    # These assertions check symbolic identities, never serve as proof oracles.
    normalized = [j.divide_s(2).tail for j in
                  [full_fold, cn.truncate(2), full_third, gap.truncate(2)]]
    guards = [t.value, 1-t.value, Y.value, 1-Y.value,
              W.value, 1-W.value, V.value, 1-V.value,
              (Y-t).value, (V-W).value, (1-Y*Y).value,
              d4.value, d3.value, (1-t*q4).value, (1-W*q3).value,
              ((1-t*t)*R*R-2).value, A.value,
              (2*A*(1+W*W)*(1-t*t)*(1+Y*Y)*(1+V*V)).value]
    names = ['fold','cosine','third','gap','density_cube'] + [
        's_pos','s_lt_one','y_pos','y_lt_one','w_pos','w_lt_one','v_pos','v_lt_one',
        'y_gt_s','v_gt_w','density_den','angle_den_four','angle_den_three',
        'atan_guard_four','atan_guard_three','height_order','A_pos','gap_den']
    return names, normalized + [C.value] + guards


class ExactPrinter(PythonCodePrinter):
    def _print_Rational(self, expr):
        return f'rat({expr.p}, {expr.q})'


def emit():
    names, values = expressions()
    replacements, reduced = S.cse(values, symbols=S.numbered_symbols('c'))
    printer = ExactPrinter({'user_functions': {'rem':'rem'}})
    lines = ['def evaluate(s, p, u, v, w):']
    for x,e in replacements:
        lines.append(f'    {x} = {printer.doprint(e)}')
    lines.append('    return ['+',\n            '.join(printer.doprint(e) for e in reduced)+']')
    return names, '\n'.join(lines)+'\n'


if __name__ == '__main__':
    import json
    from pathlib import Path
    names, code = emit()
    Path(__file__).with_name('expressions.py').write_text(code)
    Path(__file__).with_name('expression_names.json').write_text(json.dumps(names,indent=2)+'\n')
    print(json.dumps({'status':'GENERATED_NOT_PROVED','expressions':len(names),
                      'assignments':code.count('\n')-1,'bytes':len(code)}))
