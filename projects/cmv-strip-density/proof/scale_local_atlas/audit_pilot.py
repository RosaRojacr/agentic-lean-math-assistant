#!/usr/bin/env python3
"""Independent arithmetic/source spotchecks and reproducible generation audit.

These are deterministic diagnostics, NOT proofs of the full symbolic model.
The report's soundness derivation and pending Lean replay remain mandatory.
"""
from fractions import Fraction as Q
import argparse
import ast
import json
from pathlib import Path
from types import FunctionType

import check_atlas as c
import expressions
import model as producer


def contains(interval, lo, hi):
    assert Q(interval.lo,c.SCALE) <= lo <= hi <= Q(interval.hi,c.SCALE)


def arithmetic():
    intervals = [(Q(-5,3),Q(-1,7)),(Q(-1,3),Q(2,5)),(Q(0),Q(0)),
                 (Q(1,126334),Q(1,126333)),(Q(1,7),Q(5,3))]
    count = 0
    for a,b in intervals:
        x = c.I.bounds(a,b)
        for d,e in intervals:
            y = c.I.bounds(d,e)
            contains(x+y,a+d,b+e)
            products = [a*d,a*e,b*d,b*e]
            contains(x*y,min(products),max(products))
            contains(x-y,a-e,b-d)
            count += 3
        if a*b > 0:
            contains(1/x,1/b,1/a)
            count += 1
        for n in range(8):
            ends = [a**n,b**n]
            lo = 0 if n>0 and n%2==0 and a<=0<=b else min(ends)
            contains(x**n,lo,max(ends))
            count += 1
    return count


def remainders():
    count = 0
    for x in [Q(-1,2),Q(-1,3),Q(0),Q(1,126334),Q(2,5),Q(1,2)]:
        for k in [1,3]:
            value,derivative = c.rem_interval(c.I.point(x),k)
            n=80
            # Independent exact rational finite sum, not the checker's Horner loop.
            p=sum((Q((-1)**(k+j),2*(k+j)+1)*x**(2*j) for j in range(n)),Q(0))
            dp=sum((2*j*Q((-1)**(k+j),2*(k+j)+1)*x**(2*j-1)
                    for j in range(1,n)),Q(0))
            b=abs(x)
            error=b**(2*n)/Q(2*(k+n)+1)
            de=2*n*b**(2*n-1)/Q(2*(k+n)+1)+2*b**(2*n+1)/Q(2*(k+n)+3)
            contains(value,p-error,p+error)
            contains(derivative,dp-de,dp+de)
            count += 2
    return count


def arbitrary_r3(x,k):
    assert k==3
    return Q(3,7)+x/11


def direct_source(s,p,u,v,w):
    """Source residuals after exact principal-angle increment identities.

    The arbitrary R3 function tests algebraic identities, not atan accuracy.
    In contrast to the generated evaluator, this uses uncancelled source rows.
    """
    z=p+s*p*p+s*s*u
    a=5*p/12+s*(43*p*p+1056)/144+s*s*v
    b=-44+19*p*p/24+s*p*(295*p*p-14256)/216+s*s*w
    A,R=1+s*z,2+s*a
    e=6*a-2*z+s*b
    Y,W,V=s*A,s*R,s*(R+s*e)
    hc=lambda t:(1-t*t)/(1+t*t)
    hs=lambda t:2*t/(1+t*t)
    aq=lambda t:1-t*t/3+t**4/5+t**6*arbitrary_r3(t,3)
    rho=hc(s)/hc(Y)
    q4,q3=(Y-s)/(1+s*Y),(V-W)/(1+W*V)
    B4=2*(rho-1)*s*aq(s)+2*rho*q4*aq(q4)+p/2
    B3=2*(rho-1)*W*aq(W)+2*rho*q3*aq(q3)+p
    Fsrc=hc(s)*(hs(Y)-hs(s))-hs(s)*hs(Y)*B4
    Csrc=hc(W)*hc(Y)-hc(s)*hc(V)
    Asrc=2*hc(s)**2*(B3+(hc(W)+2)*(hs(V)-hs(W)))-(
        1+hc(W))**2*(B4+hc(s)*(hs(Y)-hs(s)))
    fd=2*(1+s*s)**2*(1+Y*Y)
    cd=2*(1+s*s)*(1-Y*Y)*(1+W*W)*(1+V*V)
    ad=2*(1+s*s)**2*(1+W*W)**2*(1+Y*Y)*(1+V*V)
    F=fd*Fsrc/s**2
    C=cd*Csrc/(s**3*hc(Y))
    area=ad*Asrc/s**2
    third=(area+(-2+s*(4*a-(2*z+p)/3))*C+(4-2*z*s/3)*F)/s**4
    h3,h4=(1+hc(W))/2,hc(s)
    source_gap=(h3-h4)/h4*(1/hs(s)-1/hs(Y))+h3/h4*(hs(Y)-hs(s))-(hs(V)-hs(W))
    gapden=2*A*(1+W*W)*(1-s*s)*(1+Y*Y)*(1+V*V)
    return [F/s**2,C/s**2,third,gapden*source_gap/s**4,(rho-1)/s**3]


def source_spotchecks():
    evaluate=FunctionType(expressions.evaluate.__code__,{'rat':Q,'rem':arbitrary_r3})
    count=0
    for s in [Q(1,126334),Q(1,1000),Q(1,25),Q(1,20)]:
        for p,u,v,w in [(Q(22,7),Q(53),Q(50),Q(-750)),
                        (Q(355,113),Q(69),Q(64),Q(-990))]:
            actual=evaluate(s,p,u,v,w)[:5]
            expected=direct_source(s,p,u,v,w)
            assert actual==expected, (s,[i for i in range(5) if actual[i]!=expected[i]])
            count += 5
    return count


def fail_closed():
    rejected=0
    for operation in [lambda:c.I.point(2)**Q(1,2),
                      lambda:c.D.constant(2)**Q(1,2),
                      lambda:c.I.bounds(-1,1).reciprocal(),
                      lambda:c.rem_interval(c.I.point(0),-1),
                      lambda:producer.Jet([0,0],1).divide_s(3)]:
        try:
            operation()
        except ValueError:
            rejected+=1
        else:
            raise AssertionError('invalid operation accepted')
    raw=json.loads(Path(__file__).with_name('pilot.json').read_text())
    cell=c.parse_cell(raw['bands'][0]['cells'][0])
    original=expressions.evaluate
    try:
        expressions.evaluate=lambda *args:original(*args)[:-1]
        try:
            c.check_cell(cell)
        except ValueError:
            rejected+=1
        else:
            raise AssertionError('missing guard accepted')
    finally:
        expressions.evaluate=original
    return rejected


def margin_summary(input_path, enclosure_path):
    inputs=json.loads(input_path.read_text())
    enclosures=json.loads(enclosure_path.read_text())
    assert inputs['schema']==enclosures.get('schema',c.PILOT_SCHEMA)
    metrics=[]
    for band_index,(band,data) in enumerate(zip(enclosures['bands'],inputs['bands'])):
        rows=band['cells']
        face_min={str(i):min(min(-Q(row['faces'][str(i)]['low'][1]),
                                Q(row['faces'][str(i)]['high'][0])) for row in rows)
                  for i in range(4)}
        normalized_rows=[
            (min(-Q(row['faces'][str(i)]['low'][1]),
                 Q(row['faces'][str(i)]['high'][0]))/Q(cell['radii'][i]),
             cell_index,i)
            for cell_index,(row,cell) in enumerate(zip(rows,data['cells']))
            for i in range(4)]
        normalized,weakest_cell,weakest_row=min(normalized_rows)
        guards={name:min(Q(row['guards'][name][0]) for row in rows) for name in c.NAMES[5:]}
        remainder_margins=[]
        for row in rows:
            g=row['guards']
            maxarg=max(Q(g['s_pos'][1]),Q(g['w_pos'][1]),
                       Q(g['y_gt_s'][1])/Q(g['angle_den_four'][0]),
                       Q(g['v_gt_w'][1])/Q(g['angle_den_three'][0]))
            remainder_margins.append(Q(1,2)-maxarg)
        assert min(remainder_margins)>0
        metrics.append({'band_index':band_index,'delta':band['delta'],
                        'scale':band.get('scale',data['cells'][0]['scale']),
                        'cells':len(rows),
                        'min_face_margin':face_min,
                        'min_normalized_face_margin':normalized,
                        'weakest_normalized_face':
                          {'cell_index':weakest_cell,'row':weakest_row,
                           'margin':normalized},
                        'min_guard_margin':guards,
                        'gap_upper':max(Q(row['gap'][1]) for row in rows),
                        'remainder_half_bound_margin_lower':min(remainder_margins),
                        'per_cell_remainder_half_bound_margins':remainder_margins})
    if inputs['schema']==c.PILOT_SCHEMA:
        assert metrics[0]['min_normalized_face_margin']>Q(27,100)
        assert metrics[1]['min_normalized_face_margin']>Q(79,1000)
        assert metrics[0]['gap_upper']<-18 and metrics[1]['gap_upper']<-30
    return metrics


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--certificate',type=Path,
                        default=Path(__file__).with_name('pilot.json'))
    parser.add_argument('--enclosures',type=Path,
                        default=Path(__file__).with_name('enclosures.json'))
    parser.add_argument('--metrics',type=Path,
                        default=Path(__file__).with_name('metrics.json'))
    args=parser.parse_args()
    names,code=producer.emit()
    assert names==c.NAMES
    assert code==Path(__file__).with_name('expressions.py').read_text()
    tree=ast.parse(code)
    assert all(not isinstance(n,ast.Constant) or type(n.value) is int for n in ast.walk(tree))
    result={'status':'DIAGNOSTICS_PASS_NOT_PROOF','generation_reproduced':True,
            'arithmetic_enclosures':arithmetic(),'remainder_enclosures':remainders(),
            'source_rational_spotchecks':source_spotchecks(),
            'invalid_operation_rejections':fail_closed(),
            'scope':'Finite arithmetic diagnostics and exact rational source spotchecks; not a universal identity or Lean proof.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    args.metrics.write_text(json.dumps(
        margin_summary(args.certificate,args.enclosures),default=str,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':
    main()
