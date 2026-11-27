#!/usr/bin/env python3
"""Smoke and consistency checks for interactive symbolic traces."""
import pbw_trace as T
import pbw_formal_sums as E
import pbw_178_types as F


# Check input parsing, reject incompatible parities, and compare representative stepwise
# traces with the shared normalization engine.
def tests():
    assert T.parse_order('a=b<c','abc')==(0,0,1)
    assert T.parse_order('c<a=b','abc')==(1,1,0)
    assert T.parse_order('b<a<c','abc')==(1,0,2)
    assert T.parse_order('v<u=w','uvw')==(1,0,1)
    rows=T.parse_order('a=b<c','abc');cols=T.parse_order('u<v=w','uvw')
    assert T.parse_parity('001',rows,'abc')==1
    assert T.parse_parity('011',cols,'uvw')==1
    try:
        T.parse_parity('010',rows,'abc')
    except ValueError:pass
    else:raise AssertionError('Invalid equality parity accepted')
    text,ok=T.trace_one('dtt',rows,cols,1,1)
    assert ok and 'Round 3' in text and 'LEFT-FIRST PATH' in text and 'RIGHT-FIRST PATH' in text
    assert 'difference' in text.lower()
    for kind in ('dtt','ddt'):
        selected=list(F.families([kind]))
        for ix in [0,1,7,23,55,88]:
            fam=selected[ix]
            options=T.allowed_parities(kind,fam.rows,fam.cols)
            assert options
            for er,ec in options[:2]:
                trace,ok=T.trace_one(kind,fam.rows,fam.cols,er,ec)
                assert ok and 'RESULT: PASS' in trace
                assert E.case((fam.rows,er),(fam.cols,ec),kind)=={}
    print('PASS: symbolic trace parser, parity validation, 24 representative traces, engine comparison')

if __name__=='__main__':tests()
