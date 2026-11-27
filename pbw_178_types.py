#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Diamond-Lemma check grouped into 178 UNCOLORED mixed-overlap families.

Input relations, formal constrained sums, exact Z[q,q^-1] arithmetic, and
normalization are imported UNCHANGED from pbw_formal_sums.py.  The new
classifier groups the original 1936 colored critical instances into 89
order-only types for DTT and 89 for DDT.

IMPORTANT: parity cannot be discarded: inside each of the 178 families,
all parity cuts compatible with the even-before-odd indexing convention
are still checked. In total this runs 1936 exact parity subcases.

Run: python3 pbw_178_types.py --all
     python3 pbw_178_types.py --list
     python3 pbw_178_types.py --type dtt --show 1
     python3 pbw_178_types.py --compare-original
     python3 pbw_178_types.py --bad-constant  (expected failure)
"""
from __future__ import annotations
import argparse
import collections
from dataclasses import dataclass
import sys
import time
import pbw_formal_sums as engine


# Describe one parity-unassigned mixed overlap family. Parity choices are enumerated
# separately before normalization.
@dataclass(frozen=True)
class Family:
    # Generator pattern: dtt or ddt.
    kind: str              # dtt or ddt
    # Ranks of a,b,c in their original naming order, without parity data.
    rows: tuple[int, int, int]  # ranks of a,b,c (equal ranks mean equal indices)
    # Ranks of u,v,w in their original naming order, without parity data.
    cols: tuple[int, int, int]  # ranks of u,v,w
    # Internal grouping used for count validation and odd-square guards, not printed in family labels.
    category: str

    # Identify a square family whose criticality still depends on the generator being odd.
    @property
    def is_square(self):
        return self.category == 'odd-square'

    # Format the overlap type and full row/column orders without exposing the internal
    # category label.
    def label(self):
        return '%s | rows %s | cols %s' % (
            self.kind, order_text(self.rows, 'abc'),
            order_text(self.cols, 'uvw'))


# Convert ranks in original-label order into an ascending equality/order string.
def order_text(ranks, letters):
    return '<'.join('='.join(letters[i] for i,x in enumerate(ranks) if x==j)
                    for j in range(max(ranks)+1))


# Identify the pure adjacent pair that requires reduction, returning an internal category
# or None.
def family_category(kind, r, c):
    """Return subclass label if a degree-3 *uncolored* critical family exists.

    For DTT, D T is always reducible. The pair T_B T_C is reducible iff
      (b,v) <lex (c,w), or B=C and t_B is odd (the square rule).
    For DDT, D_B T is always reducible. The pair D_A D_B is reducible iff
      (a,u) >lex (b,v), or A=B and d_A is odd (the square rule).
    Oddness in the square case is a GUARD and is decided later by parity cuts.
    """
    if kind == 'dtt':
        if r[1] < r[2]:
            if c[1] < c[2]: return 'row-strict-col-<'
            if c[1] > c[2]: return 'row-strict-col->'
            return 'row-strict-col-='
        if r[1] == r[2]:
            if c[1] < c[2]: return 'row-=-col-strict'
            if c[1] == c[2]: return 'odd-square'
        return None
    if kind == 'ddt':
        if r[0] > r[1]:
            if c[0] > c[1]: return 'row-strict-col->'
            if c[0] < c[1]: return 'row-strict-col-<' 
            return 'row-strict-col-='
        if r[0] == r[1]:
            if c[0] > c[1]: return 'row-=-col-strict'
            if c[0] == c[1]: return 'odd-square'
        return None
    raise ValueError('Unknown mixed-overlap kind: '+str(kind))


# Yield applicable families in stable global order: DTT first, then DDT by default.
def families(kinds=('dtt','ddt')):
    orders = tuple(engine.weak_orders(3))  # 13 total preorders, WITHOUT parity
    assert len(orders)==13
    for kind in kinds:
        for r in orders:
            for c in orders:
                category=family_category(kind,r,c)
                if category is not None:
                    yield Family(kind,r,c,category)


# Yield possible counts of initial even equality classes, including all-odd and all-even
# assignments.
def parity_cuts(ranks):
    """Each j=0,...,m represents first j rank-classes even, remainder odd."""
    yield from range(max(ranks)+2)


# Assert the expected five category counts and 89 families per selected overlap type;
# return the category counter.
def validate_counts(kinds, fam):
    counts=collections.Counter((x.kind,x.category) for x in fam)
    for kind in kinds:
        expected={
            'row-strict-col-<':25,
            'row-strict-col->':25,
            'row-strict-col-=':15,
            'row-=-col-strict':15,
            'odd-square':9,
        }
        got={k[1]:v for k,v in counts.items() if k[0]==kind}
        assert got==expected, (kind,got,expected)
        assert sum(got.values())==89
    assert len(fam)==89*len(kinds)
    return counts


# Return attempted configurations, actual critical configurations, and nonzero
# differences. Stop early only when failures_limit is reached.
def run_family(fam, show=False, failures_limit=1):
    """Enumerate parity assignments *inside* an uncolored family.

    A non-square family is critical for every cut; a square family is
    critical precisely when row parity XOR column parity = 1.
    """
    attempted=0; applicable=0; failures=[]
    for er in parity_cuts(fam.rows):
        for ec in parity_cuts(fam.cols):
            attempted+=1
            row_pat=(fam.rows,er)
            col_pat=(fam.cols,ec)
            # The underlying symbolic normalization maintains all formal
            # bound indices, splitting sums by equalities, intervals, parity.
            difference=engine.case(row_pat,col_pat,fam.kind)
            if difference is None:
                assert fam.is_square, ('Unexpected noncritical strict family',fam,er,ec)
                continue
            applicable+=1
            if difference:
                failures.append((row_pat,col_pat,difference))
                if len(failures)>=failures_limit:
                    return attempted,applicable,failures
    if show:
        print('  parity cuts attempted:',attempted,
              '| actual critical pairs:',applicable)
    assert applicable>0, ('No odd parity exists for square family!',fam)
    return attempted,applicable,failures


# Compare sets of critical instances from the grouped and original enumerations; this
# validates coverage, not reduction results.
def compare_original():
    """Check the 178-class classifier against all 44x44 original patterns.

    This compares the SET of critical pattern/kind triples, independently of
    whether normal forms vanish. It guards against omitted cases.
    """
    old=set()
    patterns=list(engine.patterns())
    for r in patterns:
        for c in patterns:
            for kind in ('dtt','ddt'):
                st=engine.State(engine.OrderedContext.initial(r),
                                engine.OrderedContext.initial(c),
                                tuple((kind[i],i,i) for i in range(3)))
                if st.reducible(*st.word[:2]) and st.reducible(*st.word[1:]):
                    old.add((kind,r,c))
    new=set()
    for fam in families():
        for er in parity_cuts(fam.rows):
            for ec in parity_cuts(fam.cols):
                row_pat=(fam.rows,er); col_pat=(fam.cols,ec)
                if fam.is_square:
                    which=1 if fam.kind=='dtt' else 0
                    rp=int(er<=fam.rows[which])
                    cp=int(ec<=fam.cols[which])
                    if (rp+cp)%2==0:continue
                new.add((fam.kind,row_pat,col_pat))
    assert old==new, ('Classification not exhaustive',
                       len(old-new),len(new-old))
    print('COVERAGE PASS: original colored critical instances =',len(old),
          '; regrouped instances =',len(new),'; no omissions/duplicates')
    assert len(old)==1936


# Parse command-line options, configure the engine, and return an exit status.
def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--all',action='store_true',help='check all 178 uncolored families (default)')
    p.add_argument('--list',action='store_true',help='print the 178 family descriptions')
    p.add_argument('--type',choices=['dtt','ddt','both'],default='both')
    p.add_argument('--show',type=int,default=0,metavar='N',help='run only the Nth family (1-based in selected type)')
    p.add_argument('--compare-original',action='store_true',help='check regrouping covers all 1936 old colored overlaps')
    p.add_argument('--homogeneous',action='store_true',help='omit the contraction scalar in the mixed relation')
    p.add_argument('--bad-constant',action='store_true',help='replace contraction sign by +1 (expected FAIL)')
    p.add_argument('--progress',type=int,default=25,help='progress report every N families (0 disables)')
    p.add_argument('--max-fails',type=int,default=1)
    args=p.parse_args(argv)
    engine.HOMOGENEOUS=args.homogeneous
    engine.BAD_CONSTANT=args.bad_constant
    kinds=('dtt','ddt') if args.type=='both' else (args.type,)
    fam=list(families(kinds))
    counts=validate_counts(kinds,fam)
    if args.compare_original:
        compare_original()
    if args.list:
        for i,f in enumerate(fam,1):
            print('%3d  %s' %(i,f.label()))
        print('TOTAL:',len(fam),'uncolored order families')
        return 0
    if args.show:
        if not (1<=args.show<=len(fam)):p.error('--show out of range')
        fam=[fam[args.show-1]]
    print('Exact coefficient ring:',engine.BACKEND,flush=True)
    print('Parameters k,l,r,s: not fixed; all indexed sums handled formally',flush=True)
    print('Family count:',len(fam),'(89 DTT + 89 DDT if both)',flush=True)
    for kind in kinds:
        print('Type',kind,':',sum(f.kind==kind for f in fam),'families', flush=True)
    checked=0; attempted=0; failures=0
    by_kind=collections.Counter();t0=time.monotonic()
    for i,f in enumerate(fam,1):
        if args.show:print('Family:',f.label())
        nt,nc,bad=run_family(f,show=bool(args.show),failures_limit=args.max_fails)
        attempted+=nt;checked+=nc;by_kind[f.kind]+=nc
        if bad:
            failures+=len(bad)
            print('FAIL family',i,f.label(),flush=True)
            for row_pat,col_pat,delta in bad:
                print(' row',row_pat,'col',col_pat,'difference terms:',len(delta))
                for key,co in list(delta.items())[:5]:
                    print('  ',co,'*',engine.pretty_key(key))
            if failures>=args.max_fails:return 1
        if args.progress and i%args.progress==0:
            print('... %d families; %d applicable parity subcases; %.2fs'%(
                i,checked,time.monotonic()-t0),flush=True)
    if not args.show:
        assert checked == 968*len(kinds), ('Unexpected critical count',checked,kinds)
    print('RESULT:', 'PASS' if not failures else 'FAIL')
    print('Uncolored families processed:',len(fam))
    print('Parity-cut configurations considered:',attempted)
    print('Actual critical parity subcases:',checked)
    print('By type:',dict(by_kind))
    print('Time: %.2f sec'%(time.monotonic()-t0))
    return int(bool(failures))

if __name__=='__main__':sys.exit(main())
