#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Parameter-free symbolic-index Diamond-Lemma checker for the manuscript.

No k,l,r,s, and no substitution of indexed variables by numeric values.
An unevaluated sum over h>a is implemented as a fresh symbolic index h and a
partition into all equality/order/parity cases relative to currently named
indices.  Canonicalization of the free, surviving sum indices identifies
alpha-equivalent finite-sum terms.  In a cubic critical pair there are at
most two mixed swaps, so this procedure terminates finitely.

IMPORTANT: This uses the specific original paper rules encoded in
pbw_diamond.sage. The independent encoded relations must be checked against
any new manuscript revisions. No computer program can verify its own input.
"""
import argparse
import itertools
import sys
import time
from dataclasses import dataclass
from functools import lru_cache

# Exact coefficient ring Z[q,q^{-1}], no dependency beyond Python standard library.
# Exact element of Z[q,q^-1]. The terms attribute maps integer exponents to nonzero
# integer coefficients; an empty dictionary represents zero.
class Laurent:
    # terms is the sole instance attribute; all arithmetic constructs result objects rather than editing this dictionary in place.
    __slots__ = ('terms',)
    # Accept an integer, exponent-to-coefficient mapping, or Laurent object. Remove zero
    # coefficients from mappings; Laurent input shares its terms mapping.
    def __init__(self, terms=None):
        if isinstance(terms, Laurent):
            self.terms = terms.terms
        elif isinstance(terms, int):
            self.terms = {0:terms} if terms else {}
        else:
            self.terms = {int(k):int(v) for k,v in (terms or {}).items() if v}
    # Return the exact sum, combining equal powers and removing zero coefficients.
    def __add__(self, rhs):
        rhs = Laurent(rhs)
        d = dict(self.terms)
        for k,v in rhs.terms.items():
            d[k] = d.get(k,0) + v
            if not d[k]: del d[k]
        return Laurent(d)
    __radd__=__add__
    # Return a polynomial with every coefficient negated.
    def __neg__(self): return Laurent({k:-v for k,v in self.terms.items()})
    # Return self minus rhs using exact addition and negation.
    def __sub__(self, rhs): return self + (-Laurent(rhs))
    # Support subtraction when the left operand is an integer.
    def __rsub__(self,rhs): return Laurent(rhs)-self
    # Multiply by convolution: add exponents, multiply coefficients, and collect equal
    # powers.
    def __mul__(self,rhs):
        rhs = Laurent(rhs)
        d = {}
        for k,v in self.terms.items():
            for j,w in rhs.terms.items():
                d[k+j] = d.get(k+j,0)+v*w
        return Laurent(d)
    __rmul__=__mul__
    # Use repeated squaring for nonnegative powers; negative powers require a single
    # monomial with coefficient +1 or -1.
    def __pow__(self,n):
        if n<0:
            if len(self.terms)!=1:
                raise ValueError('negative power of nonsingle Laurent monomial')
            k,v = next(iter(self.terms.items()))
            if abs(v)!=1: raise ValueError('unit required')
            return Laurent({k*n:v**abs(n)})
        ans=Laurent(1)
        b=self
        while n:
            if n&1: ans=ans*b
            b=b*b
            n>>=1
        return ans
    # Compare exact exponent-to-coefficient dictionaries after converting the other
    # operand.
    def __eq__(self,rhs): return self.terms==Laurent(rhs).terms
    # Return whether the polynomial is nonzero.
    def __bool__(self): return bool(self.terms)
    # Render the stored Laurent coefficients for diagnostic output.
    def __repr__(self):
        if not self.terms: return '0'
        return ' + '.join(f'{v}*q^{k}' for k,v in sorted(self.terms.items(),reverse=True))
q = Laurent({1:1})
Q = q-q**(-1)
ONE, ZERO = Laurent(1), Laurent(0)
BACKEND = 'exact Z[q,q^-1] (pure Python, no substitution for q)'

# Return the Laurent constant (-1)^n from the parity of integer n.
def sign(n):
    return -ONE if n%2 else ONE

# Two deliberate negative/variant modes used by regression tests.
BAD_CONSTANT = False
HOMOGENEOUS = False


# Accumulate value under key in a sparse expression dictionary; delete the key if its
# coefficient becomes zero.
def add(out, key, value):
    if not value: return
    a=out.get(key,ZERO)+value
    if a:out[key]=a
    elif key in out:del out[key]


# Generate all rank tuples with consecutive ranks starting at zero; equal ranks denote
# equal original indices.
def weak_orders(n=3):
    for ranks in itertools.product(range(n),repeat=n):
        if set(ranks)==set(range(max(ranks)+1)):
            yield ranks


# Yield every three-index weak order with every even-before-odd parity cut.
def patterns():
    for ranks in weak_orders(3):
        for even in range(max(ranks)+2):
            yield ranks,even


# Store symbolic index constraints, not numerical index values. Separate instances
# describe row and column domains.
@dataclass(frozen=True)
class OrderedContext:
    """Weak total order of symbolic labels, with monotone even/odd cut.

    classes is tuple of equivalence classes, ascending. parity per class.
    Values 0,1,2 refer to initial symbols a,b,c (rows) or u,v,w (cols).
    Values >=3 are fresh bound symbolic summation indices.
    """
    # Ordered equality blocks of symbolic labels; the outer tuple encodes strict order.
    classes: tuple
    # One parity bit per equality block (0 even, 1 odd).
    parity: tuple
    # Next unused bound-symbol label; this is NOT a numerical summation bound.
    nextid: int = 3

    # Convert (ranks, even) into ordered equality classes; even is the number of initial
    # even classes.
    @staticmethod
    def initial(pattern):
        ranks, even=pattern
        m=max(ranks)+1
        blocks=tuple(tuple(i for i in range(3) if ranks[i]==j) for j in range(m))
        return OrderedContext(blocks,tuple(int(j>=even) for j in range(m)))

    # Return the position of the equality class containing label i; raise KeyError for an
    # unknown label.
    def rank(self,i):
        for j,c in enumerate(self.classes):
            if i in c:return j
        raise KeyError(i)

    # Read the parity of the equality class containing label i.
    def p(self,i):return self.parity[self.rank(i)]
    # Compare class positions, returning -1, 0, or 1; label numbers themselves do not
    # encode order.
    def cmp(self,a,b):
        r=self.rank(a)-self.rank(b)
        return (r>0)-(r<0)

    # Yield (context, label) branches covering h>a. Reuse a label for equality branches;
    # insert fresh labels into allowed gaps for strict branches.
    def fresh_gt(self, a):
        """Enumerate all logically possible choices of h>a.

        A fresh symbol denotes a *single* universally quantified index value;
        when h coincides with an already named value, use that class label.
        The other choices introduce h in an open interval with each allowed
        parity; the resulting bound-variable class is later alpha-renamed.
        """
        pos=self.rank(a)
        # New summation variable equals an already named value.
        for j in range(pos+1,len(self.classes)):
            yield self,self.classes[j][0]
        # Otherwise it lies strictly in one of the gaps after a.
        for j in range(pos+1,len(self.classes)+1):
            for p in (0,1):
                if j>0 and self.parity[j-1]>p:continue
                if j<len(self.classes) and p>self.parity[j]:continue
                blocks=self.classes[:j]+((self.nextid,),)+self.classes[j:]
                pars=self.parity[:j]+(p,)+self.parity[j:]
                yield OrderedContext(blocks,pars,self.nextid+1),self.nextid

    # Return canonical classes, their parities, and an old-to-new label map. Fix original
    # representatives, rename bound labels by occurrence, and reject disappearing bound
    # indices.
    def canonical(self,coordinates):
        # Original three labels are fixed and may coincide in classes.
        # Identify input symbols known equal in the current order pattern.
        seen={}
        for block in self.classes:
            originals=[i for i in block if i < 3]
            if originals:
                for i in originals:seen[i]=min(originals)
        nxt=3
        for i in coordinates:
            if i not in seen:
                seen[i]=nxt;nxt+=1
        hidden=[i for block in self.classes for i in block if i not in seen]
        if hidden:
            raise HiddenSum(f'Bound index(es) {hidden} disappeared; use real symbolic summation!')
        blocks=tuple(tuple(sorted(set(seen[i] for i in b))) for b in self.classes)
        return blocks,self.parity,seen


# Signal that an unfixed bound index disappeared and might require a summation-cardinality
# factor not supported by this engine.
class HiddenSum(RuntimeError):pass

# Represent one constrained noncommutative word. Fresh labels denote bound sum indices; a
# coefficient is stored separately in a (State, Laurent) pair.
@dataclass(frozen=True)
class State:
    # Independent row-domain context, including any row summation symbols.
    rows: OrderedContext
    # Independent column-domain context, including any column summation symbols.
    cols: OrderedContext
    # Ordered (kind, row label, column label) triples; () is the multiplicative identity.
    word: tuple

    # Look up the parity of a row label.
    def rowp(self,i):return self.rows.p(i)
    # Look up the parity of a column label.
    def colp(self,j):return self.cols.p(j)
    # Return the generator parity (row parity + column parity) modulo two; both generator
    # types use the same rule.
    def parity(self,kind,a,b):return (self.rowp(a)+self.colp(b))%2
    # Return q for an even row label and q^-1 for an odd row label.
    def qrow(self,i):return q**(1-2*self.rowp(i))
    # Return q for an even column label and q^-1 for an odd column label.
    def qcol(self,i):return q**(1-2*self.colp(i))
    # Build the sorting key: t precedes D, with reverse lexicographic t order and
    # lexicographic D order.
    def letter_order(self,x):
        kind,a,b=x
        ra,cb=self.rows.rank(a),self.cols.rank(b)
        return (0,-ra,-cb) if kind=='t' else (1,ra,cb)
    # Recognize mixed D*t pairs, odd squares, and same-type pairs that violate the chosen
    # order.
    def reducible(self,x,y):
        if x[0]=='d' and y[0]=='t':return True
        if x[0]!=y[0]:return False
        if self.rows.cmp(x[1],y[1])==0 and self.cols.cmp(x[2],y[2])==0:
            return self.parity(*x)==1
        return self.letter_order(x)>self.letter_order(y)
    # Return a hashable key containing canonical row/column classes, parities, and word,
    # so dummy renamings can be collected.
    def key(self):
        rs,rp,rm=self.rows.canonical([x[1] for x in self.word])
        cs,cp,cm=self.cols.canonical([x[2] for x in self.word])
        w=tuple((k,rm[a],cm[b]) for k,a,b in self.word)
        return rs,rp,cs,cp,w


# Rewrite the adjacent pair at idx in a reducible state; return a list of (new state,
# local coefficient) branches. An empty list represents zero.
def orient(s,idx):
    """One rewrite step as (new-state, coefficient) with symbolic sum branches."""
    x,y=s.word[idx:idx+2]
    kind,a,b=x
    _,c,d=y
    pa=s.parity(*x); pb=s.parity(*y)
    eps=sign(pa*pb)
    stem=s.word[:idx]; tail=s.word[idx+2:]

    # Append a nonzero local replacement, retaining the unchanged prefix and suffix of the
    # original word.
    def output(out, st, coeff, letters):
        if coeff:out.append((State(st.rows,st.cols,stem+tuple(letters)+tail),coeff))

    out=[]
    if kind=='t' and y[0]=='t':
        if s.rows.cmp(a,c)==0 and s.cols.cmp(b,d)==0:
            assert pa==1
            return out
        if s.rows.cmp(a,c)==0:
            output(out,s,eps*s.qrow(a),(y,x))
        elif s.cols.cmp(b,d)==0:
            output(out,s,eps*s.qcol(b),(y,x))
        elif s.cols.cmp(b,d)>0:
            output(out,s,eps,(y,x))
        else:
            output(out,s,eps,(y,x))
            gamma=sign(s.rowp(c)*(s.rowp(a)+s.colp(b))+s.rowp(a)*s.colp(b))
            extra=sign(s.parity('t',a,d)*s.parity('t',c,b))
            output(out,s,eps*gamma*extra*Q,(('t',c,b),('t',a,d)))
        return out

    if kind=='d' and y[0]=='d':
        if s.rows.cmp(a,c)==0 and s.cols.cmp(b,d)==0:
            assert pa==1
            return out
        if s.rows.cmp(a,c)==0:
            output(out,s,eps*s.qrow(a),(y,x))
        elif s.cols.cmp(b,d)==0:
            output(out,s,eps*s.qcol(b),(y,x))
        elif s.cols.cmp(b,d)<0:
            output(out,s,eps,(y,x))
        else:
            output(out,s,eps,(y,x))
            gamma=sign(s.rowp(a)*(s.rowp(c)+s.colp(d))+s.rowp(c)*s.colp(d))
            output(out,s,gamma*Q,(('d',c,b),('d',a,d)))
        return out

    assert kind=='d' and y[0]=='t'
    if s.rows.cmp(a,c)!=0 and s.cols.cmp(b,d)!=0:
        output(out,s,eps,(y,x))
    elif s.rows.cmp(a,c)==0 and s.cols.cmp(b,d)!=0:
        output(out,s,eps*s.qrow(a),(y,x))
        for rows,h in s.rows.fresh_gt(a):
            new=State(rows,s.cols,s.word)
            e=new.rowp(h)+(new.rowp(a)+new.colp(b))*(new.colp(d)+new.rowp(h))
            output(out,new,sign(e)*Q,(('t',h,d),('d',h,b)))
    elif s.rows.cmp(a,c)!=0 and s.cols.cmp(b,d)==0:
        output(out,s,eps*s.qcol(b),(y,x))
        for cols,j in s.cols.fresh_gt(b):
            new=State(s.rows,cols,s.word)
            e=new.colp(j)+(new.rowp(c)+new.colp(b))*(new.rowp(a)+new.colp(j))
            output(out,new,sign(e)*Q,(('t',c,j),('d',a,j)))
    else:
        if not HOMOGENEOUS:
            output(out,s,ONE if BAD_CONSTANT else sign(s.rowp(a)+s.colp(b)+s.rowp(a)*s.colp(b)),())
        output(out,s,sign(s.rowp(a)+s.colp(b))*s.qrow(a)*s.qcol(b),(y,x))
        for cols,j in s.cols.fresh_gt(b):
            new=State(s.rows,cols,s.word)
            e=new.colp(j)+(new.rowp(a)+new.colp(b))*(new.rowp(a)+new.colp(j))
            output(out,new,Q*new.qrow(a)*sign(e),(('t',a,j),('d',a,j)))
        for rows,h in s.rows.fresh_gt(a):
            new=State(rows,s.cols,s.word)
            e=new.rowp(h)+(new.rowp(a)+new.colp(b))*(new.colp(b)+new.rowp(h))
            output(out,new,Q*new.qcol(b)*sign(e),(('t',h,b),('d',h,b)))
        for rows,h in s.rows.fresh_gt(a):
            for cols,j in s.cols.fresh_gt(b):
                new=State(rows,cols,s.word)
                e=new.rowp(h)+new.colp(j)+(new.rowp(a)+new.colp(j))*(new.colp(b)+new.rowp(h))
                output(out,new,Q**2*sign(e),(('t',h,j),('d',h,j)))
    return out


# Recursively expand the leftmost reducible pair, multiplying local coefficients; yield
# terminal state/coefficient pairs before collection.
def normal_terms(state, coefficient=ONE):
    """Expand completely, always reducing the leftmost reducible pair."""
    for idx in range(len(state.word)-1):
        if state.reducible(*state.word[idx:idx+2]):
            for st,c in orient(state,idx):
                yield from normal_terms(st,coefficient*c)
            return
    if coefficient:
        yield state,coefficient


# Normalize a linear combination of (state, coefficient) pairs and collect its canonical
# keys into a sparse coefficient dictionary.
def normal_linear(start):
    out={}
    for st,c in start:
        for s,co in normal_terms(st,c):
            add(out,s.key(),co)
    return out


# Render a word using fixed original names and generated bound-index names; the empty word
# prints as 1.
def word_string(w):
    rows=['a','b','c']; cols=['u','v','w']
    for i in range(3,20):rows.append(f'h{i-2}');cols.append(f'j{i-2}')
    return ' '.join(f'{k}_{{{rows[a]},{cols[b]}}}' for k,a,b in w) or '1'


# Return None for a noncritical input, otherwise return the difference of the two computed
# normal forms; an empty dictionary means agreement.
def case(rowpat,colpat,kind,verbose=False):
    r=OrderedContext.initial(rowpat); c=OrderedContext.initial(colpat)
    s=State(r,c,tuple((kind[j],j,j) for j in range(3)))
    if not(s.reducible(*s.word[:2]) and s.reducible(*s.word[1:])):
        return None
    lhs=normal_linear(orient(s,0))
    rhs=normal_linear(orient(s,1))
    difference=dict(lhs)
    for key,v in rhs.items():add(difference,key,-v)
    if verbose:
        print('Input',word_string(s.word),'row=',rowpat,'column=',colpat)
        print('left terms',len(lhs),'right terms',len(rhs))
        print('difference',difference)
    return difference



# Render a canonical key with explicit order/parity annotations for diagnostic reports.
def pretty_key(key):
    """Human-readable normal form with formal order and parity conditions."""
    rb,rp,cb,cp,word=key
    row_names=['a','b','c']+[f'h{i}' for i in range(1,20)]
    col_names=['u','v','w']+[f'j{i}' for i in range(1,20)]
    # Format ordered equality classes and their parity annotations for one index domain.
    def constraints(blocks,ps,names):
        return ' < '.join('='.join(names[j] for j in b)+'('+str(p)+')'
                          for b,p in zip(blocks,ps))
    normal=' '.join((('t' if kind=='t' else 'D')+'_{'+row_names[a]+','+col_names[b]+'}')
                    for kind,a,b in word) or '1'
    return normal+'  [row: '+constraints(rb,rp,row_names)+'; col: '+constraints(cb,cp,col_names)+']'


# Parse command-line options, configure the engine, and return an exit status.
def main():
    ap=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument('--quick',action='store_true',help='small diagnostic set of order types')
    ap.add_argument('--bad-constant',action='store_true',help='negative regression test: replace signed constant by +1')
    ap.add_argument('--homogeneous',action='store_true',help='omit contraction constant (gr algebra)')
    ap.add_argument('--all',action='store_true',help='all 44x44 symbolic initial row/column patterns')
    ap.add_argument('--types',default='dtt,ddt',help='comma-separated critical types')
    ap.add_argument('--max-fails',type=int,default=3)
    ap.add_argument('--progress',type=int,default=100)
    args=ap.parse_args()
    global BAD_CONSTANT, HOMOGENEOUS
    BAD_CONSTANT=args.bad_constant
    HOMOGENEOUS=args.homogeneous
    pats=list(patterns())
    if args.quick:
        # first 12 plus hand-picked three-distinct orders, including odd cuts
        inds=sorted(set(list(range(12))+[17,18,20,23,27,31,36,40,43]))
        pats=[pats[i] for i in inds]
    kinds=args.types.split(',')
    assert all(x in ('dtt','ddt','ttt','ddd') for x in kinds)
    n=0; checked=0; fails=[];t0=time.monotonic()
    print('Exact coefficient backend:',BACKEND,flush=True)
    print('Symbolic input row/column patterns:',len(pats),'x',len(pats),flush=True)
    for rp in pats:
        for cp in pats:
            n+=1
            for kind in kinds:
                res=case(rp,cp,kind)
                if res is None:continue
                checked+=1
                if res:
                    fails.append((rp,cp,kind,res))
                    print('FAIL row',rp,'col',cp,'kind',kind,'terms=',len(res),flush=True)
                    for key,coef in list(res.items())[:6]:print(' ',coef,key)
                    if len(fails)>=args.max_fails:
                        print('FAILED',checked,'critical pairs');return 1
            if args.progress and n%args.progress==0:
                print(f'... {n} initial symbolic types; {checked} critical triples; {time.monotonic()-t0:.1f}s',flush=True)
    print('RESULT:', 'PASS' if not fails else 'FAIL','; order-type pairs:',n,'; critical triples:',checked,'; seconds:',round(time.monotonic()-t0,2),flush=True)
    return int(bool(fails))

if __name__=='__main__':sys.exit(main())
