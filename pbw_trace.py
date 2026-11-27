#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Interactive, step-by-step symbolic Diamond-Lemma trace.

Depends on pbw_formal_sums.py and pbw_178_types.py in the same directory.

Examples:
    python pbw_trace.py --interactive
    python pbw_trace.py --family 1 --parity-choice 1
    python pbw_trace.py --type dtt --rows 'a=b<c' --cols 'u<v=w' \
        --row-parity 001 --col-parity 011 --output trace.txt
    python pbw_trace.py --type ddt --rows 'b<a=c' --cols 'v<u=w' --all-parities --output all.txt
    python pbw_trace.py --list

A trace line indexed by a fresh h/j stands for the summand in its displayed
symbolic constrained sum. It is NOT a numerical evaluation of that sum. The
coefficient and the constraint are printed for every symbolic branch.

This is a trace of the already encoded relations in pbw_formal_sums.py;
it is not an independent verification of those relations or of confluence.
"""
from __future__ import annotations

import argparse
import io
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import pbw_formal_sums as E
import pbw_178_types as F


# Parse a full weak order into ranks in original-letter order, rejecting missing,
# duplicate, or invalid labels.
def parse_order(s: str, letters: str):
    """Parse e.g. 'b<a=c' into ranks by the letters' original positions."""
    cleaned=''.join(s.split())
    if not cleaned:
        raise ValueError('The index order cannot be empty')
    parts=[]
    token=''
    for ch in cleaned:
        if ch in '<=':
            if not token or len(token)!=1 or token not in letters:
                raise ValueError(f'Invalid index in {s!r}')
            parts.append((token,ch));token=''
        else:token+=ch
    if not token or len(token)!=1 or token not in letters:
        raise ValueError(f'Invalid final index in {s!r}')
    parts.append((token,None))
    names=[name for name,_ in parts]
    if set(names)!=set(letters) or len(names)!=3:
        raise ValueError(f'Use each of {letters!r} exactly once: got {s!r}')
    ranks={};rank=0
    for i,(name,sep) in enumerate(parts):
        ranks[name]=rank
        if sep=='<':rank+=1
    # Above increments at the previous separator. '=' means same rank.
    answer=tuple(ranks[x] for x in letters)
    if set(answer)!=set(range(max(answer)+1)):
        raise ValueError('Not a valid weak order')
    return answer


# Display a rank tuple as an ascending order/equality relation.
def order_string(ranks, letters):
    return F.order_text(ranks,letters)


# Validate three parity bits, equality consistency, and even-before-odd order; return the
# number of even classes.
def parse_parity(s: str, ranks, letters):
    """Input 3 digits in the order a,b,c (or u,v,w), not sorted order."""
    s=''.join(s.split())
    if len(s)!=3 or any(x not in '01' for x in s):
        raise ValueError(f'Parity must contain exactly three bits for {letters}, e.g. 001')
    byclass={}
    for idx,p in enumerate(s):
        r=ranks[idx]
        if r in byclass and byclass[r]!=int(p):
            raise ValueError('Equal indices must have the same parity')
        byclass[r]=int(p)
    pseq=[byclass[i] for i in range(max(ranks)+1)]
    if pseq!=sorted(pseq):
        raise ValueError('Parity must be nondecreasing along ascending indices (even before odd)')
    even=sum(p==0 for p in pseq)
    return even


# Render parity bits in original-label order from a rank tuple and an even-block cut.
def parity_string(ranks, even):
    return ''.join(str(int(x>=even)) for x in ranks)


# Create the original cubic word for kind and its row/column pattern pair.
def initial(kind, rpat, cpat):
    rows=E.OrderedContext.initial(rpat)
    cols=E.OrderedContext.initial(cpat)
    state=E.State(rows,cols,tuple((kind[i],i,i) for i in range(3)))
    return state


# Enumerate parity cuts for which both adjacent pairs in the original word are reducible.
def allowed_parities(kind, ranks, colranks):
    result=[]
    for er in F.parity_cuts(ranks):
        for ec in F.parity_cuts(colranks):
            st=initial(kind,(ranks,er),(colranks,ec))
            if st.reducible(*st.word[:2]) and st.reducible(*st.word[1:]):
                result.append((er,ec))
    return result


# Return the leftmost reducible position, or None when the word is already normal.
def loc(st):
    for i in range(len(st.word)-1):
        if st.reducible(*st.word[i:i+2]):
            return i
    return None


# Collect equivalent symbolic terms while retaining a representative State alongside each
# summed coefficient; no rewriting is performed here.
def combine(seq):
    """Combine structurally alpha-equivalent terms while keeping a representative State."""
    d={}
    for st,c in seq:
        if not c:continue
        key=st.key()
        if key in d:
            oldst,oldc=d[key]
            nc=oldc+c
            if nc:d[key]=(oldst,nc)
            else:del d[key]
        else:d[key]=(st,c)
    return d


# Perform one reduction per term, using a forced position for the first step or the
# leftmost reducible position thereafter; retain normal terms.
def advance(current, forced=None):
    out=[]
    for st,co in current.values():
        pos=forced if forced is not None else loc(st)
        if pos is None:
            out.append((st,co));continue
        if not st.reducible(*st.word[pos:pos+2]):
            raise ValueError('The requested first rewrite is not a valid reduction')
        for newst,delta in E.orient(st,pos):
            out.append((newst,co*delta))
    return combine(out)


# Format a Laurent coefficient with conventional signs and parentheses around multi-term
# polynomials.
def format_coeff(c):
    if not c:return '0'
    chunks=[]
    for power,coeff in sorted(c.terms.items(),reverse=True):
        prefix='q' if power==1 else ('q^'+str(power) if power!=0 else '')
        a=abs(coeff)
        mag=(str(a) if (a!=1 or not prefix) else '') + (('*' if a!=1 and prefix else '')+prefix)
        sign='-' if coeff<0 else '+'
        chunks.append((sign,mag))
    initial=chunks[0][1] if chunks[0][0]=='+' else '-'+chunks[0][1]
    for s,t in chunks[1:]:initial+=' '+s+' '+t
    return '('+initial+')' if len(chunks)>1 else initial


# Render a canonical term as a coefficient, explicit constrained sum when needed, and
# word; original labels are never summed.
def format_key(key, coeff):
    """Display a constrained symbolic term as an explicit finite sum."""
    rb, rp, cb, cp, word = key
    # Map labels 0..2 to original names and larger labels to h or j names in the
    # appropriate domain.
    def name(i, col=False):
        return ('uvw' if col else 'abc')[i] if i < 3 else ('j' if col else 'h') + str(i-2)
    bound = []
    constraints = []
    for blocks, parities, col in ((rb, rp, False), (cb, cp, True)):
        fresh = [i for block in blocks for i in block if i >= 3]
        bound.extend(name(i, col) for i in fresh)
        if fresh:
            constraints.append(' < '.join('='.join(name(i, col) for i in block) for block in blocks))
            constraints.extend('[' + name(i, col) + ']=' + str(p)
                               for block, p in zip(blocks, parities)
                               for i in block if i >= 3)
    letters = []
    for kind, a, b in word:
        letters.append(('t' if kind == 't' else 'D') + '_{' + name(a) + ',' + name(b, True) + '}')
    product = ' '.join(letters) or '1'
    summation = ('Σ_{' + ', '.join(bound) + ' : ' + '; '.join(constraints) + '} ') if bound else ''
    factor = '' if coeff == E.ONE else ('-' if coeff == -E.ONE else format_coeff(coeff) + ' ')
    return factor + summation + product


# Canonicalize the state for display and attach its coefficient.
def format_term(st, coeff):
    return format_key(st.key(), coeff)


# Display a collected linear combination; an optional limit truncates display only, not
# the stored expression.
def format_equation(cur, limit=0):
    if not cur:
        return '    0\n'
    items = sorted(cur.items(), key=lambda pair: repr(pair[0]))
    cut = items if not limit else items[:limit]
    lines = []
    for i, (_, (st, co)) in enumerate(cut):
        value = format_term(st, co)
        if i:
            value = ('- ' + value[1:]) if value.startswith('-') else '+ ' + value
        lines.append('    ' + value)
    if limit and len(items) > limit:
        lines.append(f'    ... {len(items)-limit} further terms omitted FROM DISPLAY ONLY')
    return '\n'.join(lines) + '\n'


# Record successive expressions along one first-pair choice and return the report plus its
# final coefficient dictionary; a round guard detects excessive expansion.
def trace_path(st,firstpos,heading,term_limit=0,maximum_rounds=30):
    lines=[]
    current=combine([(st,E.ONE)])
    lines.append(f'=== {heading} ===')
    lines.append('Round 0: original word')
    lines.append(format_equation(current,term_limit))
    current=advance(current,forced=firstpos)
    lines.append('Round 1: reduce original adjacent positions '+str(firstpos+1)+' & '+str(firstpos+2))
    lines.append(format_equation(current,term_limit))
    n=1
    while any(loc(qst) is not None for qst,_ in current.values()):
        if n>=maximum_rounds:
            raise RuntimeError('Exceeded maximum rounds; may indicate an incorrect ordering')
        current=advance(current)
        n+=1
        lines.append(f'Round {n}: reduce leftmost remaining reducible pair in every term')
        lines.append(format_equation(current,term_limit))
    lines.append(f'Normal form reached after {n} round(s); {len(current)} displayed symbolic terms in total.')
    return '\n'.join(lines),{key:co for key,(_,co) in current.items()}


# Validate one critical parity case, trace both paths, compare their final keys and
# coefficients, and return (report, passed).
def trace_one(kind,ranks,cols,er,ec,term_limit=0):
    st=initial(kind,(ranks,er),(cols,ec))
    if not(st.reducible(*st.word[:2]) and st.reducible(*st.word[1:])):
        raise ValueError('Not a critical overlap for this parity choice (possibly an even square)')
    out=[]
    out.append('SYMBOLIC DIAMOND-LEMMA TRACE')
    out.append(f'Kind: {kind} = '+('D_{a,u} t_{b,v} t_{c,w}' if kind=='dtt' else 'D_{a,u} D_{b,v} t_{c,w}'))
    out.append('Rows: '+order_string(ranks,'abc')+'; column indices: '+order_string(cols,'uvw'))
    out.append('Row parity [a][b][c] = '+parity_string(ranks,er))
    out.append('Column parity [u][v][w] = '+parity_string(cols,ec))
    out.append('q is formal. Fresh h_i and j_i are bound summation indices.')
    out.append('Σ_{h1, j1 : conditions} means a finite sum ONLY over the listed indices.')
    out.append('a,b,c,u,v,w are fixed original indices, never summation variables. [x] denotes parity.')
    out.append('Each sum binds its own dummy indices independently; all ranges lie in the original index domains.')
    out.append('No concrete k,l,r,s or upper summation bounds are substituted.\n')
    left_text,left=trace_path(st,0,'LEFT-FIRST PATH',term_limit)
    right_text,right=trace_path(st,1,'RIGHT-FIRST PATH',term_limit)
    out.extend((left_text,'',right_text,''))
    difference=dict(left)
    for key,value in right.items():E.add(difference,key,-value)
    if not difference:
        out.append('=== COMMON NORMAL FORM: LEFT = RIGHT ===')
        if not left:
            out.append('    0')
        for i, (key, val) in enumerate(sorted(left.items(), key=lambda z: repr(z[0]))):
            value = format_key(key, val)
            if i:
                value = ('- ' + value[1:]) if value.startswith('-') else '+ ' + value
            out.append('    ' + value)
        out.append('')
    out.append('=== CRITICAL PAIR DIFFERENCE: LEFT - RIGHT ===')
    if difference:
        items=sorted(difference.items(),key=lambda z:repr(z[0]))
        for key,val in items if not term_limit else items[:term_limit]:
            out.append('    '+format_key(key,val))
        if term_limit and len(items)>term_limit:
            out.append(f'    ... {len(items)-term_limit} further difference terms OMITTED FROM DISPLAY')
        out.append('RESULT: FAIL; nonzero terms = '+str(len(difference)))
    else:
        out.append('    0')
        out.append('RESULT: PASS, the overlap is resolved for this order and parity pattern.')
    return '\n'.join(out)+'\n',not difference


# Resolve a one-based global family number to its type and rank tuples; reject out-of-
# range numbers.
def choose_family(n):
    fam=list(F.families())
    if n<1 or n>len(fam):
        raise ValueError(f'Family index must be between 1 and {len(fam)}')
    x=fam[n-1]
    return x.kind,x.rows,x.cols


# Prompt for type, orders, and parity choice, then display or save the selected trace.
def interactive():
    print('PBW SYMBOLIC TRACE — interactive input')
    print('Type dtt for D_{a,u} t_{b,v} t_{c,w}, or ddt for D_{a,u} D_{b,v} t_{c,w}.')
    kind=input('type [dtt]: ').strip() or 'dtt'
    if kind not in ('dtt','ddt'):
        raise ValueError('Type must be dtt or ddt')
    sr=input('Row order, using a,b,c (e.g. a=b<c): ').strip()
    sc=input('Column order, using u,v,w (e.g. u<v=w): ').strip()
    rp=parse_order(sr,'abc'); cp=parse_order(sc,'uvw')
    if F.family_category(kind,rp,cp) is None:
        raise ValueError('This order is not a critical triple: no two initial adjacent reductions')
    options=allowed_parities(kind,rp,cp)
    for i,(er,ec) in enumerate(options,1):
        print(f'{i:2} row={parity_string(rp,er)} col={parity_string(cp,ec)}')
    n=int(input(f'Select parity branch [1..{len(options)}] (default 1): ').strip() or '1')
    er,ec=options[n-1]
    result,ok=trace_one(kind,rp,cp,er,ec)
    target=input('Save to filename (leave empty to print only): ').strip()
    if target:
        Path(target).write_text(result,encoding='utf-8')
        print('Saved',target,'; result:', 'PASS' if ok else 'FAIL')
    else:print(result)
    return 0 if ok else 1


# Create a new output directory and write every family/parity trace without truncation,
# plus a final summary. Return 1 if any case fails.
def export_all(output_dir=None):
    """Export complete traces for every global family and parity choice."""
    from datetime import datetime
    target = Path(output_dir or ('pbw_all_traces_' + datetime.now().strftime('%Y%m%d_%H%M%S_%f')))
    target.mkdir(parents=True, exist_ok=False)
    summary = ['PBW COMPLETE SYMBOLIC TRACE EXPORT',
               f'Homogeneous: {E.HOMOGENEOUS}',
               f'Bad constant control: {E.BAD_CONSTANT}',
               'All terms are displayed; all compatible critical parity cases are included.', '']
    total = failures = 0
    for number, fam in enumerate(F.families(), 1):
        choices = allowed_parities(fam.kind, fam.rows, fam.cols)
        parts = [f'FAMILY {number}: {fam.label()}\n']
        failed = 0
        for index, (er, ec) in enumerate(choices, 1):
            block, ok = trace_one(fam.kind, fam.rows, fam.cols, er, ec, term_limit=0)
            parts.append(f'######## PARITY CASE {index}/{len(choices)} ########\n' + block)
            failed += int(not ok)
        filename = f'family_{number:03d}_all_parities.txt'
        (target / filename).write_text('\n'.join(parts), encoding='utf-8')
        total += len(choices)
        failures += failed
        message = f'Family {number:03d}: {len(choices)} cases; {failed} failed; file: {filename}'
        print(message, flush=True)
        summary.append(message)
    summary.extend(['', f'Families: {number}', f'Parity cases: {total}',
                    f'Failed cases: {failures}', 'RESULT: ' + ('FAIL' if failures else 'PASS')])
    (target / 'summary.txt').write_text('\n'.join(summary) + '\n', encoding='utf-8')
    print(f'Export complete: {number} families; {total} cases; {failures} failed.')
    print('Output directory:', target)
    return int(bool(failures))


# Parse command-line options, configure the engine, and return an exit status.
def main(argv=None):
    ap=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--interactive',action='store_true',help='prompt for one case and its parity')
    ap.add_argument('--all-families', action='store_true', help='export all 178 families and all parity cases, without truncation')
    ap.add_argument('--output-dir', help='new directory for --all-families (default: timestamped directory)')
    ap.add_argument('--list',action='store_true',help='list all 178 family IDs')
    ap.add_argument('--family',type=int,help='1..178 from the classification; supplies type/rows/cols')
    ap.add_argument('--type',choices=['dtt','ddt'],help='kind of mixed critical triple')
    ap.add_argument('--rows',help='symbolic weak order e.g. a=b<c')
    ap.add_argument('--cols',help='symbolic weak order e.g. u<v=w')
    ap.add_argument('--row-parity',help='three 0/1 bits for a,b,c (such as 001)')
    ap.add_argument('--col-parity',help='three 0/1 bits for u,v,w (such as 011)')
    ap.add_argument('--parity-choice',type=int,help='1-based choice from valid parity patterns')
    ap.add_argument('--all-parities',action='store_true',help='produce traces for ALL compatible parity configurations')
    ap.add_argument('--show-parities',action='store_true',help='list valid internal parity cases')
    ap.add_argument('--homogeneous',action='store_true',help='use gr version (omit contraction constant)')
    ap.add_argument('--bad-constant',action='store_true',help='negative control: deliberately wrong scalar')
    ap.add_argument('--max-terms',type=int,default=0,help='display at most N terms per round (0=no limit)')
    ap.add_argument('--output',help='write full trace to UTF-8 text file')
    args=ap.parse_args(argv)
    E.HOMOGENEOUS=args.homogeneous
    E.BAD_CONSTANT=args.bad_constant
    if args.output_dir and not args.all_families:
        ap.error('--output-dir requires --all-families')
    if args.all_families:
        conflicting = (args.interactive, args.list, args.family is not None, args.type,
                       args.rows, args.cols, args.row_parity, args.col_parity,
                       args.parity_choice is not None, args.show_parities,
                       args.output, args.max_terms != 0)
        if any(conflicting):
            ap.error('--all-families cannot be combined with case selection, --output, or --max-terms')
        try:
            return export_all(args.output_dir)
        except (OSError, ValueError, E.HiddenSum) as exc:
            ap.error(str(exc))
    if args.list:
        lines = [f'{i:3d}: {fam.label()}' for i, fam in enumerate(F.families(), 1)]
        listing = '\n'.join(lines) + '\n'
        if args.output:
            try:
                Path(args.output).write_text(listing, encoding='utf-8')
            except OSError as exc:
                ap.error(str(exc))
            print(f'Wrote {len(lines)} families to {args.output}')
        else:
            print(listing, end='')
        return 0
    if args.interactive or (args.family is None and not args.rows and not args.cols):
        return interactive()
    try:
        if args.family is not None:
            kind,rp,cp=choose_family(args.family)
            if args.type and kind != args.type:
                raise ValueError(f'Family {args.family} is of type {kind}, not {args.type}')
        else:
            kind=args.type or 'dtt'
            rp=parse_order(args.rows,'abc')
            cp=parse_order(args.cols,'uvw')
            if F.family_category(kind,rp,cp) is None:
                raise ValueError('The chosen order does not produce a mixed critical overlap')
        options=allowed_parities(kind,rp,cp)
        if not options:raise ValueError('No compatible critical parity configurations')
        if args.show_parities:
            print('Available parity patterns for',kind,order_string(rp,'abc'),order_string(cp,'uvw'))
            for i,(er,ec) in enumerate(options,1):
                print(f'{i:2d}: [abc]={parity_string(rp,er)}; [uvw]={parity_string(cp,ec)}')
            if not args.all_parities and args.row_parity is None and args.col_parity is None and args.parity_choice is None:
                return 0
        if args.row_parity is not None or args.col_parity is not None:
            if args.row_parity is None or args.col_parity is None:
                raise ValueError('Provide BOTH --row-parity and --col-parity')
            er=parse_parity(args.row_parity,rp,'abc')
            ec=parse_parity(args.col_parity,cp,'uvw')
            if (er,ec) not in options:
                raise ValueError('This parity choice gives no critical overlap, e.g. an even square')
            choices=[(er,ec)]
        elif args.all_parities:
            choices=options
        else:
            i=args.parity_choice or 1
            if i<1 or i>len(options):
                raise ValueError(f'--parity-choice must be in 1..{len(options)}')
            choices=[options[i-1]]
        parts=[];good=True
        for j,(er,ec) in enumerate(choices,1):
            block,ok=trace_one(kind,rp,cp,er,ec,args.max_terms)
            parts.append(f'######## PARITY CASE {j}/{len(choices)} ########\n'+block)
            good=good and ok
        text='\n'.join(parts);ok=good;num=len(choices)
        if not args.all_parities and args.row_parity is None:
            text+=f'\nNote: this output covers ONE of {len(options)} allowed parity branches. Use --all-parities for all.\n'
        if args.output:
            target=Path(args.output)
            target.write_text(text,encoding='utf-8')
            print(f'Wrote {target}: {num} parity case(s);', 'PASS' if ok else 'FAIL')
        else:print(text)
        return 0 if ok else 1
    except (ValueError,E.HiddenSum) as exc:
        ap.error(str(exc))

if __name__=='__main__':
    sys.exit(main())
