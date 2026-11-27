#  Readme

This project aims to verify the resolvability of all overlap ambiguities arising in the proof of Proposition 3.11.

## Requirements and setup

This program requires Python 3.10 or later and uses only the Python standard library. No third-party packages, including SageMath or SymPy, are required. The program has been tested on Windows with Python 3.10.7.

Place `pbw_formal_sums.py`, `pbw_178_types.py`, `pbw_trace.py`, and `test_pbw_trace.py` in the same directory. 

## Main Results and Usage

We divide the overlap ambiguities into two main types, corresponding to the monomials $\partial_{a,u}t_{b,v}t_{c,w}$ and $\partial_{a,u}\partial_{b,v}t_{c,w}$.  Overlap ambiguities arsing from $\partial_{a,u}\partial_{b,v}t_{c,w}$ is further divided into 89 families according to the relative orders  of the row indices \(a,b,c\) and  the column indices \(u,v,w\) as follow:

|       | Conditions | numbers of possible relative orderings of (a,b,c,u,v,w) |
| ----- | ---------- | ------------------------------------------------------- |
|       | $a>b,u>v$  | $5\times 5=25$                                          |
|       | $a>b,u<v$  | $5\times 5=25$                                          |
|       | $a>b,u=v$  | $5\times3=15$                                           |
|       | $a=b,u>v$  | $3\times5=15$                                           |
|       | $a=b,u=v$  | $3\times3=9$                                            |
| Total |            | 89                                                      |

Similarly, Overlap ambiguities arsing from $\partial_{a,u}t_{b,v}t_{c,w}$ is  is also divided into 89 families.

 For computational purposes, each family is further subdivided according to the compatible parity assignments of \(a,b,c,u,v,w\).

The file `families_178.txt` lists all 178 mixed overlap families. Each entry specifies the family number, the overlap type (`dtt` or `ddt`), and the order and equality relations among the row indices \(a,b,c\) and the column indices \(u,v,w\). The list contains 89 DTT families and 89 DDT families; parity assignments are considered separately within each family.

We export both reduction paths for every case to the `all_symbolic_results` directory. 

Each file named `family_NNN_all_parities.txt` contains the complete computations for one overlap family, including all compatible critical parity assignments. For each assignment, the file specifies the original word, the index order relations, and the parities, followed by the step-by-step calculations along both reduction paths. It then displays the common normal form when the paths agree, the difference between the two final normal forms, and a `PASS` or `FAIL` result.

The file `summary.txt` records whether any unresolved overlap ambiguities occur in each family. All cases pass, with no unresolved overlap ambiguities.

To reproduce our results, run the following commands from the directory containing the program files.

### Listing the overlap ambiguities families

To display the complete list of 178 mixed overlap families, run:

    python -X utf8 pbw_trace.py --list

To save the list as a text file, run:

    python -X utf8 pbw_trace.py --list --output families_178.txt

The file `families_178.txt` will be created in the current directory.

Each entry gives the family number, the overlap type (`dtt` or `ddt`), and the order relations among the row and column indices. For example, family 25 appears as:

    25: dtt | rows a<b=c | cols u<v<w

It means that family 25 corresponds to the overlap ambiguity arising from
$\partial_{a,u}t_{b,v}t_{c,w}$  with  $a<b=c$, $u<v<w$.

The possible parity assignments for $(a,b,c)$ are

$[a]=[b]=[c]=0$ or $[a]=0,[b]=[c]=[1]$ or $[a]=[b]=[c]=1$.

The possible parity assignments for $(u,v,w)$ are
$[u]=[v]=[w]=0$ or $[u]=[v]=0,[w]=1$  or$[u]=0,[v]=[w]=1$ or $[u]=[v]=[w]=1$.

Therefore, family 25 is further divided into $3\times 4=12$ subcases
according to all possible parity assignments.

To display all compatible critical parity configurations for a particular family, run:

    python -X utf8 pbw_trace.py --family 25 --show-parities

### Exporting all symbolic calculations

To export the complete calculations for all 178 families, run:

    python -X utf8 pbw_trace.py --all-families

The program creates a timestamped directory containing 178 trace files, named `family_001_all_parities.txt` through `family_178_all_parities.txt`, together with a summary file named `summary.txt`. Every trace file includes all compatible critical parity configurations for its family, and no intermediate terms are omitted.

To specify the output directory explicitly, run:

    python -X utf8 pbw_trace.py --all-families --output-dir all_symbolic_results

For the supplied relations, the expected result is 178 families, 1936 critical parity cases, and zero failed cases. The summary should end with `RESULT: PASS`. 

### Verifying the classification and reductions

To check all mixed critical pairs and verify that the family classification covers the original enumeration, run:

    python -X utf8 pbw_178_types.py --all --compare-original --progress 0

The expected output includes  `RESULT: PASS`, with 178 families and 1936 actual critical parity cases.

## Replacing the Constant Term with 1

We tested replacing the constant term $(-1)^{[a]+[b]+[a][b]}$ in the inhomogeneous relation with $1$ and found that this modification produces unresolved overlap ambiguities. Thus,  the chosen constant term is essential for resolving the overlap ambiguities and establishing the PBW basis. The test results are provided in the `bad_constant_all_results` directory, where `summary.txt` records the families containing unresolved overlap ambiguities and the number of failing parity cases in each family.

To reproduce this test, run the following command from the
directory containing the program files:

    python -X utf8 pbw_trace.py --all-families --bad-constant --output-dir bad_constant_all_results

The output directory must not already exist. The program exports the
complete reduction traces for all 178 families and records the results
in `summary.txt`. The expected outcome is 14 failing parity cases across
12 families. 

## Implementation

The key to the implementation is  to represent the order relations among indices and their corresponding parities, and to implement symbolic summation. We define a class `OrderedContext` to store the order relations among indices and their parities.

```python
@dataclass(frozen=True)
class OrderedContext:
    classes: tuple
    parity: tuple
    nextid: int = 3
```

For example, the relations

$a=b<h<c$,  $[a]=[b]=[h]=0$, $[c]=1$.

can be represented as follows：

```python
rows = OrderedContext(
    classes=((0, 1), (3,), (2,)),
    parity=(0, 0, 1),
    nextid=4,
)
```

Here, the labels \(0,1,2\) represent \(a,b,c\), respectively, and \(3\) represents the new index \(h\). We then define a class `State` to represent a formal sum by recording the noncommutative word being summed and the summation indices together with their constraints.

```python
@dataclass(frozen=True)
class State:
    rows: OrderedContext
    cols: OrderedContext
    word: tuple
```

For example, the polynomial
$$
\sum_{a<h<c,[h]=0}t_{h,v}\partial_{h,u},
$$
can be represented as follows：

```python
from pbw_formal_sums import OrderedContext, State

# Row labels: 0=a, 1=b, 2=c, 3=h.
rows = OrderedContext(
    classes=((0, 1), (3,), (2,)),
    parity=(0, 0, 1),
    nextid=4,
)

# Column labels: 0=u, 1=v, 2=w.
cols = OrderedContext(
    classes=((0,), (1, 2)),
    parity=(0, 1),
    nextid=3,
)
#t_hvd_hu
state = State(
    rows=rows,
    cols=cols,
    word=(
        ('t', 3, 1),
        ('d', 3, 0),
    ),
)
```

Here, the labels $0,1,2$ represent the original indices, while labels greater than or equal to $3$ represent summation indices. The coefficients lie in $\mathbb{Z}[q,q^{-1}]$, and we define a class `Laurent` to represent Laurent polynomials in $q$:

```python
class Laurent:
    __slots__ = ('terms',)
```

We use a dictionary to store the coefficient of each power \(q^n\) in a Laurent polynomial. For example, $f=q^2-2+q^{-2}$ is represented by the following code:

```python
f = Laurent({2: 1, 0: -2, -2: 1})
```

For a more general expression, we use a list to store its individual terms. For example,$terms=c_1s_1+c_2s_2$ can be represented as

```python
c1 = Laurent({2: 3, 0: -1})  # 3q^2 - 1
c2 = Laurent({-1: 2})        # 2q^(-1)
terms = [(s1, c1), (s2, c2)]
```

