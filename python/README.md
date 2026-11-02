# Approximation of the Riemann zeta function and non-trivial zeros

The python code contains: 
- numerical approximations of Hardy's Z-function, 
the real-valued phase shift of the Riemann zeta function;
- algorithms for finding zeros of the approximation along the critical line;
- algorithms for finding sequences of Gram points that satisfy the properties 
  needed to apply Turing's method;
- scripts which store data and generate corresponding Lean certificate files.

Built on [SageMath](https://www.sagemath.org/) for arbitrary-precision
arithmetic.

---

## Table of contents

- [Fundamental classes](#fundamental-classes)
- [Euler-Maclaurin approximation](#euler-maclaurin-approximation)
- [Riemann-Siegel approximation](#riemann-siegel-approximation)
- [Zero-finding algorithm](#zero-finding-algorithm)
- [Finding Gram points](#finding-gram-points)
- [Installation](#installation)
- [Usage](#usage)
- [Running the tests](#running-the-tests)
- [Directory structure](#directory-structure)
- [Global constants](#global-constants)
- [References](#references)

---

## Fundamental classes

We list the key abstract objects upon which the Python code rests.
- `Approximation` encodes the tuple `(value, error)` of an approximation to any 
   real number. It also includes a method `certified_sign` which returns the sign
   of the value when `|value| > margin * error` for some inflation factor `margin` 
   which is fixed repository wide.
- `ZApproximant` is the abstract class encoding an approximant of Hardy's Z-function, 
   of which specific approximants are implemented as child classes.
- `GramPoint` packages Gram indices and values, fixing the precision of gram points across 
   the Python code. 
- `SignedPoint` packages a float value with its sign, allowing alternative constructions 
   of the sign value, for example `certified_sign` described above. `SignedGramPoint` 
   is a child of `SignedPoint` packaging Gram indices, values, and methods for determining 
   when Gram's law holds. 
- `ZInterval` encodes all the necessary information needed to communicate approximant values,
   parameters, and metadata of an interval on the critical line.
- `ZeroSearch` holds a search configuration and methods to run the zero search algorithm 
   described in [Zero-finding algorithm](#zero-finding-algorithm).

## Euler-Maclaurin Approximation

### Euler-Maclaurin for `ζ(s)`

The Euler-Maclaurin formula is at once a method of analytic continuation of the 
Riemann zeta function and a method for approximating values. 
It consists of a partial summation, correction terms, summation of terms 
containing Bernoulli numbers, and a remainder term:

$$
  ζ(s)  =   \sum_{n=1}^{N - 1}  n^{-s}  +  \frac{N^{1-s}}{s-1}  +  \frac{1}{2 N^{s}}  +  \sum_{k=1}^{M}  T_k(s, N)  +  R_M(s, N)
$$

where the `k`-th Bernoulli correction term is

$$
  T_k(s, N) = \frac{B_{2k}}{(2k)!} (s)_{2k-1} N^{-s-2k+1}
$$

with $B_{2k}$ the Bernoulli numbers and $(s)_m = s(s+1)…(s+m−1)$ the rising
factorial. This maps into the Python code as follows:

| Term in the formula        | Function in `src/euler_maclaurin/zeta_values.py` |
| -------------------------- | -------------------------------- |
| $\sum_{n=1}^{N - 1}  n^{-s}$          | `partial_zeta(s, N)`             |
| $\frac{N^{1-s}}{s-1}$           | `integral_term(s, N)`            |
| $ \frac{1}{2 N^{s}}$                 | `correction_term(s, N)`          |
| $T_k(s, N)$               | `bernoulli_term(s, N, k)`        |
| $\sum_{k=1}^{M}  T_k(s, N)$    | `bernoulli_sum(s, N, M)`         |
| the whole identity         | `Z_euler_maclaurin(s, N, M)`  |

Here `N` is the **cutoff** (how many terms are summed directly) and `M` is the
**number of Bernoulli correction terms** retained.

### Choosing the cutoff `N`

The size of the Bernoulli terms is governed by the ratio $|s| / (2\pi N)$ and we have roughly that

$$
  |T_k(s, N)| \approx \left(\frac{|s|}{2\pi N}\right)^{2k} N^{1-\sigma},
$$

so the series is only useful once $N > |t| / 2\pi$. Below that the terms grow from the start;
above it each further Bernoulli term gains a factor of about $(|t| / 2\pi N)^2$, so a larger `N`
lets a small fixed `M` reach a given error.

`adaptive_cutoff(b, t)` in `src/euler_maclaurin/zeta_zeros.py` chooses

$$
  N(t) = \left\lceil b \left(\frac{t}{2\pi} + 50\right) \right\rceil,
$$

with inflation factor `b = 1.25` by default. The factor `b` keeps the ratio
$|t| / 2\pi N$ below $1/b$. The constant offset `50 * b` is an empirical floor with no derivation
behind it. Its point is to keep `N ≥ 63` even at small heights, where $t / 2\pi$ alone would give 
a cutoff of 1 or 2. 

### The error bound and optimal truncation

The Bernoulli sum is a series with the following behaviour at fixed `N`: 
as `M` grows the terms first shrink, reach a minimum, then diverge. So there is an optimal number of terms,
beyond which adding more makes the answer *worse*. The remainder after `M` terms
is bounded (Borwein, [§3](https://cr.yp.to/bib/2000/borwein.pdf)) by

$$
  |R_M(s, N)|  \leq  \left|\frac{s + 2M + 1}{Re(s) + 2M + 1}\right| |T_{M+1}(s, N)|
$$
(valid for $Re(s) > -2M-1)$ i.e. essentially the size of the first omitted term. 
This is `error_bound(s, N, M)`.

`Z_euler_maclaurin` returns an `Approximation` which tracks the value and error `|R_M(s, N)|` 
for every input. There are two methods for choosing the value of `M`:

- **Fixed `M`**: pass `M` explicitly; uses exactly that many terms.
- **Automatic (`M=None`)**: `bernoulli_sum` keeps adding terms until the next
  term stops shrinking ($|T_{k+1}| ≥ |T_k|$), thus picking the optimal truncation point 
  automatically. 

In general we prefer a fixed `M` because, as long as the error is not too large, the 
certification in Lean will pass. Moreover, optimal `M` means more Bernoulli terms, 
which will unnecessarily inflate both Python and Lean's kernel computation time.

### Applying Euler-Maclaurin

Compared to the Riemann-Siegel approximator below, Euler-Maclaurin is heavier computationally
and it requires various parameter choices. However, Riemann-Siegel is only effective for large 
enough heights, hence we apply Euler-Maclaurin to the range `(0, 149.5)` along the critical line.
Found zeros are stored alongside parameter choices for each, ready for communication to the 
Lean certifier.

---

## Riemann-Siegel approximation 

The Riemann-Siegel formula [[Edwards 1974]](#references) approximates Hardy's $Z$ directly,
with a sum of only about $\sqrt{t/2\pi}$ terms rather than the $O(t)$ that Euler-Maclaurin
needs. Writing $\tau = t / 2\pi$, $N = \lfloor \sqrt{\tau} \rfloor$ and $p = \sqrt{\tau} - N$ for
the fractional part, the first-order formula is

$$
  Z(t) = 2 \sum_{n=1}^{N} \frac{\cos(\theta(t) - t \log n)}{\sqrt{n}}
         + (-1)^{N-1} \tau^{-1/4} \left( C_0(p) + C_1(p) \tau^{-1/2} \right) + R(t)
$$

with correction terms

$$
  C_0(p) = \frac{\cos\left(2\pi(p^2 - p - \frac{1}{16})\right)}{\cos(2\pi p)},
  \qquad
  C_1(p) = -\frac{C_0'''(p)}{96 \pi^2},
$$

both of which have removable singularities at $p = 1/4, 3/4$. The remainder is bounded by

$$
  |R(t)| \leq \frac{25}{4} \tau^{-5/4} + \frac{1}{32} \tau^{-15/4} \qquad (t \geq 32\pi),
$$

a bound proved in Lean (`hardyZErrorBoundRS`, `Zeta/RiemannSiegel/`). This maps into the
Python code as follows:

| Term in the formula        | Function in `src/riemann_siegel/zeta_zeros.py` |
| -------------------------- | ---------------------------------------------- |
| the main sum               | `Z_RS_main_sum(t)`                             |
| $C_0(p)$                   | `Z_RS_correction(t)`                           |
| $C_1(p)$                   | `Z_RS_C1(t)`                                   |
| the bound on $\|R(t)\|$    | `Z_RS_error_bound(t)`                          |
| the whole formula          | `Z_riemann_siegel(t)`                          |

### Applying Riemann-Siegel

Unlike Euler-Maclaurin there are no parameters to choose: $N$ is fixed by the height, and
$\theta$ is evaluated by the Stirling series with a fixed number of terms (`RS_THETA_CUTOFF`,
`RS_THETA_BERNOULLI`). So the store records only the interval endpoints, and Lean recomputes $N$
at each one. The approximant refuses heights below `RS_MIN_HEIGHT` (just above $32\pi$, where the
bound starts to hold); in practice it takes over from Euler-Maclaurin at height $149.5$.

---

## Zero-finding algorithm

To find non-trivial zeros, one considers the phase-shift of the zeta function to make 
it real valued, enabling one to find zeros via IVT and sign changes. Specifically, 
we work with the **Hardy `Z`-function** and approximants thereof:

$$
  Z(t) = e^{iθ(t)}ζ\left(\frac{1}{2} + i·t\right)
$$

where $θ(t) = \arg Γ\left(\frac{1}{4} + \frac{it}{2}\right) - \frac{t}{2}\log π$ is the
Riemann-Siegel theta function [[Edwards 1974]](#references).
This is a $\mathbb{R} \to\mathbb{R}$ function which has the same zeros as $\zeta$ on the
critical line. It is approximated directly by the Riemann-Siegel approximant, or 
by combining Euler-Maclaurin expansions of $\log\Gamma$ and $\zeta$. 

The zero search algorithm is found in `src/search.py`. A naive approach to finding zeros 
along the critical line `(0, T)` is to carve up the line into a fine-enough grid and 
look for sign changes along this grid. Fine-enough can be chosen by a heuristic using 
the density of the zeros given by the Riemann-von Mangoldt formula, which is
about $\frac{1}{2\pi}\log\frac{t}{2\pi}$ zeros per unit length at height $t$ [[Edwards 1974]](#references). Note that the density increases as the height increases,
so this method becomes unnecessarily expensive as one goes up the line. 

Instead, one can take advantage of Gram's law: so-called Gram points often 
bound a single zero of $Z$. Such points are the monotonically increasing sequence $g_n$ such 
that $\theta(g_n) = n\pi$ [[Gram 1903]](#references). These form a naturally adaptive grid of
the critical line. Thus a computational improvement to the naive approach is to take a grid of Gram points. 


However Gram's law quickly fails at height $282$ [[Hutchinson 1925]](#references).
To resolve this, there is a higher level rule, Rosser's rule, involving so-called Rosser blocks. 
We say that a Gram point $g_n$ is called *good* when the expected number of zeros, $n + 1$,
lie below it, and *bad* otherwise. This can be determined by the check $(-1)^n Z(g_n) > 0$.
A Rosser block is a sequence of Gram intervals where Gram's law fails for the first interval
(either no zero or more than one zero), but the defect in expected zeros rebalances 
some $k$ intervals later. For example 

```
                   Gram's law holds                         Rosser block, k = 3
zeros                ×           ×                           ×             ×   ×
           ────┼───────────┼───────────┼──────────────┼──────────────┼──────────────┼────
            g_{n-2}     g_{n-1}       g_n          g_{n+1}        g_{n+2}        g_{n+3}
sign Z         +           -           +              +              -              -
             good        good        good            bad            bad           good
                                       └────────────────────────────────────────────┘
                  1 zero per interval               0 + 1 + 2 = 3 zeros
```

> **Terminology.** In the literature a Rosser block is called a *Gram block*
> [[Rosser, Yohe, Schoenfeld 1969]](#references), [[Brent 1979]](#references),
> [[Brent et al. 1982]](#references). We say *Rosser block* to avoid a clash with the Gram block
> of Turing's method (`src/gram.py`).

Therefore while Gram intervals may quickly fail to bound a single zero, Rosser's rule
states that Rosser blocks of length $k$ contain $k$ zeros
[[Rosser, Yohe, Schoenfeld 1969]](#references). 
Unlike Gram's law, Rosser's rule holds until large heights, failing for the first time 
at around $t = 6,800,000$ [[Brent 1979]](#references). 

The implemented algorithm is essentially built on Rosser's rule:
- first search Gram points for sign changes;
- if a failure occurs at an interval bounded by Gram points, track along the next intervals 
  until it is rectified and extract a Rosser block
    - carve up the Rosser block dyadically until we find $k$ zeros;
- continue

Of course Rosser's rule also fails eventually [[Lehman 1970]](#references). At this point we go a step above, 
and collect a consecutive run of Rosser blocks and Gram intervals growing out centrally from 
the failing Rosser block until the deficit is restored. Specifically:
- if a Rosser block fails, extend the window to include the neighbouring block or Gram interval on the right and search again;
- if this fails, extend again over the neighbouring block or Gram interval on the left and search again;
- repeat until the window holds as many zeros as there are Gram intervals.

Finally, once the initial set of zeros are found, an optional bisection search routine
occurs which helps to improve the precision.
Error bounds are checked at every level to ensure that bisection search on the approximant 
zero does not lose track of the true zero.
Conversely, an optional widening routine reduces precision maximally by interpolating 
the found zero intervals to create a tiling of the critical line.
The latter is actually our preference as it helps to speed up Lean certification.

--- 

## Finding Gram points 

We briefly describe Turing's method [[Turing 1953]](#references) for pinning down the total number of zeros 
in the critical strip up to a fixed height.
Let $g_m$ be a Gram point somewhere above the desired search range ($g_m > T$). 
Let $N(T)$ be the number of zeros of the Riemann zeta function
in the rectangle $\{\sigma + it\mid 0 < \sigma < 1, 0 < t < T\}$, counted with multiplicity.
The argument principle (applied to $\zeta$, or rather $\xi$, around this rectangle) gives
$N(T) = \theta(T)/\pi + 1 + S(T)$ where $S(T) = \frac{1}{\pi}\arg\zeta\left(\frac{1}{2} + iT\right)$,
the argument taken by continuous variation along the segments from $2$ to $2 + iT$ to
$\frac{1}{2} + iT$, and $T$ is not the height of a zero of $\zeta$.
Thus by definition $N(g_m) = m + 1 + S(g_m)$. Since all but $S(g_m)$ are integers, it suffices 
to bound $S(g_m) < 1$ to obtain $N(g_m) \leq m + 1$. 
Supposing further that we have found $m + 1$ zeros in $\{1/2 + it | 0 < t < g_m\}$, then 
we get $N(g_m) = m + 1$ exactly and therefore all zeros in the critical strip in this range lie 
on the critical line.

To bound $S(g_m)$, we can prove a bound of the form $|\int_{t_1}^{t_2} S(t)dt| \leq A + B\log (t_2/2\pi)$.
There are many proven variations of this with values of $A$ and $B$. For example $A = 2.3$ and $B = 0.128$ 
holds by [[Lehman 1970]](#references) whenever $168\pi \leq t_1 < t_2$.
Smaller values of $A$ and $B$ are generally preferable as they mean one needs to find fewer Gram 
points above $T$ in what follows. 
In our work we use $A = 5$ and $B = 0.128$ to avoid formalization burden. $A$ is set by `LEHMAN_CONST` 
in `src/config.py`.

Now suppose $k$ is large enough so that $5 + 0.128\log(g_{m + k} / 2\pi) < h/2$, 
where $h = g_{m + k} - g_m > 0$.
Suppose further that each Gram interval in the run $g_m$ to $g_{m + k}$ contains a zero.
By integrating $N(T) = \theta(T)/\pi + 1 + S(T)$ over the window $g_m$ to $g_{m + k}$ one gets 
$$ S(g_m) \leq \frac{1}{h}\int_{g_m}^{g_{m + k}} S(t)dt + \frac{1}{h}\int_{g_m}^{g_{m + k}} \{x(t)\}dt,$$
where $x(t) := (\theta(t) - \theta(g_m))/\pi$.
In this derivation we have used the fact that each Gram interval contains a zero to get 
a lower bound on $N(t) - N(g_m) \geq \lfloor x(t)\rfloor$. 
Now $\{x(t)\}$ is a convex sawtooth function, and thus has average $\leq 0.5$. 
Finally, using the weak Lehman bound we get 
$ S(g_m) \leq 0.5 + (5 + 0.128 \log(g_{m + k} / 2\pi))/h < 1$ by assumption.

Hence, to apply Turing's method, we also need to find a string of Gram points above $T$ such that 
- The width $h := g_{m + k} - g_m$ satisfies $5 + 0.128\log(g_{m + k} / 2\pi) < h/2$
- Every $[g_j, g_{j + 1}]$ contains a zero of the Hardy $Z$ approximant, for $m \leq j < m + k$.
- $g_m$ itself is good, $(-1)^m Z(g_m) > 0$, so that the zero search below it ends on a Rosser-block
  boundary and its count is exact.

This search is performed in `src/gram.py`. Gram points and zeros found between them are stored and 
communicated to the Lean certifier in `out/riemann_siegel/gram`.

---

## Installation

The only hard requirement is **SageMath 10.8** (which bundles Python 3.12, NumPy,
matplotlib, mpmath, etc.). Note that the Sage Python package is not supported 
on Windows. The conda environment is the simplest route (macOS and Linux).

### conda (recommended)

```bash
# from python/
conda env create -f environment.yml
conda activate zeta
```

The resulting environment has `sagelib` installed, so the plain `python`
interpreter inside it can `import sage.all` directly — no separate `sage`
launcher needed. It also installs this project in editable mode (`pip install -e .`), so the
modules in `src/` import from anywhere without setting `PYTHONPATH`. A new top-level module in
`src/` must be added to `py-modules` in `pyproject.toml`.

Edit `PROJECT_ROOT` within `python/src/config.py` to match the location of the repository 
on your local machine.

---

## Usage 

The `src/data_gen` subdirectory contains scripts which run search algorithms, catalogue 
resultant data, and communicate with the Lean certifier. 
All data is stored in `python/out/<method>` alongside `manifest.json` containing metadata on the 
search algorithms and the outputs of the search.

Scripts consist of the following storing scripts.
- `store_zeros.py`: run zero search and file zeros to `out`.
- `store_gram.py`: run the Gram-block search and file Gram points and bounded zeros to `out`.
- `store.py`: combine the two above to apply Turing's method; first it runs Gram-block search to 
   find a good `g_m >= end`, and then sets the upper limit of the zero-search to `g_m`

Note that `store_zeros.py` and `store.py` are parallelizable using the `--num-workers` flag
which will speed up zero search.


Scripts also consist of the following Lean generator scripts. These scripts read the data in 
`python/out` and generate corresponding Lean files in `Zeta` consisting of theorem statements 
and complete proofs certifying that the data is correct.
- `gen_zero_certificates.py`: emits Lean files with zero certificates across all found methods 
   in `out`. The Lean files are batched into modules of `BATCH_SIZE` zeros, or sized by height.
- `gen_gram_certificates.py`: emits a Lean file with certificates of the Gram points in the 
   block found by `store_gram.py` (or `store.py`), as well as the zeros bound in each Gram 
   interval.
- `gen_count_certificate.py`: generates Lean files containing assembly proofs, which count
   the number of zeros proved in the zero certificates and that the Gram block assembles 
   with it correctly to apply Turing's method.
- `gen_comparator.py`: generates the various Comparator setups described in `comparator/README.md`.

An end-to-end workflow consists of the following steps.

1. Compute zeros within `(1, 149.5)` using Euler-Maclaurin. 
   ```
   python python/src/data_gen/store_zeros.py euler_maclaurin 1 149.5 --M 20
   ```
   This computes the adaptive cutoff `N` as described in [Choosing the cutoff N](#choosing-the-cutoff-n).
   Typically we use a fixed truncation of `20` Bernoulli terms; intervals are widened into a tiling by default (`--no-widen` turns this off). 
   Bisection search can optionally be configured using `--bisection-depth 10` for up to 10 bisections.
   The default precision used here is `1000` (see global constant `PREC`).

2. Run the tail using the combined Gram-point and zero search with Riemann-Siegel.
   ```
   python python/src/data_gen/store.py riemann_siegel 149.5 10000 --num-workers -1
   ```
   The `--gram-cap` parameter (default `1000`) sets the maximum number of iterations for the
   Gram-search algorithm; the number needed grows with height (`500` is sufficient for `1e7`).
   We use the maximum number of workers to speed up this search with `--num-workers -1`.
   The option `--window-retries` can also be configured above `6e6`, which handles windowed searches 
   to overcome failures of Rosser's rule.
   `--halving-depth` (default `10`) sets how many times such a Rosser block's search is refined
   (its Gram intervals halved) before the block counts as failed.
   The default precision used here is `200` (less is required than for Euler-Maclaurin, see the 
   global constant `RS_PREC`).
   At the conclusion of the search, the script performs a count check on the zeros to verify that 
   the right number of zeros have been found (that is `m + 1`, where `m` is the index of the 
   smallest Gram point found in the Gram block).

3. The main theorems found in `Zeta/Main.lean` and `comparator/Main` must be hand-edited to the 
floor of the first Gram point found in the store. 

4. Run the Lean generators once the store has been populated.
   ```
   python python/src/data_gen/gen_zero_certificates.py Zeta/Zeros 
   python python/src/data_gen/gen_gram_certificates.py Zeta/Gram/Certificates.lean python/out/riemann_siegel/gram
   python python/src/data_gen/gen_count_certificate.py Zeta/Zeros/CountCertificates.lean
   python python/src/data_gen/gen_comparator.py comparator
   ```


After that, the Lean files are ready for compilation. 

--- 

## Running the tests

The tests check the approximants and the search against the reference zero lists (see
[Reference data](#reference-data)). 
The certification pipeline does not require that they are run and these are primarily for 
development purposes.

```bash
# from python/
pytest                                        # everything
pytest test/riemann_siegel                    # one method
pytest test/test_gram.py::test_wideness       # one test
```

---

## Directory structure

```
python/
├── src/                        # installed editable by environment.yml (`pip install -e .`)
│   ├── config.py               # global constants (see "Global constants")
│   ├── util.py                 # Approximation, ZApproximant, SignedPoint, SignedGramPoint, ZInterval; Gram-point helpers
│   ├── approximants.py         # CLI subcommands that build an approximant (euler_maclaurin | riemann_siegel)
│   ├── search.py               # ZeroSearch: grid bracketing, Rosser-block search, bisection, widening
│   ├── gram.py                 # Gram blocks: finding a good block for Turing's method
│   ├── euler_maclaurin/        # the Euler-Maclaurin approximant (used below height 150)
│   │   ├── zeta_values.py      # ζ(s) via Euler-Maclaurin + Borwein error bound
│   │   ├── gamma_values.py     # log Γ via Euler-Maclaurin, for the Riemann-Siegel θ
│   │   └── zeta_zeros.py       # Hardy Z, adaptive cutoff, ZEulerMaclaurin
│   ├── riemann_siegel/
│   │   └── zeta_zeros.py       # Riemann-Siegel Z, its error bound, ZRiemannSiegel (above height 150)
│   └── data_gen/               # stores and Lean emitters
│       ├── store_zeros.py      # search and write a zero store
│       ├── store_gram.py       # find and write a good Gram block
│       ├── store.py            # both: the Gram block, then the zeros up to it, with a count check
│       ├── lean_dialect.py     # per-method rendering of store rows into Lean
│       ├── gen_zero_certificates.py   # zero store  -> Zeta/Zeros/Certificates/
│       ├── gen_gram_certificates.py   # Gram store  -> Zeta/Gram/Certificates.lean
│       ├── gen_count_certificate.py   # both       -> Zeta/Zeros/CountCertificates.lean
│       └── gen_comparator.py          # batches    -> comparator/ targets
├── test/
│   ├── helpers.py              # tolerances, reference-zero loaders
│   ├── test_gram.py            # Gram points and blocks, both approximants
│   ├── euler_maclaurin/        # ζ, log Γ and Z values; zeros vs. reference lists
│   └── riemann_siegel/         # Z values; zeros vs. reference lists (up to zero #500,000)
├── out/                        # generated stores and plots, one directory per method
│   ├── euler_maclaurin/
│   │   └── zeros/              # manifest.json + zeros_<k>.txt
│   └── riemann_siegel/
│       ├── zeros/              # manifest.json + zeros_<k>.txt
│       └── gram/               # manifest.json, gram_block.txt, zeros_<idx>.txt
├── environment.yml             # conda environment (SageMath 10.8 + deps, this project)
└── pyproject.toml
```

### Reference data 

Reference data (zero lists) lives outside the package, in `data/` at the repository root
(`DATA_DIR` in `config.py`). 
These are as follows; the tests read them through the loaders in `test/helpers.py`:
- `lmfdb_zeta.txt`: first 100,000 zeros (up to height ≈ 74921) to ~31 dp, as `index height`
  rows ([source](https://www.lmfdb.org/zeros/zeta/)). Loader: `lmfdb_zeta`.
- `odlyzko_zeta_100.txt`: first 100 zeros to 1000 dp
  ([source](https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros2)). Loader: `odlyzko_zeta_100`.

---

## Global constants

Global constants are defined in `python/src/config.py` which govern key numerical and algorithmic
properties across the package. Care should be taken when changing any of them.

| Constant | Explanation |
| -------- | ----------- |
| `PROJECT_ROOT` | Repository root. The paths below are built from it so it should be edited to the location of the repository on your local machine.|
| `DATA_DIR` | Reference zero lists read by the tests (`<root>/data`, see [Reference data](#reference-data)). |
| `OUT_DIR` | Where stores are written and read: `<root>/python/out/<method>/{zeros,gram}/`. |
| `PREC` | Default working precision in bits for Euler-Maclaurin (1000), and mpmath's global precision. Euler-Maclaurin needs `PREC ≳ 9.06 * N` for its truncation bound to stay above roundoff. |
| `RS_PREC` | Default working precision in bits for Riemann-Siegel (200). About 60 bits suffice at height `1e7`. |
| `GRAM_PREC` | Precision in bits of every Gram point `g_n`, so each use (grid boundaries, Gram's-law checks, block edges) sees the same value. |
| `DIGITS` | Decimal places written per endpoint in a store (trailing zeros trimmed, keeping at least `IMPORT_DP`). |
| `ROWS_PER_FILE` | Rows per store file (250,000), keeping each well under GitHub's 100 MB limit. Independent of the Lean batches. |
| `BATCH_SIZE` | Zeros per generated Lean batch module, the same for every batch; `None` (the default) sizes each batch by its height instead (below). |
| `WORKER_GB`, `BATCH_BASE_GB`, `BATCH_ROW_NU_GB`, `MAX_BATCH_SIZE` | Height-sized batches: a batch's peak memory is about `BATCH_BASE_GB + BATCH_ROW_NU_GB · rows · ν` (0.6 GB and 2.4e-5 GB, measured), with `ν = ⌊√(t/2π)⌋`, so each batch gets the most rows, up to `MAX_BATCH_SIZE` (200), that keep a worker under `WORKER_GB` (3.35 GB). That is 200 rows below height ≈ 2·10⁶, about 90 at 10⁷ and 34 at 7·10⁷. |
| `BATCHES_PER_GROUP` | Children per fold module (125): each level-1 group folds that many batches, each higher level that many groups of the level below, until at most that many remain for the assembler. |
| `SIGN_MARGIN` | A sign is Python-certified only when `\|approx\| > SIGN_MARGIN * error`, leaving headroom for the radius of Lean's enclosure. Must be below 2. |
| `IMPORT_DP`, `IMPORT_DP_MAX` | Decimal places of a zero-batch boundary: each is placed at the fewest places from `IMPORT_DP` (3) up to `IMPORT_DP_MAX` (6) that separate its two zeros, and Lean reads it exactly as written. Only close pairs take more than 3 (a handful at `1e8`). |
| `GRAM_WIDEN_DP` | Gram-point brackets are widened outward to this many decimal places, giving a certified margin of at least `10^-GRAM_WIDEN_DP`. |
| `GRAM_ZERO_DP` | Zero brackets inside a Gram block are rounded outward to this many decimal places. At least `GRAM_WIDEN_DP`, so rounding cannot push a bracket past a Gram point. |
| `GRAM_GAP_MARGIN` | How far the zero search inside a Gram interval stays from each Gram point, so its brackets still lie between Lean's widened Gram brackets. |
| `RS_MIN_HEIGHT` | Lowest height at which the Riemann-Siegel error bound is used: `504/5`, Lean's rational form of `t ≥ 32π`. |
| `RS_THETA_CUTOFF` | Stirling cutoff for `θ` in the Riemann-Siegel main sum (1, Lean shift 0). Must match `hardyZApproximantRS`. |
| `RS_THETA_BERNOULLI` | Bernoulli terms for `θ` in the Riemann-Siegel main sum (2). Must match `hardyZApproximantRS`. |
| `LEHMAN_CONST` | Constant `A` in Lehman's bound `\|∫S\| ≤ A + B log(t/2π)` (5). Must match `CertifiedGramBlockSeq.wide` in `Zeta/Gram/Block.lean`. |
| `LEHMAN_LOG_COEFF` | Coefficient `B` in Lehman's bound (0.128). Must match `CertifiedGramBlockSeq.wide`. |
| `LEHMAN_MIN_HEIGHT_PI` | A Gram block must start above `168π`, where Lehman's bound holds. Must match `CertifiedGramBlockSeq.high`. |
| `PI_LOWER` | Rational lower bound on `π` (3.141592) used in the emitted proofs. Must be what `Real.pi_gt_d6` proves. |
| `PI_UPPER` | Rational upper bound on `π` (3.141593) used in the emitted proofs. Must be what `Real.pi_lt_d6` proves. |

---

## References

- **[Gram 1903]** J.-P. Gram, *Note sur les zéros de la fonction ζ(s) de Riemann*, Acta Math. **27** (1903),
  289–304. Gram points; the first zeros located between them.
- **[Hutchinson 1925]** J. I. Hutchinson, *On the roots of the Riemann zeta function*, Trans. Amer. Math. Soc. **27**
  (1925), 49–60. Names Gram's law and finds its first failure, at `g_126 ≈ 282.5`.
- **[Turing 1953]** A. M. Turing, *Some calculations of the Riemann zeta-function*, Proc. London
  Math. Soc. (3) **3** (1953), 99–117. Turing's method for counting the zeros up to a height.
- **[Rosser, Yohe, Schoenfeld 1969]** J. B. Rosser, J. M. Yohe, L. Schoenfeld, *Rigorous computation and the zeros of the Riemann
  zeta-function*, Information Processing 68 (Proc. IFIP Congress 1968), North-Holland (1969),
  70–76. Gram blocks and Rosser's rule.
- **[Lehman 1970]** R. S. Lehman, *On the distribution of zeros of the Riemann zeta-function*, Proc. London Math.
  Soc. (3) **20** (1970), 303–320. Rosser's rule fails infinitely often.
- **[Brent 1979]** R. P. Brent, *On the zeros of the Riemann zeta function in the critical strip*, Math. Comp.
  **33** (1979), 1361–1372 ([AMS](https://www.ams.org/mcom/1979-33-148/S0025-5718-1979-0537983-2/)).
  The search by Gram blocks at scale; the first failure of Rosser's rule, at Gram point
  13,999,525 (height ≈ 6.8·10⁶; [OEIS A216700](https://oeis.org/A216700)).
- **[Brent et al. 1982]** R. P. Brent, J. van de Lune, H. J. J. te Riele, D. T. Winter, *On the zeros of the Riemann zeta
  function in the critical strip. II*, Math. Comp. **39** (1982), 681–688. Statistics of Gram
  blocks and of the failures of Rosser's rule.
- **[Edwards 1974]** H. M. Edwards, *Riemann's Zeta Function*, Academic Press (1974), Chapters 6–8. Textbook account
  of Gram points, Rosser's rule, the Riemann-Siegel formula and Turing's method.
