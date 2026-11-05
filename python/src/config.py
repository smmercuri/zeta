from decimal import Decimal
from fractions import Fraction

# paths
# ------------------------------------------------------
PROJECT_ROOT = "~/zeta"
DATA_DIR = f"{PROJECT_ROOT}/data"
OUT_DIR = f"{PROJECT_ROOT}/python/out"

# working precision in Sage and mpmath
# ------------------------------------------------------
PREC = 1000

#: Default working precision (bits) of the Riemann–Siegel approximant, far below `PREC`, which
#: Euler–Maclaurin needs (its truncation bound must stay above roundoff, `PREC ≳ 9.06·N`). At
#: height 1e7 Riemann–Siegel needs ~60 bits: ~26 for the integer part of the phase
#: `θ(t) − t log n`, ~23 to sit below the ~1e-7 error bound, ~7 for the ~2√N-sized sum.
RS_PREC = 200

#: Precision (bits) at which Gram points are converted to Sage reals (`util.gram_point`), so
#: every use of `g_n` (grid boundaries, Gram's-law checks, block edges) sees the same value.
GRAM_PREC = 100

# number of digits to print when generating data
# ------------------------------------------------------
DIGITS = 30

# output layout
# ------------------------------------------------------
#: Rows per store file. A store is split into files so none nears GitHub's 100 MB limit (at
#: height 1e6 a row is ~35 bytes, so ~9 MB a file); the split is independent of the Lean
#: batches, which locate their rows through the store's manifest.
ROWS_PER_FILE = 250_000

#: Zeros per generated Lean batch module (`gen_zero_certificates.py`), the same for every batch; or
#: `None` to size each batch by its height (below). Any size is sound: each batch's metaprogram
#: reads its own rows `[lo, hi)`. It sets the cost per module: larger batches import Mathlib fewer
#: times, but a batch's peak memory grows with its rows, which caps how many build in parallel.
BATCH_SIZE: int | None = None

#: Height-sized batches. A batch's peak private memory is about
#: `BATCH_BASE_GB + BATCH_ROW_NU_GB · rows · ν`, ν = ⌊√(t/2π)⌋, its proof term included, while
#: CPU per row does not depend on the batch size. So
#: each batch gets the most rows, up to `MAX_BATCH_SIZE`, that keep a worker under `WORKER_GB`:
#: 200 rows below ν ≈ 570 (height ≈ 2·10⁶), about 90 at 10⁷ and 34 at 7·10⁷.
WORKER_GB = 3.35
BATCH_BASE_GB = 0.6
BATCH_ROW_NU_GB = 2.4e-5
MAX_BATCH_SIZE = 200

#: Batch modules per generated group module (`gen_zero_certificates.py`). Any size is sound: a group
#: folds its batches' statements, and the assembler folds the groups'. It bounds the size of every
#: fold module: one flat assembler would need a prefix theorem per batch (8,740 at height 10⁶).
BATCHES_PER_GROUP = 125

# sign certification
# ------------------------------------------------------
#: In exact arithmetic, a check such as `|Z̃| > error` suffices. However, in Lean's
#: interval arithmetic this becomes `|Z̃| > error + r`. Thus we introduce an inflation
#: factor and check `|Z̃| > SIGN_MARGIN * error` to guard against interval arithmetic
#: failures. This should be below 2.
SIGN_MARGIN = 1.5

# decimal places at which endpoints reach Lean
# ------------------------------------------------------
#: Zero-batch boundaries are written to the store at the fewest decimal places, from `IMPORT_DP`
#: up to `IMPORT_DP_MAX`, at which they separate their two zeros with a certified sign
#: (`ZInterval.place_boundary` in `util.py`). Lean, the native check and the generator import every
#: endpoint exactly as written, so there is no precision to keep in step between them.
#: Consecutive zeros closer than ~10^-dp cannot be separated at dp places, and the closest pair
#: below height T gets closer as T grows. Expected number of pairs below T needing more than dp
#: places (GUE small-gap law P(gap < x·mean) ≈ (π²/9)x³, calibrated by 1e7 passing and 1e8
#: failing when every boundary had 3):
#:
#:   dp   1e6     1e7     1e8     1e9     1e10
#:   3    0.01    0.3     5       -       -
#:   4    -       -       0.005   0.08    1.3
#:   5    -       -       -       1e-4    0.001
#:
#: so a handful of boundaries take 4 places at 1e8, and 5 or 6 places suffice beyond 1e10.
IMPORT_DP = 3
IMPORT_DP_MAX = 6

#: Gram-point brackets are widened outward to this many places, so their certified margin is
#: at least `10^-GRAM_WIDEN_DP`. This does not have a Lean counterpart, but must be chosen
#: so that `10^-GRAM_WIDEN_DP` can clear `gram_bound`'s resolution by a good margin.
GRAM_WIDEN_DP = 5

#: Zero brackets inside a Gram block are rounded outward to this many places. This does not have
#: a Lean counterpart, but rounding must not push a bracket past a Gram point, so it must be
#: at least `GRAM_WIDEN_DP`.
GRAM_ZERO_DP = 5

#: The zero search in a Gram interval stays this far from each Gram point, so that zero
#: brackets still lie between Lean's widened Gram brackets (`GRAM_WIDEN_DP`) after outward
#: rounding (`GRAM_ZERO_DP`).
#: TODO: search directly between the widened Gram brackets `[b_n, a_{n+1}]` Lean sees
#: (`GramBlock.Certificate.contains_zero`) instead; that needs the widening moved from the
#: emitter into `gram.py`, and removes this margin.
GRAM_GAP_MARGIN = 1e-4

# values fixed by the Lean statements and proofs
# ------------------------------------------------------
#: Lowest height at which the Riemann–Siegel error bound may be used. The bound needs `t ≥ 32π`,
#: which Lean proves as `t ≥ 504/5` from `π < 3.15` (`thirtyTwoPi_le_dec`). Exact, since
#: `100.8` is not a binary float.
RS_MIN_HEIGHT = Fraction(504, 5)

#: Stirling parameters of θ in the Riemann–Siegel main sum. MUST match
#: `riemannSiegelThetaApproximant 2 0` in `hardyZApproximantRS`: `M = 2` Bernoulli terms and
#: Lean shift `0`, which is cutoff `1` in `euler_maclaurin.gamma_values.theta`.
RS_THETA_CUTOFF = 1
RS_THETA_BERNOULLI = 2

#: Lehman's bound `|∫S| ≤ LEHMAN_CONST + LEHMAN_LOG_COEFF · log(t/2π)`. MUST match the `wide`
#: field of `CertifiedGramBlockSeq` (`Zeta/Gram/Block.lean`), which fixes `5 + 0.128·log(·)`.
LEHMAN_CONST = 5
LEHMAN_LOG_COEFF = 0.128

#: A Gram-block sequence must start above `LEHMAN_MIN_HEIGHT_PI · π`. MUST match the `high` field
#: of `CertifiedGramBlockSeq` (`168 * π < …`).
LEHMAN_MIN_HEIGHT_PI = 168

#: Rational bounds `PI_LOWER < π < PI_UPPER` used in the emitted `wide`/`high` proofs. MUST be
#: the bounds `Real.pi_gt_d6` and `Real.pi_lt_d6` prove.
PI_LOWER = Decimal("3.141592")
PI_UPPER = Decimal("3.141593")
