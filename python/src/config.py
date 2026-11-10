from decimal import Decimal
from fractions import Fraction
from pathlib import Path

# paths
# ------------------------------------------------------
#: The repository this file is in (`python/src/config.py`), wherever it is checked out.
PROJECT_ROOT = str(Path(__file__).resolve().parents[2])
DATA_DIR = f"{PROJECT_ROOT}/data"
OUT_DIR = f"{PROJECT_ROOT}/python/out"

# working precision in Sage and mpmath
# ------------------------------------------------------
PREC = 1000

#: Default working precision (bits) of the Riemann–Siegel approximant which can be
#: lower than that used in Euler-Maclaurin (`PREC`). Derived from the fact that
#: at height t, the approximation uses `log2 (t log ⌊√(t/2π)⌋)` bits for the
#: integer part, `log2 (1/error)` to be below the error, and `log2 (2 √⌊√(t/2π)⌋)`
#: for the summation.
RS_PREC = 200

#: Precision (bits) at which Gram points are converted to Sage reals (`util.gram_point`), so
#: every use of `g_n` (grid boundaries, Gram's-law checks, block edges) sees the same value.
GRAM_PREC = 100

# output layout
# ------------------------------------------------------
#: Rows per store file. A store is split into files to stay under GitHub's 100 MB limit.
#: Independent of Lean batches.
ROWS_PER_FILE = 250_000

#: Zeros per generated Lean batch module, the same for every batch; or
#: `None` to size each batch by its height, computed so that
#: `BATCH_BASE_GB + BATCH_ROW_NU_GB * rows * ⌊√(t/2π)⌋ <= WORKER_GB`.
BATCH_SIZE: int | None = None

#: Limits the number of zeros in a Lean certificate batch. Batches amortise
#: per-file costs.
MAX_BATCH_SIZE = 200

#: A machine-specific value specifying the peak memory allowed per worker when
#: building a certificate batch. Used as a cap to compute adaptive batch sizes.
WORKER_GB = 3.35

#: Model of a batch's peak private memory: a fixed overhead and a component contributing
#: per row per unit of ⌊√(t/2π)⌋.
BATCH_BASE_GB = 0.6
BATCH_ROW_NU_GB = 2.4e-5

#: Batches are successively assembled into `k` levels of groups. This parameter
#: controls up to how many level `i` groups are assembled into level `i + 1` groups.
CHILDREN_PER_GROUP = 125

# sign certification
# ------------------------------------------------------
#: In exact arithmetic, a check such as `|approx| > error` suffices. However, in Lean's
#: interval arithmetic this becomes `|approx| > error + r`. Thus we introduce an inflation
#: factor and check `|approx| > SIGN_MARGIN * error` to guard against interval arithmetic
#: failures. This should be below 2.
SIGN_MARGIN = 1.5

# decimal places at which endpoints reach Lean
# ------------------------------------------------------
#: Widened zero intervals are written to the store at the fewest decimal places, from `IMPORT_DP`
#: up to `IMPORT_DP_MAX`, at which they separate their two zeros with a certified sign.
#: Imported directly by Lean. Consecutive zeros closer than `~10^-dp` cannot be separated
#: at `dp` places, and the minimum zero gap tends to `0` in `T`. Calibrating the GUE small-gap
#: law with store data, the expected number of pairs below `T` needing more than `dp` places:
#:
#:   dp   1e6     1e7     1e8     1e9     1e10
#:   3    0.01    0.3     5       -       -
#:   4    -       -       0.005   0.08    1.3
#:   5    -       -       -       1e-4    0.001
IMPORT_DP = 3
IMPORT_DP_MAX = 6

#: Decimal places non-widened intervals are written as (when using `--no-widen`).
#: 13 suffices up to height `1e8` with auto stopping in bisection search.
NO_WIDEN_DP = 13

#: Decimal places Gram-point brackets and their zeros are written as. The generator widens them
#: to `GRAM_WIDEN_DP` before they reach Lean.
GRAM_DP = 30

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
GRAM_GAP_MARGIN = 1e-4

# values fixed by the Lean statements and proofs
# ------------------------------------------------------
#: Lowest height at which the Riemann–Siegel error bound may be used. The bound needs `t ≥ 32π`,
#: which Lean proves as `t ≥ 504/5` from `π < 3.15` (`thirtyTwoPi_le_dec`).
RS_MIN_HEIGHT = Fraction(504, 5)

#: Stirling parameters of θ in the Riemann–Siegel main sum. Must match
#: `riemannSiegelThetaApproximant 2 0` in `hardyZApproximantRS`: `M = 2` Bernoulli terms and
#: Lean shift `0`, which is cutoff `1` in `euler_maclaurin.gamma_values.theta`.
RS_THETA_CUTOFF = 1
RS_THETA_BERNOULLI = 2

#: Lehman's bound `|∫S| ≤ LEHMAN_CONST + LEHMAN_LOG_COEFF * log(t/2π)`. Must match the `wide`
#: field of `CertifiedGramBlockSeq`.
LEHMAN_CONST = 5
LEHMAN_LOG_COEFF = 0.128

#: A Gram-block sequence must start above `LEHMAN_MIN_HEIGHT_PI * π`. Must match the `high` field
#: of `CertifiedGramBlockSeq`.
LEHMAN_MIN_HEIGHT_PI = 168

#: Rational bounds `PI_LOWER < π < PI_UPPER` used in the emitted `wide`/`high` proofs. Must be
#: the bounds `Real.pi_gt_d6` and `Real.pi_lt_d6` prove.
PI_LOWER = Decimal("3.141592")
PI_UPPER = Decimal("3.141593")
