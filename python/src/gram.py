from sage.all import pi, log, RealField
from config import PREC, DIGITS, GRAM_GAP_MARGIN, GRAM_ZERO_DP, LEHMAN_LOG_COEFF
from util import ZInterval, coe_int
from decimal import ROUND_CEILING, ROUND_FLOOR
from fractions import Fraction
import mpmath as mp
from mpmath import grampoint, siegeltheta
from search import UncertainSign, ZeroSearch
from util import ZApproximant, next_gram_index, gram_point, round_import

mp.mp.prec = PREC


class GramBlockSearchError(RuntimeError):
    """Raised when no good Gram block is found within the iteration cap.

    Callers must not fall back on a partial result: the Gram block reached when
    the cap is exhausted has at least one constituent interval with no located
    zero, so it does not certify anything.
    """


def gram_point_interval(
    n: int, seed_dps: int = 30, safety: int = 8, out_digits: int = DIGITS
):
    """
    Untrusted candidate rational interval (a, b) around the Gram point g_n
    (theta(g_n) = n*pi). Half-width is derivative-sized
    (safety * |residual| / theta'), measured above the seed precision so the
    residual is visible; endpoints rounded outward to exact rationals.
    """
    n = int(n)
    with mp.workdps(seed_dps):
        g_hat = grampoint(n)
    with mp.workdps(seed_dps + 40):
        g = +g_hat
        residual = siegeltheta(g) - n * mp.pi
        slope = mp.mpf("0.5") * mp.log(g / (2 * mp.pi))
        delta = safety * abs(residual) / slope
        scale = mp.mpf(10) ** out_digits
        a_int = int(mp.floor((g - delta) * scale))
        b_int = int(mp.ceil((g + delta) * scale))
    d = 10**out_digits
    return Fraction(a_int, d), Fraction(b_int, d)


def gram_brackets_for_block(bl, **kwargs):
    return {n: gram_point_interval(n, **kwargs) for n in range(bl.lower, bl.upper + 1)}


class GramBlock:
    """Class containing the data of a Gram block, which is a sequence of gram
    points with zeta zeros contained within."""

    def __init__(self, lower, upper, blocks):
        self.lower = lower
        self.upper = upper
        self.blocks = blocks
        self.gram_lower = gram_point(lower)
        self.gram_upper = gram_point(upper)
        self.gram_blocks = [(gram_point(l), gram_point(u)) for l, u in blocks]

    def get_zeros_in_block(
        self,
        approx: ZApproximant,
        i: int,
        bisection_depth: int,
        epsilon: float = 1 / 4,
    ) -> list[ZInterval]:
        """Locates the zeta zeros in the `i`th constituent interval of the block.

        Each zero bracket is rounded outward to `GRAM_ZERO_DP` decimal places, as it is written
        into the Lean certificate, and the signs at the rounded endpoints are checked again.

        If the search raises `UncertainSign` (the sign of `Z̃` cannot be certified at an edge of
        the search range, or two zeros are too close to separate), no zeros are returned for this
        interval, so the block is not good and the search moves higher.

        Args:
            approx (ZApproximant): approximant of Hardy's Z-function
            i (int): index of the constituent interval, in `range(len(blocks))`
            bisection_depth (int): max depth of the bisection search for each zero.
            epsilon (float, optional): Minimization factor of the expected
                density of zeros. Defaults to 1/4.

        Returns:
            list[ZInterval]: the located zeros, possibly empty.

        Raises:
            RuntimeError: if the sign at a rounded bracket endpoint is not certified, or the
                certified signs at the rounded endpoints are equal.
        """
        gl, gu = self.gram_blocks[i]
        search = ZeroSearch(approx, bisection_depth, epsilon)
        try:
            zeros = search.find_zeros(gl + GRAM_GAP_MARGIN, gu - GRAM_GAP_MARGIN)
        except UncertainSign:
            return []
        rounded = []
        for z in zeros:
            lo = round_import(z.lower, approx.prec, GRAM_ZERO_DP, ROUND_FLOOR)
            hi = round_import(z.upper, approx.prec, GRAM_ZERO_DP, ROUND_CEILING)
            r = ZInterval(lo, hi, approx)
            s_lo, s_hi = r.endpoint_signs()
            if s_lo == 0 or s_hi == 0:
                raise RuntimeError(
                    f"zero bracket [{float(z.lower)}, {float(z.upper)}]: the sign at an endpoint "
                    f"is not certified after rounding outward to {GRAM_ZERO_DP} decimals"
                )
            if s_lo == s_hi:
                raise RuntimeError(
                    f"zero bracket [{float(z.lower)}, {float(z.upper)}] is not a sign-change "
                    f"bracket after rounding outward to {GRAM_ZERO_DP} decimals"
                )
            rounded.append(r)
        return rounded

    def block_data(self, i, seed_dps=30, safety=8, out_digits=DIGITS):
        l_idx, u_idx = self.blocks[i]
        gl, gu = self.gram_blocks[i]
        il = gram_point_interval(l_idx, seed_dps, safety, out_digits)
        iu = gram_point_interval(u_idx, seed_dps, safety, out_digits)
        return {"lower": (l_idx, gl, il[0], il[1]), "upper": (u_idx, gu, iu[0], iu[1])}

    def data(self, seed_dps=30, safety=8, out_digits=DIGITS):
        return [
            self.block_data(i, seed_dps, safety, out_digits)
            for i in range(len(self.blocks))
        ]

    def gram_intervals(self, seed_dps=30, safety=8, out_digits=DIGITS):
        intervals = self.data(seed_dps, safety, out_digits)
        return [g["lower"] for g in intervals] + [intervals[-1]["upper"]]

    def __repr__(self):
        return (
            f"GramBlock(lower={self.lower}, upper={self.upper}, "
            f"n_intervals={len(self.blocks)}, "
            f"t=[{float(self.gram_lower):.4f}, {float(self.gram_upper):.4f}])"
        )


def get_wide_gramBlock(N: int, lehman_const: float):
    """Returns the smallest Gram block starting at g_N whose half-span exceeds
    the Lehman bound: `(g_t - g_N)/2 > lehman_const + LEHMAN_LOG_COEFF * log(t/(2 * pi))`,
    where t is the highest index in the Gram block. This is the "wide enough"
    width Turing's method requires.

    Args:
        N (int): Starting index of the Gram block
        lehman_const (float): constant in the Lehman-style bound

    Returns:
        GramBlock: wide-enough Gram-block starting from g_N

    Raises:
        TypeError: if `N` is not an integer.
        ValueError: if `N < -1`
    """
    N = coe_int(N, "N")
    if N < -1:
        raise ValueError(f"Gram indices start at `-1`, got `N` = {N}")
    gN = gram_point(N)
    n = N
    gu = gram_point(n + 1)
    blocks = [(n, n + 1)]
    while (gu - gN) / 2 <= lehman_const + LEHMAN_LOG_COEFF * log(gu / (2 * pi)):
        n += 1
        gu = gram_point(n + 1)
        blocks.append((n, n + 1))
    return GramBlock(N, n + 1, blocks)


def is_good_gramBlock(
    bl: GramBlock,
    approx: ZApproximant,
    bisection_depth: int,
    epsilon: float = 1 / 4,
) -> tuple[bool, int, list[list[ZInterval]]]:
    """Predicate determining whether the GramBlock `bl` has the property that
    each constituent interval contains at least one zeta zero using an abstract
    approximant of the Hardy Z-function to find zeros.

    Args:
        bl (GramBlock): Gram block to check
        approx (ZApproximant): approximant of Hardy's Z-function
        bisection_depth (int): bisection_depth of bisection search on zero search
        epsilon (float, optional): Minimization factor of the expected density
          of zeros. Defaults to 1/4.

    Returns:
        tuple[bool, int, list[list[ZInterval]]]:
            whether the block satisfies the property,
            the failure index,
            the list of containing zeros
    """
    # The block must start at a *good* gram point, `(-1)^N Z(g_N) > 0`, so that the
    # zero search up to `g_N` ends on a Gram-block boundary and its count is exact.
    # Checked before the interval scans, which are the expensive part.
    if (
        approx(RealField(approx.prec)(bl.gram_lower)).certified_sign()
        != (-1) ** bl.lower
    ):
        return False, -1, []
    zeros = [
        bl.get_zeros_in_block(approx, i, bisection_depth, epsilon)
        for i in range(len(bl.blocks))
    ]
    return (
        all([0 < len(z) for z in zeros]),
        next((i for i, z in enumerate(zeros) if 0 == len(z)), -1),
        zeros,
    )


def get_good_gramBlock(
    T: float,
    lehman_const: float,
    approx: ZApproximant,
    bisection_depth: int,
    gram_cap: int = 1000,
    epsilon: float = 1 / 4,
) -> tuple[GramBlock, list[list[ZInterval]]]:
    """Finds a Gram block above `T` which satisfies the condition of
    `is_good_gramBlock` using an abstract approximant to Hardy's Z-function.

    A good block is a run of consecutive non-empty gram intervals, so on failure
    of the block starting at `g_N` the search restarts at the gram point just
    above the *last* empty interval of that block: every interval beyond it is
    already known to be non-empty. The search is retried up to `gram_cap` times.

    Args:
        T (float): the height to search above
        lehman_const (float): the constant in the Lehman style bound determining
            a good Gram block
        approx (ZApproximant): approximant of Hardy's Z-function
        bisection_depth (int): max depth to use in bisection search of zero search.
        gram_cap (int, optional): the max number of iterations to move to higher
            heights if Gram block search fails (`--gram-cap`). Defaults to 1000.
        epsilon (float, optional): Minimization factor of the expected density
          of zeros. Defaults to 1/4.

    Returns:
        tuple[GramBlock, list[list[ZInterval]]]:
            found GramBlock, list of contained zeros. Every returned block is
            good.

    Raises:
        GramBlockSearchError: no good Gram block was found within `gram_cap`
            iterations.
    """
    N = next_gram_index(T)
    bl = get_wide_gramBlock(N, lehman_const)
    i = 0
    is_good, fails_at, zeros = is_good_gramBlock(bl, approx, bisection_depth, epsilon)
    while not is_good and i < gram_cap:
        if zeros:  # some interval was empty: restart just above the last such one
            N = bl.blocks[max(j for j, z in enumerate(zeros) if not z)][1]
        else:  # only the start point `g_N` was bad: try the next gram point
            N = bl.lower + 1
        i += 1
        bl = get_wide_gramBlock(N, lehman_const)
        is_good, fails_at, zeros = is_good_gramBlock(bl, approx, bisection_depth, epsilon)

    if not is_good:
        raise GramBlockSearchError(
            f"no good Gram block found above T={T} after {i} shift(s) "
            f"(gram_cap={gram_cap}, lehman_const={lehman_const}, "
            f"bisection_depth={bisection_depth}); "
            f"last block g_{bl.lower}..g_{bl.upper} has no located zero in "
            f"interval {fails_at}. Increase --gram-cap to search further."
        )

    return bl, zeros
