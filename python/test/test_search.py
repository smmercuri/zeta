import mpmath as mp
import pytest

from search import GramSearchGrid, ZeroSearch, ZeroSlice
from util import (
    Approximation,
    GramPoint,
    SignedGramPoint,
    SignedPoint,
    ZApproximant,
    ZInterval,
    next_good_gram_point,
    prev_good_gram_point,
    round_import,
)


def _ramp(x):
    return 3 * x**2 - 2 * x**3


def _bump(x):
    return mp.sin(mp.pi * x) ** 2


class CosTheta(ZApproximant):
    """Fake approximant `Z̃(t) = cos(θ(t) + φ(t))`, with a tiny error bound.

    With `φ = 0` every Gram point is good and each Gram interval holds exactly one zero. Each
    phase `(n_lo, n_hi, amplitude, shape)` adds `amplitude * shape(x)`, with `x` running from 0 to
    1 over `[g_{n_lo}, g_{n_hi}]` and held at `shape(1)` above it, which builds Rosser blocks.
    """

    name = "cos-theta"

    def __init__(self, *phases):
        super().__init__()
        self.phases = [
            (GramPoint(lo).t, GramPoint(hi).t, amplitude, shape)
            for lo, hi, amplitude, shape in phases
        ]

    def params_at(self, t) -> tuple:
        return ()

    def eval(self, t, params: tuple) -> Approximation:
        t = mp.mpf(t)
        phase = mp.siegeltheta(t)
        for lo, hi, amplitude, shape in self.phases:
            x = min(max((t - mp.mpf(lo)) / (mp.mpf(hi) - mp.mpf(lo)), 0), 1)
            phase += amplitude * shape(x)
        return Approximation(mp.cos(phase), mp.mpf(10) ** -12)


N_START, M, N_END = 30, 45, 60
# `g_M` is bad, but `[g_{M - 1}, g_{M + 1}]` holds both its zeros, in its first Gram interval
HALVING = (M - 1, M + 1, mp.pi, _bump)
# `g_M` is bad and `[g_{M - 1}, g_{M + 1}]` holds no zero
MISSING = (M - 1, M + 1, -2 * mp.pi, _ramp)
# `g_{M + 2}` is bad too and `[g_{M + 1}, g_{M + 3}]` holds the two zeros missing before it
EXTRA = (M + 1, M + 3, 2 * mp.pi, _ramp)
# a zero sits exactly on `g_M` (the phase rises by `π/2` up to `g_M` and falls back after it), so
# its sign is not certified, and `[g_{M - 1}, g_{M + 1}]` holds that zero and one more
UNCERTAIN = ((M - 1, M, mp.pi / 2, _ramp), (M, M + 1, -mp.pi / 2, _ramp))


class CountingCosTheta(CosTheta):
    """`CosTheta` counting its evaluations."""

    def __init__(self, *phases):
        super().__init__(*phases)
        self.evals = 0

    def eval(self, t, params: tuple) -> Approximation:
        self.evals += 1
        return super().eval(t, params)


def assert_brackets(approx, zeros):
    """Every interval is a certified sign change, and they are disjoint and increasing."""
    assert all(z.is_sign_change() for z in zeros)
    assert all(z.upper <= w.lower for z, w in zip(zeros, zeros[1:]))


def zeros_in(zeros, n_lo, n_hi):
    lo, hi = GramPoint(n_lo).t, GramPoint(n_hi).t
    return sum(lo <= z.lower and z.upper <= hi for z in zeros)


def expected_zero_count(start, end):
    """Zeros of `cos θ` in `[start, end]`: the crossings of `θ` through `(k + 1/2)π`."""
    return int(mp.floor(mp.siegeltheta(end) / mp.pi - 0.5)) - int(
        mp.floor(mp.siegeltheta(start) / mp.pi - 0.5)
    )


def test_gram_grid_all_good():
    search = ZeroSearch(CosTheta())
    gram_range = search._search_gram_grid(N_START, N_END)
    assert not gram_range.search_blocked
    assert [(z.lower, z.upper) for z in gram_range.zeros] == [
        (GramPoint(n).t, GramPoint(n + 1).t) for n in range(N_START, N_END)
    ]


def test_gram_grid_rosser_block_by_halving():
    approx = CosTheta(HALVING)
    search = ZeroSearch(approx)
    assert not SignedGramPoint(GramPoint(M), approx).is_good
    gram_range = search._search_gram_grid(N_START, N_END)
    assert not gram_range.search_blocked
    assert len(gram_range.zeros) == N_END - N_START
    assert_brackets(approx, gram_range.zeros)
    assert zeros_in(gram_range.zeros, M - 1, M) == 2
    assert zeros_in(gram_range.zeros, M, M + 1) == 0


def test_gram_grid_rosser_block_by_window():
    approx = CosTheta(MISSING, EXTRA)
    search = ZeroSearch(approx)
    gram_range = search._search_gram_grid(N_START, N_END)
    assert not gram_range.search_blocked
    assert len(gram_range.zeros) == N_END - N_START
    assert_brackets(approx, gram_range.zeros)
    assert zeros_in(gram_range.zeros, M - 1, M + 1) == 0
    assert zeros_in(gram_range.zeros, M + 1, M + 3) == 4


@pytest.mark.parametrize("window_retries", [0, 3])
def test_gram_grid_window_failure_raises(window_retries):
    search = ZeroSearch(CosTheta(MISSING), halving_depth=2, window_retries=window_retries)
    with pytest.raises(RuntimeError, match="window retries"):
        search._search_gram_grid(N_START, N_END)


def test_gram_grid_window_blocked_at_lower_edge():
    search = ZeroSearch(CosTheta(MISSING))
    gram_range = search._search_gram_grid(M - 1, N_END)
    assert gram_range.lower_search_blocked
    assert not gram_range.upper_search_blocked


def test_gram_grid_rosser_block_with_uncertified_gram_point():
    approx = CosTheta(*UNCERTAIN)
    assert SignedGramPoint(GramPoint(M), approx).sign == 0
    gram_range = ZeroSearch(approx)._search_gram_grid(N_START, N_END)
    assert not gram_range.search_blocked
    assert len(gram_range.zeros) == N_END - N_START
    assert_brackets(approx, gram_range.zeros)


def test_rosser_block_halving_evaluates_only_midpoints():
    approx = CountingCosTheta(HALVING)
    grid = GramSearchGrid(M - 1, M + 1, approx)
    approx.evals = 0
    zeros = ZeroSearch(approx)._search_rosser_block(grid, 0, 2)
    assert len(zeros) == 2
    # one halving round of two cells: their two midpoints, the cell endpoints already known
    assert approx.evals == 2


def test_gram_grid_window_blocked_at_upper_edge():
    search = ZeroSearch(CosTheta(MISSING))
    gram_range = search._search_gram_grid(N_START, M + 1)
    assert not gram_range.lower_search_blocked
    assert gram_range.upper_search_blocked


def test_gram_grid_window_blocked_after_growing_to_the_edge():
    # `[g_{M - 1}, g_{M + 1}]` stops short of the range's end `g_{M + 2}`, so the window grows
    # one block to the right before it reaches the edge
    gram_range = ZeroSearch(CosTheta(MISSING))._search_gram_grid(N_START, M + 2)
    assert not gram_range.lower_search_blocked
    assert gram_range.upper_search_blocked


@pytest.mark.parametrize("widen", [False, True])
def test_merge_stitches_window_across_cut(widen):
    approx = CosTheta(MISSING, EXTRA)
    search = ZeroSearch(approx, bisection_depth=2, widen=widen)
    cuts = [N_START, M + 1, N_END]
    ranges = list(map(search._search_gram_grid, cuts[:-1], cuts[1:]))
    # the Rosser window straddles the cut, so neither range resolves it alone
    assert ranges[0].upper_search_blocked and ranges[1].lower_search_blocked
    merged = list(search._search_merged_gram_ranges(iter(ranges)))
    whole = search._search_gram_grid(N_START, N_END).zeros
    assert [(z.lower, z.upper) for z in merged] == [(z.lower, z.upper) for z in whole]


def gram_slice(n_lower, n_upper, zeros, **blocked):
    """A `ZeroSlice` between the Gram points `g_{n_lower}` and `g_{n_upper}`."""
    approx = CosTheta()
    lower = SignedGramPoint(GramPoint(n_lower), approx)
    upper = SignedGramPoint(GramPoint(n_upper), approx)
    return ZeroSlice(lower, upper, zeros, **blocked)


class RecordingZeroSearch(ZeroSearch):
    """A `ZeroSearch` whose range search records its calls and returns a range holding the single
    zero `(n_start, n_end)`, to test the merge on its own."""

    def __init__(self):
        super().__init__(CosTheta())
        self.calls = []

    def _search_gram_grid(self, n_start, n_end):
        self.calls.append((n_start, n_end))
        return gram_slice(n_start, n_end, [(n_start, n_end)])


def test_merge_concatenates_unblocked_ranges():
    search = RecordingZeroSearch()
    ranges = [gram_slice(0, 10, ["a"]), gram_slice(10, 20, ["b", "c"]), gram_slice(20, 30, [])]
    assert list(search._search_merged_gram_ranges(iter(ranges))) == ["a", "b", "c"]
    assert search.calls == []


@pytest.mark.parametrize(
    "blocked", [(True, False), (False, True), (True, True)], ids=["upper", "lower", "both"]
)
def test_merge_searches_blocked_seam_again(blocked):
    search = RecordingZeroSearch()
    ranges = [
        gram_slice(0, 10, ["a"], upper_search_blocked=blocked[0]),
        gram_slice(10, 20, ["b"], lower_search_blocked=blocked[1]),
        gram_slice(20, 30, ["c"]),
    ]
    assert list(search._search_merged_gram_ranges(iter(ranges))) == [(0, 20), "c"]
    assert search.calls == [(0, 20)]


def test_merge_chains_seams():
    search = RecordingZeroSearch()
    ranges = [
        gram_slice(0, 10, ["a"], upper_search_blocked=True),
        gram_slice(10, 20, ["b"]),
        gram_slice(20, 30, ["c"], lower_search_blocked=True),
    ]
    # the merged `[0, 20]` is merged again with `[20, 30]`, searched from `0`
    assert list(search._search_merged_gram_ranges(iter(ranges))) == [(0, 30)]
    assert search.calls == [(0, 20), (0, 30)]


def test_merge_raises_on_blocked_first_edge():
    ranges = [gram_slice(0, 10, ["a"], lower_search_blocked=True), gram_slice(10, 20, ["b"])]
    with pytest.raises(RuntimeError, match="g_0"):
        list(RecordingZeroSearch()._search_merged_gram_ranges(iter(ranges)))


def test_merge_raises_on_blocked_last_edge():
    ranges = [gram_slice(0, 10, ["a"]), gram_slice(10, 20, ["b"], upper_search_blocked=True)]
    with pytest.raises(RuntimeError, match="g_20"):
        list(RecordingZeroSearch()._search_merged_gram_ranges(iter(ranges)))


def test_gram_range_cut_lands_on_good_points():
    approx = CosTheta(MISSING)
    g_start = SignedGramPoint(GramPoint(N_START), approx)
    g_end = SignedGramPoint(GramPoint(N_END), approx)
    cuts = ZeroSearch._gram_range_cut(g_start, g_end, 2)
    # the naive cut `g_M` is bad, so it moves up to `g_{M + 1}`
    assert cuts == [N_START, M + 1, N_END]
    assert all(SignedGramPoint(GramPoint(n), approx).is_good_rounded for n in cuts)


def test_gram_range_cut_more_ranges_than_points():
    approx = CosTheta()
    g_start = SignedGramPoint(GramPoint(N_START), approx)
    g_end = SignedGramPoint(GramPoint(N_START + 2), approx)
    assert ZeroSearch._gram_range_cut(g_start, g_end, 10) == [N_START, N_START + 1, N_START + 2]


def test_signed_gram_point():
    approx = CosTheta(MISSING)
    assert SignedGramPoint(GramPoint(M - 1), approx).is_good
    assert not SignedGramPoint(GramPoint(M), approx).is_good
    assert SignedGramPoint(GramPoint(M), approx).next_good().n == M + 1
    assert SignedGramPoint(GramPoint(M + 1), approx).next_good().n == M + 1


def test_next_prev_good_gram_point():
    approx = CosTheta(MISSING)
    mid = (GramPoint(M - 1).t + GramPoint(M).t) / 2
    assert next_good_gram_point(mid, approx).n == M + 1
    mid = (GramPoint(M).t + GramPoint(M + 1).t) / 2
    assert prev_good_gram_point(mid, approx).n == M - 1


def test_widen_edges_snaps_only_the_edges():
    approx = CosTheta()
    search = ZeroSearch(approx)
    zeros = search._search_gram_grid(N_START, N_START + 5).zeros
    inner = [(z.lower, z.upper) for z in zeros[1:-1]]
    start, end = GramPoint(N_START).t - 0.2, GramPoint(N_START + 5).t + 0.2
    snapped = list(search._widen_edges(iter(zeros), start, end))
    assert snapped[0].lower == start and snapped[0].upper == zeros[0].upper
    assert snapped[-1].upper == end and snapped[-1].lower == zeros[-1].lower
    assert [(z.lower, z.upper) for z in snapped[1:-1]] == inner
    assert_brackets(approx, snapped)


def test_widen_edges_single_interval():
    approx = CosTheta()
    search = ZeroSearch(approx)
    (zero,) = search._search_gram_grid(N_START, N_START + 1).zeros
    start, end = zero.lower - 0.2, zero.upper + 0.2
    (snapped,) = search._widen_edges(iter([zero]), start, end)
    assert (snapped.lower, snapped.upper) == (start, end)


def test_widen_edges_empty():
    assert list(ZeroSearch(CosTheta())._widen_edges(iter([]), 1, 2)) == []


def test_snap_across_zero_raises():
    approx = CosTheta()
    search = ZeroSearch(approx)
    (zero,) = search._search_gram_grid(N_START, N_START + 1).zeros
    # just below the upper endpoint, past the zero: both endpoints have the same sign
    with pytest.raises(RuntimeError, match="no certified sign change"):
        zero.snap_lower(zero.upper - 0.01)


@pytest.mark.parametrize("start", [0, -1])
def test_iter_zeros_rejects_nonpositive_start(start):
    with pytest.raises(ValueError):
        ZeroSearch(CosTheta()).find_zeros(start, 50)


START, END = 100, 170


@pytest.mark.parametrize(
    "phases", [(), (HALVING,), (MISSING, EXTRA)], ids=["none", "halving", "window"]
)
def test_find_zeros_widen_tiles_the_range(phases):
    approx = CosTheta(*phases)
    search = ZeroSearch(approx, widen=True, bisection_depth=2)
    zeros = search.find_zeros(START, END)
    assert len(zeros) == expected_zero_count(START, END)
    assert zeros[0].lower == round_import(START, approx.prec)
    assert zeros[-1].upper == round_import(END, approx.prec)
    assert all(z.upper == w.lower for z, w in zip(zeros, zeros[1:]))
    assert all(z.is_sign_change() for z in zeros)


def test_find_zeros_without_widen_brackets_each_zero():
    approx = CosTheta(MISSING, EXTRA)
    search = ZeroSearch(approx, bisection_depth=2)
    zeros = search.find_zeros(START, END)
    assert len(zeros) == expected_zero_count(START, END)
    assert_brackets(approx, zeros)


def test_find_zeros_window_failure_raises():
    search = ZeroSearch(CosTheta(MISSING), bisection_depth=0, window_retries=1, halving_depth=2)
    with pytest.raises(RuntimeError, match="window retries"):
        search.find_zeros(START, END)


def test_find_zeros_raises_on_blocked_edge():
    # the last good Gram point before `end` is `g_{M + 2}`, so the Rosser window around the
    # missing zero runs into the edge of the only Gram range
    end = (GramPoint(M + 2).t + GramPoint(M + 3).t) / 2
    with pytest.raises(RuntimeError, match=f"g_{M + 2}: a Rosser window failed"):
        ZeroSearch(CosTheta(MISSING)).find_zeros(START, end)



class Polynomial(ZApproximant):
    """Fake approximant `Z̃(t) = (t - z_1)(t - z_2)…`, zeros exactly where we put them."""

    name = "polynomial"

    def __init__(self, zeros):
        super().__init__()
        self.zeros = zeros

    def params_at(self, t) -> tuple:
        return ()

    def eval(self, t, params: tuple) -> Approximation:
        value = 1
        for z in self.zeros:
            value *= t - z
        return Approximation(value, 1e-12)


def test_place_boundary_repairs_close_in_on_the_midpoint():
    approx = Polynomial([100.1, 100.2])
    fst = ZInterval(100.0, 100.12, approx)
    snd = ZInterval(100.13, 100.3, approx)
    # every point between the zeros has this sign, so passing this point as the previous boundary
    # makes every attempt fail; the last one tried should then sit midway between the zeros
    between = SignedPoint.of_approx(100.15, approx)
    with pytest.raises(RuntimeError, match=r"near t = 100\.150000"):
        fst.place_boundary(snd, between, cap=12)
