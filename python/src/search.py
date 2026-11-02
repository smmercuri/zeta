from sage.all import RealField
import os
from concurrent.futures import ProcessPoolExecutor
from collections.abc import Iterator
from itertools import chain

from config import SIGN_MARGIN
from util import (
    ZInterval,
    adaptive_width,
    ZApproximant,
    SignedPoint,
    GramPoint,
    SignedGramPoint,
    next_good_gram_point,
    round_import,
    prev_good_gram_point,
)


class UncertainSign(RuntimeError):
    """A range edge where the approximant value and error bound cannot determine the
    sign of `Z` (`|approx| ≤ SIGN_MARGIN * error`). In this case, a zero lies too
    close to it to be bracketed from there. Also raised for an interior grid point
    that no perturbation within its cell resolves: two zeros closer than the error
    bound can separate.
    """


class SearchGrid:
    """A tiling of a segment of the critical line to search for sign
    changes with the approximant `approx`. Boundaries are `SignedPoint` provided
    as a list `points` to the constructor. It is expected that `points` is strictly
    increasing; this is not checked."""

    def __init__(self, points: list[SignedPoint], approx: ZApproximant):
        self.approx = approx
        self.points = points

    def _perturb_to_certified_sign(self, i: int) -> SignedPoint:
        """Perturbs the `i`th interior point to a nearby point whose sign is certified.
        We perturb by offsets of `±h/8, ±h/4, ±3h/8` with `h` the distance to
        the nearer neighbour, ensuring perturbations stay strictly inside the cell
        and order is maintained.

        Args:
            i (int): index of the point to be perturbed;
                must have `0 < i < len(self.points) - 1`.

        Returns:
            SignedPoint: the perturbed grid point.

        Raises:
            IndexError: if `i` is out of bounds or an edge index.
            UncertainSign: if no offset resolves the sign.
        """
        if not 0 < i < len(self.points) - 1:
            raise IndexError(f"{i} is not an interior grid point.")
        t = self.points[i].t
        h = min(t - self.points[i - 1].t, self.points[i + 1].t - t)
        for k in (1, 2, 3):
            for u in (t + k * h / 8, t - k * h / 8):
                s = self.approx(u).certified_sign()
                if s != 0:
                    return SignedPoint(u, s)
        raise UncertainSign(
            f"no point within {float(3 * h / 8):.2e} of t = {float(t)} has |Z| above "
            f"{SIGN_MARGIN}*error: zeros there are closer than the error bound can separate"
        )

    def perturb_to_valid(self):
        """Perturbs any invalid interior point to one with a certified sign. Mutates
        `SearchGrid.points`.
        """
        for i in range(1, len(self.points) - 1):
            if self.points[i].sign == 0:
                self.points[i] = self._perturb_to_certified_sign(i)

    @property
    def is_valid(self) -> bool:
        return all(p.sign != 0 for p in self.points)

    def detect_sign_changes(self) -> list[ZInterval]:
        """Returns a list of all intervals whose grid endpoints have opposing
        certified signs of the approximant."""
        if not self.is_valid:
            raise UncertainSign(
                "grid contains points with uncertified signs, use `perturb_to_valid` "
                "to obtain a grid whose interior points have certified signs and "
                "move endpoints as needed."
            )
        intervals = []
        for i in range(len(self.points) - 1):
            p, q = self.points[i], self.points[i + 1]
            if p.sign != q.sign:
                intervals += [ZInterval(p.t, q.t, self.approx)]
        return intervals

    def num_zeros(self) -> int:
        return len(self.detect_sign_changes())

    def halve_cell(self, i: int) -> "SearchGrid":
        """Halves `i`th cell `[p_i, p_{i + 1}]` in `self`,
        returning a `SearchGrid` object with 3 points which are effectively
        `[p_i, (p_i + p_{i + 1})/2, p_{i + 1}]`. However in case the midpoint
        does not have a certified sign it is perturbed, so this method may not
        exactly halve the cell.

        Args:
            i (int): cell index.

        Returns:
            SearchGrid: grid with three points, whose interior point splits the
                `i`th cell in two.
        """
        p, q = self.points[i], self.points[i + 1]
        mid = (p.t + q.t) / 2
        grid = SearchGrid([p, SignedPoint.of_approx(mid, self.approx), q], self.approx)
        grid.perturb_to_valid()
        return grid

    def halve(self) -> "SearchGrid":
        """Halves all cells in the grid using `halve_cell`."""
        grid = SearchGrid([], self.approx)
        for j in range(len(self) - 1):
            grid = grid.join(self.halve_cell(j))
        return grid

    def join(self, snd: "SearchGrid") -> "SearchGrid":
        """Joins the grid in `self` to the grid in `snd` assuming that
        the last point in `self` is the first point in `snd`. For example
        the grid `[1, 2, 3]` joins to `[3, 4, 5]` to give `[1, 2, 3, 4, 5]`.

        Args:
            snd (SearchGrid): grid to join `self` to.

        Raises:
            ValueError: if the last point in `self` does not match the first
                point in `snd`.

        Returns:
            SearchGrid: resulting join.
        """
        if self.points == []:
            return snd
        if snd.points == []:
            return self
        if self.points[-1] != snd.points[0]:
            raise ValueError(
                f"Expected the endpoint {self.points[-1]} of self to match "
                f"the first point {snd.points[0]} of snd."
            )
        points = self.points[:-1] + snd.points
        return SearchGrid(points, self.approx)

    def __len__(self):
        return len(self.points)

    def __repr__(self):
        return f"SearchGrid({self.points})"

    def __getitem__(self, i):
        if isinstance(i, slice):
            return SearchGrid(self.points[i], self.approx)
        return self.points[i]


class ZeroSlice:
    """Packages the results of a search on a slice of the grid. It contains the
    lower and upper bounds of the slice, a list of zeros, and whether search methods
    halted due to hitting the two edges of the slice. Nothing in this class
    checks whether the list of zeros are indeed contained within the bounds of
    the slice.

    Args:
        lower (SignedPoint): the lower bound of the slice.
        upper (SignedPoint): the upper bound of the slice.
        zeros (list[ZInterval]): the found zeros bounded by the slice.
        lower_search_blocked (bool): whether a search which spans multiple cells
            was cut short by the lower boundary.
        upper_search_blocked (bool): whether a search which spans multiple cells
            was cut short by the upper boundary.
    """

    def __init__(
        self,
        lower: SignedPoint,
        upper: SignedPoint,
        zeros: list[ZInterval],
        lower_search_blocked: bool = False,
        upper_search_blocked: bool = False,
    ):
        self.lower = lower
        self.upper = upper
        self.zeros = zeros
        self.lower_search_blocked = lower_search_blocked
        self.upper_search_blocked = upper_search_blocked

    def needs_merge_with(self, after: "ZeroSlice") -> bool:
        return self.upper_search_blocked or after.lower_search_blocked

    @property
    def search_blocked(self) -> bool:
        return self.lower_search_blocked or self.upper_search_blocked


class GramSearchGrid(SearchGrid):
    """A specialised `SearchGrid` where the cell boundaries are always
    `SignedGramPoint`. This lets one talk about whether points in the grid are
    good Gram points."""

    def __init__(self, n_start: int, n_end: int, approx: ZApproximant):
        # compute all Gram points first, then their certified signs
        gram_points = [GramPoint(n) for n in range(n_start, n_end + 1)]
        points = [SignedGramPoint(g, approx) for g in gram_points]
        super().__init__(points, approx)

    def validate_good_endpoints(self):
        if not self.points[0].is_good:
            raise ValueError(f"g_{self.points[0].n} is not a good Gram point.")
        if not self.points[-1].is_good:
            raise ValueError(f"g_{self.points[-1].n} is not a good Gram point.")

    def next_good_offset(self, i: int) -> int:
        """The offset `k >= 1` such that `self.points[i + k]` is the first good
        Gram point after `i`, or the last point of the grid if there is none.
        The block `points[i: i + k + 1]` corresponds to a Rosser block if
        `self.points[i]` and `self.points[i + k]` are good. If `k = 1` then this
        gives a Gram interval in which Gram's law holds.
        """
        k = 1
        while i + k < len(self.points) - 1 and not self.points[i + k].is_good:
            k += 1
        return k

    def prev_good_offset(self, i: int) -> int:
        """The offset `k >= 1` such that `self.points[i - k]` is the last good
        Gram point before `i`, or the first point of the grid if there is none.
        """
        k = 1
        while i - k > 0 and not self.points[i - k].is_good:
            k += 1
        return k


class AdaptiveGrid(SearchGrid):
    """A specialised `SearchGrid` where the interval `[start, end]` is split up
    into a grid of points whose steps are `epsilon` times the average spacing
    `2 * pi / log (t / (2 * pi))` between zeros at height `t` on the critical line.

    Args:
        start (float): starting point of the grid (inclusive).
        end (float): end point of the grid (inclusive).
        approx (ZApproximant): approximant of Hardy's Z-function.
        epsilon (float): factor which shrinks average spacing. Should be small
            and < 1 so that a cell is unlikely to contain more than a single zero.
            Smaller values will result in greater computational cost.
    """

    def __init__(self, start, end, approx, epsilon):
        RR = RealField(approx.prec)
        step = adaptive_width(epsilon)
        pts = [RR(start)]
        while pts[-1] < end:
            pts.append(pts[-1] + RR(step(pts[-1])))
        pts[-1] = RR(end)
        super().__init__([SignedPoint.of_approx(p, approx) for p in pts], approx)

    def validate_endpoints(self):
        for p in (self.points[0], self.points[-1]):
            if p.sign == 0:
                raise UncertainSign(
                    f"range edge t = {float(p.t)} has |Z| within {SIGN_MARGIN}*error; move the edge"
                )


class ZeroSearch:
    """A search for the zeros of `approx` on the critical line, configured by
    constructor parameters. The methods `iter_zeros` and `find_zeros` run
    the algorithm on the range `[start, end]` specified by their input parameters.
    The algorithm returns `ZInterval`s which contain zeros of the approximant,
    whose endpoints have certified signs and so should bracket zeros of the true
    Z-function.

    The algorithm proceeds by splitting up the range into the following
    segments: `[start, g_{start}]`, `[g_{start}, g_{end}]`, `[g_{end}, end]`, where
    `g_{start}` is the first good Gram point at or after `start` and `g_{end}` is the
    largest good Gram point at or before `end`.

    The segment `[g_{start}, g_{end}]` is split into a grid defined by Gram points.
    These often bound a single zero (Gram's law). When this fails, the deficit is
    often restored some `k` Gram intervals later, which forms so-called Rosser blocks.
    Rosser blocks are searched dyadically for `k` zeros, as predicted by Rosser's rule.
    When dyadic search cannot find `k` zeros (for example, if Rosser's rule fails
    as it first does around height 7e6) we perform a window search
    over successive Rosser blocks and Gram intervals until the deficit is restored.
    The window search is performed forwards and backwards in alternation.

    The head and tail segments are searched using `AdaptiveGrid` which carves
    up the segment using the average spacing of zeros, shrunk by the parameter
    `epsilon`.

    Once a set of zeros are found, then the precision of the intervals can be increased
    through bisection search, up to a maximum iterations specified by `bisection_depth`.
    This search is halted if it would cause endpoint signs to lose certification,
    which means that the interval is close to losing track of the true zero.

    If `widen` is true, then precision of the intervals is minimised by expanding
    the zero intervals so they form a tiling of `[start, end]`.
    This is useful to make certification more computationally efficient.

    Search can be parallelised across cores using the `num_workers` parameter to
    `iter_zeros`/`find_zeros`. This cuts up the Gram segment `[g_{start}, g_{end}]`
    into `64 * num_workers` consecutive segments, whose endpoints remain good Gram
    points. Whenever window search over Rosser blocks is blocked because it hits an
    endpoint of the parallel segments, neighbouring segments around the endpoint are
    merged and searched again.

    By design, the search on the Gram segment will raise if not enough zeros can be
    found as predicted by Rosser's rule. The head and tail segments do not have
    this check, since there is no count rule. Reduce `epsilon` or make sure `start` and
    `end` correspond to good Gram points to avoid silent head and tail errors.

    Args:
        approx (ZApproximant): approximant of Hardy's Z function
        bisection_depth (int): cap on the depth of bisection search. If `0` then
            no bisection search occurs. Increasing costs time. Defaults to 0.
        epsilon (float, optional): factor which shrinks average spacing of zeros
            to create the adaptive grid for searching head and tail segments.
            Defaults to 1/4.
        widen (bool, optional): Whether to create a coarse tiling of zeros at the
            end of search and bisection. Defaults to False.
        window_retries (int, optional): how many times the window may grow across
            consecutive Rosser blocks. May be increased freely without
            costing time. Defaults to 100.
        halving_depth (int, optional): how many times a failed Rosser block's cells are
            halved in dyadic search before it fails. Increasing costs time.
            Defaults to 10.
    """

    def __init__(
        self,
        approx: ZApproximant,
        bisection_depth: int = 0,
        epsilon: float = 1 / 4,
        widen: bool = False,
        window_retries: int = 100,
        halving_depth: int = 10,
    ):
        self.approx = approx
        self.bisection_depth = bisection_depth
        self.epsilon = epsilon
        self.widen = widen
        self.window_retries = window_retries
        self.halving_depth = halving_depth

    def _widen_zeros(
        self, start: float, end: float, intervals: list[ZInterval], max_repair: int = 12
    ) -> list[ZInterval]:
        """Widens the zero intervals into a tiling of `[start, end]`, placing a
        boundary between each pair of consecutive brackets (`ZInterval.place_boundary`).
        Every boundary, including `start` and `end` (rounded to `IMPORT_DP` decimals),
        has a certified sign (`|approx| > SIGN_MARGIN * error`), and the sign alternates
        from one boundary to the next, so `approx` changes sign across every interval
        at its stored endpoints, and the zero interval counts are preserved.

        Args:
            start (float): start of the range.
            end (float): end of the range.
            intervals (list[ZInterval]): list of intervals to widen.
            max_repair (int): number of times to repair the boundary until the sign
                is certified, see `ZInterval.place_boundary`. Defaults to 12.

        Returns:
            list[ZInterval]: list of widened intervals

        Raises:
            RuntimeError: if the sign at `start` or `end` is not certified, or does not alternate
                with its neighbour (move the range edge), or a boundary cannot be placed.
        """
        start = round_import(start, self.approx.prec)
        end = round_import(end, self.approx.prec)
        if intervals == []:
            return []
        intervals[0].lower = start
        intervals[-1].upper = end
        boundary = SignedPoint.of_approx(start, self.approx)
        if boundary.sign == 0:
            raise RuntimeError(
                f"start boundary t = {float(start)}: sign of approx not certified; "
                "move the range edge"
            )
        for fst, snd in zip(intervals, intervals[1:]):
            boundary = fst.place_boundary(snd, boundary, max_repair)
            fst.meet_at(boundary.t, snd)
        if self.approx(end).certified_sign() in (0, boundary.sign):
            raise RuntimeError(
                f"end boundary t = {float(end)}: sign of approx not certified or not "
                "alternating; move the range edge"
            )
        return intervals

    @staticmethod
    def _widen_edges(
        zeros: Iterator[ZInterval], start: float, end: float
    ) -> Iterator[ZInterval]:
        """Snaps the lower boundary of the first interval in `zeros` to `start` and
        the upper boundary of the last interval in `zeros` to `end`. Deals with the
        case where the head `[start, g_start]` and `[g_end, end]` contain no zeros.
        """
        prev = next(zeros, None)
        if prev is None:
            return
        prev = prev.snap_lower(start)
        for z in zeros:
            yield prev
            prev = z
        yield prev.snap_upper(end)

    def _bisect_zeros(self, intervals: list[ZInterval]) -> list[ZInterval]:
        """Performs bisection search across all zero intervals in `intervals`."""
        if self.bisection_depth == 0:
            return intervals
        return [i.bisect_zero(self.bisection_depth) for i in intervals]

    def _postprocess(
        self, start: float, end: float, zeros: list[ZInterval], blocked: bool = False
    ) -> list[ZInterval]:
        zeros = self._bisect_zeros(zeros)
        if self.widen and not blocked:
            zeros = self._widen_zeros(start, end, zeros)
        return zeros

    def _search_rosser_block(
        self, grid: GramSearchGrid, i: int, k: int
    ) -> list[ZInterval]:
        """Searches a Rosser block dyadically until the expected number of `k` zeros are
        found. Halves all intervals and counts resultant sign changes.
        Repeats across the whole until the stop condition of `k` zeros found
        or `self.halving_depth` iterations are spent.

        Args:
            grid (GramSearchGrid): grid of Gram points
            i (int): start index of the Rosser block
            k (int): size of the Rosser block

        Returns:
            list[ZInterval]: list of intervals containing zeros within the block
        """
        rosser_block = grid[i : i + k + 1]
        rosser_block.perturb_to_valid()
        zeros = rosser_block.detect_sign_changes()
        for _ in range(self.halving_depth):
            if len(zeros) >= k:
                break
            rosser_block = rosser_block.halve()
            zeros = rosser_block.detect_sign_changes()
        return zeros if len(zeros) == k else []

    def _search_rosser_window(self, grid: GramSearchGrid, i: int, k: int) -> ZeroSlice:
        """Searches over consecutive blocks strictly bounding points neighbouring
        `grid[i : i + k]` which do not satisfy `good`, using `self._search_rosser_block`
        and growing outwards from the centre. This searches the right neighbouring
        block, then the left and repeats until all the expected number of zeros are
        found or limits are hit.

        Returns a slice with empty zeros if this fails, either because limits are too
        small or the edge of the grid was reached before the correct number of zeros
        was found.

        Args:
            grid (GramSearchGrid): grid of Gram points
            i (int): starting index
            k (int): length of initial block to search

        Returns:
            ZeroSlice: results of search, comprising the found list of zero intervals,
                and whether the upper or lower boundaries were hit.
        """
        left, right = 0, k
        candidates = self._search_rosser_block(grid, i, k)
        upper_search_blocked = i + right >= len(grid) - 1
        lower_search_blocked = i - left <= 0
        for step in range(self.window_retries):
            # candidates is non-empty iff the correct number of zeros are found
            if candidates:
                return ZeroSlice(grid[i - left], grid[i + right], candidates)
            if lower_search_blocked or upper_search_blocked:
                # an edge of the grid is reached: stop, so the range is searched again together
                # with its neighbour
                break
            if step % 2 == 0:
                right += grid.next_good_offset(i + right)
            else:
                left += grid.prev_good_offset(i - left)
            upper_search_blocked = i + right >= len(grid) - 1
            lower_search_blocked = i - left <= 0
            candidates = self._search_rosser_block(grid, i - left, left + right)
        return ZeroSlice(
            grid[i - left],
            grid[i + right],
            candidates,
            lower_search_blocked,
            upper_search_blocked,
        )

    def _search_gram_grid(self, n_start: int, n_end: int) -> ZeroSlice:
        """Searches the gram range `[g_{n_start}, g_{n_end}]` split up into a
        grid of all Gram points contained within. Where Gram's law holds, there
        is a single zero per Gram interval meaning that in such cases this grid
        suffices. When it fails, Rosser window search is used
        (`self._search_rosser_window`). The zeros are then
        bisected and/or widened as specified in the object configuration.

        Args:
            n_start (int): starting index of Gram points.
            n_end (int): End index of Gram points.

        Returns:
            ZeroSlice: results of search, comprising the found list of zero intervals,
                and whether the upper or lower boundaries were hit.

        Raises:
            ValueError: if `n_end < n_start`, or `g_{n_start}` or `g_{n_end}` is not good.
            RuntimeError: if a Rosser window fails without reaching either end of the range.
        """
        if n_end < n_start:
            raise ValueError(f"No gram points in index range [{n_start}, {n_end}]")
        grid = GramSearchGrid(n_start, n_end, self.approx)
        grid.validate_good_endpoints()
        intervals = []
        i = 0
        # `n_start_blocked` is True if the edge `n_start` of the grid blocked a Rosser
        # window search from succeeding. Similarly `n_end_blocked`. These are returned
        # to stitch Gram ranges together later on.
        n_start_blocked = False
        n_end_blocked = False
        while i < len(grid) - 1:
            k = grid.next_good_offset(i)
            # Gram law holds, so interval contains a single zero
            if k == 1:
                intervals += [ZInterval(grid[i].t, grid[i + 1].t, self.approx)]
                i += 1
            else:
                rosser_window = self._search_rosser_window(grid, i, k)
                # deal with duplicates, just remove the backwards range from those
                # found previously
                while intervals and intervals[-1].lower >= rosser_window.lower.t:
                    intervals.pop()
                if not rosser_window.zeros:
                    if not rosser_window.search_blocked:
                        # windowing failed
                        raise RuntimeError(
                            f"g_{rosser_window.lower.n}..g_{rosser_window.upper.n}: the expected "
                            f"zeros are not found after {self.window_retries} window retries of "
                            f"{self.halving_depth} halvings each; increase --halving-depth or "
                            f"--window-retries"
                        )
                    if rosser_window.lower_search_blocked:
                        n_start_blocked = True
                    if rosser_window.upper_search_blocked:
                        n_end_blocked = True
                intervals += rosser_window.zeros
                i = rosser_window.upper.n - n_start
        zeros = self._postprocess(
            grid[0].t, grid[-1].t, intervals, n_start_blocked or n_end_blocked
        )
        return ZeroSlice(grid[0], grid[-1], zeros, n_start_blocked, n_end_blocked)

    def _search_adaptive(self, start: float, end: float) -> list[ZInterval]:
        """Searches `[start, end]` for zeros by using a grid of points using the
        average spacing of zeros (`AdaptiveGrid`). Granularity of this grid can be
        modified through `self.epsilon`. Interior points are perturbed so that
        they always have a certified sign for `self.approx`. The zeros are then
        bisected and/or widened as specified in the object configuration.

        Args:
            start (float): start of search range.
            end (float): end of search range.

        Raises:
            UncertainSign: if the sign at `start` or `end` is not certified or
                if perturbation of interior points fails.

        Returns:
            list[ZInterval]: A list of intervals which contain a zero of the Z
                approximant.
        """
        grid = AdaptiveGrid(start, end, self.approx, self.epsilon)
        grid.validate_endpoints()
        grid.perturb_to_valid()
        return self._postprocess(start, end, grid.detect_sign_changes())

    def _search_merged_gram_ranges(
        self,
        gram_ranges: Iterator[ZeroSlice],
        verbose: bool = False,
        num_ranges: int | None = None,
    ) -> Iterator[ZInterval]:
        """In parallelised search, the initial global Gram grid is cut up into
        smaller segments, each dispatched to parallel workers. Search methods which
        span multiple Rosser blocks and Gram intervals may fail due to hitting the
        edge of such segments before finding the expected number of zeros.
        In such cases, the segment is merged with its neighbour at the blocked edge
        and searched again; this is repeated if the merge segment is still blocked.

        If the block occurs at the edge of the global Gram grids, then we can merge no
        further and errors are raised.

        Args:
            gram_ranges (Iterator[ZeroSlice]): iterator containing search results
                over all paralllel segments.
            verbose (bool, optional): whether to print progress to CLI.
                Defaults to False.
            num_ranges (int | None, optional): used for CLI printing information
                if `verbose=True`. Defaults to None.

        Raises:
            RuntimeError: if Rosser window search gets blocked at the boundaries of
                the global Gram grid.

        Yields:
            Iterator[ZInterval]: list of zeros found after bad segments have been
                merged and researched.
        """
        prev: ZeroSlice = None
        for j, gram_range in enumerate(gram_ranges, start=1):
            if verbose:
                print(f"\rrange {j}/{num_ranges} done", end="", flush=True)
            if prev is not None and prev.needs_merge_with(gram_range):
                gram_range = self._search_gram_grid(prev.lower.n, gram_range.upper.n)
            elif prev is not None:
                yield from prev.zeros
            if gram_range.lower_search_blocked:
                raise RuntimeError(
                    f"g_{gram_range.lower.n}: a Rosser window failed against this edge"
                )
            prev = gram_range
        if prev.upper_search_blocked:
            raise RuntimeError(
                f"g_{prev.upper.n}: a Rosser window failed against this edge"
            )
        yield from prev.zeros

    @staticmethod
    def _gram_range_cut(
        g_start: SignedGramPoint,
        g_end: SignedGramPoint,
        num_ranges: int,
    ) -> list[int]:
        """Interpolates the range `[g_start, g_end]` to produce up to `num_ranges + 1`
        strictly increasing indices, all of which are good after rounding. The inputs
        `g_start` and `g_end` must also be good after rounding. Produces fewer than
        the expected number of ranges whenever there are not enough Gram points in the
        range.

        Args:
            g_start (SignedGramPoint): start of Gram range.
            g_end (SignedGramPoint): end of Gram range.
            num_ranges (int): number of ranges to produce

        Returns:
            list[int]: list of gram indices defining the Gram ranges

        Raises:
            ValueError: if `g_start` or `g_end` are not good after rounding.
        """
        if not g_start.is_good_rounded or not g_end.is_good_rounded:
            raise ValueError(
                f"g_{g_start.n} and g_{g_end.n} must be good after rounding."
            )
        n_start, n_end = g_start.n, g_end.n
        range_idx = range(1, num_ranges)
        gram_pts = [
            GramPoint(n_start + j * (n_end - n_start) // num_ranges) for j in range_idx
        ]
        cuts = [SignedGramPoint(g, g_start.approx).next_good().n for g in gram_pts]
        return sorted({n_start, *cuts, n_end})

    def _parallel_gram_zeros(
        self,
        g_start: SignedGramPoint,
        g_end: SignedGramPoint,
        num_workers: int,
        verbose: bool,
    ) -> Iterator[ZInterval]:
        """Runs a parallelised Gram grid search over `[g_start, g_end]`. The
        range is cut up into up to `64 * num_workers` segments, which are
        passed to parallel workers. Smaller and more numerous segments are preferred
        so that if a merge is needed (`self._search_merged_gram_ranges`) the
        additional cost is low."""
        cuts = self._gram_range_cut(g_start, g_end, 64 * num_workers)
        with ProcessPoolExecutor(max_workers=num_workers) as ex:
            ranges = ex.map(self._search_gram_grid, cuts[:-1], cuts[1:])
            yield from self._search_merged_gram_ranges(ranges, verbose, len(cuts) - 1)
        if verbose:
            print()

    def iter_zeros(
        self,
        start: float,
        end: float,
        verbose: bool = False,
        num_workers: int = 1,
    ) -> Iterator[ZInterval]:
        """Performs the overall zero-search algorithm as described in the class
        docstring, returning the zeros as an iterator.

        Args:
            start (float): lower bound (inclusive) of the heights to search.
            end (float): upper bound (inclusive) of the heights to search.
            verbose (bool, optional): Whether to print CLI information.
                Defaults to False.
            num_workers (int, optional): Number of worker processes. Requires `approx`
                to pickle if `> 1`. Use `-1` to select the maximum possible.
                Defaults to 1.

        Yields:
            ZInterval: zero intervals in increasing order.

        Raises:
            ValueError: if `start <= 0` or `end < start`.
            RuntimeError: if a Rosser block is not resolved within `halving_depth` and
                `window_retries`, or if the window search is blocked by `g_{start}`
                or `g_{end}`. Also raises if `widen` when a boundary cannot be placed.
            UncertainSign: if the sign at a range edge cannot be certified, or if
                there are two zeros closer than the error bound can separate.
        """
        if start <= 0:
            raise ValueError(f"start should be strictly positive, got {start}")
        if end < start:
            raise ValueError(f"end should be at least start, got [{start}, {end}]")
        if self.widen:
            start, end = round_import(start, self.approx.prec), round_import(
                end, self.approx.prec
            )
        g_start = next_good_gram_point(start, self.approx)
        g_end = prev_good_gram_point(end, self.approx)
        if g_start.n > g_end.n:
            # Not enough good Gram points to bound a Rosser search so use
            # epsilon-carving on the whole
            yield from self._search_adaptive(start, end)
        else:
            if num_workers == -1:
                num_workers = os.cpu_count()
            head = self._search_adaptive(start, g_start.t)
            if num_workers == 1:
                gram_zeros = self._search_merged_gram_ranges(
                    [self._search_gram_grid(g_start.n, g_end.n)]
                )
            else:
                gram_zeros = self._parallel_gram_zeros(
                    g_start, g_end, num_workers, verbose
                )
            tail = self._search_adaptive(g_end.t, end)
            zeros = chain(head, gram_zeros, tail)
            yield from (self._widen_edges(zeros, start, end) if self.widen else zeros)

    def find_zeros(
        self,
        start: float,
        end: float,
        verbose: bool = False,
        num_workers: int = 1,
    ) -> list[ZInterval]:
        """Performs the overall zero-search algorithm as described in the class
        docstring, returning the zeros as a list.

        Args:
            start (float): lower bound (inclusive) of the heights to search.
            end (float): upper bound (inclusive) of the heights to search.
            verbose (bool, optional): Whether to print CLI information.
                Defaults to False.
            num_workers (int, optional): Number of worker processes. Requires pickling
                if `> 1`. Use `-1` to select the maximum possible. Defaults to 1.

        Returns:
            list[ZInterval]: List of found zero intervals

        Raises:
            ValueError: if `start <= 0` or `end < start`.
        """
        return list(
            self.iter_zeros(
                start=start,
                end=end,
                verbose=verbose,
                num_workers=num_workers,
            )
        )
