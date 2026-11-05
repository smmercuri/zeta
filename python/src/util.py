from sage.all import RealField, pi, log
from mpmath import grampoint
from collections.abc import Callable
from abc import ABC, abstractmethod
from config import PREC, DIGITS, GRAM_PREC, SIGN_MARGIN, IMPORT_DP, IMPORT_DP_MAX
from itertools import chain
import mpmath as mp
import operator
from decimal import ROUND_HALF_UP, Decimal

mp.mp.prec = PREC
RR = RealField(PREC)


class Approximation:
    """Class encoding an approximation, packaging `val` and `error`."""

    def __init__(self, val, error):
        self.val = val
        self.error = error

    def certified_sign(self, margin: float = SIGN_MARGIN) -> int:
        """Returns the sign of an approximation if the sign of the true value
        matches, else it returns `0`. This is done by checking if
        `|val| > margin * error` and returning the sign if true and `0` if false.

        `margin` is used to inflate the error, to provide some headroom for
        interval enclosure used in the Lean certificates.

        Floating point roundoff in `val` is not tracked."""
        if abs(self.val) > margin * self.error:
            return 1 if self.val > 0 else -1
        return 0

    def __repr__(self):
        return f"Approximation(val={self.val}, error={self.error})"

    def __iter__(self):
        return iter((self.val, self.error))


class ZApproximant(ABC):
    name: str
    cols: tuple[str, ...] = ()

    def __init__(self, prec: int = PREC):
        self.prec = prec

    @abstractmethod
    def params_at(self, t) -> tuple:
        """Method-specific parameters at height `t`, in `cols` order."""

    @abstractmethod
    def eval(self, t, params: tuple) -> Approximation:
        """Method-specific approximation of `Z(t)` with error bound."""

    def __call__(self, t) -> Approximation:
        return self.eval(t, self.params_at(t))

    @staticmethod
    def row_cols_of(cols: tuple[str, ...]) -> tuple[str, ...]:
        """Column names for a row carrying `cols` at each endpoint, in `ZInterval.row()` order."""
        return ("left", "right") + tuple(
            chain.from_iterable((f"left_{c}", f"right_{c}") for c in cols)
        )

    @property
    def row_cols(self) -> tuple[str, ...]:
        """Column names of a zero-interval row, in `ZInterval.row()` order."""
        return self.row_cols_of(self.cols)

    def metadata(self) -> dict:
        """Run provenance for the manifest. The schema lives in `row_cols`, which the
        manifest records separately."""
        return {"method": self.name, "prec": self.prec}

    def __repr__(self):
        args = ", ".join(
            f"{k}={v!r}" for k, v in self.metadata().items() if k != "method"
        )
        return f"{type(self).__name__}({args})"


def round_import(t, prec: int, dp: int = IMPORT_DP, rounding: str = ROUND_HALF_UP):
    """Rounds the float `t` to `dp` decimal places in order to match the value that
    Lean imports."""
    return RealField(prec)(str(Decimal(str(t)).quantize(Decimal(10) ** -dp, rounding)))


def gram_point(n: int) -> float:
    """Wrapper around `mpmath.grampoint` to fix `RealField` conversion across
    all usages in the code. This ensures canonical precision across grid boundaries and
    Gram goodness checks. Do not use under `mp.workdps`."""
    return RealField(GRAM_PREC)(grampoint(n))


class GramPoint:
    """Class encoding a Gram point's index and value, with normalized precision
    as `GRAM_PREC`."""

    def __init__(self, n: int):
        self.n = n
        self.t = gram_point(n)

    def __repr__(self):
        return f"GramPoint({self.n})"


class SignedPoint:
    """A height `t` paired with a `sign`. This allows alternative constructors
    to compute `sign` from `t`. `SignedPoint.of_approx` constructs
    the sign value from `approx(..).certified_sign()`, giving `0` in the case
    that the sign of the true Z-function cannot be inferred from the sign of
    the approximant."""

    def __init__(self, t: float, sign: int):
        self.t = t
        self.sign = sign

    @classmethod
    def of_approx(cls, t: float, approx: ZApproximant) -> "SignedPoint":
        return SignedPoint(t, approx(t).certified_sign())

    def __repr__(self):
        return f"SignedPoint({self.t}, {self.sign})"


class SignedGramPoint(SignedPoint):
    """`SignedGramPoint(GramPoint(n), approx)` is a Gram point paired with the
    certified sign coming from the `approx`, which is `0` when the sign of the true
    Z-function cannot be inferred from that of `approx`. It takes a `GramPoint`, so
    that the caller computes `gram_point(n)` separately from
    `approx(..).certified_sign()` (see `GramSearchGrid`)."""

    def __init__(self, g: GramPoint, approx: ZApproximant):
        super().__init__(g.t, approx(g.t).certified_sign())
        self.n = g.n
        self.approx = approx

    @property
    def is_good(self) -> bool:
        """The `n`th Gram point `g_n` is good if `(-1) ^ n Z(g_n) > 0`, which is
        inferred through the certified sign of the approximant. This tracks whether
        the number of zeros in `(0, g_n]` has the parity of `n + 1`."""
        return self.sign == (-1) ** self.n

    @property
    def is_good_rounded(self) -> bool:
        """Whether the Gram point is good and remains good after rounding to the
        number of decimal places imported by Lean, see `IMPORT_DP` and
        `SignedGramPoint.is_good`."""
        return (
            self.is_good
            and self.approx(round_import(self.t, self.approx.prec)).certified_sign()
            == self.sign
        )

    def next_good(self) -> "SignedGramPoint":
        """Gets the next good (after rounding) Gram point after `self`, returning
        `self` if it is already good."""
        g = self
        while not g.is_good_rounded:
            g = SignedGramPoint(GramPoint(g.n + 1), self.approx)
        return g

    def prev_good(self) -> "SignedGramPoint":
        """The last Gram point from `self` down, `self` included, that is good after
        rounding (`is_good_rounded`); stops at `g_{-1}`."""
        g = self
        while g.n > -1 and not g.is_good_rounded:
            g = SignedGramPoint(GramPoint(g.n - 1), self.approx)
        return g

    def __repr__(self):
        return f"SignedGramPoint(GramPoint({self.n}), {self.approx!r})"


class ZInterval:
    """Class encoding data required for reconstructing an input interval to an
    approximant of Hardy's Z-function, including approximant endpoints."""

    def __init__(self, lower: float, upper: float, approx: ZApproximant):
        self.lower = lower
        self.upper = upper
        self.approx = approx

    def endpoint_signs(self) -> tuple[int, int]:
        """`certified_sign` of the approximant at both endpoints."""
        return (
            self.approx(self.lower).certified_sign(),
            self.approx(self.upper).certified_sign(),
        )

    def is_sign_change(self) -> bool:
        """Whether the approximant has certified, opposite signs at the two endpoints."""
        s_lower, s_upper = self.endpoint_signs()
        if s_lower == 0 or s_upper == 0:
            raise ValueError(
                f"({self.lower}, {self.upper}): the sign at a bracket endpoint is not certified"
            )
        return s_lower != s_upper

    def params(self):
        """The approximant's parameters at both endpoints, indexed first by parameters
        and second by interval endpoint."""
        return tuple(
            chain.from_iterable(
                zip(
                    self.approx.params_at(self.lower), self.approx.params_at(self.upper)
                )
            )
        )

    def data(self):
        return (self.lower, self.upper) + self.params()

    def row(self, digits: int = DIGITS) -> str:
        return ", ".join(
            (
                f"{self.lower:.{digits}f}",
                f"{self.upper:.{digits}f}",
                *map(str, self.params()),
            )
        )

    def snap_lower(self, lower: float):
        """Returns a new interval with the same upper endpoint, but lower endpoint
        set to `lower`, checked so that it remains a sign change.

        Args:
            lower (float): new lower bound.

        Raises:
            ValueError: if the sign at an endpoint is not certified.
            RuntimeError: if the signs at the two endpoints are the same.
        """
        return ZInterval(lower, self.upper, self.approx)._checked()

    def snap_upper(self, upper: float):
        """Returns a new interval with the same lower endpoint, but upper endpoint
        set to `upper`, checked so that it remains a sign change.

        Args:
            upper (float): new upper bound.

        Raises:
            ValueError: if the sign at an endpoint is not certified.
            RuntimeError: if the signs at the two endpoints are the same.
        """
        return ZInterval(self.lower, upper, self.approx)._checked()

    def _checked(self) -> "ZInterval":
        if not self.is_sign_change():
            raise RuntimeError(
                f"[{float(self.lower)}, {float(self.upper)}]: no certified sign change"
            )
        return self

    def meet_at(self, t: float, i: "ZInterval"):
        """Makes `t` the shared endpoint between `self` and `i`. Mutates the current
        object."""
        self.upper = i.lower = t

    def bisect_zero(self, max_depth: int) -> "ZInterval":
        """Performs bisection search on a single interval if it contains a zero of
        the approximant, up to `max_depth` bisections.

        This process will eventually lose track of the zero of the Z-function if too
        many bisections occur, which happens when the precision of the resultant
        interval goes beyond the error bound of the approximant. Bisection will thus
        stop once `|approx(mid)| > SIGN_MARGIN * error(mid)` no longer holds
        (i.e., whenever `approx(mid).certified_sign()` returns `0`), after which
        bisection search tracking of the true zero is no longer safe. It therefore
        does not matter if `max_depth` is too large.

        Args:
            max_depth (int): maximum number of bisections to perform
        """
        RR = RealField(self.approx.prec)
        start, end = self.lower, self.upper
        s_start, s_end = self.endpoint_signs()
        if not s_start != s_end:
            raise ValueError(f"({start}, {end}) is not a sign-change bracket")
        for _ in range(max_depth):
            mid = (RR(start) + end) / 2
            s_mid = self.approx(mid).certified_sign()
            if s_mid == 0:
                break  # the sign at `mid` is not certified
            if s_mid == s_start:
                start = mid
            else:
                end = mid
        return ZInterval(start, end, self.approx)

    def place_boundary(
        self, snd: "ZInterval", prev: SignedPoint, cap: int
    ) -> SignedPoint:
        """Gives a boundary between the intervals `self` and `snd` where
        `self.upper <= snd.lower`. This is used to widen intervals containing zeros
        into a tiling, thereby minimising the precision. Thus the two resulting
        intervals, given by `[self.lower, boundary]` and `[boundary, snd.upper]`
        must remain certifiable zero intervals by Lean.

        The natural choice is the midpoint of `self.upper` and `snd.lower`, rounded
        to the decimal places Lean expects. This fails to be certifiable if the
        midpoint is too close to a zero for the sign to be certified. It may also
        fail if the rounding of the midpoint carries it over a zero, giving one interval
        two zeros and the other no zeros.

        Checks are performed on the initial midpoint and, if there is a failure, then
        the intervals are bisected and a new midpoint is calculated. This moves the
        midpoint closer to the true midpoint of the zeros which avoids the above two
        issues provided that the zeros are not too close. This is repeated until a
        passing boundary is found, with the number of repetitions limited by `cap`.

        This may fail if the two zeros are closer than `10^-IMPORT_DP`. Hence,
        on failure, we also increase the decimal places used in rounding, up to
        `IMPORT_DP_MAX`.

        Args:
            snd (ZInterval): the interval to interpolate with `self`, expected to
                lie above `self`.
            prev (SignedPoint): `self.lower` as a `SignedPoint`, needed to check
                the failure mode where rounding carries a boundary across a zero.
                Passing it in saves recomputing its approx value.
            cap (int): maximum number of bisection iterations per number of
                decimal places.

        Returns:
            SignedPoint: the boundary and its certified sign.

        Raises:
            ValueError: if `self` does not precede `snd`.
            RuntimeError: no boundary is found within `cap` attempts at `IMPORT_DP_MAX` places:
                the two zeros are closer than the error bound can separate, and a sharper
                approximant is needed there.
        """
        if self.upper > snd.lower:
            raise ValueError(
                f"[{self.lower}, {self.upper}] must precede [{snd.lower}, {snd.upper}]"
            )
        fst = self
        for dp in range(IMPORT_DP, IMPORT_DP_MAX + 1):
            for i in range(cap + 1):
                if i > 0:
                    fst, snd = fst.bisect_zero(2), snd.bisect_zero(2)
                t = round_import((fst.upper + snd.lower) / 2, self.approx.prec, dp)
                s = self.approx(t).certified_sign()
                if s not in (0, prev.sign):
                    return SignedPoint(t, s)
        raise RuntimeError(
            f"cannot place a boundary near t = {float(t):.6f} within {cap} tries at up to "
            f"{IMPORT_DP_MAX} decimal places: the two zeros are closer than the error bound can "
            "separate"
        )

    def __repr__(self):
        return (
            f"ZInterval(lower={self.lower!r}, upper={self.upper!r}, "
            f"approx={self.approx!r})"
        )

    def __str__(self):
        return self.row()


def coe_int(value, name: str) -> int:
    """Coerces `value` to a Python `int`, validating the type along the way.

    Args:
        value: value to coerce and validate
        name (str): name of param

    Raises:
        TypeError: if the value is not a strict integer type

    Returns:
        int: coerced value
    """
    try:
        return operator.index(value)
    except TypeError:
        raise TypeError(
            f"`{name}` must be an integer, got {type(value).__name__}"
        ) from None


def next_gram_index(T: float) -> int:
    """Gets the smallest Gram point index strictly above `T`.

    Args:
        T (float): height to search above

    Returns:
        int: index of the smallest Gram point above `T`.
    """
    # theta is increasing and by defn `theta(g_n) = n*pi`; gram indices start at -1
    # (`g_{-1} ≈ 9.67`), and `gram_point` is not real below that, so never step under it.
    n = max(-1, int(mp.siegeltheta(T) / mp.pi) - 1)
    while gram_point(n) <= T:
        n += 1
    while n > -1 and gram_point(n - 1) > T:
        n -= 1
    return n


def next_good_gram_point(T: float, approx: ZApproximant) -> SignedGramPoint:
    """Gets the smallest good Gram point strictly above `T`, as a `SignedGramPoint`.

    Args:
        T (float): height to search above.
        approx (ZApproximant): approximant used to get certified signs and define
            goodness.

    Returns:
        SignedGramPoint: smallest good Gram point strictly above `T`.
    """
    return SignedGramPoint(GramPoint(next_gram_index(T)), approx).next_good()


def prev_gram_index(T: float) -> int:
    """Gets the largest Gram point index strictly below `T`.

    Args:
        T (float): height to search below

    Returns:
        int: index of the largest Gram point below `T` (`-1` if there is none).
    """
    n = max(-1, int(mp.siegeltheta(T) / mp.pi) + 1)
    while n > -1 and gram_point(n) >= T:
        n -= 1
    while gram_point(n + 1) < T:
        n += 1
    return n


def prev_good_gram_point(T: float, approx: ZApproximant) -> SignedGramPoint:
    """Gets the largest good Gram point strictly below `T`, as a `SignedGramPoint`.

    Args:
        T (float): height to search below.
        approx (ZApproximant): approximant used to get certified signs and define
            goodness.

    Returns:
        SignedGramPoint: largest good Gram point strictly below `T`.
    """
    return SignedGramPoint(GramPoint(prev_gram_index(T)), approx).prev_good()


def adaptive_width(epsilon: float):
    """Returns the step function to create adaptive widths for zeros of the
    Riemann zeta function along the critical line. This is guided by the
    asymptotic average spacing of zeros being `2 * pi / log (t / (2 * pi))`. This
    average is shrunk by a factor of epsilon. Moreover, this is asymptotic in
    `t`, and for small values this returns negative or even undefined values;
    specifically if `t = 2 * pi` then it is undefined and for smaller values
    it is negative. Hence we lower cap `t` to `7`.

    Args:
        epsilon (float): width minimization factor; should be `< 1`.
    """

    def _adaptive_width(t):
        return epsilon * 2 * RR.pi() / (max(t, 7) / (2 * RR.pi())).log()

    return _adaptive_width
