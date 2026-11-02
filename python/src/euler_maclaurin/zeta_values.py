from sage.all import (
    bernoulli,
    QQ,
    rising_factorial,
    real_part,
    factorial,
    ComplexField,
    RealField,
)

from config import PREC
from util import Approximation, coe_int


def partial_zeta(s, N: int):
    """Computes the partial zeta sum `1/n^s` from `n = 1` to `n = N - 1`, where
    `s` may be complex.

    Args:
        s: zeta function input
        N (int): partial sum upper limit (exclusive)

    Returns:
        Element: sum of `1/n ** s` from `n = 1` to `n = N - 1`

    Raises:
        TypeError: If `N` is not an integer
        ValueError: If `N` is negative.
    """
    N = coe_int(N, "N")
    if N < 0:
        raise ValueError(f"input `N` must be a non-negative integer, got {N}")
    return sum(1 / x**s for x in range(1, N))


def zeta_integral_term(s, N):
    """Computes the value of the integral of `1/x ** s` from `N`
    to infinity, valid for `Re(s) > 1`, and the anlaytic continutation for `Re(s) <= 1`.
    Has a pole when `s = 1`.

    Args:
        s: zeta function input
        N (int): lower integral limit

    Returns:
        closed form expression `N ** (1 - s) / (s - 1)` of the
          integral from `N` to infinity of `1/x ** s`
    """
    if s == 1:
        raise ValueError(f"Received `s` = {s}, which is a pole.")
    return N ** (1 - s) / (s - 1)


def zeta_correction_term(s, N: int):
    """Euler-Maclaurin correction term. This is the average of the endpoints.
    For application to the zeta function the endpoints are `N` and infinity,
    which latter vanishes, leaving `1/(2 * N ** s)`.

    Args:
        s: zeta function input
        N (int): lower endpoint

    Returns:
        correction term `1/(2 * N ** s)`
    """
    return 1 / (2 * N**s)


def zeta_term_derivative(s, N, d: int):
    """value of the `d`th derivative of `1/x ** s` at `x = N`, where 
    `d` is a non-negative integer.

    Args:
        s: zeta function input
        N (int): value to use in the derivative
        d (int): degree of derivative

    Returns:
        value of the `d`th derivative of `1/x ** s` at `x = N`.

    Raises:
        TypeError: if `d` is not an integer
        ValueError: if `d` is negative.
    """
    d = coe_int(d, "d")
    if d < 0:
        raise ValueError(f"`d` must be non-negative, got {d}")
    return (-1) ** d * rising_factorial(s, d) * N ** (-s - d)


def zeta_bernoulli_term(s, N, k: int):
    """the `k`th Bernoulli term appearing in the Euler-Maclaurin summation
    formula for the zeta function. This is
    `-bernoulli(2*k) / factorial(2 * k) * zeta_term_derivative(s, N, 2 * k - 1)`

    Args:
        s: zeta function input
        N (int): derivative input
        k (int): index of the Bernoulli term

    Returns:
        `-bernoulli(2*k) / factorial(2 * k) *
          zeta_term_derivative(s, N, 2 * k - 1)`

    Raises:
        TypeError: if `k` is not an integer
        ValueError: if `k < 1`.
    """
    k = coe_int(k, "k")
    if k < 1:
        raise ValueError(f"`k` must be at least 1, got {k}")
    return -bernoulli(2 * k) / factorial(2 * k) * zeta_term_derivative(s, N, 2 * k - 1)


def zeta_error_bound(s, N: int, M: int, prec: int = PREC):
    """A bound for the error term in Euler-Maclaurin summation, valid when
    the real part of `s` is `> -2*M - 1` and `N > 0`. See section 3 of
    https://cr.yp.to/bib/2000/borwein.pdf for a reference. Mirrors `zetaRemainderBound`
    (`Zeta/EulerMaclaurin/ErrorBound.lean`).

    Args:
        s: zeta function input
        N (int): Euler-Maclaurin cutoff value
        M (int): number of Bernoulli terms used
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns:
        `abs((s + 2 * M + 1) / (real_part(s) + 2 * M + 1) *
          bernoulli_term(s, N, M + 1))`

    Raises:
        ValueError: if `Re(s) + 2 * N + 1` is non-positive.
        ValueError: if `N` is not at least `1`.
        TypeError: if `N` or `M` are not integers.
    """
    RR = RealField(prec)
    x = RR(real_part(s) + 2 * M + 1)
    if x <= 0:
        raise ValueError(f"Error bound is only valid for `Re(s) + 2 * M + 1 > 0`, got {real_part(s) + 2 * M + 1}")
    N, M = coe_int(N, "N"), coe_int(M, "M")
    if N <= 0:
        raise ValueError(f"Error bound is only valid for `N >= 1`, got {N}.")
    return RR(
        abs((s + 2 * M + 1) / (real_part(s) + 2 * M + 1) * zeta_bernoulli_term(s, N, M + 1))
    )


def zeta_bernoulli_sum(s, N: int, M: int = None):
    """Bernoulli sum appearing in the Euler-Maclaurin summation. This is
    essentially just the sum of `bernoulli_term` for `k = 1` to `k = M`.

    However, this function provides an adaptive stopping criteria. Notably, the
    bernoulli terms do not continue to decrease and eventually blow up. So for
    a given `N` there is an optimal number of terms `M` to use. Theoretically
    this is given at approximately `pi * N`, but here if `M=None` we just check
    whether consecutive terms have begun to increase at which point we
    automatically stop.

    Args:
        s: zeta function input
        N (int): cut-off value in Euler-Maclaurin
        M (int, optional): number of Bernoulli terms to use; if `None` then
        automatic stopping is employed. Defaults to None.

    Returns:
        Sum of Bernoulli terms.

    Raises:
        TypeError: If `M` is supplied and it is not an integer.
        ValueError: If `M` is supplied and it is non-positive.
    """
    if M is not None:
        M = coe_int(M, "M")
        if M < 1:
            raise ValueError(f"input `M` must be a positive integer, got {M}")
        return sum(zeta_bernoulli_term(s, N, k) for k in range(1, M + 1)), M
    else:
        total, k = 0, 1
        curr = zeta_bernoulli_term(s, N, k)
        while True:
            nxt = zeta_bernoulli_term(s, N, k + 1)
            total += curr
            if abs(nxt) >= abs(curr) or nxt == 0:
                break
            k += 1
            curr = nxt
        return total, k


def zeta_euler_maclaurin(s, N: int, M: int = None, prec: int = PREC):
    """The Euler-Maclaurin summation approximation of the zeta function at `s`.
    This computes the formula with a cut-off value of `N` with `M` Bernoulli
    terms (if provided). If `M` is not provided, then automatic stopping is
    employed.

    Args:
        s: zeta function input
        N (int): cut-off value
        M (int, optional): number of Bernoulli terms; if `None` then automatic
          stopping is employed. Defaults to None.
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns:
        Euler-Maclaurin approximation of the zeta function.

    Raises:
        ValueError: if `s = 1`, giving a pole of the zeta function.
        TypeError: if `N` or `M` are non-integral
        ValueError: if `N` or `M` are negative
    """
    CC = ComplexField(prec)
    try:
        s = QQ(s)
    except (TypeError, ValueError):
        s = CC(s)
    bernoulli_terms, M = zeta_bernoulli_sum(s, N, M)
    val = partial_zeta(s, N) + zeta_integral_term(s, N) + zeta_correction_term(s, N) + bernoulli_terms
    return Approximation(val, zeta_error_bound(s, N, M, prec))
