from sage.all import bernoulli, log, pi, imag_part, I, ComplexField, RealField, factorial, real_part, ZZ
from config import PREC
from util import Approximation, coe_int


def partial_log_gamma(s, N: int, prec: int = PREC):
    """Computes the shifting factor in the relation between `log(Gamma(s))` and
    `log(Gamma(s + N))

    Args:
        s: log-Gamma input
        N (int): log-Gamma shift factor
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns:
        the sum of `log(s - 1 + k)` from `k = 1` to `k = N`

    Raises:
        TypeError: If `N` is not an integer.
        ValueError: If `N` is negative.
        ValueError: if `N` and `s` are such that a zero occurs 
            in the sum, yielding a pole of `log`.
    """
    N = coe_int(N, "N")
    if N < 0:
        raise ValueError(f"input `N` must be a non-negative integer, got {N}")
    CC = ComplexField(prec)
    z = CC(s)
    if z.imag_part().is_zero() and z.real_part() in ZZ and 1 - N <= z.real_part() <= 0:
        raise ValueError(
            f"`s` = {s} and `N` = {N} are such that one of the summands `log(s - 1 + k)` is "
            f"a pole due to a zero input to `log`."
        )
    return sum(log(CC(s) - 1 + k) for k in range(1, N + 1))


def integral_term(s, N: int, prec: int = PREC):
    """Computes the value of the integral of `log(x)` from `1` to `s + N - 1`.

    Args:
        s: integral upper limit
        N (int): shifting value
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns:
        `1` if `s + N - 1 = 0` else  `(s + N - 1) * log(s + N - 1) - s - N + 2`
    """
    CC = ComplexField(prec)
    z = CC(s) + N - 1
    if z.is_zero():
        return CC(1)
    return z * log(z) - s - N + 2


def correction_term(s, N: int, prec: int = PREC):
    """Euler-Maclaurin correction term; average of the endpoints (here `1`
    and `s + N - 1`). The former vanishes.

    Args:
        s: log-Gamma input
        N (int): cut-off
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns:
        `log(s + N - 1) / 2`

    Raises:
        ValueError: if `s` and `N` are such that `s + N - 1 = 0`, yielding a pole.
    """
    CC = ComplexField(prec)
    z = CC(s) + N - 1
    if z.is_zero():
        raise ValueError(f"`s` = {s}, `N` = {N} give `s + N - 1 = 0` which is a pole of `log`.")
    return log(z) / 2


def integral_shifting_term(prec: int = PREC):
    """integral-shifting term used to make the Euler-Maclaurin integrals
    converge.

    Args:
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns:
        `log(2 * pi) / 2 - 1`
    """
    CC = ComplexField(prec)
    return log(CC(2 * pi)) / 2 - 1


def gamma_bernoulli_term(s, N: int, k: int, prec: int = PREC):
    """Individual `k`th Bernoulli term appearing in the Euler-Maclaurin
    summation of log-Gamma.

    Args:
        s: log-Gamma input
        N (int): cut-off value
        k (int): Bernoulli term index
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns:
        `bernoulli(2 * k) / (2 * k * (2 * k - 1)) * (s + N - 1) ** (2 * k - 1)`

    Raises:
        TypeError: If `k` is not an integer
        ValueError: If `k < 1` or `s + N - 1 == 0`.
    """
    k = coe_int(k, "k")
    if k < 1:
        raise ValueError(f"`k` must be at least 1, got {k}")
    CC = ComplexField(prec)
    z = CC(s) + N - 1
    if z.is_zero():
        raise ValueError(f"`s` = {s}, `N` = {N} gives zero division with `s + N - 1`.")
    return CC(bernoulli(2 * k) / (2 * k * (2 * k - 1) * z ** (2 * k - 1)))


def log_gamma_error_bound(s, N: int, M: int, prec: int = PREC):
    """Error bound for Euler-Maclaurin applied to the log-Gamma function, valid 
    when `Re(s) + N - 1 > 0`.

    Args:
        s: input to log-Gamma
        N (int): Euler-Maclaurin shifting value
        M (int): number of Bernoulli terms used
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns: float; error bound

    Raises:
        ValueError: if `Re(s) + N - 1` is non-positive.
        ValueError: if `M` is not at least `1`.
        TypeError: if `N` or `M` are not integers.
    """
    RR = RealField(prec)
    x = RR(real_part(s) + N - 1)
    if x <= 0:
        raise ValueError(f"Error bound is only valid for `Re(s) + N - 1 > 0`, got {real_part(s) + N - 1}")
    M, N = coe_int(M, "M"), coe_int(N, "N")
    if M < 1:
        raise ValueError(f"Error bound only valid for `M` at least one, got {M}")
    return factorial(2 * M + 1) / (2 * M * (2 * RR(pi)) ** (2 * M)) * RR(real_part(s) + N - 1) ** (-2 * M)


def gamma_bernoulli_sum(s, N: int, M: int = None, prec: int = PREC):
    """Returns the sum over the first `M` Bernoulli terms for `log-Gamma`,
    together with the number of terms used. Employs automatic stopping if
    `M=None`.

    The automatic stopping halts where the *error bound* `gamma_error_bound`
    is minimised. The terms decay with the modulus `|s + N - 1|` (smallest near
    `k ~ pi * |s + N - 1|`), whereas the provable bound decays with the real part
    `Re(s) + N - 1` (smallest near `k ~ pi * (Re(s) + N - 1)`). For inputs with
    large imaginary part the terms keep shrinking after the bound has begun to
    grow, so the stopping rule follows the bound.

    Args:
        s: log-Gamma input
        N (int): cutoff value
        M (int, optional): number of Bernoulli terms to use; automatic stopping
          is employed if `None`. Defaults to None.
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns:
        `(sum over the first M Bernoulli terms, the number of terms M)`

    Raises:
        TypeError: If `M` is supplied and it is not an integer.
        ValueError: If `M` is supplied and it is non-positive.
    """
    if M is not None:
        M = coe_int(M, "M")
        if M < 1:
            raise ValueError(f"input `M` must be a positive integer, got {M}")
        return sum(gamma_bernoulli_term(s, N, k, prec) for k in range(1, M + 1)), M
    else:
        total, k = 0, 1
        curr_bound = log_gamma_error_bound(s, N, k, prec)
        while True:
            total += gamma_bernoulli_term(s, N, k, prec)
            next_bound = log_gamma_error_bound(s, N, k + 1, prec)
            if next_bound >= curr_bound:
                break
            k += 1
            curr_bound = next_bound
        return total, k


def log_gamma_euler_maclaurin(s, N: int, M: int = None, prec: int = PREC):
    """The Euler-Maclaurin summation approximation of the log-Gamma function
    at `s`. This computes the formula with a cut-off value of `N` with `M`
    Bernoulli terms (if provided). If `M` is not provided, then automatic
    stopping is employed.

    Here the cutoff value shifts the domain of convergence for input values `s`.
    If `N = 0` is used (i.e., no cutoff) then the
    approximation only works for `Re(s) - 1 > 0`. To
    extend this, one uses the formula
    `Gamma(s + N)) = s * (s + 1)...(s + N - 1) * Gamma(s)` to shift so that 
    `Re(s) + N - 1 > 0`.

    Args:
        s: log-Gamma input
        N (int): cutoff value.
        M (int, optional): number of Bernoulli terms. Defaults to None.
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns:
        Approximation: approximation + error of log-Gamma with Euler Maclaurin
    
    Raises:
        ValueError: if `s` is a non-positive integer, giving a pole of `Gamma`.
        TypeError: if `N` or `M` are non-integral
        ValueError: if `N` or `M` are negative
    """
    s = ComplexField(prec)(s)
    if s.imag_part().is_zero() and s.real_part() in ZZ and s.real_part() <= 0:
        raise ValueError(f"`s` = {s} is a pole of Gamma.")
    if real_part(s) + N - 1 <= 0:
        raise ValueError(f"Approximation requires `Re(s) + N - 1 > 0`, got {real_part(s) + N - 1}")
    bernoulli_terms, M = gamma_bernoulli_sum(s, N, M, prec)
    val = (
        integral_term(s, N, prec) + correction_term(s, N, prec)
        + integral_shifting_term(prec) + bernoulli_terms
        - partial_log_gamma(s, N, prec)
    )
    return Approximation(val, log_gamma_error_bound(s, N, M, prec))


def theta_error_bound(N: int, M: int = None, prec: int = PREC): 
    """Error bound for the Riemann-Siegel theta function when approximated 
    using Euler-Maclaurin

    Args:
        N (int): Euler-Maclaurin cutoff value
        M (int, optional): number of Bernoulli terms. Defaults to None.
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns: float; error bound

    Raises:
        TypeError: if `N` or `M` are not integers.
        ValueError: if `N - 3/4` is non-positive or `M` is not positive.
    """
    RR = RealField(prec)
    x = RR(N - 3/4)
    if x <= 0:
        raise ValueError(f"`theta_error_bound` is only valid for `N - 3/4 > 0`, got {N - 3/4}")
    if M is not None:
        M = coe_int(M, "M")
        if M < 1:
            raise ValueError(f"Error bound only valid for `M` at least one, got {M}")
    N = coe_int(N, "N")
    return factorial(2 * M + 1) / (2 * M * (2 * RR(pi)) ** (2 * M)) * x ** (-2 * M)


def theta(t, N: int, M: int = None, prec: int = PREC):
    """Hardy Z-function phase shifting function. This is the phase one
    multiplies zeta(1/2 + it) such that it is real. It can be expressed as the
    imaginary part of `log-Gamma(-3/4 + t*I/2 + 1) - t * log(pi) / 2`. Hence
    we use Euler-Maclaurin to approximate it.

    Args:
        t: height along the critical line
        N (int): cutoff value
        M (int, optional): number of Bernoulli terms. Defaults to None.
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns:
        Approximation of the phase of `zeta(1/2 + it)`.
    """
    RR = RealField(prec)
    s = ComplexField(prec)(RR(1) / 4, RR(t) / 2)
    _, M = gamma_bernoulli_sum(s, N, M, prec)
    val = RR(imag_part(log_gamma_euler_maclaurin(s, N, M, prec).val) - RR(t) / 2 * RR(pi).log())
    return Approximation(val, theta_error_bound(N, M, prec))
