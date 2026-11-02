from sage.all import (
    QQ,
    pi,
    RealField,
    cos,
    var,
    diff,
    fast_callable,
)
from euler_maclaurin.gamma_values import theta
from config import PREC, RS_MIN_HEIGHT, RS_THETA_BERNOULLI, RS_THETA_CUTOFF
from util import (
    Approximation,
    ZApproximant,
)
from functools import lru_cache

_z = var("z")
_PSI_D3 = diff(cos(2 * pi * (_z**2 - _z - 1 / 16)) / cos(2 * pi * _z), _z, 3)


@lru_cache(maxsize=None)
def _psi_d3(prec: int):
    """Compiled third derivative of the Riemann-Siegel correction kernel."""
    return fast_callable(_PSI_D3, vars=[_z], domain=RealField(prec))


#: `log n` and `√n` for `n = 1, 2, …` at each working precision, grown on demand. They are
#: independent of `t`, so each process computes them once.
_LOG_SQRT: dict[int, tuple[list, list]] = {}


def _log_sqrt_table(N: int, prec: int) -> tuple[list, list]:
    """`log n` and `√n` for `n = 1..N` (at least) at precision `prec`."""
    logs, sqrts = _LOG_SQRT.setdefault(prec, ([], []))
    RR = RealField(prec)
    for n in range(len(logs) + 1, N + 1):
        logs.append(RR(n).log())
        sqrts.append(RR(n).sqrt())
    return logs, sqrts


def Z_RS_main_sum(t: float, prec: int = PREC) -> RealField:
    """The main sum of the Riemann-Siegel approximation of Hardy's Z-function.

    Args:
        t (float): approximant input.
        prec (int, optional): working precision. Defaults to PREC.

    Returns:
        RealField: Riemann-Siegel main sum
    """
    RR = RealField(prec)
    T = t / (2 * RR.pi())
    N = T.sqrt().floor()
    theta_val, _ = theta(t, RS_THETA_CUTOFF, RS_THETA_BERNOULLI, prec)
    logs, sqrts = _log_sqrt_table(int(N), prec)
    return 2 * sum((theta_val - t * logs[n]).cos() / sqrts[n] for n in range(int(N)))


def Z_RS_correction(t: float, prec: int = PREC) -> RealField:
    """The zeroth-order correction term of Riemann-Siegel in its closed form. The closed
    form has removable singularities whenever the fractional
    part of `(t / (2 * pi)).sqrt()` if `1/4` or `3/4`, taking values `1/2` there.

    Args:
        t (float): approximant input.
        prec (int, optional): working precision. Defaults to PREC.

    Returns:
        RealField: zeroth-order correction term.
    """
    RR = RealField(prec)
    T = t / (2 * RR.pi())
    N = T.sqrt().floor()
    p = T.sqrt() - N
    if p == 1 / 4 or p == 3 / 4:
        # singularity val via L'Hopital
        return RR(1) / 2
    return (2 * RR.pi() * (p**2 - p - RR(1) / 16)).cos() / (2 * RR.pi() * p).cos()


def Z_RS_C1(t: float, prec: int = PREC) -> RealField:
    """First-order correction term of Riemann-Siegel in its closed form.
    This has removable singularities whenever the fractional
    part of `(t / (2 * pi)).sqrt()` if `1/4` or `3/4`, taking values `(-)1/96` there.

    Args:
        t (float): approximant input.
        prec (int, optional): working precision. Defaults to PREC.

    Returns:
        RealField: first-order correction term.
    """
    RR = RealField(prec)
    T = RR(t) / (2 * RR.pi())
    N = T.sqrt().floor()
    p = T.sqrt() - N
    if p == RR(1) / 4:
        # singularity
        return RR(1) / 96
    if p == RR(3) / 4:
        return -RR(1) / 96

    return RR(-_psi_d3(prec)(p) / (96 * RR.pi() ** 2))


def Z_RS_error_bound(t: float, prec: int = PREC) -> RealField:
    """Error bound for first-order Riemann-Siegel approximation. Mirrors `hardyZErrorBoundRS`
    (`Zeta/RiemannSiegel/Defs.lean`).

    Args:
        t (float): approximant input.
        prec (int, optional): working precision. Defaults to PREC.

    Returns:
        RealField: first-order Riemann-Siegel error bound.
    """
    RR = RealField(prec)
    T = t / (2 * RR.pi())
    return RR(25) / 4 * T ** (RR(-5) / 4) + RR(1) / 32 * T ** (RR(-15) / 4)


def Z_riemann_siegel(t: float, prec: int = PREC) -> Approximation:
    """First-order Riemann-Siegel summation for Hardy's Z-function.

    Args:
        t (float): approximant input.
        prec (int, optional): working precision. Defaults to PREC.

    Returns:
        Approximation: First-order Riemann-Siegel approximation and error bound.
    """
    RR = RealField(prec)
    t = RR(t)
    T = t / (2 * RR.pi())
    N = T.sqrt().floor()
    approx = Z_RS_main_sum(t, prec) - (-1) ** N / T.nth_root(4) * (
        Z_RS_correction(t, prec) + Z_RS_C1(t, prec) / T.sqrt()
    )
    return Approximation(
        approx,
        Z_RS_error_bound(t, prec),
    )


class ZRiemannSiegel(ZApproximant):
    """Hardy Z approximation using first-order Riemann-Siegel summation, with
    Euler-Maclaurin approximation of the theta function using the first two
    terms.

    Attributes:
        name (str): used for metadata.
        cols (tuple[str, ...]): used for metadata.
    """

    name = "riemann_siegel"
    cols = ()

    def params_at(self, t):
        return ()

    def theta_params_at(self, t):
        """Fixed: the Riemann-Siegel phase is the order-`2` Stirling approximant of `theta`,
        independent of the height."""
        return (RS_THETA_CUTOFF, RS_THETA_BERNOULLI)

    def eval(self, t, params):
        """Result of evaluating the approximant"""
        if RealField(self.prec)(t).exact_rational() < QQ(RS_MIN_HEIGHT):
            raise ValueError(
                f"Riemann-Siegel error bound requires t >= {RS_MIN_HEIGHT} (> 32π), got {t}"
            )
        return Z_riemann_siegel(t, self.prec)
