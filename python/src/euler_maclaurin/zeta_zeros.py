from sage.all import (
    real_part,
    exp,
    I,
    pi,
    ComplexField,
    RealField,
    ceil,
)

from euler_maclaurin.zeta_values import zeta_euler_maclaurin
from euler_maclaurin.gamma_values import theta
from config import PREC
from util import (
    Approximation,
    ZApproximant,
)


def Z_error_bound(zeta_val, zeta_error, theta_error):
    """Propagated error bound for `Z = Re(exp(i*theta) * zeta)`. Mirrors `hardyZErrorBoundEM`
    (`Zeta/Zeros/HardyZ.lean`).

    From `|Z_approx - Z_true| <= |zeta_approx - zeta_true|
    + |theta_approx - theta_true| * |zeta_true|` and
    `|zeta_true| <= |zeta_approx| + zeta_error`, using `|e^{ia} - e^{ib}| <=
    |a - b|` for real `a, b`.

    Args:
        zeta_val: computed `zeta(1/2 + it)` approximation.
        zeta_error: error bound on `zeta_val`.
        theta_error: error bound on the `theta` approximation.

    Returns:
        bound on the Hardy `Z` error, rigorous for the exact approximant (roundoff in
        `zeta_val` is not included).
    """
    return theta_error * (abs(zeta_val) + abs(zeta_error)) + abs(zeta_error)


def Z_euler_maclaurin(t: float, N: int, M: int = None, prec: int = PREC):
    """Approximates Hardy's Z function using Euler-Maclaurin. This function
    is the phase shift of the zeta function at `1/2 + it`, so that it is real
    valued.

    Args:
        t (float): height at the critical line
        N (int): Euler-Maclaurin cut-off value
        M (int, optional): Number of Bernoulli terms. Defaults to None.
        prec (int, optional): working precision in bits. Defaults to `PREC`.

    Returns:
        (Approximation of Hardy's Z function, error bound)
    """
    CC = ComplexField(prec)
    RR = RealField(prec)
    # Construct `s = 1/2 + i t` directly; `CC(1/2 + I*t)` sends `t` through the
    # symbolic ring, which truncates it to 53 bits (see `gamma_values.theta`).
    s = CC(RR(1) / 2, RR(t))
    theta_val, theta_error = theta(t, N, M, prec)
    zeta_val, zeta_error = zeta_euler_maclaurin(s, N, M, prec)
    return Approximation(
        real_part(exp(CC(I) * theta_val) * zeta_val),
        Z_error_bound(zeta_val, zeta_error, theta_error),
    )


def adaptive_cutoff(b: float, t: float) -> int:
    """As the height `t` increases, the value of the cutoff parameter `N` should
    increase. This is guided by the fact that the remainder term in
    Euler-Maclaurin is O((|t|/(2 * pi * N)) ** (2 * M + 1)). For this to be
    small, the ratio needs to be `< 1`. Hence we can choose `N` accordingly.
    `t / (2 * pi)` represents the minimum value, but higher `N` generally
    yields better approximation, so we inflate with a factor `b` and add
    a linear factor too.

    Args:
        b (float): inflation factor
        t (float): height
    """

    return ceil(b * t / (2 * pi) + b * 50)


def adaptive_num_bernoulli(b: float, t: float):
    """Theoretically it can be seen that the optimal number of bernoulli terms
    to use, given `N`, is `N * pi`. If `N` is adaptive then we also need an
    adaptive Bernoulli term number. The default is automatic stopping
    (`zeta_bernoulli_sum` with `M=None`).
    """
    return max(20, int(pi * adaptive_cutoff(b)(t)))


class ZEulerMaclaurin(ZApproximant):
    """Hardy Z approximation using Euler-Maclaurin summation. The cut-off value
    used for choosing the tail to approximate and the number of Bernoulli terms used
    in the tail approximation can be set using constructor arguments.

    Attributes:
        name (str): used for metadata.
        cols (tuple[str, ...]): used for metadata.
    """

    name: str = "euler_maclaurin"
    cols: tuple[str, ...] = ("cutoff", "bernoulli")

    def __init__(
        self,
        N: int | None = None,
        M: int | None = None,
        b: float = 1.25,
        prec: int = PREC,
    ):
        super().__init__(prec)
        self.b = b
        self.N = N
        self.M = M

    def params_at(self, t) -> tuple:
        """The cut-off and number of Bernoulli terms used."""
        N = self.N if self.N is not None else adaptive_cutoff(self.b, t)
        return (N, self.M)

    def theta_params_at(self, t) -> tuple:
        """The same `(N, M)` drives `theta` and `zeta_euler_maclaurin`; see `Z`."""
        return self.params_at(t)

    def eval(self, t, params: tuple) -> Approximation:
        """Result of evaluating the approximant."""
        return Z_euler_maclaurin(t, *params, self.prec)

    def metadata(self):
        return {**super().metadata(), "N": self.N, "M": self.M, "b": self.b}
