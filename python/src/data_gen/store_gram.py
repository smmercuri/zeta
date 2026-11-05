import json
import argparse
import math
from pathlib import Path
from itertools import chain

from collections.abc import Callable

from config import OUT_DIR, LEHMAN_CONST, DIGITS
from gram import get_good_gramBlock, GramBlock
from data_gen.store_zeros import write_rows
from util import ZInterval, ZApproximant
from approximants import method_subparsers, build_approx

THETA_COLS = ("theta_cutoff", "theta_bernoulli")


#: Theta error the gram brackets are certified against. The emitter widens every bracket
#: outward to `GRAM_WIDEN_DP` places (`config.py`), so the certified margin is at
#: least `theta'(t) · 1e-5 ≥ 2e-5` above `168π`, and `gram_bound`'s working resolution is
#: `1/D = 3e-7/t`; `1e-10` sits well below both at every height.
THETA_TARGET = 1e-10


def theta_stirling_error(t: float, N: int, M: int) -> float:
    """Mirrors `riemannSiegelThetaStirlingErrorBound' M N t` (`Zeta/Zeros/HardyZ.lean`), the Lean
    bound on `|theta(t) - theta_{M,N}(t)|`:

        (2M+1)! 2^{2M+1} / (2M (2π)^{2M}) · ((1/4 + N)² + t²/4)^{-M}

    `N` is the Stirling *shift* in Lean's convention (argument `1/4 + N + it/2`), not the
    `euler_maclaurin.gamma_values.theta` cutoff, which is one larger. With the modulus in the
    base the bound decays like `t^{-2M}`, so `N = 0` and a small `M` serve at every height.
    """
    return (
        math.factorial(2 * M + 1) * 2 ** (2 * M + 1) / (2 * M * (2 * math.pi) ** (2 * M))
        * ((0.25 + N) ** 2 + (t / 2) ** 2) ** (-M)
    )


def theta_params_rule(
    N: Callable[[float], int] | int | None = None,
    M: Callable[[float], int] | int | None = None,
    target: float = THETA_TARGET,
):
    """Stirling parameters for bracketing a gram point, as a rule in the height `t`.

    Independent of the approximant that certifies the *zeros*: bracketing `g_n` is a question
    about `theta`, and `riemannSiegelThetaApproximant` needs Stirling orders whichever method
    found the zeros around it. The parameters are chosen by inverting
    `theta_stirling_error`: the shift `N` defaults to `0`, and `M` to the smallest order whose
    bound at `t` is below `target` — `M = 2` from `~530` up, `M = 3` from `~130` up. Every
    gram-point certificate then carries `N` certified `log` terms, so the shift must not grow
    with the height; the old `(1/4 + N)^{-2M}` bound forced `N ≈ 1.25·t/(2π)`.

    Args:
        N (Callable[[float], int] | int, optional): shift at height `t`; a bare `int` is
          broadcast to a constant rule. Defaults to `0`.
        M (Callable[[float], int] | int, optional): Bernoulli terms at height `t`. Defaults to
          the smallest order meeting `target`.
        target (float, optional): theta error to certify against. Defaults to `THETA_TARGET`.

    Raises:
        ValueError: if no `M ≤ 20` meets `target` at some height (the series is asymptotic:
          past the optimal order the bound grows again, so a larger `M` cannot compensate).
    """
    N = 0 if N is None else N
    shift = N if callable(N) else (lambda _: N)

    def smallest_order(t):
        n = shift(t)
        for m in range(1, 21):
            if theta_stirling_error(t, n, m) <= target:
                return m
        raise ValueError(
            f"no Stirling order M ≤ 20 brings the theta error at t = {t} (shift {n}) below "
            f"{target}; raise the shift or the target"
        )

    if M is None:
        bernoulli = smallest_order
    else:
        bernoulli = M if callable(M) else (lambda _: M)
    return lambda t: (shift(t), bernoulli(t))


class Manifest:
    """Packaging data for generating the `gram/manifest.json` file."""

    def __init__(
        self,
        approx: ZApproximant,
        height: float,
        params,
        gram_points: list[tuple[int, ZInterval]],
        lehman_const: float,
    ):
        self.approx = approx
        self.height = height
        self.gram_cols = ("idx",) + ZApproximant.row_cols_of(THETA_COLS)
        self.zero_cols = ("idx",) + approx.row_cols
        self.params = params
        self.gram_points = gram_points
        self.lehman_const = lehman_const

    def to_dict(self):
        return {
            "height": self.height,
            "Lehman constant": self.lehman_const,
            "gram_cols": self.gram_cols,
            "zero_cols": self.zero_cols,
            "params": self.params,
            "zeros_map": {
                f"{idx}": f"zeros_{idx}.txt" for idx, _ in self.gram_points[:-1]
            },
        }

    def write(self):
        out = Path(f"{OUT_DIR}/{self.approx.name}/gram/manifest.json").expanduser()
        with open(out, "w") as f:
            json.dump(self.to_dict(), f, indent=2)


def prune_stale_zeros(approx: ZApproximant, keep: set[str]):
    """Delete the `zeros_<idx>.txt` files left behind by earlier runs.

    The gram store holds exactly one gram block, so any zero file not named in the
    current manifest's `zeros_map` is orphaned. Pruning is not merely tidiness:
    `gen_gram_certificates.parse_zeros` falls back to the `zeros_<idx>.txt` naming
    convention when an index is absent from `zeros_map`, so a stale file can be read
    silently into the generated Lean. Called only after the new block is fully
    written, so a run that fails partway leaves the previous store intact.

    Args:
        keep (set[str]): file names of the current run, i.e. the `zeros_map` values.
    """
    out_dir = Path(f"{OUT_DIR}/{approx.name}/gram").expanduser()
    for path in out_dir.glob("zeros_*.txt"):
        if path.name not in keep:
            path.unlink()


class GramInterval(ZInterval):
    """A bracket around a Gram point. Its row carries the Stirling parameters `theta_params` at
    each endpoint, which certify `theta` there, rather than the approximant's parameters."""

    def __init__(self, lower, upper, theta_params):
        super().__init__(lower, upper, approx=None)
        self.theta_params = theta_params

    def params(self):
        return tuple(
            chain.from_iterable(
                zip(self.theta_params(self.lower), self.theta_params(self.upper))
            )
        )


def gram_rows(bl: GramBlock, theta_params) -> list[tuple[int, GramInterval]]:
    return [
        (gp[0], GramInterval(gp[2], gp[3], theta_params))
        for gp in bl.gram_intervals()
    ]


def store_gram(
    T: float,
    approx: ZApproximant,
    bisection_depth: int,
    lehman_const: float = LEHMAN_CONST,
    gram_cap: int = 1000,
    epsilon: float = 1 / 4,
    digits: int = DIGITS,
    theta_params=None,
):
    bl, zeros = get_good_gramBlock(
        T=T,
        lehman_const=lehman_const,
        approx=approx,
        bisection_depth=bisection_depth,
        gram_cap=gram_cap,
        epsilon=epsilon,
    )
    theta_params = theta_params or theta_params_rule()
    params = approx.metadata() | {
        "bisection_depth": bisection_depth,
        "epsilon": epsilon,
        # The theta parameterisation is not the approximant's; record it so a store says
        # which Stirling orders its gram brackets were certified with.
        "theta_at_height": dict(zip(THETA_COLS, map(str, theta_params(T)))),
    }
    rows = gram_rows(bl, theta_params)
    write_rows(rows, f"{OUT_DIR}/{approx.name}/gram/gram_block.txt", digits)

    for (idx, _), zs in zip(rows, zeros):
        write_rows(
            [(i + 1, z) for i, z in enumerate(zs)],
            f"{OUT_DIR}/{approx.name}/gram/zeros_{idx}.txt",
            digits,
        )

    manifest = Manifest(approx, T, params, rows, lehman_const)
    manifest.write()
    prune_stale_zeros(approx, set(manifest.to_dict()["zeros_map"].values()))
    return bl


def gram_opts():
    p = argparse.ArgumentParser(add_help=False)
    g = p.add_argument_group("Gram block")
    g.add_argument(
        "--lc",
        type=float,
        default=LEHMAN_CONST,
        metavar="A",
        help="additive constant in Lehman's bound (default: %(default)s)",
    )
    g.add_argument(
        "--gram-cap",
        type=int,
        default=1000,
        metavar="N",
        help="how many times the Gram block search moves up after a failed block "
        "(default: %(default)s)",
    )
    g.add_argument(
        "--theta-N",
        type=int,
        default=None,
        metavar="N",
        help="theta Stirling shift at a gram bracket (default: 0)",
    )
    g.add_argument(
        "--theta-M",
        type=int,
        default=None,
        metavar="M",
        help="theta Bernoulli terms at a gram bracket (default: the smallest order whose "
        "error bound clears THETA_TARGET at the height)",
    )
    return p


def gram_flags():
    p = argparse.ArgumentParser(add_help=False, parents=[gram_opts()])
    p.add_argument("T", type=float, help="lower height bound")
    return p


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Find and store a good gram block from `T`. This is a sequence of "
        "gram points which is sufficiently narrow and contain at least one zeta zero "
        "between each."
    )
    method_subparsers(parser, parents=[gram_flags()])
    args = parser.parse_args()
    approx = build_approx(args)
    store_gram(
        args.T,
        approx,
        args.bisection_depth,
        args.lc,
        args.gram_cap,
        args.epsilon,
        theta_params=theta_params_rule(N=args.theta_N, M=args.theta_M),
    )
    print(f"stored gram block -> {OUT_DIR}/{approx.name}/gram/")
