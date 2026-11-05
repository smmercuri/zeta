import argparse
from config import PREC, RS_PREC
from euler_maclaurin.zeta_zeros import ZEulerMaclaurin
from riemann_siegel.zeta_zeros import ZRiemannSiegel
from util import ZApproximant


def _shared_flags(prec: int):
    p = argparse.ArgumentParser(add_help=False)
    g = p.add_argument_group("approximant and search")
    g.add_argument(
        "--prec", type=int, default=prec, metavar="BITS",
        help="working precision in bits (default: %(default)s)",
    )
    g.add_argument(
        "--bisection-depth", type=int, default=0, metavar="N",
        help="how many times each bracket is bisected once found; 0 for none "
        "(default: %(default)s)",
    )
    g.add_argument(
        "--epsilon", type=float, default=0.125, metavar="EPS",
        help="factor shrinking the average zero spacing into the adaptive grid's step, "
        "below 1; smaller is slower (default: %(default)s)",
    )
    g.add_argument(
        "--verbose", action=argparse.BooleanOptionalAction, default=True,
        help="print progress (default: %(default)s)",
    )
    return p


def method_subparsers(parser, parents=()):
    subs = parser.add_subparsers(dest="method", required=True, metavar="METHOD",
                                 title="methods (run `METHOD -h` for its options)")
    em = subs.add_parser(
        "euler_maclaurin", parents=[_shared_flags(PREC), *parents],
        help="the Euler–Maclaurin approximant (heights below 150)",
        description="Euler–Maclaurin approximant (heights below 150).",
    )
    g = em.add_argument_group("Euler–Maclaurin")
    g.add_argument("--b", type=float, default=1.25, help="cutoff inflation factor "
                   "(default: %(default)s)")
    g.add_argument(
        "--M",
        default="auto",
        help="Bernoulli terms: 'auto' to choose them by height, or a fixed number "
        "(default: %(default)s)",
    )
    subs.add_parser(
        "riemann_siegel", parents=[_shared_flags(RS_PREC), *parents],
        help="the Riemann–Siegel approximant (heights from 150)",
        description="Riemann–Siegel approximant (heights from 150).",
    )


def build_approx(args: argparse.Namespace) -> ZApproximant:
    """Builds a Hardy-Z approximant from parsed CLI arguments.

    Args:
        args (argparse.Namespace): parsed arguments.

    Raises:
        ValueError: if an unknown method parameter has been parsed to args.

    Returns:
        ZApproximant: constructed approximant.
    """
    if args.method == "euler_maclaurin":
        if args.M == "auto":
            M = None
        else:
            M = int(args.M)
        return ZEulerMaclaurin(M=M, b=args.b, prec=args.prec)
    if args.method == "riemann_siegel":
        return ZRiemannSiegel(args.prec)
    raise ValueError(f"unknown method {args.method!r}")
