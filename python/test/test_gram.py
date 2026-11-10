import pytest
from sage.all import pi, log
from config import PREC, LEHMAN_CONST
from gram import (
    get_wide_gramBlock,
    is_good_gramBlock,
    get_good_gramBlock,
)
from util import next_gram_index
from euler_maclaurin.zeta_zeros import ZEulerMaclaurin
from riemann_siegel.zeta_zeros import ZRiemannSiegel
from helpers import RR
import mpmath as mp

mp.mp.prec = PREC


@pytest.mark.parametrize("T", [1, 10, 100, 200])
def test_gram_point_above(T):
    assert mp.grampoint(next_gram_index(T)) >= T


@pytest.mark.parametrize("N", [2.4, 5.5, RR(pi)])
def test_wide_block_non_int(N):
    with pytest.raises(TypeError):
        get_wide_gramBlock(N, LEHMAN_CONST)


@pytest.mark.parametrize("N", [-2, -4, -8])
def test_wide_black_neg(N):
    with pytest.raises(ValueError):
        get_wide_gramBlock(N, LEHMAN_CONST)


@pytest.mark.parametrize("N", [2, 4, 8, 64, 128])
def test_wideness(N):
    bl = get_wide_gramBlock(N, LEHMAN_CONST)
    assert (bl.gram_upper - bl.gram_lower) / 2 > LEHMAN_CONST + 0.128 * log(
        bl.gram_upper / (2 * pi)
    )


@pytest.mark.parametrize("N", [0, 3, 10, 50])
def test_is_good_gramBlock_euler_maclaurin(N):
    bl = get_wide_gramBlock(N, LEHMAN_CONST)
    approx = ZEulerMaclaurin(M=20)
    assert is_good_gramBlock(bl, approx, 1)[0]


@pytest.mark.parametrize("T, lower, upper", [(17, 0, 3), (30, 3, 6)])
def test_get_good_gramBlock_euler_maclaurin(T, lower, upper):
    approx = ZEulerMaclaurin(M=20)
    bl, zeros = get_good_gramBlock(T, LEHMAN_CONST, approx, 1, 10)
    assert bl.lower == lower and bl.upper == upper
    assert all([len(z) > 0 for z in zeros])


@pytest.mark.parametrize("T", [30, 250, 500, 1000])
def test_get_good_gramBlock_euler_maclaurin_zeros(T):
    approx = ZEulerMaclaurin(M=20)
    bl, zeros = get_good_gramBlock(T, LEHMAN_CONST, approx, 1, 10, 1 / 8)
    assert len(zeros) == len(bl.gram_blocks)
    for i in range(len(zeros)):
        assert all(
            [
                bl.gram_blocks[i][0] <= z.lower and z.upper <= bl.gram_blocks[i][1]
                for z in zeros[i]
            ]
        )


@pytest.mark.parametrize("N", [35, 50, 100])
def test_is_good_gramBlock_riemann_siegel(N):
    bl = get_wide_gramBlock(N, LEHMAN_CONST)
    approx = ZRiemannSiegel()
    assert is_good_gramBlock(bl, approx, 1)[0]


@pytest.mark.parametrize("N", [29, 31])
def test_is_good_gramBlock_rejects_unresolved_gram_point(N):
    # `g_33 ≈ 111.131` lies within the Riemann–Siegel error bound of a zero (`|Z̃| ≈ 0.82·error`),
    # so the zero in `[g_32, g_33]` cannot be bracketed by a sign Lean could certify
    bl = get_wide_gramBlock(N, LEHMAN_CONST)
    assert bl.lower <= 32 and 33 <= bl.upper
    assert not is_good_gramBlock(bl, ZRiemannSiegel(), 1)[0]


@pytest.mark.parametrize(
    "T, lower, upper", [(105, 34, 40), (150, 52, 58), (200, 79, 86)]
)
def test_get_good_gramBlock_euler_maclaurin(T, lower, upper):
    approx = ZRiemannSiegel()
    bl, zeros = get_good_gramBlock(T, LEHMAN_CONST, approx, 1, 10)
    assert bl.lower == lower and bl.upper == upper
    assert all([len(z) > 0 for z in zeros])


@pytest.mark.parametrize("T", [250, 500, 1000])
def test_get_good_gramBlock_riemann_siegel_zeros(T):
    approx = ZRiemannSiegel()
    bl, zeros = get_good_gramBlock(T, LEHMAN_CONST, approx, 1, 10, 1 / 8)
    assert len(zeros) == len(bl.gram_blocks)
    for i in range(len(zeros)):
        assert all(
            [
                bl.gram_blocks[i][0] <= z.lower and z.upper <= bl.gram_blocks[i][1]
                for z in zeros[i]
            ]
        )
