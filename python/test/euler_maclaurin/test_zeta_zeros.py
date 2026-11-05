import pytest
from sage.all import pi, zeta
from euler_maclaurin.zeta_zeros import (
    ZEulerMaclaurin,
    Z_euler_maclaurin,
)
from search import ZeroSearch
from helpers import RR, CC, lmfdb_zeta

APPROX = ZEulerMaclaurin(M=20)


@pytest.mark.parametrize("N, M", [(4.4, 10), (5, 10.5)])
def test_Z_non_int(N, M):
    with pytest.raises(TypeError):
        Z_euler_maclaurin(1, N, M)


@pytest.mark.parametrize("N", [0, -1, -10])
def test_Z_bad_N(N):
    with pytest.raises(ValueError):
        Z_euler_maclaurin(5, N, 3)


@pytest.mark.parametrize("M", [0, -1, -10])
def test_Z_bad_M(M):
    with pytest.raises(ValueError):
        Z_euler_maclaurin(5, 2, M)


@pytest.mark.parametrize("t", [2, 7, 14.13, 21, pi, 30])
@pytest.mark.parametrize("N", [8, 16, 32])
def test_Z(t, N):
    approx, err = Z_euler_maclaurin(t, N, 20)
    gt = abs(zeta(CC(RR(1) / 2, RR(t))))
    assert abs(abs(approx) - gt) <= err


def test_first_zero():
    search = ZeroSearch(APPROX, bisection_depth=1)
    gt = lmfdb_zeta(1, 1)
    est = [z.data() for z in search.find_zeros(1, 15)]
    assert RR(est[0][0]) <= gt[0] and gt[0] <= RR(est[0][1])


def test_zeros_10():
    search = ZeroSearch(APPROX, bisection_depth=1)
    gt = lmfdb_zeta(1, 10)
    est = [z.data() for z in search.find_zeros(1, 50)]
    assert len(gt) == len(est)
    for i in range(len(gt)):
        assert RR(est[i][0]) <= gt[i] and gt[i] <= RR(est[i][1])


def test_zeros_500():
    search = ZeroSearch(APPROX, bisection_depth=1, epsilon=1 / 8)
    gt = lmfdb_zeta(1, 500)
    est = [z.data() for z in search.find_zeros(1, 812)]
    assert len(gt) == len(est)
    for i in range(len(est)):
        assert RR(est[i][0]) <= gt[i] and gt[i] <= RR(est[i][1])


def test_zeros_1000():
    search = ZeroSearch(APPROX, bisection_depth=1, epsilon=1 / 8)
    gt = lmfdb_zeta(1, 1000)
    est = [z.data() for z in search.find_zeros(1, 1420)]
    assert len(gt) == len(est)
    for i in range(len(est)):
        assert RR(est[i][0]) <= gt[i] and gt[i] <= RR(est[i][1])
