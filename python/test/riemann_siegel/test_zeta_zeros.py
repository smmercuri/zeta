import pytest
from sage.all import pi, zeta
from riemann_siegel.zeta_zeros import ZRiemannSiegel, Z_riemann_siegel
from search import ZeroSearch
from helpers import RR, CC, lmfdb_zeta

APPROX = ZRiemannSiegel(prec=100)


@pytest.mark.parametrize("t", [2, 7, 14.13, 21, pi, 30])
def test_Z_RS(t):
    approx, err = Z_riemann_siegel(t)
    gt = abs(zeta(CC(RR(1) / 2, RR(t))))
    assert abs(abs(approx) - gt) <= err


def test_first_zero():
    search = ZeroSearch(APPROX, 10)
    gt = lmfdb_zeta(31, 31)
    est = [z.data() for z in search.find_zeros(103, 104)]
    assert RR(est[0][0]) <= gt[0] and gt[0] <= RR(est[0][1])


def test_zeros_10():
    search = ZeroSearch(APPROX, bisection_depth=1)
    gt = lmfdb_zeta(31, 40)
    est = [z.data() for z in search.find_zeros(103, 123.5)]
    assert len(gt) == len(est)
    for i in range(len(gt)):
        assert RR(est[i][0]) <= gt[i] and gt[i] <= RR(est[i][1])


def test_zeros_500():
    search = ZeroSearch(APPROX, bisection_depth=1, epsilon=1 / 4)
    gt = lmfdb_zeta(31, 500)
    est = [z.data() for z in search.find_zeros(103, 812)]
    assert len(gt) == len(est)
    for i in range(len(est)):
        assert RR(est[i][0]) <= gt[i] and gt[i] <= RR(est[i][1])


@pytest.mark.skip()
def test_zeros_1000():
    search = ZeroSearch(APPROX, bisection_depth=1, epsilon=1 / 4)
    gt = lmfdb_zeta(31, 1000)
    est = [z.data() for z in search.find_zeros(103, 1420)]
    assert len(gt) == len(est)
    for i in range(len(est)):
        assert RR(est[i][0]) <= gt[i] and gt[i] <= RR(est[i][1])


def test_zeros_10000():
    search = ZeroSearch(APPROX)
    gt = lmfdb_zeta(31, 10000)
    est = [z.data() for z in search.find_zeros(103, 9878)]
    assert len(gt) == len(est)
    for i in range(len(est)):
        assert RR(est[i][0]) <= gt[i] and gt[i] <= RR(est[i][1])


def test_zeros_100_000():
    search = ZeroSearch(APPROX)
    gt = lmfdb_zeta(31, 100000)
    est = [z.data() for z in search.find_zeros(103, 74921)]
    assert len(gt) == len(est)
    for i in range(len(est)):
        assert RR(est[i][0]) <= gt[i] and gt[i] <= RR(est[i][1])
