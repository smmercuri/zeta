import pytest
import numpy as np
from sage.all import (
    zeta,
    pi,
    QQ,
    e,
    I,
    Integer,
    oo,
    integrate,
    var,
    derivative,
    ceil,
)
from euler_maclaurin.zeta_values import (
    zeta_euler_maclaurin,
    partial_zeta,
    zeta_integral_term,
    zeta_correction_term,
    zeta_error_bound,
    zeta_term_derivative,
    zeta_bernoulli_term,
    zeta_bernoulli_sum,
)
from helpers import RR, CC, assert_close, ZETA


@pytest.mark.parametrize("N", [4.5, 3.0, "5", None])
def test_non_int_partial_zeta(N):
    with pytest.raises(TypeError):
        partial_zeta(3, N)


@pytest.mark.parametrize("N", [-1, -1000])
def test_neg_partial_zeta(N):
    with pytest.raises(ValueError):
        partial_zeta(3, N)


@pytest.mark.parametrize("s", [(3 + 2 * I), -11, Integer(2), RR(pi)])
@pytest.mark.parametrize("N", [0, 3, Integer(5), 10, np.int64(10)])
def test_partial_zeta(s, N):
    assert_close(partial_zeta(s, N), sum(1 / x**s for x in range(1, N)))


def test_partial_zeta_zero():
    assert partial_zeta(2, 0) == 0


@pytest.mark.parametrize("N", [1, 2, 5, 10])
def test_partial_zeta_one(N):
    assert partial_zeta(0, N + 1) == N


def test_zeta_integral_pole():
    with pytest.raises(ValueError):
        zeta_integral_term(1, 5)


@pytest.mark.parametrize("N", [1, 2, 5, 10])
def test_zeta_integral_two(N):
    assert zeta_integral_term(2, N) == 1 / N


@pytest.mark.parametrize("s", [2, 4, QQ(3) / 2, QQ(9) / 2])
@pytest.mark.parametrize("N", [1, 2, 5, 10])
def test_zeta_integral(s, N):
    s = RR(s)
    x = var("x")
    assert_close(zeta_integral_term(s, N), integrate(x ** (-s), x, N, oo))


@pytest.mark.parametrize("N", [1, 2, 5, 10])
def test_zeta_correction_zero(N):
    assert zeta_correction_term(0, N) == 1 / 2


@pytest.mark.parametrize("d", [5.5, pi])
def test_zeta_term_derivative_non_int(d):
    with pytest.raises(TypeError):
        zeta_term_derivative(2, 2, d)


@pytest.mark.parametrize("d", [-1, -5])
def test_zeta_term_derivative_neg(d):
    with pytest.raises(ValueError):
        zeta_term_derivative(2, 2, d)


@pytest.mark.parametrize("s", [2, 4, QQ(3) / 2, QQ(9) / 2])
@pytest.mark.parametrize("N", [1, 2, 5, 10])
@pytest.mark.parametrize("d", [0, 1, 5])
def test_zeta_term_derivative(s, N, d):
    x = var("x")
    assert_close(zeta_term_derivative(s, N, d), derivative(x ** (-s), x, d)(x=N))


@pytest.mark.parametrize("k", [1.5, RR(pi)])
def test_zeta_bernoulli_non_int(k):
    with pytest.raises(TypeError):
        zeta_bernoulli_term(2, 2, k)


@pytest.mark.parametrize("k", [0, -1, -5])
def test_zeta_bernoulli_neg(k):
    with pytest.raises(ValueError):
        zeta_bernoulli_term(2, 2, k)


@pytest.mark.parametrize("s, M", [(-10, 3), (-5, 1)])
def test_bad_error_bound(s, M):
    with pytest.raises(ValueError):
        zeta_error_bound(s, 3, M)


@pytest.mark.parametrize("N", [0, -5])
def test_bad_error_bound_M(N):
    with pytest.raises(ValueError):
        zeta_error_bound(2, N, 3)


@pytest.mark.parametrize("N, M", [(5.5, 5.5), (pi, pi)])
def test_error_bound_non_int(N, M):
    with pytest.raises(TypeError):
        zeta_error_bound(2, N, M)


@pytest.mark.parametrize("M", [4.5, 3.0, "5"])
def test_non_int_bernoulli_sum(M):
    with pytest.raises(TypeError):
        zeta_bernoulli_sum(3, 3, M)


@pytest.mark.parametrize("M", [-1, -1000])
def test_neg_bernoulli_sum(M):
    with pytest.raises(ValueError):
        zeta_bernoulli_sum(3, 3, M)


def test_bernoulli_sum_one():
    assert zeta_bernoulli_sum(2, 2, 1)[0] == zeta_bernoulli_term(2, 2, 1)


@pytest.mark.parametrize("s", [1 / 2 + 14 * I, Integer(2), RR(pi)])
@pytest.mark.parametrize("N", [4, 8, 16])
def test_zeta_bernoulli_sum_auto_stops(s, N):
    _, k = zeta_bernoulli_sum(s, N)
    nxt = zeta_bernoulli_term(s, N, k + 1)
    assert abs(nxt) >= abs(zeta_bernoulli_term(s, N, k)) or nxt == 0


@pytest.mark.parametrize("M", [1, 2, 3, 5, 10])
def test_bernoulli_sum_return_idx(M):
    assert zeta_bernoulli_sum(3, 3, M)[1] == M


@pytest.mark.parametrize("N", [-1, -5])
def test_zeta_euler_maclaurin_neg(N):
    with pytest.raises(ValueError):
        zeta_euler_maclaurin(2, N, 3)


@pytest.mark.parametrize("M", [-1, -5])
def test_zeta_euler_maclaurin_neg_M(M):
    with pytest.raises(ValueError):
        zeta_euler_maclaurin(2, 2, M)


def test_zeta_euler_maclaurin_pole():
    with pytest.raises(ValueError):
        zeta_euler_maclaurin(1, 2, 2)


@pytest.mark.parametrize("N, M", [(5.5, 3), (2.5, 4), (RR(pi), 2), (5, RR(pi))])
def test_zeta_euler_maclaurin_non_int(N, M):
    with pytest.raises(TypeError):
        zeta_euler_maclaurin(2, N, M)


@pytest.mark.parametrize("s, val", ZETA.items())
def test_zeta_exact(s, val):
    N = 10
    M = max(5, ceil(-(s + 1) / 2) + 1)
    est, err = zeta_euler_maclaurin(s, N, M)
    assert abs(est - val) <= err


@pytest.mark.parametrize("t", [2, 16, pi, e, 500])
def test_zeta_critical_line(t):
    s = CC(1 / 2 + I * t)
    gt = zeta(s)
    N = 10
    M = 5
    est, err = zeta_euler_maclaurin(1 / 2 + I * t, N, M)
    assert abs(est - gt) <= err
