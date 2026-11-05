import pytest
from sage.all import (
    pi,
    QQ,
    I,
    RealField,
    ComplexField,
    Integer,
    log,
    exp,
    log_gamma,
    imag_part,
)
from config import PREC
from euler_maclaurin.gamma_values import (
    partial_log_gamma,
    correction_term,
    integral_term,
    integral_shifting_term,
    log_gamma_error_bound,
    log_gamma_euler_maclaurin,
    gamma_bernoulli_sum,
    gamma_bernoulli_term,
    theta,
    theta_error_bound,
)
from helpers import RR, CC, STIRLING, assert_close
import numpy as np


@pytest.mark.parametrize("N", [4.5, 3.0, "5", None])
def test_non_int_partial_gamma(N):
    with pytest.raises(TypeError):
        partial_log_gamma(3, N)


@pytest.mark.parametrize("N", [-1, -1000])
def test_neg_partial_gamma(N):
    with pytest.raises(ValueError):
        partial_log_gamma(3, N)


@pytest.mark.parametrize("N", [5, 6, 7, 10])
def test_pole_partial_gamma(N):
    with pytest.raises(ValueError):
        partial_log_gamma(-4, N)


@pytest.mark.parametrize("s", [(3 + 2 * I), -11, Integer(2), RR(pi)])
@pytest.mark.parametrize("N", [0, 3, Integer(5), 10, np.int64(10)])
def test_partial_gamma(s, N):
    assert_close(
        partial_log_gamma(s, N), sum(log(CC(s) - 1 + k) for k in range(1, N + 1))
    )


def test_integral_term_one():
    assert integral_term(1, 1) == 0


@pytest.mark.parametrize("s", [(3 + 2 * I), -4, Integer(2), RR(pi)])
@pytest.mark.parametrize("N", [0, 3, Integer(5), 10, np.int64(10)])
def test_integral_term_shift(s, N):
    assert_close(integral_term(s, N), integral_term(s + 1, N - 1))


@pytest.mark.parametrize("s, N", [(-4, 5), (-5, 6), (1, 0)])
def test_correction_term_pole(s, N):
    with pytest.raises(ValueError):
        correction_term(s, N)


@pytest.mark.parametrize("s", [(3 + 2 * I), -11, Integer(2), RR(pi)])
@pytest.mark.parametrize("N", [0, 3, Integer(5), 10, np.int64(10)])
def test_correction_term_shift(s, N):
    assert_close(correction_term(s, N), correction_term(s + 1, N - 1))


def test_correction_term_zero():
    assert correction_term(2, 0) == 0


@pytest.mark.parametrize("s", [(3 + 2 * I), -11, Integer(2), RR(pi)])
@pytest.mark.parametrize("N", [0, 3, Integer(5), 10, np.int64(10)])
def test_correction_term_exp(s, N):
    assert_close(exp(2 * correction_term(s, N)), CC(s) + N - 1)


def test_integral_shifting_term():
    assert_close(exp(2 * (integral_shifting_term() + 1)), 2 * CC(pi))


@pytest.mark.parametrize("k", [2.5, pi, 3.0])
def test_bernoulli_non_int(k):
    with pytest.raises(TypeError):
        gamma_bernoulli_term(2, 2, k)


@pytest.mark.parametrize("k", [-1, 0, -10])
def test_bernoulli_neg(k):
    with pytest.raises(ValueError):
        gamma_bernoulli_term(2, 2, k)


@pytest.mark.parametrize("s, N", [(-4, 5), (-2, 3), (1, 0)])
def test_bernoulli_zero_div(s, N):
    with pytest.raises(ValueError):
        gamma_bernoulli_term(s, N, 3)


@pytest.mark.parametrize("s", [(3 + 2 * I), -11, Integer(2), RR(pi)])
@pytest.mark.parametrize("N", [0, 3, Integer(5), 10, np.int64(10)])
def test_bernoulli_term_shift(s, N):
    assert_close(gamma_bernoulli_term(s, N, 3), gamma_bernoulli_term(s + 1, N - 1, 3))


@pytest.mark.parametrize("k, val", STIRLING.items())
def test_bernoulli_term_val(k, val):
    assert_close(gamma_bernoulli_term(2, 2, k) * 3 ** (2 * k - 1), val)


@pytest.mark.parametrize("M", [4.5, 3.0, "5"])
def test_non_int_bernoulli_sum(M):
    with pytest.raises(TypeError):
        gamma_bernoulli_sum(3, 3, M)


@pytest.mark.parametrize("M", [-1, -1000])
def test_neg_bernoulli_sum(M):
    with pytest.raises(ValueError):
        gamma_bernoulli_sum(3, 3, M)


@pytest.mark.parametrize("s", [(3 + 2 * I), -11, Integer(2), RR(pi)])
@pytest.mark.parametrize("N", [0, 3, Integer(5), 10, np.int64(10)])
def test_bernoulli_sum_shift(s, N):
    assert_close(
        gamma_bernoulli_sum(s, N, 3)[0], gamma_bernoulli_sum(s + 1, N - 1, 3)[0]
    )


@pytest.mark.parametrize("M", [1, 2, 3, 5, 10])
def test_bernoulli_sum_return_idx(M):
    assert gamma_bernoulli_sum(3, 3, M)[1] == M


@pytest.mark.parametrize("s, N", [(-4, 5), (-2, 3), (1, 0)])
def test_bernoulli_sum_zero_div(s, N):
    with pytest.raises(ValueError):
        gamma_bernoulli_sum(s, N, 3)


@pytest.mark.parametrize("s, N", [(-4, 5), (-2, 3), (1, 0)])
def test_log_gamma_euler_maclaurin_zero_div(s, N):
    with pytest.raises(ValueError):
        log_gamma_euler_maclaurin(s, N, 3)


@pytest.mark.parametrize("M", [4.5, 3.0, "5"])
@pytest.mark.parametrize("N", [pi, 2.0, None])
def test_non_int_log_gamma(N, M):
    with pytest.raises(TypeError):
        log_gamma_euler_maclaurin(3, N, M)


@pytest.mark.parametrize("M", [-1, -1000])
@pytest.mark.parametrize("N", [-5, -3])
def test_neg_log_gamma(N, M):
    with pytest.raises(ValueError):
        log_gamma_euler_maclaurin(3, N, M)


@pytest.mark.parametrize("N", [0, -1, -10, -11.0])
def test_pole_log_gamma(N):
    with pytest.raises(ValueError):
        log_gamma_euler_maclaurin(-4, N, 3)


@pytest.mark.parametrize("s, N", [(-10, 3), (-5, 1)])
def test_bad_error_bound(s, N):
    with pytest.raises(ValueError):
        log_gamma_error_bound(s, N, 3)


@pytest.mark.parametrize("M", [0, -5])
def test_bad_error_bound_M(M):
    with pytest.raises(ValueError):
        log_gamma_error_bound(2, 3, M)


@pytest.mark.parametrize("N, M", [(5.5, 5.5), (pi, pi)])
def test_error_bound_non_int(N, M):
    with pytest.raises(TypeError):
        log_gamma_error_bound(2, N, M)


@pytest.mark.parametrize("s, N", [(-10, 3), (-5, 1)])
def test_bad_log_gamma_euler_maclaurin(s, N):
    with pytest.raises(ValueError):
        log_gamma_euler_maclaurin(s, N, 3)


@pytest.mark.parametrize("s", [pi, -2.5, 2, 3 / 2 + I * 1 / 4])
@pytest.mark.parametrize("N", [5, 10])
@pytest.mark.parametrize("M", [3, 5, None])
def test_log_gamma_euler_maclaurin(s, N, M):
    gt = log_gamma(CC(s))
    est, err = log_gamma_euler_maclaurin(s, N, M)
    assert abs(est - gt) <= err


@pytest.mark.parametrize("N", [-1, -5, -11])
def test_bad_theta_error_bound(N):
    with pytest.raises(ValueError):
        theta_error_bound(N, 3)


@pytest.mark.parametrize("M", [0, -5])
def test_bad_theta_error_bound_M(M):
    with pytest.raises(ValueError):
        theta_error_bound(3, M)


@pytest.mark.parametrize("N, M", [(5, 5.5), (2, pi), (5.5, 5), (pi, 2)])
def test_error_bound_non_int(N, M):
    with pytest.raises(TypeError):
        theta_error_bound(N, M)


@pytest.mark.parametrize("N", [0, -1, -10])
def test_bad_N_theta(N):
    with pytest.raises(ValueError):
        theta(5, N, 3)


@pytest.mark.parametrize("t", [pi, -2.5, 2, 10])
@pytest.mark.parametrize("N", [5, 10])
@pytest.mark.parametrize("M", [3, 5, None])
def test_theta(t, N, M):
    s = CC(RR(1) / 4, RR(t) / 2)
    gt = RR(imag_part(log_gamma(s)) - RR(t) / 2 * RR(pi).log())
    est, err = theta(t, N, M)
    assert abs(est - gt) <= err
