from sage.all import RealField, ComplexField, QQ, pi, bernoulli
from pathlib import Path
from config import PREC, DATA_DIR

RR = RealField(PREC)
CC = ComplexField(PREC)
TOL = RR(2) ** (-PREC + 20)
STIRLING = {1: QQ(1) / 12, 2: QQ(-1) / 360, 3: QQ(1) / 1260, 4: QQ(-1) / 1680}
ZETA = {
    2: RR(pi) ** 2 / 6,
    4: RR(pi) ** 4 / 90,
    -1: -QQ(1) / 12,
    -2: QQ(0),
    -4: QQ(0),
    -6: QQ(0),
    -8: QQ(0),
    -10: QQ(0),
    -3: -QQ(bernoulli(4)) / 4,
    -5: -QQ(bernoulli(6)) / 6,
    -7: -QQ(bernoulli(8)) / 8,
    -9: -QQ(bernoulli(10)) / 10,
    -11: -QQ(bernoulli(12)) / 12,
}


def assert_close(a, b, tol=TOL):
    assert abs(a - b) <= tol * max(abs(a), abs(b), 1)


def odlyzko_zeta_100(start=1, end=100):
    zeros = (
        Path(f"{DATA_DIR}/odlyzko_zeta_100.txt")
        .expanduser()
        .read_text()
        .strip()
        .split("\n\n")
    )
    zeros = [zero.replace("\n ", "") for zero in zeros]
    return zeros[start - 1 : end]


def lmfdb_zeta(start, end):
    db = Path(f"{DATA_DIR}/lmfdb_zeta.txt").expanduser().read_text()
    RR = RealField(PREC)
    return [RR(line.split()[1]) for line in db.splitlines() if line.strip()][
        start - 1 : end
    ]
