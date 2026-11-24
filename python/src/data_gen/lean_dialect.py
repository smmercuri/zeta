"""How a store row renders as Lean.

The certificate generators read a store and emit Lean. What varies between approximation
methods is the *rendering*: which interval structure a row builds, which obligations its
certificate carries, and which smart constructor bundles them. A `LeanDialect` captures that;
batch splitting, seam theorems and the assembler are method-agnostic and live in the
generators themselves.

The dialect is selected from the store's own manifest (`params.method`), so a generator reads
the method from the data it is pointed at.
"""

from __future__ import annotations

from abc import ABC, abstractmethod
from decimal import ROUND_CEILING, ROUND_FLOOR, Decimal
from pathlib import Path

from config import GRAM_ZERO_DP


def _round_out(s: str, rounding: str) -> str:
    q = Decimal(1).scaleb(-GRAM_ZERO_DP)
    return str(Decimal(s).quantize(q, rounding=rounding))


class LeanDialect(ABC):
    """The method-specific half of certificate generation."""

    #: value of `params.method` in the store manifest
    method: str
    #: directory and namespace component for this method's generated modules
    subdir: str
    #: short identifier for generated names that must be unique across methods
    tag: str
    #: the Lean interval structure a row builds
    interval_type: str
    #: `CertifiedZeroIntervals` smart constructor for this method
    constructor: str
    #: number of comma-separated fields in a store row, including the leading index
    row_width: int

    #: theorem proving `∃ t ∈ Ioo …, ζ = 0` from this method's certificate, and its module
    exists_zero_theorem: str
    exists_zero_module: str

    #: Lean module providing this dialect's certificate tactics, or `None` when its
    #: ball-arithmetic obligations are emitted as `sorry`. Generated modules import it.
    tactic_module: str | None = None

    #: True when `certificate_block` discharges every obligation (no `sorry` emitted).
    proves_obligations: bool = False

    #: Tactic closing a batch's `BatchSpec` goal straight from the store rows `[lo, hi)`: the
    #: batch module is a single theorem and the bracket numbers live in the data file (and, at
    #: import precision, in the statement).
    metaprogram: str

    #: Definitions a seam's `norm_num` must unfold to compare two exported endpoints.
    seam_unfold: tuple[str, ...] = ("Enclosure.sfrac",)

    #: Tactic closing a batch's `BatchSpec` goal from the store rows `[lo, hi)` by compiled
    #: evaluation (`native_decide`, `Native.BuildCerts`), or `None` when this method has no native
    #: check; a native build then keeps its kernel-checked module.
    native_metaprogram: str | None = None

    @abstractmethod
    def interval_block(self, name: str, row: list[str]) -> str:
        """The `abbrev <name> : <type> where …` block for one row."""

    @abstractmethod
    def certificate_block(self, name: str, row: list[str]) -> str:
        """The `theorem <name>_cert : <name>.Certificate where …` block for one row."""

    def check_row(self, path: Path, parts: list[str]) -> None:
        """Reject a row this dialect cannot render. Default: accept."""

    def interval_ref(self, name: str) -> str:
        """How an interval is written where a `NonemptyInterval ℝ` is expected."""
        return name

    def exists_zero_term(self, name: str) -> str:
        """A proof that the interval `name` brackets a `ζ`-zero, from its certificate."""
        return f"{self.exists_zero_theorem} _ {name}_cert"


class EulerMaclaurinDialect(LeanDialect):
    """Euler–Maclaurin: the cutoff and Bernoulli count are per-endpoint row data."""

    method = "euler_maclaurin"
    subdir = "EulerMaclaurin"
    tag = "EM"
    interval_type = "ZIntervalEM"
    constructor = "ofCertifiedEM"
    row_width = 7
    tactic_module = "Zeta.Zeros.BuildCerts"
    proves_obligations = True
    metaprogram = "build_batch"

    def check_row(self, path: Path, parts: list[str]) -> None:
        if parts[5] == "None" or parts[6] == "None":
            raise SystemExit(
                f"{path}: row {parts[0]} has Bernoulli count None; the Lean "
                "`fstBernoulli : Nat` needs a concrete number; regenerate the "
                "store with a real `--M` (not automatic stopping)."
            )

    exists_zero_theorem = "riemannZeta.exists_zero_of_zIntervalEM_certificate"
    exists_zero_module = "Zeta.Zeros.Interval"

    def interval_block(self, name: str, row: list[str]) -> str:
        """Used where a row must be named individually: inside a gram block. Whole batches
        go through `build_batch`, which builds the same term unnamed."""
        idx, left, right, lc, rc, lb, rb = row
        return f"""/-- Interval bracketing zeta zero #{idx} (`t ≈ {left}`). -/
abbrev {name} : ZIntervalEM where
  fst := {left}
  snd := {right}
  fst_le_snd := by norm_num
  fstCutoff := {lc}
  sndCutoff := {rc}
  fstBernoulli := {lb}
  sndBernoulli := {rb}
"""

    def certificate_block(self, name: str, row: list[str]) -> str:
        # The three ball-arithmetic obligations are discharged by the `Enclosure` engine:
        # `hardy_sign_change` builds named enclosures of both endpoint values and combines
        # their signs; `hardy_error_ok_full` compares `‖Z̃(t)‖` against `hardyZErrorBoundEM`
        # through the strengthened bound. Both read `M`/`N`/`t` off the goal.
        return f"""theorem {name}_cert : {name}.Certificate where
  fst_nonneg := by norm_num
  fstBernoulli_pos := by decide
  fstCutoff_pos := by decide
  sndBernoulli_pos := by decide
  sndCutoff_pos := by decide
  is_sign_change := by hardy_sign_change
  fst_error := by hardy_error_ok_full
  snd_error := by hardy_error_ok_full
"""

    def interval_ref(self, name: str) -> str:
        # A `ZIntervalEM` carries the parameters; the bundles hold the bare interval.
        return f"{name}.toNonemptyInterval"


class RiemannSiegelDialect(LeanDialect):
    """Riemann–Siegel: no per-endpoint data, but the `t ≥ 32π` threshold to discharge."""

    method = "riemann_siegel"
    subdir = "RiemannSiegel"
    tag = "RS"
    interval_type = "ZIntervalRS"
    constructor = "ofCertifiedRS"
    row_width = 3
    tactic_module = "Zeta.Zeros.BuildCertsRS"
    proves_obligations = True
    metaprogram = "build_batch_rs"

    exists_zero_theorem = "riemannZeta.exists_zero_of_zIntervalRS_certificate"
    exists_zero_module = "Zeta.Zeros.IntervalRS"

    native_metaprogram = "build_batch_rs +native"

    def interval_block(self, name: str, row: list[str]) -> str:
        idx, left, right = row
        lo = _round_out(left, ROUND_FLOOR)
        hi = _round_out(right, ROUND_CEILING)
        return f"""/-- Interval bracketing zeta zero #{idx} (`t ≈ {left}`). -/
abbrev {name} : ZIntervalRS where
  fst := {lo}
  snd := {hi}
  fst_le_snd := by norm_num
"""

    def certificate_block(self, name: str, row: list[str]) -> str:
        """Used where a row must be named individually: inside a gram block. Whole batches
        go through `build_batch_rs`, which builds the same term unnamed.

        `norm_num` runs first in `le_fst` to reduce the interval's `toProd.1` projection to
        the literal that `linarith` then uses. The three ball-arithmetic obligations are
        discharged by the `Enclosure` engine against the concrete
        `hardyZApproximantRS₀`/`hardyZErrorBoundRS₀`."""
        return f"""theorem {name}_cert : {name}.Certificate where
  le_fst := by
    norm_num
    linarith [Real.pi_lt_d2]
  is_sign_change := by hardy_sign_change_rs
  fst_error := by hardy_error_ok_rs
  snd_error := by hardy_error_ok_rs
"""


DIALECTS: dict[str, LeanDialect] = {
    d.method: d for d in (EulerMaclaurinDialect(), RiemannSiegelDialect())
}


def dialect_for(store: Path, manifest: dict) -> LeanDialect:
    """The dialect named by a store manifest.

    A store without the `method` key is Euler–Maclaurin. Both the zeros and the gram store
    record `params` at top level.
    """
    method = manifest.get("params", {}).get("method", "euler_maclaurin")
    if method not in DIALECTS:
        raise SystemExit(
            f"{store}: no Lean dialect for method {method!r} "
            f"(known: {', '.join(sorted(DIALECTS))})."
        )
    return DIALECTS[method]
