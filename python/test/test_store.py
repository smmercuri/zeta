import json

import pytest

from data_gen import store
from data_gen.gen_zero_certificates import write_module
from data_gen.store_zeros import write_store

COLS = ("idx", "left", "right")


@pytest.fixture
def out(tmp_path, monkeypatch):
    monkeypatch.setattr(store, "OUT_DIR", str(tmp_path))
    return tmp_path


def manifest_path(out):
    return out / "euler_maclaurin" / "zeros" / "manifest.json"


def write_unwidened(out):
    (out / "euler_maclaurin" / "zeros").mkdir(parents=True)
    rows = ["1, 14.1, 14.2", "2, 147.4, 147.5"]
    return write_store(out / "euler_maclaurin" / "zeros", rows, COLS, {}, 149.5)


def test_zeros_below_matches_the_searched_end_not_the_last_bracket(out):
    manifest = write_unwidened(out)
    assert manifest["height"] == "147.500"
    assert store.zeros_below(149.5) == 2
    assert store.zeros_below(150.0) is None


def test_zeros_below_ignores_a_store_above_start(out):
    write_unwidened(out)
    (out / "riemann_siegel" / "zeros").mkdir(parents=True)
    write_store(out / "riemann_siegel" / "zeros", ["1, 149.6, 150.9"], COLS, {}, 10000.0)
    assert store.zeros_below(149.5) == 2


@pytest.mark.parametrize("height, below", [("149.500", 2), ("147.500", None)])
def test_zeros_below_falls_back_to_height_for_older_manifests(out, height, below):
    write_unwidened(out)
    old = json.loads(manifest_path(out).read_text())
    del old["end"]
    old["height"] = height
    manifest_path(out).write_text(json.dumps(old))
    assert store.zeros_below(149.5) == below


def test_zeros_below_is_zero_under_the_first_zero(out):
    assert store.zeros_below(10.0) == 0


def test_write_module_refuses_a_long_line(tmp_path):
    with pytest.raises(SystemExit, match="over 100 columns"):
        write_module(tmp_path / "A.lean", "x" * 101 + "\n")
    assert not (tmp_path / "A.lean").exists()


def test_write_module_ignores_style_on_request(tmp_path):
    write_module(tmp_path / "A.lean", "x" * 101 + "\n", ignore_style=True)
    assert (tmp_path / "A.lean").exists()
