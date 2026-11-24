#!/usr/bin/env python3
"""The Python half of `build.sh` (stdlib only): run from the project root, by `build.sh`.

    build_tools.py load-max                the largest rows·ν of any batch the stores make
    build_tools.py constants FILE LOAD     the constants an earlier `--estimate` measured, or why not
    build_tools.py estimate …              `scripts/build.sh --estimate`: sample, measure, project
    build_tools.py disk …                  the proof-term disk check before a build
    build_tools.py stages …                the stage plan of a build (see `plan_stages`)

`build.sh`'s header describes what each one is for; the measurement details are documented here.
"""
import argparse, glob, json, math, os, re, shutil, statistics, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

LIB = ".lake/build/lib/lean"
GB = 2**30
SPEC = re.compile(r"BatchSpec\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)")
BATCH_IMPORT = re.compile(r"^public import (Zeta\.Zeros\.Certificates\.[\w.]+\.Batch\d+)$", re.M)
#: the module each method's batches import (the metaprogram): a batch is rebuilt when it changes
PREREQ = {"EulerMaclaurin": "Zeta.Zeros.BuildCerts", "RiemannSiegel": "Zeta.Zeros.BuildCertsRS"}


def olean(mod):
    return os.path.join(LIB, mod.replace(".", "/") + ".olean")


def built_after(*mods):
    """When the newest of `mods`' oleans was written, or infinity if Lake would rebuild one of them
    (then so is every module importing it). One `lake build --no-build`."""
    if subprocess.run(["lake", "build", "--no-build", *mods], capture_output=True).returncode:
        return math.inf
    return max(os.path.getmtime(olean(m)) for m in mods)


def is_built(src, since):
    """Whether `src`'s olean exists and is newer than both `src` and `since`, its prerequisites'
    newest olean: cheap, from file times (Lake itself decides by hashes)."""
    o = os.path.join(LIB, src[:-len(".lean")] + ".olean")
    return os.path.exists(o) and os.path.getmtime(o) >= max(os.path.getmtime(src), since)


def nu(t):
    """The Riemann–Siegel cutoff ⌊√(t/2π)⌋ at height `t`."""
    return math.floor(math.sqrt(t / (2 * math.pi)))


def batch_load(rows, an, ad, bn, bd):
    """A batch's rows·ν (ν at its top), which its memory grows with: each row's certificate holds
    main sums of ν terms."""
    return rows * nu(bn / bd)


def plan_stages(cores, last, fits):
    """The stages of a build, up the height: lists of consecutive group modules, each built on as
    many workers as fit at its largest batch (`fits(rows·ν)`, at most `cores`), up to where only `last`
    fit, the count the last stage (the rest of the build) runs on. Each new stage costs about half a
    batch's time while the previous one drains (its last batches finish on fewer and fewer
    workers), and running n batches on one worker fewer than fit costs about n / W² of a batch's
    time on W workers; so a stage boundary is placed wherever the count drops, unless the stage
    would hold fewer than W²/2 batches still to build, in which case it carries on at the lower
    count (and a last such stage is left to the last stage). Batches already built are not
    counted, and groups with none left to build are skipped. Each stage: `workers`, `top` height,
    `groups` and the `batches` it builds."""
    since = built_after(PREREQ["RiemannSiegel"])
    small = lambda st: len(st["batches"]) < st["workers"] ** 2 / 2
    stages = []
    for g in sorted(glob.glob("Zeta/Zeros/Certificates/Groups/Level1/Group*.lean")):
        ends, loads, left = [], [], []
        for mod in BATCH_IMPORT.findall(open(g).read()):
            src = mod.replace(".", "/") + ".lean"
            if m := SPEC.search(open(src).read()):
                spec = tuple(map(int, m.groups()))
                ends.append(spec[3] / spec[4])
                loads.append(batch_load(*spec))
            if not is_built(src, since):
                left.append(mod)
        w = max(1, min(cores, fits(max(loads)))) if ends else last
        if w <= last:
            break  # groups run up in height: the rest is the last stage's
        if not left:
            continue  # built already: no stage needs it
        if stages and w < stages[-1]["workers"] and small(stages[-1]):
            stages[-1]["workers"] = w  # too little left in this stage for a boundary: carry on at w
        if not stages or w < stages[-1]["workers"]:
            stages.append(dict(workers=w, top=0.0, groups=[], batches=[]))
        st = stages[-1]
        st["top"] = max(st["top"], max(ends))
        st["groups"].append(g[:-len(".lean")].replace("/", "."))
        st["batches"] += left
    if stages and small(stages[-1]):
        stages.pop()  # too little for a stage of its own: the last stage builds it
    return stages


# --- load-max, constants -----------------------------------------------------------------------

def cmd_load_max(_):
    """The largest rows·ν of any batch, from the zero stores' top height and the generator's batch
    sizes (`batch_rows`); default a modest height's. Within one ν a batch's rows only fall with the
    height, so each ν's first height decides."""
    hs = [float(h) for m in glob.glob("python/out/*/zeros/manifest.json")
          if (h := json.load(open(m))["height"])]
    if not hs:
        print(200 * 60)
        return
    sys.path.insert(0, "python/src")
    from data_gen.gen_zero_certificates import batch_rows
    print(max(batch_rows(2 * math.pi * k * k) * k for k in range(1, nu(max(hs)) + 1)))


def cmd_constants(a):
    """The constants an earlier `--estimate` measured (shared import GB, per-worker GB and GB per
    row per unit of ν, proof-term kB per row and per row per unit of ν, date), or `stale <why>` when
    the estimate predates the rows·ν memory model or this build's largest rows·ν is more than twice
    the sampled one: the fit is linear and only measured up to there."""
    e = json.load(open(a.file))
    if e.get("model") != "rows·ν":
        print(f"stale --estimate of {e['date']} predates the rows·ν memory model")
        return
    sampled = max(s["load"] for s in e["samples"])
    if a.load <= 2 * sampled:
        d = e.get("disk") or [48e3, 3.24e3]
        print(f'{e["base"]["rss"] / GB:.2f} {e["mem"][0] / GB:.3f} {e["mem"][1] / GB:.3e} '
              f'{d[0] / 1e3:.2f} {d[1] / 1e3:.3f} {e["date"]}')
    else:
        print(f"stale --estimate measured up to rows·ν {sampled} on {e['date']}, this build reaches "
              f"{a.load}")


# --- stages --------------------------------------------------------------------------------------

def cmd_stages(a):
    """The stage plan from the memory model's constants, one line per stage:
    `workers top-height batches-to-build group…`."""
    fits = lambda n: int((a.avail_gb - a.shared_gb) / (a.base_gb + a.per_row_nu_gb * n))
    for st in plan_stages(a.cores, a.last, fits):
        print(st["workers"], f"{st['top']:.0f}", len(st["batches"]), *st["groups"])


# --- disk ----------------------------------------------------------------------------------------

ARCHIVE_RATIO = 3  # the assumed `zstd -3` compression ratio of a proof term (see `proofs.sh`)
DISK_MARGIN = 0.9  # the share of the free disk `--proofs=auto` is willing to fill


def cmd_disk(a):
    """Proof-term disk for the batches not yet built, against the free disk; a warning when they
    would take more than `--warn` of it and the proof terms are kept. With `--proofs auto`, prints
    the mode to use instead: keep them if under `--warn` of the free disk, else archive, else
    discard, and exits 2 if even discarding would not leave room."""
    auto = a.proofs == "auto"
    log = sys.stderr if auto else sys.stdout
    since = {d: built_after(m) for d, m in PREREQ.items()}
    need, largest, n = 0.0, 0.0, 0
    for src in glob.glob("Zeta/Zeros/Certificates/*/**/Batch*.lean", recursive=True):
        if is_built(src, since.get(src.split("/")[3], math.inf)):
            continue  # built already, against the current metaprogram: not to come
        if not (m := SPEC.search(open(src).read())):
            continue
        rows, an, ad, bn, bd = map(int, m.groups())
        size = rows * (a.row_kb * 1e3 + a.row_nu_kb * 1e3 * nu((an / ad + bn / bd) / 2))
        need, largest, n = need + size, max(largest, size), n + 1
    if not n:
        if auto:
            print("keep")
        return
    free = shutil.disk_usage(".").free
    gb = lambda x: f"{x / GB:,.1f} GB"
    print(f"build.sh: {n} certificate batches to build; their proof terms take ≈ {gb(need)} "
          f"kept in full, {gb(free)} free on disk", file=log)
    if auto:
        peak = a.workers * largest  # one batch per worker in flight, before it is shrunk
        if need <= a.warn * free:
            mode = "keep"
        elif shutil.which("zstd") and need / ARCHIVE_RATIO + peak <= DISK_MARGIN * free:
            mode = "archive"
        elif peak <= DISK_MARGIN * free:
            mode = "discard"
        else:
            print(f"build.sh: not enough disk: even discarding proof terms needs ≈ {gb(peak)} at "
                  f"peak, with {gb(free)} free", file=log)
            sys.exit(2)
        print(f"build.sh: --proofs=auto: using --proofs={mode}", file=log)
        print(mode)
        return
    if a.proofs == "keep" and need > a.warn * free:
        print("\n" + "!" * 78)
        print(f"!! WARNING: the proof terms would take ≈ {gb(need)} of {gb(free)} free disk"
              + ("" if need <= free else " -- MORE THAN IS FREE: the build will run out of disk"))
        print("!! `lake build` never reads a batch's proof term again once it is built, so")
        print("!! consider   scripts/build.sh --proofs=discard   (≈ "
              f"{gb(a.workers * largest)} at peak: one batch per worker in flight;")
        print("!! `scripts/proofs.sh restore` rebuilds any batch whose proof term you need back).")
        print("!" * 78 + "\n")


# --- estimate ------------------------------------------------------------------------------------

MEASURE = r"""
import json, resource, subprocess, sys, time
t = time.monotonic()
r = subprocess.run(sys.argv[1:], capture_output=True, text=True)
u = resource.getrusage(resource.RUSAGE_CHILDREN)
print(json.dumps({"ok": r.returncode == 0, "wall": time.monotonic() - t,
                  "cpu": u.ru_utime + u.ru_stime,
                  "rss": u.ru_maxrss * (1 if sys.platform == "darwin" else 1024),
                  "tail": (r.stdout + r.stderr)[-3000:]}))
"""


def measure(cmd, env=None):
    """Run `cmd` in a fresh process, so its peak RSS is its own."""
    r = json.loads(subprocess.run([sys.executable, "-c", MEASURE, *cmd], env=env,
                                  capture_output=True, text=True).stdout)
    if not r["ok"]:
        sys.exit(f"build.sh --estimate: `{' '.join(cmd)}` failed:\n{r['tail']}")
    return r


def fit(xs, ys):
    """`y = a·x₀ + b·x₁` through two samples, else (one sample, or a negative coefficient) the
    proportional `y = b·x₁`."""
    if len(xs) == 2:
        (p0, p1), (q0, q1) = xs
        det = p0 * q1 - q0 * p1
        if det:
            a, b = (ys[0] * q1 - ys[1] * p1) / det, (p0 * ys[1] - q0 * ys[0]) / det
            if a >= 0 and b >= 0:
                return a, b
    return 0.0, sum(ys) / max(sum(x[1] for x in xs), 1e-9)


def cmd_estimate(a):
    """Build two of the modules not yet built (batches, or with `--mode native` shards): the one
    with the highest mean ν and one near the median, plus an import-only probe beside them. Lake
    builds each once, which records the exact `lean` invocation; that process alone is re-run and
    measured (`lean_cost`), and the import's cost is subtracted. CPU time (not wall: on a loaded
    machine wall times are too noisy to fit) is fitted as a fixed cost per module plus b·Σ rows·ν,
    disk as rows·(a + b·ν), per-worker memory as c + d·(largest rows·ν); the projection is stage by stage
    (`plan_stages`), and the fit is saved to `--out` for later builds."""
    mode, out, cores, avail = a.mode, a.out, a.cores, a.avail_gb * GB

    def mean_nu(an, ad, bn, bd):
        return nu((an / ad + bn / bd) / 2)

    # the modules to build, each with its rows R, Σ rows·ν = S, largest ν and largest batch rows·ν
    if mode == "native":
        files, prereq = glob.glob("Native/Certificates/*/**/Shard*.lean", recursive=True), ["Native.BuildCerts", "Native.PluginCheck"]
    else:
        files, prereq = glob.glob("Zeta/Zeros/Certificates/RiemannSiegel/**/Batch*.lean", recursive=True), ["Zeta.Zeros.BuildCertsRS"]
    since = built_after(prereq[0])  # the module the batches import (not PluginCheck)
    mods = []
    for f in sorted(files):
        specs = [tuple(map(int, m)) for m in SPEC.findall(open(f).read())]
        if specs:
            mods.append(dict(src=f, mod=f[:-5].replace("/", "."), R=sum(r for r, *_ in specs),
                             S=sum(r * mean_nu(*e) for r, *e in specs),
                             numax=max(mean_nu(*e) for _, *e in specs),
                             load=max(batch_load(*spec) for spec in specs), built=is_built(f, since)))
    todo = [m for m in mods if not m["built"]]
    if not todo:
        sys.exit(f"build.sh --estimate: every {mode} module is built already; nothing to estimate")

    print(f"build.sh --estimate ({mode}): {len(todo)} of {len(mods)} modules to build; building the "
          f"prerequisites {', '.join(prereq)} first (not measured)", flush=True)
    if subprocess.run(["lake", "build", *prereq]).returncode:
        sys.exit("build.sh --estimate: the prerequisites failed to build")

    lake_env = lambda *cmd: subprocess.run(["lake", "env", *cmd], capture_output=True,
                                           text=True).stdout.strip()
    env = dict(os.environ, LEAN_PATH=lake_env("printenv", "LEAN_PATH"))
    lean = lake_env("sh", "-c", "command -v lean")
    repeats = 1 if mode == "kernel" else 2  # a kernel batch is slow enough that one run is clean
    load = max(1, int(os.environ.get("LEAN_NUM_THREADS") or cores or 1))  # copies run at once
    base = None  # the import alone, measured first

    def lean_cost(src, mod, also=0):
        """Lake builds `mod` once, unmeasured, writing the exact `lean` invocation it uses; then
        just that `lean` process is re-run into scratch outputs and measured, so Lake's own work
        (checking its job graph) is not in the numbers. Short modules are run twice, keeping
        the cheaper. That run alone gives the memory; then `load` copies (fewer if they would not
        fit in the available memory) run at once, and their median CPU time and wall time replace
        the lone run's (`cpu_alone` keeps it): a process sharing the machine runs slower (two
        hyperthreads share a core; clocks drop with every core busy) and its CPU time grows to
        match, so this is what makes `wall = CPU ÷ workers` hold on a busy, hyperthreaded machine.
        With `also` (more than `load`), that many copies (as many as fit) are run at once too, for
        `cpu_also` at `copies_also`."""
        built = subprocess.run(["lake", "build", mod], capture_output=True, text=True)
        if built.returncode:
            sys.exit(f"build.sh --estimate: `lake build {mod}` failed:\n{(built.stdout + built.stderr)[-3000:]}")
        setup = os.path.join(".lake/build/ir", src[:-5] + ".setup.json")

        def run(_):
            with tempfile.TemporaryDirectory() as d:
                return measure([lean, src, "-o", f"{d}/m.olean", "-i", f"{d}/m.ilean", "-c",
                                f"{d}/m.c", "--setup", setup, "--json"], env)
        r = min((run(i) for i in range(repeats)), key=lambda r: r["cpu"])
        k = min(load, max(1, int(avail / max(r["rss"], 1)))) if avail else load
        r["cpu_alone"], r["copies"] = r["cpu"], 1
        if k > 1:
            with ThreadPoolExecutor(k) as ex:
                loaded = list(ex.map(run, range(k)))
            r["cpu"] = statistics.median(x["cpu"] for x in loaded)
            r["wall"] = statistics.median(x["wall"] for x in loaded)
            r["copies"] = k
        if also:
            # sized like the workers: the copies share the import
            k2 = min(also, max(1, int((avail - base["rss"]) / max(r["rss"] - base["rss"], 1)))) if avail else also
            if k2 > r["copies"]:
                with ThreadPoolExecutor(k2) as ex:
                    r["cpu_also"] = statistics.median(x["cpu"] for x in ex.map(run, range(k2)))
                r["copies_also"] = k2
        return r

    def stale(m):
        """Lake's own answer: `--no-build` exits non-zero when the module would be rebuilt."""
        return subprocess.run(["lake", "build", "--no-build", m["mod"]], capture_output=True).returncode != 0

    # the samples: the highest mean ν, and one near the median, each confirmed not built yet
    mean = lambda m: m["S"] / m["R"]
    order = sorted(todo, key=mean)
    top = next((m for m in reversed(order) if stale(m)), None)
    if top is None:
        sys.exit(f"build.sh --estimate: Lake reports every {mode} module up to date; nothing to estimate")
    mid_first = sorted((m for m in order if m is not top),
                       key=lambda m: abs(order.index(m) - len(order) // 2))
    mid = next((m for m in mid_first if mean(m) < mean(top) and stale(m)), None)
    samples = [top] + ([mid] if mid else [])

    # the import alone, measured the way the samples are: a module beside them, built by Lake
    probe_src = os.path.join(os.path.dirname(top["src"]), "EstimateProbe.lean")
    probe_mod = probe_src[:-5].replace("/", ".")
    try:
        with open(probe_src, "w") as f:
            # stamped, so that Lake rebuilds it rather than replaying an earlier probe
            f.write(f"module\n\npublic import {prereq[0]}\n\n-- build.sh --estimate {time.time()}\n")
        r = lean_cost(probe_src, probe_mod)
    finally:
        os.remove(probe_src)
    base = {"wall": r["wall"], "cpu": r["cpu"], "rss": r["rss"]}
    load_note = lambda r: (f", {r['copies']} at once ({r['cpu'] / max(r['cpu_alone'], 1e-9):.2f}× "
                           f"the {r['cpu_alone']:.1f} s alone)" if r["copies"] > 1 else ", alone")
    print(f"  import only: {base['cpu']:.1f} s CPU{load_note(r)} ({base['wall']:.1f} s wall), "
          f"{base['rss'] / GB:.2f} GB peak RSS", flush=True)

    # The build may run stages on more workers than `load` (the count for the top), and a
    # process's CPU time grows with how many share the machine; so the lowest sample (it needs the
    # least memory) is also run with one copy per core, and the CPU per batch is interpolated
    # between the two loads.
    stageable = mode == "kernel" and cores > load
    for m in samples:
        print(f"  sampling {m['mod']} ({m['R']} rows, ν ≤ {m['numax']}) ...", flush=True)
        r = lean_cost(m["src"], m["mod"], cores if stageable and m is samples[-1] else 0)
        if "cpu_also" in r:
            m["cpu_also"], m["copies_also"] = r["cpu_also"], r["copies_also"]
        m["time"], m["cpu"], m["rss"] = r["wall"], r["cpu"], r["rss"]
        m["cpu_alone"], m["copies"] = r["cpu_alone"], r["copies"]
        m["private"] = max(0.0, r["rss"] - base["rss"])
        priv = os.path.join(LIB, m["src"][:-5] + ".olean.private")
        m["disk"] = os.path.getsize(priv) if mode == "kernel" and os.path.exists(priv) else 0
        print(f"    {m['cpu']:.1f} s CPU{load_note(r)} ({m['time']:.1f} s wall), "
              f"{m['rss'] / GB:.2f} GB peak RSS "
              f"({m['private'] / GB:.2f} GB over the import)"
              + (f", {m['disk'] / GB:.2f} GB proof term" if m["disk"] else "")
              + (f"; {m['cpu_also']:.1f} s CPU with {m['copies_also']} at once" if "cpu_also" in m else ""),
              flush=True)

    # CPU time as a fixed cost per module over the import plus a cost per row per unit of ν
    t_fit = fit([(1, m["S"]) for m in samples], [max(0.0, m["cpu"] - base["cpu"]) for m in samples])
    m_fit = fit([(1, m["load"]) for m in samples], [m["private"] for m in samples])
    d_fit = fit([(m["R"], m["S"]) for m in samples], [m["disk"] for m in samples]) if mode == "kernel" else None

    left = [m for m in todo if m not in samples]
    times = {m["mod"]: base["cpu"] + t_fit[0] + t_fit[1] * m["S"] for m in left}
    peak = m_fit[0] + m_fit[1] * max((m["load"] for m in left), default=0)
    workers = (min(cores, max(1, int((avail - base["rss"]) / max(peak, 1)))) if cores and avail else None)
    w = workers or int(os.environ.get("LEAN_NUM_THREADS") or 4)
    dur = lambda x: f"{x / 3600:.1f} h" if x >= 3600 else f"{x / 60:.0f} min"

    # CPU per batch on `k` workers relative to on `load` (the samples' load), linear in `k`
    # between the two loads measured
    hi = next((m for m in samples if "cpu_also" in m), None)

    def load_factor(k):
        if hi is None:
            return 1.0
        f0, f1 = hi["cpu"], hi["cpu_also"]
        return (f0 + (f1 - f0) * (k - hi["copies"]) / (hi["copies_also"] - hi["copies"])) / f0

    # the stages the build will run (`plan_stages`, from these measured constants), then the rest
    plan = []
    if stageable and workers and cores > w:
        fits = lambda n: int((avail - base["rss"]) / max(m_fit[0] + m_fit[1] * n, 1))
        plan = [(st["workers"], st["top"], [b for b in st["batches"] if b in times])
                for st in plan_stages(cores, w, fits)]
    staged = {b for _, _, bs in plan for b in bs}
    plan.append((w, None, [b for b in times if b not in staged]))
    rows, wall_total, cpu_total = [], 0.0, 0.0
    for k, top_t, bs in plan:
        if not bs:
            continue
        c = load_factor(k) * sum(times[b] for b in bs)
        wall = max(c / k, max(times[b] for b in bs) * load_factor(k))
        rows.append((k, top_t, len(bs), c, wall))
        cpu_total, wall_total = cpu_total + c, wall_total + wall
    print(f"\nprojection for the {len(left)} modules still to build "
          f"(load average now {', '.join(f'{x:.1f}' for x in os.getloadavg())}):")
    print(f"  CPU ≈ {dur(cpu_total)}; wall ≈ {dur(wall_total)}"
          + (f" in {len(rows)} stages" if len(rows) > 1 else f" on {w} workers")
          + f" (CPU measured with {samples[0]['copies']} copies at once"
          + (f" and {hi['copies_also']}" if hi and len(rows) > 1 else "")
          + (f"; {w} workers will run, so expect more" if samples[0]["copies"] < w else "")
          + "; swapping can add half again or more)")
    if len(rows) > 1:
        for k, top_t, n, c, wall in rows:
            where = f"up to t ≈ {top_t:,.0f}" if top_t else "the rest"
            print(f"    {k:3d} workers: {n:,} modules {where}: CPU ≈ {dur(c)}, wall ≈ {dur(wall)}")
    elif hi:
        print(f"  ({hi['copies_also']} at once took {hi['cpu_also'] / hi['cpu']:.2f}× the CPU of "
              f"{hi['copies']})")
    print(f"  per worker ≈ {peak / GB:.2f} GB over the shared import ({base['rss'] / GB:.2f} GB)"
          + (f" -> {workers} workers fit in {avail / GB:.1f} GB available at the top" if workers else ""))
    if d_fit:
        disk = sum(d_fit[0] * m["R"] + d_fit[1] * m["S"] for m in left)
        print(f"  proof terms ≈ {disk / GB:,.1f} GB kept in full (scripts/build.sh --proofs=discard keeps ≈ one "
              "batch per worker)")
    keys = ("mod", "R", "S", "numax", "load", "time", "cpu", "cpu_alone", "copies", "rss", "private", "disk",
            "cpu_also", "copies_also")
    json.dump({"mode": mode, "model": "rows·ν", "date": time.strftime("%Y-%m-%d %H:%M"),
               "load": os.getloadavg(),
               "base": base, "time": t_fit, "mem": m_fit, "disk": d_fit,
               "samples": [{k: m[k] for k in keys if k in m} for m in samples]},
              open(out, "w"), indent=1)
    print(f"\nsaved to {out}; later `scripts/build.sh{' --native' if mode == 'native' else ''}` runs size "
          "workers (and the disk check) from it")


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("load-max").set_defaults(run=cmd_load_max)
    c = sub.add_parser("constants")
    c.add_argument("file")
    c.add_argument("load", type=int)
    c.set_defaults(run=cmd_constants)
    e = sub.add_parser("estimate")
    e.add_argument("--mode", choices=["kernel", "native"], required=True)
    e.add_argument("--cores", type=int, default=0)
    e.add_argument("--avail-gb", type=float, default=0.0)
    e.add_argument("--out", required=True)
    e.set_defaults(run=cmd_estimate)
    d = sub.add_parser("disk")
    d.add_argument("--proofs", choices=["keep", "discard", "archive", "auto"], required=True)
    d.add_argument("--row-kb", type=float, required=True)
    d.add_argument("--row-nu-kb", type=float, required=True)
    d.add_argument("--warn", type=float, required=True)
    d.add_argument("--workers", type=int, required=True)
    d.set_defaults(run=cmd_disk)
    s = sub.add_parser("stages")
    for k in ("--avail-gb", "--shared-gb", "--base-gb", "--per-row-nu-gb"):
        s.add_argument(k, type=float, required=True)
    s.add_argument("--cores", type=int, required=True)
    s.add_argument("--last", type=int, required=True)
    s.set_defaults(run=cmd_stages)
    a = p.parse_args()
    a.run(a)


if __name__ == "__main__":
    main()
