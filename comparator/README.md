# Comparator verification

This `comparator` subdirectory contains various configurations for independent and external 
verification of the proofs contained within this project. This makes use of 
[`leanprover/comparator`](https://github.com/leanprover/comparator), which 
checks that the solution module proves exactly the statement of the challenge module, 
using only the setup allowed in the `config` file (typically using only the standard axioms 
`propext`, `Quot.sound` and `Classical.choice`). 

The height-dependent scale of the formalization in this project presents challenges 
in facilitating independent verification. 
Comparator exports the solution's entire dependency closure and re-checks it in a fresh kernel, 
so it does not need to trust any pre-compiled oleans. 
Up to height `1e5`, the main theorem of this project can be built on a local machine in under 
an hour and requires approximately 30GB of local storage for the `olean` files.
However, at height `1e6` and beyond, this becomes a build of a day or more with around 1TB of
storage required.
We thus provide two methods, _sharded_ and _global_, for the independent verification of the 
main theorem. Sharded is the main method; see the warning under [Running](#running).

## Verifying the main theorem

**Sharded.** The project's proof of the main theorem computes certificates for the zeros of 
the Riemann zeta function in independent, pairwise disjoint batches. 
A single batch exports `BatchSpec`, the totality of which are assembled to give the proof 
which covers the entire critical line from `0` through `<T>`. 
The sharded approach to verification mirrors this structure.

- `Batches/Statements.lean` names each batch's statement: `Spec.RS0001 : Prop := BatchSpec …`.
- `Batches/<Method>/BatchNNNN/` provides a single batch challenge, which states that batch's 
   `Spec`. Each batch proves a self-contained statement, so the batches may be verified 
   independently and in any order.
- `Reduction/` is the conditional challenge that the main theorem is true, given every batch's 
   `Spec` as a hypothesis. This is a cheap check because it does not actually import 
   any batch.

A _shard_ is a collection of batches. The idea here is that independent verification for large 
heights may be performed by multiple runs, either sequentially on the same machine or in parallel
across independent machines, each taking disjoint shards according to machine specifications.
Each run only needs the shard's proofs, keeping memory and storage requirements manageable.

Verifying every batch target and the reduction implies the main result. The batch challenges and 
the reduction's hypotheses refer to the same named statements in `Batches/Statements.lean`, and 
comparator checks that each target sees the same definition of each name, so the pieces are 
guaranteed to fit together; what remains is only coverage, that every `Spec` the reduction 
assumes has a passing batch target. 

**Global.** `Main` is the challenge `riemannHypothesisUpTo_<T>`, with its solution 
coming from the project's main theorem. The global approach to verification involves 
directly running this challenge, which builds (if not already built) and then re-checks the entire 
set of zero and Gram certificates in one run. This is feasible locally only at height `1e4`: 
it becomes impractical as the height grows, and at `1e6` it is infeasible on an ordinary 
machine. See the warning under [Running](#running).

**Background.**
`Analytic/` checks the main theorems in the background material used for the main theorem's proof. 
These are the Riemann–von Mangoldt formula (`riemannZeta_N_eq`), Lehman's bound with constant 5
(`norm_integral_argZeta_le_five`), and Turing's bound at a Gram point
(`riemannZeta_N_le_of_gramPoints`).

## Running

Comparator's tools must be built first; see the Comparator section of the
[root README](../README.md#comparator).

| Coverage | Command | What it checks |
|---|---|---|
| **Full** | `comparator/sharded_run.sh [--size 10] [--jobs 1]` | The complete result: the reduction and every batch, in shards. **Recommended.** |
| | `comparator/run.sh --force` | The main theorem, in one run. Needs `--force`; see the first warning below. |
| **Partial** | `comparator/sharded_run.sh --sample 300 --seed <public value>` | A reproducible random selection of batches, without the reduction. |
| | `comparator/run.sh <config.json>` | One target, e.g. `comparator/Reduction/config.json`. |
| | `comparator/shard.sh <Method/BatchNNNN> …` | Several chosen batches in one run. |

`sharded_run.sh` discards the proofs of batches it had to build once their shard passes, and an
interrupted run resumes where it stopped. `--jobs N` checks `N` shards at once; each needs memory
for its own export. Each shard's output goes to a log under `comparator/Shard/`.

> **Warning.** Use `sharded_run.sh`. Lean hashes `Nat` literals modulo $2^{64}$
> ([lean4#15686](https://github.com/leanprover/lean4/issues/15686)), and these proofs contain many large dyadic literals that are multiples of
> $2^{64}$. Exported together they collide in the exporter's table and lookups become quadratic,
> so a global export can take hours or longer. Shards keep each export small.

> **Warning.** `sharded_run.sh` does not check the formal theorem `Zeta.riemannHypothesisUpTo_<T>`
> itself. It checks each batch's statement and the theorem that those statements imply the main
> theorem's statement (`Comparator.riemannHypothesisUpTo_of_batches`, in
> `comparator/Reduction/Solution.lean`). Applying that theorem to the checked batches is the one
> step comparator does not check.

> **Warning.** Comparator reads each batch's proof term, so a batch built with `--proofs=discard`
> has to be rebuilt first with `scripts/proofs.sh restore <Method/BatchNNNN>`; Lake will not rebuild it
> on its own. Otherwise the run fails with `invalid header`.

## Regenerating

Much like the project's formal code itself, the batch and reduction challenges are generated from 
project data using Python scripts, and should never be handwritten. 
First, make sure that the project's formal certificates have already been generated using 
`gen_zero_certificates.py`. 
Activate the Python `zeta` environment.
Then run

    python python/src/data_gen/gen_comparator.py comparator

Alternatively pass `--comparator` to `scripts/gen_certificates.sh` when generating all 
Lean certificate files; `scripts/pipeline.sh` regenerates them by default.
Conversely, `Main` and `Analytic` challenges are handwritten. 
If you run `comparator/shard.sh` or `comparator/sharded_run.sh` then a gitignored `Shard` 
challenge will appear in your directory. 
The `Shard` challenge is what enables multi-batch verification in a single comparator run. 
