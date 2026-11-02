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
an hour and requires approximately 41GB of local storage for the `olean` files.
However, at height `1e6` and beyond, this becomes a build of a day or more with around 2TB of 
storage required.
We thus provide two methods, _global_ and _sharded_, for the independent verification of the 
main theorem.

## Verifying the main theorem

**Global.** `Main` is the challenge `riemannHypothesisUpTo_<T>`, with its solution 
coming from the project's main theorem. The global approach to verification involves 
directly running this challenge, which builds (if not already built) and then re-checks the entire 
set of zero and Gram certificates in one run. At height 1e4 this is feasible locally, 
however it becomes impractical as the height grows and at 1e6 it is infeasible on an 
ordinary machine.

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
When using parallelisation across independent machines, computation is also divided.

Verifying every batch target and the reduction implies the main result. The batch challenges and 
the reduction's hypotheses refer to the same named statements in `Batches/Statements.lean`, and 
comparator checks that each target sees the same definition of each name, so the pieces are 
guaranteed to fit together; what remains is only coverage, that every `Spec` the reduction 
assumes has a passing batch target. 

**Background.**
`Analytic/` checks the main theorems in the background material used for the main theorem's proof. 
These are the Riemann–von Mangoldt formula (`riemannZeta.N_eq`) and Lehman's bound with constant 5
(`norm_integral_argZeta_le_five_unconditional`).

## Running

Scripts are provided to run comparator in the global and sharded modes described above.
Use `comparator/run.sh <config.json>` to run comparator for a single challenge. 
So `comparator/run.sh comparator/Main/config.json` runs the global method. 
Sharding can be achieved by multiple invocations of `comparator/run.sh` on a batch `config.json`,
but this accrues fixed overheads for each run and is inefficient. To reduce this, when running 
sharded verification, use `comparator/shard.sh <Method/BatchNNNN> … <Method/BatchNNNN>`. 
For example

    comparator/run.sh comparator/Reduction/config.json
    comparator/run.sh comparator/Batches/RiemannSiegel/Batch0050/config.json
    comparator/shard.sh RiemannSiegel/Batch0041 … RiemannSiegel/Batch0050

## Regenerating

Much like the project's formal code itself, the batch and reduction challenges are generated from 
project data using Python scripts, and should never be handwritten. 
First, make sure that the project's formal certificates have already been generated using 
`gen_zero_certificates.py`. Then run

    PYTHONPATH=python/src python3 python/src/data_gen/gen_comparator.py comparator

Conversely, `Main` and `Analytic` challenges are handwritten. 
If you run `comparator/shard.sh` then a gitignored `Shard` challenge will appear in your 
directory. 
The `Shard` challenge is what enables multi-batch verification in a single comparator run. 
