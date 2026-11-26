# Boolean circuit research archive

[Read the research memo](MEMO.md) for the results, evidence, and open cases.
This archive covers 28 swarm assignments. The formal submissions are
preserved alongside the exploratory work, including failed searches.

| Entry | Contents |
| --- | --- |
| [Petersen graph reduction](submissions/R_meta_7893_1.lean) | Symmetry reduction to three premises. [Swarm PR #21990](https://github.com/open-goat/pequalnp-proofs/pull/21990) |
| [Nine-bit majority](submissions/L_meta_18232.lean) | Thirty binary AND/OR gates, checked on every input. [Swarm PR #22816](https://github.com/open-goat/pequalnp-proofs/pull/22816) |
| [Assignment index](assignments.json) | Original formal statements, identifiers and modules. |
| [Working files](work/) | Lean source, search programs, instances, solver certificates, numerical outputs and check logs. |

## Where to start in the working files

- [Two-point incidence](work/TwoPoints2056.lean) and
  [shared ORs](work/SharedOr2056.lean) study the cost of reusing an input pair.
- [The 25-vertex graph](work/Optimum9738.lean) has a 59-gate optimum
  under the stated degree restriction.
- [Fano witnesses](work/WitnessDegree4928.lean) and the
  [prefix bound](work/LongPrefix4928.lean) delimit the 27-gate question.
- [The star counting lemma](work/StarCost4697.lean) is the last result.
  A stronger accounting result already exists upstream. The missing step
  is a lower bound for unrestricted circuits.

## Checking a result

Use the repository's pinned Lean toolchain and Lake dependencies. From the
repository root, check either submission directly, for example:

```sh
cd lean
lake build PEqualNP.Defs
lake env lean ../research/2026-11-25/submissions/L_meta_18232.lean
```

Local helper imports use the short names of other files in the work folder.
For the final counting result, run this from the repository root:

```sh
cd lean
lake env bash -c '
  set -eu
  src=../research/2026-11-25/work
  obj=$(mktemp -d)
  export LEAN_PATH="$obj:$LEAN_PATH"
  for mod in PoolCharge4697 PackedCharge4697 StarCost4697; do
    lean --root="$src" -o "$obj/$mod.olean" "$src/$mod.lean"
  done
'
```

The original working checkout was based on commit
`3ee6584f765446ba5f509eef0de6c1a4c555a563`. Later work also used modules
from upstream. Search scripts retain their original paths. Scripts referring
to `.pnp/` expect the working files there in a disposable checkout.
Historical logs report individual runs. They include errors, timeouts and
superseded drafts. An assignment statement, a candidate witness, or a search
timeout on its own provides no proof. The linked PRs carry the project's
verdicts. Compiled caches, duplicate project catalogs, and private lease
records are omitted.
