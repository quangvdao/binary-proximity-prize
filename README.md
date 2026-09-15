# Binary proximity challenge

A sample Lean competition for half-rate and quarter-rate Reed–Solomon codes on
LeanVM's exact binary-field evaluation domains. Forked from
[the Proximity Prize](https://github.com/proximity-prize/proximity-prize).
All inherited contestant submissions have been removed.

| Profile | Exact domain | RS dimension | Rate | Challenge field |
|---|---|---:|---:|---|
| Direct aggregation | D22, length 2^22 | 2^21 | 1/2 | GF(2^192) |
| Recursion | D21, length 2^21 | 2^19 | 1/4 | GF(2^192) |

Both use 64 interleaving lanes. Half rate uses 256 scoring queries; quarter
rate uses 128. At the asymptotic Johnson agreement, both choices give a
128-bit query score. The base field is
GF(2^64) with modulus X^64+X^4+X^3+X+1; the cubic extension has modulus
Y^3+Y+1. D_d is the span of the first d powers of the base-field generator.
The main challenge allows extension-valued sources.

There are four tracks: `half-lower`, `half-upper`, `quarter-lower`, and
`quarter-upper`. Soundness entries maximize query bits at a certified safe
radius. Combinatorial upper-bound entries minimize query bits at a certified unsafe suffix. The
algebraic error target is always 2^-128; the query score is a separate quantity.

## Build and inspect

Install [elan](https://github.com/leanprover/elan), then run:

```sh
./setup.sh
```

This builds the pinned Lean library, checks the axiom closure, and reproduces
the initial finite arithmetic. It does not build or submit contestant code.
For an already initialized workspace:

```sh
LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true lake build
lake env lean scripts/check-axioms.lean
python3 scripts/check-initial-bounds.py
python3 scripts/test-contract.py
```

The repository contains no `Submission*/Solution.lean` entries. Read
[how to prepare a candidate](docs/submissions.md) to create one.

## Initial bounds

The baseline files distinguish unique-decoding lower certificates (106.24 bits
at half rate and 86.79 bits at quarter rate) from numerical support
for upper constructions. See [the exact proof status](docs/initial-bounds.md).

| Profile | Mathematical upper target | Agreement | Lean status |
|---|---:|---:|---|
| Half D22 | 233.61 bits | 17/32 | Count/score arithmetic; construction proof pending |
| Quarter D21 | 234.25 bits | 9/32 | Count/score arithmetic; construction proof pending |
| Supplementary half D23 | 212.50 bits | 9/16 | Count/score arithmetic; no additional contest profile |

These upper targets are not accepted submissions or full `ProtocolClaimUpper`
proofs. A contestant must prove the support construction and the entire unsafe
suffix, not just the numeric inequalities.

## Where to work

- [Challenge specification](docs/challenge.md): fields, domains, scoring,
  source alphabets, and exact track contracts.
- [Initial bounds](docs/initial-bounds.md): support-tree construction,
  half-rate lift, capacity endpoint, and formalization obligations.
- `ProximityPrize/Benchmark/`: protected field, domain, profile, and targets.
- `ProximityPrize/Baselines/`: reusable initial Lean results.
- `initial-bounds.json`: exact finite construction targets.

This fork has **no official better.codes verifier registration, leaderboard,
or prize**. Optional local Comparator checks are diagnostics. The challenge
is an algebraic research benchmark, not an end-to-end LeanVM attack claim.
The existing `ProximityPrize` Lean namespace is retained for compatibility;
all runner identifiers are specific to this binary sample.
