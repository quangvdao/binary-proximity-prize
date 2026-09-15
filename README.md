# Binary proximity challenge

This repository defines a sample Lean competition for half-rate and
quarter-rate interleaved Reed–Solomon codes on concrete binary-field domains
used by LeanVM. It is forked from
[the Proximity Prize](https://github.com/proximity-prize/proximity-prize), whose
current half-rate challenge uses 128 queries. All inherited contestant
submissions have been removed.

The challenge asks where the combination-round error crosses `2^-128`. The
leaderboard score is the separate fixed-query quantity

```text
B = -t log2(1 - delta) bits.
```

Half rate uses `t = 128`; quarter rate uses `t = 64`. These choices put the
Johnson reference at 64 bits and the capacity reference at 128 bits for both
profiles. They are competition parameters, not claims about LeanVM's deployed
query schedule.

## Concrete profiles

Let

```text
F = GF(2)[u] / (u^64 + u^4 + u^3 + u + 1),
E = F[v] / (v^3 + v + 1) = GF(2^192),
D_d = span_GF(2)(1, u, ..., u^(d-1)) ⊆ F ⊆ E.
```

The Lean development proves these field presentations, the exact prefix
domains, and the following code parameters.

| Profile | Domain | Length `N` | Per-lane dimension `K` | Rate | Queries |
|---|---|---:|---:|---:|---:|
| Half | `D_22` | `2^22` | `2^21` | `1/2` | 128 |
| Quarter | `D_21` | `2^21` | `2^19` | `1/4` | 64 |

There are 64 interleaving lanes. A received word is an arbitrary function

```text
D_d → (GF(2^192))^64.
```

A codeword is `x ↦ (P_0(x), ..., P_63(x))`, with every `deg P_j < K`.
Agreement is blockwise over the `N` domain points: a point agrees only when all
64 lanes agree there. Scalar constructions embed without loss by using one
active lane and 63 zero lanes.

## What the four tracks prove

For a radius `delta`, the toy problem considers two arbitrary received words
`f_1, f_2`, a linear functional `v` on messages, and claimed values
`mu_1, mu_2`. The pair is violating when no two codewords both

1. agree with `f_1, f_2` on one common set of at least `(1-delta)N` blocks; and
2. have messages satisfying `<M_i,v> = mu_i`.

A challenge `gamma ∈ GF(2^192)` is winning when `f_1 + gamma f_2` is
`delta`-close to a codeword satisfying the combined claim
`<M,v> = mu_1 + gamma mu_2`.

`winningSetDensity(delta)` is the supremum, over every violating tuple
`(v, mu_1, mu_2, f_1, f_2)`, of the fraction of winning challenges. Thus the
source words are **not fixed by the challenge**.

- A `lower` entry chooses one admissible `delta`, proves ArkLib's universal
  `certifiedGammaError(delta) <= 2^-128`, and maximizes the induced bit score.
- An `upper` entry chooses `delta*`, proves
  `winningSetDensity(delta) > 2^-128` for every admissible
  `delta >= delta*`, and minimizes the induced bit score.

The upper condition is universal over radii, but the violating tuple inside
the supremum may depend on the radius. It does not require one received pair to
work throughout the suffix. The protected Lean theorem types in
[`ProximityPrize/Benchmark`](ProximityPrize/Benchmark) are authoritative.

| Track | Objective | Candidate theorem |
|---|---|---|
| `half-lower` | maximize certified bits | `ProximityPrize.Benchmark.ProtocolClaim` |
| `half-upper` | minimize combinatorial upper bits | `ProximityPrize.Benchmark.Upper.ProtocolClaimUpper` |
| `quarter-lower` | maximize certified bits | `ProximityPrize.Benchmark.Quarter.ProtocolClaim` |
| `quarter-upper` | minimize combinatorial upper bits | `ProximityPrize.Benchmark.Quarter.Upper.ProtocolClaimUpper` |

The `2^-128` combination-round threshold and the displayed query score are
different quantities. In particular, a 128-bit query score does not by itself
prove that their sum is at most `2^-128`.

## Initial bounds and proof status

| Profile | Proved lower certificate | Current upper target | Upper-target status |
|---|---:|---:|---|
| Half `D_22` | 53.12 bits at agreement `3/4` | 116.81 bits at agreement `17/32` | exact count and score proved; construction bridge pending |
| Quarter `D_21` | 43.39 bits at agreement `5/8` | 117.13 bits at agreement `9/32` | exact count and score proved; construction bridge pending |

The lower certificates are universal unique-decoding bounds for the complete
MCA-plus-list combination term. They are full `ProtocolClaim` theorems.

The upper targets come from explicit reciprocal support-tree pairs. In the
quarter-rate construction, for an exterior pole `beta`, write

```text
f(x) = R(x)/(x+beta),     g(x) = 1/(x+beta).
```

Their common agreement with two degree-`<K` codewords is exactly `K=N/4`,
while many combinations `f + gamma g` have agreement `K+m=9N/32`. For half
rate, multiplying both words by a fixed vanishing polynomial gives common
agreement `N/2` and combination agreement `17N/32`. Embedding these scalar
pairs in one lane preserves those block agreements.

For the concrete domains, the checked bad-challenge counts have densities
about `2^-54.17` at half rate and `2^-61.17` at quarter rate, both above
`2^-128`. Lean currently proves the finite counts and score inequalities. It
does not yet formalize the support-tree construction, its embedding into
`winningSetDensity`, or the separate ordinary-list argument needed for the
final `1/N`-wide capacity band. Therefore 116.81 and 117.13 are research
targets, not accepted `ProtocolClaimUpper` certificates.

See [the challenge specification](docs/challenge.md) for the exact quantifiers
and [the initial-bounds note](docs/initial-bounds.md) for the construction and
remaining proof obligations.

## Build and inspect

Install [elan](https://github.com/leanprover/elan), then run:

```sh
./setup.sh
```

This builds the pinned Lean library, audits its axiom closure, and reproduces
the finite arithmetic. For an initialized workspace, the individual checks
are:

```sh
LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true lake build
lake env lean scripts/check-axioms.lean
python3 scripts/check-initial-bounds.py
python3 scripts/test-contract.py
```

The repository starts with no contestant `Solution.lean`. Read
[how to prepare a candidate](docs/submissions.md) for the four local tracks.

This fork has no official better.codes registration, hosted verifier,
leaderboard, or prize. Optional Comparator runs are local diagnostics. The
benchmark studies the algebraic reduction and is not an end-to-end LeanVM
attack claim.
