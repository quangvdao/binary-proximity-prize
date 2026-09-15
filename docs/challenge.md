# Binary proximity challenge specification

This is a sample research challenge, forked from the Proximity Prize. It has no
official better.codes leaderboard, hosted verifier registration, prize, or
end-to-end LeanVM security claim.

## Two concrete profiles

Both use LeanVM's field presentation:

- F = GF(2)[u]/(u^64 + u^4 + u^3 + u + 1).
- E = F[v]/(v^3 + v + 1), of cardinality 2^192.
- D_d is the span over GF(2) of 1,u,...,u^(d-1), embedded in E.
- The RS code has strict polynomial degree bound K.
- Each interleaved column has 64 coordinates; received words are unrestricted
  E-valued words, not just base-valued initial commitments.

| Profile | Domain | N | K | Rate | Total message dimension | Scoring queries |
|---|---|---:|---:|---:|---:|---:|
| Half | D22 | 2^22 | 2^21 | 1/2 | 2^27 | 128 |
| Quarter | D21 | 2^21 | 2^19 | 1/4 | 2^25 | 64 |

The half-rate size corresponds to the current direct 900-XMSS benchmark; the
quarter-rate size corresponds to its 2-to-1 recursion benchmark. These sizes
are inferred by rounding the reported committed stack size upward to a power
of two and applying LeanVM's 64-lane layout. This pins examples, not every
possible LeanVM workload. The source snapshot is
[leanVM b7a10725](https://github.com/leanEthereum/leanVM/tree/b7a1072565e17a222e31924ff96f79a8e5cab458),
with [benchmarks](https://github.com/leanEthereum/leanVM/blob/b7a1072565e17a222e31924ff96f79a8e5cab458/README.md)
and [configuration](https://github.com/leanEthereum/leanVM/blob/b7a1072565e17a222e31924ff96f79a8e5cab458/crates/pcs/src/whir_config.rs).
The half-rate count matches the current better.codes challenge. The quarter-rate
count is halved so its Johnson and capacity reference scores match half rate.
These are contest conventions, not LeanVM's query schedule.

## Four tracks

Write delta for relative Hamming distance, a=1-delta for agreement, and B for
an integer number of centibits. All profiles fix epsilon*=2^-128. Set t=128 for
half rate and t=64 for quarter rate.

A **soundness** entry proves:

1. 0 < delta < (N-K+1)/N;
2. ArkLib's certified IRS combination-round error at delta is <= epsilon*;
3. a^t <= 2^(-B/100).

Its score is B/100, and larger is better. This is an upper bound on the
certified reduction error at one radius, not a proof that the bound is optimal.

A **combinatorial upper-bound** entry gives an integer unsafe index i, delta*=i/N, and proves:

1. 0 < delta* < (N-K+1)/N;
2. winningSetDensity(delta) > epsilon* for EVERY
   delta in [delta*, (N-K+1)/N);
3. 2^(-B/100) <= (1-delta*)^t.

Its score is B/100, and smaller is better. The entire suffix is required;
monotonicity of winningSetDensity is not assumed. The maximum allowed index is
N-K: 2^21 for half rate and 3*2^19 for quarter rate.

The exact protected theorem types are the authority:

| Track | Target | Exported candidate namespace |
|---|---|---|
| half-lower | `ProximityPrize.Benchmark.TargetLower` | `ProximityPrize.Benchmark` |
| half-upper | `ProximityPrize.Benchmark.TargetUpper` | `ProximityPrize.Benchmark.Upper` |
| quarter-lower | `ProximityPrize.Benchmark.QuarterTargetLower` | `ProximityPrize.Benchmark.Quarter` |
| quarter-upper | `ProximityPrize.Benchmark.QuarterTargetUpper` | `ProximityPrize.Benchmark.Quarter.Upper` |

The public namespace `ProximityPrize` is retained from the fork. All challenge
identifiers and local score paths are specific to this binary sample.

The reduction threshold and bit score follow better.codes and remain separate.
A score of 128 does not certify combined error at most 2^-128: combining two
terms each at most 2^-128 can give a bound close to 2^-127.

## What a bad count establishes

For a source pair with common agreement below T, a set of more than 2^64
challenges admitting T-agreement witnesses has density greater than 2^-128.
Embedding the scalar pair into one interleaving coordinate and taking the zero
linear constraint gives the corresponding winning-set lower bound while the
source pair still violates the required common-agreement threshold.

An upper entry bounds this algebraic threshold; it does not supply an
end-to-end attacking prover.

The bad-density exponent and the query score are different quantities. A
count of roughly 2^137.83 in E gives density roughly 2^-54.17. At agreement
17/32 it supports a 116.81-bit query-score ceiling, not a claim of 54-bit or
116-bit end-to-end LeanVM security.

If both sources are F-valued, every exceptional challenge above common
agreement belongs to F, by coefficientwise projection on the independent
coordinates 1,z for z outside F. Hence this MCA count is at most 2^64. It cannot
meet the strict attack target by itself. The unrestricted E-valued profile
models the broader algebraic reduction problem; reachability and compatibility
with actual opening constraints are additional protocol questions.

## Reference markers

These asymptotic markers help interpret scores. They are not automatically
finite Lean certificates.

| Rate | Unique-decoding agreement | Johnson agreement | Capacity agreement |
|---|---:|---:|---:|
| 1/2 | 3/4 (53.12 bits) | sqrt(1/2) (64 bits) | 1/2 (128 bits) |
| 1/4 | 5/8 (43.39 bits) | 1/2 (64 bits) | 1/4 (128 bits) |

See [initial bounds](initial-bounds.md) for the distinction between completed
certificates and construction targets.
