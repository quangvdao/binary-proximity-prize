# Prepare a candidate

The default library build is independent of contestant entries. Each rate has
separate soundness and attack contracts; a proof for one profile cannot be
submitted for the other.

## Choose a track

| Track | Candidate directory | Target import | Candidate theorem |
|---|---|---|---|
| half-lower | `ProximityPrize/SubmissionHalfLower` | `ProximityPrize.Benchmark.TargetLower` | `ProximityPrize.Benchmark.candidate` |
| half-upper | `ProximityPrize/SubmissionHalfUpper` | `ProximityPrize.Benchmark.TargetUpper` | `ProximityPrize.Benchmark.Upper.candidate` |
| quarter-lower | `ProximityPrize/SubmissionQuarterLower` | `ProximityPrize.Benchmark.QuarterTargetLower` | `ProximityPrize.Benchmark.Quarter.candidate` |
| quarter-upper | `ProximityPrize/SubmissionQuarterUpper` | `ProximityPrize.Benchmark.QuarterTargetUpper` | `ProximityPrize.Benchmark.Quarter.Upper.candidate` |

Create a flat directory containing `Solution.lean`, `score.txt`, and either
`radius.txt` for soundness or `unsafe-index.txt` for attack. Helpers must be
flat `.lean` files in the same candidate directory. Put a canonical
nonnegative integer number of centibits in `score.txt`; put an exact positive
fraction P/Q in `radius.txt`, or a positive integer grid index in
`unsafe-index.txt`.

The maximum unsafe index is 2097152 for half rate and 1572864 for quarter
rate. Scores and fractions are validated before a trusted declaration type
is generated.

A lower proof exports `ProtocolClaim B P Q`; an upper proof exports
`ProtocolClaimUpper B i`, in the namespace listed above. Those exact types,
not prose or numeric metadata, determine what has been certified.

## Validate locally

Prepare the optional Comparator tools:

```sh
./setup.sh --verifier
```

On macOS, run an explicitly unranked local diagnostic, for example:

```sh
BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh quarter-upper
```

On Linux with the supported sandbox and tool prerequisites, omit that
variable. Both paths remain local diagnostics: this sample has no registered
independent verifier service. Setup requires Git/network access; the Linux
sandbox additionally needs Go and the supported systemd/Landlock environment.

The preliminary source check permits the matching target, Mathlib, ArkLib,
CompPoly, and same-directory helpers. It rejects cross-track imports and
imports of the local Baselines namespace. You may adapt baseline proofs into
your own candidate directory, but they do not become trusted assumptions.

Comparator checks the submitted declaration against the separately generated
protected type and allows only `propext`, `Classical.choice`, and `Quot.sound`.
The generated target deliberately has a placeholder proof because Comparator
uses its TYPE as the contract; it is ignored by Git and is never a submitted
certificate. Candidate proofs containing `sorry` or extra axioms do not pass.

The local score JSON is written only after the runner reports success and is
marked non-authoritative. Editing a JSON file or running its writer manually
cannot create an accepted proof. Never use local diagnostics as official
better.codes receipts.

## Validation scope of the initial fork

The library build, complete local axiom audit, fixed-score arithmetic, and
contract/parser tests are checked during initialization. The optional
Comparator pipeline has not yet been exercised end to end on a submitted
proof in this fork. No contestant entry or verifier receipt is included.
