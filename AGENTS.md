# Binary proximity challenge

Work directly on main in this fork. Do not send submissions or requests to the
upstream better.codes verifier. This is an independent sample challenge.

## Mathematical contract

The primary profiles are the exact LeanVM polynomial-prefix domains D22 at
half rate and D21 at quarter rate over the 64-bit field, both with 192-bit
challenges and 64 interleaving lanes; half rate uses 128 scoring queries and quarter rate uses 64. Preserve the distinction between base-valued initial
sources and the unrestricted extension-valued sources in the main challenge.
The upper contract requires an entire unsafe suffix, including the capacity
endpoint; one MCA counterexample does not by itself discharge that contract.

Never relabel an arithmetic bound or a conditional theorem as a completed
ProtocolClaim. Do not introduce sorry, new axioms, or native_decide into the
protected profile or baseline proofs. Check the full axiom closure. Explicitly
mark mathematical constructions whose Lean formalization remains incomplete.
The root library and baselines must build without any contestant submission.

## Development

Use bounded independent agents for substantial proof changes, with disjoint
file ownership. One agent owns Lake builds; do not concurrently rebuild shared
dependency-cache entries. Respect the pinned Lake manifest and toolchain.
Use LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true for builds in Documents/Lean.

Keep only the challenge, reusable baseline material, and concise documentation.
Old contest submissions belong in Git history, not another archive directory.

## Candidate validation

All four SubmissionHalf*/SubmissionQuarter* candidate roots start absent. Each candidate root must be
flat and contain Solution.lean, score.txt, and radius.txt (lower) or
unsafe-index.txt (upper). Imports may use the matching protected target,
Mathlib, ArkLib, CompPoly, and helpers in the same candidate root. Cross-track
imports and imports of the local Baselines namespace are not allowed.
The textual import check is a preliminary filter; the Comparator validates
exact declaration types and the permitted axiom closure. Its local results
are diagnostics, not official leaderboard receipts.

Do not restore hosted-verifier workflows, credentials, fleet assumptions, or
upstream challenge identifiers. Local setup and optional Comparator setup are
separate. Preserve the Apache license and upstream copyright notices.
