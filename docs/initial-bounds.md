# Initial bounds and their proof status

The fork removes all inherited KoalaBear submissions. Initial bounds are
maintained as reusable baseline material and explicit research targets, not as
historical contestant entries.

## Initial lower certificates

`Baselines/InitialLower.lean` proves `ProtocolClaim 5312 1 4` for half rate;
`Baselines/QuarterInitialLower.lean` proves `ProtocolClaim 4339 3 8` for quarter
rate. These use unique decoding, bound the complete combination-round term by
(N+1)/2^192, and separately certify the fixed-query score. They are reusable
baseline theorems, not contestant submissions. The scores are 53.12 and 43.39
bits; improving them toward the 64-bit Johnson marker is the first milestone.

## Construction targets

The mathematical support-tree construction gives the following bounds on the
exact binary prefix domains. The source pairs are E-valued.

| Profile | Agreement | Nonzero bad count (log2, approximate) | Bad-density bits | Attack score ceiling |
|---|---:|---:|---:|---:|
| Half D22 | 17/32 | 137.82999 | 54.17001 | 116.81 |
| Quarter D21 | 9/32 | 130.82990 | 61.17010 | 117.13 |
| Half D23, supplementary | 9/16 | 64.41504 | 127.58496 | 106.25 |

D23 is a supplementary parameter calculation, not a third registered profile.
The exact integers are in [initial-bounds.json](../initial-bounds.json).
The script `python3 scripts/check-initial-bounds.py` reproduces the finite
counting inequalities and integer score comparisons. The Lean arithmetic
module checks these numerical implications as well.

**These numerical certificates are not `ProtocolClaimUpper` proofs.** The
support-tree existence theorem, its exact distinct-label count, and its bridge
to the full unsafe-suffix contract still require Lean formalization. No attack
entry is scored from a numerical certificate alone.

## The mathematical derivation

Let N=2^d, k=N/4, h>=2, m=k/2^h, and H be a fixed hyperplane of D.
The support-tree bank consists of sets A of size k inside H, together with a
fixed affine m-flat W outside H. It has exact quarter-rate agreement k+m and
common agreement k. The correction polynomials have degree at most k, and
division at one exterior pole gives witnesses of degree strictly less than k.

The relevant bank size and total exterior collision budget are

    M = product_{i=0}^{2^h-2} (2^(d-1)-2^i) / delta_h,
    delta_2=3, delta_3=576,
    F = ((k-2m) M^2 + 2m M)/4.

Writing Q=2^192-N, one nonzero-label lower bound is

    M - floor(F/Q) - 1.

The second-moment bound is

    ceil(Q M^2 / (Q M + 2F)) - 1.

Use the stronger of the two bounds. The subtraction of one accounts for
removing the possible zero label. Every advertised count exceeds 2^64.

### Half-rate lift

Choose S inside (D minus H) minus W, with |S|=k. This is possible because
|D minus H|=2k and m<=k/4. Multiply both reciprocal source words and every
witness by the vanishing polynomial V_S.

- Every new witness has degree at most k+(k-1)<2k.
- Its exact agreement set is the disjoint union S, W, A, of size 2k+m.
- The new direction is V_S/(X+beta). For any polynomial G of degree <2k,
  (X+beta)G-V_S is nonzero at beta and has degree at most 2k. Thus direction
  agreement, and consequently common agreement, is at most 2k. Interpolating
  both sources on any 2k points gives equality.
- Labels remain the same evaluations of the original correction polynomials.
  Their distinctness and collision bounds are unchanged.

This gives half-rate agreement 1/2+2^(-h-2): 17/32 at h=3 and 9/16 at h=2.
At D22 the h=2 bank is only about 2^61.415, below the required 2^64. This is
why the first half-rate profile uses h=3. At D23, h=2 clears the threshold.

### Completing the unsafe suffix

The MCA pair covers all radii from 1-T/N up to, but excluding, 1-K/N. At
1-K/N it no longer violates common agreement. A separate ordinary-list
construction is needed for the last band [1-K/N,1-K/N+1/N).

Use the received word X^K. For each K-subset S of D, the polynomial
H_S=X^K-P_S has degree <K and agrees with X^K at exactly S. At an exterior
point beta, pool the nonzero evaluations H_S(beta). Take the first source zero
with claimed evaluation one, and the second source X^K with claimed evaluation
zero. The challenge gamma=1/H_S(beta) admits witness gamma H_S for the folded
claim. The first source cannot have K agreements with a nonzero degree-<K
polynomial, so the initial constrained relation is false. Counting distinct
labels supplies the capacity band. This is an ordinary-list argument, not an
extension of the same false-proximity pair past its valid radius.

## What is still required for a scored attack entry

1. Formalize the finite Boolean support-tree bank, including no overcount.
2. Formalize the locator gaps and exterior-pole collision budget.
3. Formalize the multiplier lift and exact common-agreement statement.
4. Embed the witnesses into the specified IRS winning-set definition.
5. Prove the capacity-band handoff and the entire unsafe suffix.
6. Export the exact `ProtocolClaimUpper` declaration and pass Comparator.

The numerical score and count calculations are available to reuse. They do
not replace any of these semantic obligations.

## Mathematical source

The construction is in the collaborative
[binary-field counterexamples manuscript](https://github.com/GUJustin/binary_field_counterexamples),
with the half-rate lift derived from its support-tree and multiplier arguments.
The field/domain/rate comparison is recorded in [the challenge specification](challenge.md).
