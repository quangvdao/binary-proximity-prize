/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.ProofSystem.ToyProblem.Codegen

/-!
# Arithmetic baselines for support-tree upper candidates

This file checks the finite arithmetic behind support-tree constructions
after the degree-doubling multiplier lift from quarter rate to half rate.  It
does **not** formalize the support construction, the multiplier lift, the
collision-pooling theorem, or a `ProtocolClaimUpper`.  Accordingly, the three
results below are numerical candidates rather than benchmark certificates.
The spot-check inequalities use 128 queries for half rate and 64 queries for
quarter rate. They do not supply the missing winning-set suffix theorem.

For height `h`, the number of distinct half-supports on a `v`-dimensional
binary active space is

`B_h(v) = (prod i < 2^h - 1, (2^v - 2^i)) / delta_h`,

where `delta_2 = 3` and `delta_3 = 576`.  For one fixed active space the
pair-collision budget is

`F_0 = ((K - 2m) M_0^2 + 2m M_0) / 4`.

At a challenge-field size `q`, collision pooling certifies the arithmetic
count `M_0 - floor(F_0 / (q - N)) - 1`.  Formalizing the hypotheses that make
this arithmetic count a winning-set lower bound is deliberately left outside
this module.
-/

namespace ProximityPrize.Baselines.SupportTreeCandidates

open scoped NNReal

/-- The essential binary dimension of a height-`h` support tree. -/
def essentialDimension (h : Nat) : Nat := 2 ^ h - 1

/-- Support-tree normalization, with `delta_2 = 3` and
`delta_(h+1) = 2^(2(2^h-1)) delta_h^2` for `h ≥ 2`. -/
def treeDenominator : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | h + 1 => 2 ^ (2 * (2 ^ h - 1)) * treeDenominator h ^ 2

/-- Exact fixed-active-space support-tree count. -/
def supportTreeCount (v h : Nat) : Nat :=
  ((Finset.range (essentialDimension h)).prod fun i => 2 ^ v - 2 ^ i) /
    treeDenominator h

/-- Pair-collision budget for a fixed active-space bank. -/
def fixedBankCollisionBudget (K m M : Nat) : Nat :=
  ((K - 2 * m) * M ^ 2 + 2 * m * M) / 4

/-- The first-moment collision-pooling count, with a possible zero label removed. -/
def pooledNonzeroLabels (N q K m M : Nat) : Nat :=
  M - fixedBankCollisionBudget K m M / (q - N) - 1

/-- These are arithmetic candidates; no protocol upper certificate is proved here. -/
inductive BoundaryStatus where
  | numericalCandidate
  | protocolCertified
  deriving DecidableEq

/-! ## Half-rate candidate from `N = 2^22`, height three -/

namespace N22H3

def N : Nat := 2 ^ 22
def q : Nat := 2 ^ 192
def K : Nat := N / 4
def m : Nat := K / 8
def M0 : Nat := supportTreeCount 21 3
def F0 : Nat := fixedBankCollisionBudget K m M0
def badLabels : Nat := pooledNonzeroLabels N q K m M0
def agreementNumerator : Nat := 17
def agreementDenominator : Nat := 32
def repetitions : Nat := 128
def centiBits : Nat := 11681
def status : BoundaryStatus := .numericalCandidate

set_option maxRecDepth 100000 in
theorem M0_eq :
    M0 = 309713815693517644672002215228857724928000 := by
  decide

set_option maxRecDepth 100000 in
theorem F0_eq :
    F0 =
      18859159905521804866353990796318363631129729739711547630920174134878245137499876753408000 := by
  decide

set_option maxRecDepth 100000 in
theorem collisionQuotient_eq :
    F0 / (q - N) = 3004437509624025023904710676751 := by
  decide

set_option maxRecDepth 100000 in
theorem badLabels_eq :
    badLabels = 309713815690513207162378190204953014251248 := by
  decide

theorem agreement_eq :
    K + (K + m) = N * agreementNumerator / agreementDenominator := by
  norm_num [N, K, m, agreementNumerator, agreementDenominator]

theorem badLabels_gt_two_pow_64 : 2 ^ 64 < badLabels := by
  rw [badLabels_eq]
  norm_num

theorem status_eq : status = .numericalCandidate := rfl

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
theorem score_nat : (2 : Nat) ^ 52319 ≤ 17 ^ 12800 := by
  decide

theorem score :
    (2 : NNReal) ^ (-((centiBits : Real) / 100)) ≤
      ((agreementNumerator : NNReal) / agreementDenominator) ^ repetitions := by
  have hnat : (2 : Nat) ^ 64000 ≤ 2 ^ centiBits * 17 ^ 12800 := by
    calc
      (2 : Nat) ^ 64000 = 2 ^ centiBits * 2 ^ 52319 := by
        norm_num [centiBits, ← pow_add]
      _ ≤ 2 ^ centiBits * 17 ^ 12800 := Nat.mul_le_mul_left _ score_nat
  have hbase :
      ((2 : NNReal) ^ centiBits)⁻¹ ≤ ((17 : NNReal) / 32) ^ (12800 : Nat) := by
    rw [div_pow, le_div_iff₀ (by positivity), inv_mul_eq_div,
      div_le_iff₀ (by positivity)]
    have hcast :
        ((2 : Nat) ^ 64000 : NNReal) ≤
          ((2 ^ centiBits * 17 ^ 12800 : Nat) : NNReal) := by
      exact_mod_cast hnat
    push_cast at hcast
    have hden : (32 : NNReal) ^ (12800 : Nat) = 2 ^ (64000 : Nat) := by
      rw [show (32 : NNReal) = 2 ^ (5 : Nat) by norm_num, ← pow_mul]
    simpa [hden, mul_comm] using hcast
  have hstart :
      (2 : NNReal) ^ (-(centiBits : Real)) ≤
        ((17 : NNReal) / 32) ^ ((12800 : Nat) : Real) := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, NNReal.rpow_natCast]
    exact hbase
  have hmono := NNReal.rpow_le_rpow hstart (by norm_num : (0 : Real) ≤ 1 / 100)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul] at hmono
  rw [show (-(centiBits : Real)) * (1 / 100) =
      -((centiBits : Real) / 100) by ring,
    show ((12800 : Nat) : Real) * (1 / 100) = ((128 : Nat) : Real) by norm_num,
    NNReal.rpow_natCast] at hmono
  simpa [agreementNumerator, agreementDenominator, repetitions] using hmono

end N22H3

/-! ## Half-rate candidate from `N = 2^23`, height two -/

namespace N23H2

def N : Nat := 2 ^ 23
def q : Nat := 2 ^ 192
def K : Nat := N / 4
def m : Nat := K / 4
def M0 : Nat := supportTreeCount 22 2
def F0 : Nat := fixedBankCollisionBudget K m M0
def badLabels : Nat := pooledNonzeroLabels N q K m M0
def agreementNumerator : Nat := 9
def agreementDenominator : Nat := 16
def repetitions : Nat := 128
def centiBits : Nat := 10625
def status : BoundaryStatus := .numericalCandidate

set_option maxRecDepth 100000 in
theorem M0_eq : M0 = 24595617716531538600 := by
  decide

set_option maxRecDepth 100000 in
theorem F0_eq :
    F0 = 158582547639896662892786175495326006928998400 := by
  decide

set_option maxRecDepth 100000 in
theorem collisionQuotient_eq_zero : F0 / (q - N) = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem badLabels_eq : badLabels = 24595617716531538599 := by
  decide

theorem agreement_eq :
    K + (K + m) = N * agreementNumerator / agreementDenominator := by
  norm_num [N, K, m, agreementNumerator, agreementDenominator]

theorem badLabels_gt_two_pow_64 : 2 ^ 64 < badLabels := by
  rw [badLabels_eq]
  norm_num

theorem status_eq : status = .numericalCandidate := rfl

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
theorem score_nat : (2 : Nat) ^ 40575 ≤ 9 ^ 12800 := by
  decide

theorem score :
    (2 : NNReal) ^ (-((centiBits : Real) / 100)) ≤
      ((agreementNumerator : NNReal) / agreementDenominator) ^ repetitions := by
  have hnat : (2 : Nat) ^ 51200 ≤ 2 ^ centiBits * 9 ^ 12800 := by
    calc
      (2 : Nat) ^ 51200 = 2 ^ centiBits * 2 ^ 40575 := by
        norm_num [centiBits, ← pow_add]
      _ ≤ 2 ^ centiBits * 9 ^ 12800 := Nat.mul_le_mul_left _ score_nat
  have hbase :
      ((2 : NNReal) ^ centiBits)⁻¹ ≤ ((9 : NNReal) / 16) ^ (12800 : Nat) := by
    rw [div_pow, le_div_iff₀ (by positivity), inv_mul_eq_div,
      div_le_iff₀ (by positivity)]
    have hcast :
        ((2 : Nat) ^ 51200 : NNReal) ≤
          ((2 ^ centiBits * 9 ^ 12800 : Nat) : NNReal) := by
      exact_mod_cast hnat
    push_cast at hcast
    have hden : (16 : NNReal) ^ (12800 : Nat) = 2 ^ (51200 : Nat) := by
      rw [show (16 : NNReal) = 2 ^ (4 : Nat) by norm_num, ← pow_mul]
    simpa [hden, mul_comm] using hcast
  have hstart :
      (2 : NNReal) ^ (-(centiBits : Real)) ≤
        ((9 : NNReal) / 16) ^ ((12800 : Nat) : Real) := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, NNReal.rpow_natCast]
    exact hbase
  have hmono := NNReal.rpow_le_rpow hstart (by norm_num : (0 : Real) ≤ 1 / 100)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul] at hmono
  rw [show (-(centiBits : Real)) * (1 / 100) =
      -((centiBits : Real) / 100) by ring,
    show ((12800 : Nat) : Real) * (1 / 100) = ((128 : Nat) : Real) by norm_num,
    NNReal.rpow_natCast] at hmono
  simpa [agreementNumerator, agreementDenominator, repetitions] using hmono

end N23H2

/-! ## Quarter-rate candidate from `N = 2^21`, height three -/

namespace QuarterN21H3

def N : Nat := 2 ^ 21
def q : Nat := 2 ^ 192
def K : Nat := N / 4
def m : Nat := K / 8
def M0 : Nat := supportTreeCount 20 3
def F0 : Nat := fixedBankCollisionBudget K m M0
def badLabels : Nat := pooledNonzeroLabels N q K m M0
def agreementNumerator : Nat := 9
def agreementDenominator : Nat := 32
def unsafeIndex : Nat := 1507328
def centiBits : Nat := 11713
def repetitions : Nat := 64
def status : BoundaryStatus := .numericalCandidate

set_option maxRecDepth 100000 in
theorem M0_eq : M0 = 2419492655753877318639150109884493824000 := by
  decide

set_option maxRecDepth 100000 in
theorem F0_eq :
    F0 =
      575466180894420201898511654994690645374661406375934022738974737045661726206328832000 := by
  decide

set_option maxRecDepth 100000 in
theorem collisionQuotient_eq :
    F0 / (q - N) = 91677051791318537469208530 := by
  decide

set_option maxRecDepth 100000 in
theorem badLabels_eq :
    badLabels = 2419492655753785641587358791347024615469 := by
  decide

theorem agreement_eq :
    K + m = N * agreementNumerator / agreementDenominator := by
  norm_num [N, K, m, agreementNumerator, agreementDenominator]

theorem unsafeIndex_eq :
    unsafeIndex = N * (agreementDenominator - agreementNumerator) /
      agreementDenominator := by
  norm_num [unsafeIndex, N, agreementNumerator, agreementDenominator]

theorem badLabels_gt_two_pow_128 : 2 ^ 128 < badLabels := by
  rw [badLabels_eq]
  norm_num

theorem status_eq : status = .numericalCandidate := rfl

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
theorem score_nat : (2 : Nat) ^ 20287 ≤ 9 ^ 6400 := by
  decide

theorem score :
    (2 : NNReal) ^ (-((centiBits : Real) / 100)) ≤
      ((agreementNumerator : NNReal) / agreementDenominator) ^ (64 : Nat) := by
  have hnat : (2 : Nat) ^ 32000 ≤ 2 ^ centiBits * 9 ^ 6400 := by
    calc
      (2 : Nat) ^ 32000 = 2 ^ centiBits * 2 ^ 20287 := by
        norm_num [centiBits, ← pow_add]
      _ ≤ 2 ^ centiBits * 9 ^ 6400 :=
        Nat.mul_le_mul_left _ score_nat
  have hbase :
      ((2 : NNReal) ^ centiBits)⁻¹ ≤ ((9 : NNReal) / 32) ^ (6400 : Nat) := by
    rw [div_pow, le_div_iff₀ (by positivity), inv_mul_eq_div,
      div_le_iff₀ (by positivity)]
    have hcast :
        ((2 : Nat) ^ 32000 : NNReal) ≤
          ((2 ^ centiBits * 9 ^ 6400 : Nat) : NNReal) := by
      exact_mod_cast hnat
    push_cast at hcast
    have hden : (32 : NNReal) ^ (6400 : Nat) = 2 ^ (32000 : Nat) := by
      rw [show (32 : NNReal) = 2 ^ (5 : Nat) by norm_num, ← pow_mul]
    simpa [hden, mul_comm] using hcast
  have hstart :
      (2 : NNReal) ^ (-(centiBits : Real)) ≤
        ((9 : NNReal) / 32) ^ ((6400 : Nat) : Real) := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, NNReal.rpow_natCast]
    exact hbase
  have hmono := NNReal.rpow_le_rpow hstart (by norm_num : (0 : Real) ≤ 1 / 100)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul] at hmono
  rw [show (-(centiBits : Real)) * (1 / 100) =
      -((centiBits : Real) / 100) by ring,
    show ((6400 : Nat) : Real) * (1 / 100) = ((64 : Nat) : Real) by norm_num,
    NNReal.rpow_natCast] at hmono
  simpa [agreementNumerator, agreementDenominator, repetitions] using hmono

end QuarterN21H3

end ProximityPrize.Baselines.SupportTreeCandidates
