/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.Baselines.UniqueDecoding

/-!
# Initial half-rate lower certificate

This is the axiom-clean unique-decoding baseline at radius `1/4`.  It bounds
the complete MCA-plus-list combination-round error and certifies 53.12 bits
for the profile's 128 spot checks.
-/

namespace ProximityPrize.Baselines.InitialLower

open Code ProximityGap ToyProblem
open scoped NNReal

def centiBits : Nat := 5312

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
theorem score_nat :
    (3 : Nat) ^ 12800 * 2 ^ centiBits ≤ 2 ^ 25600 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem score :
    (1 - ProximityPrize.Benchmark.claimedRadius 1 4) ^
        ProximityPrize.Benchmark.IRSProfile.repetitions ≤
      ProximityPrize.Benchmark.claimedError centiBits := by
  have hbase :
      ((3 : NNReal) / 4) ^ (12800 : Nat) ≤
        ((2 : NNReal) ^ centiBits)⁻¹ := by
    rw [div_pow, show ((2 : NNReal) ^ centiBits)⁻¹ =
      1 / (2 : NNReal) ^ centiBits by rw [one_div],
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hcast :
        (((3 : Nat) ^ 12800 * 2 ^ centiBits : Nat) : NNReal) ≤
          ((2 : Nat) ^ 25600 : NNReal) := by
      exact_mod_cast score_nat
    push_cast at hcast
    have hden : (4 : NNReal) ^ (12800 : Nat) = 2 ^ (25600 : Nat) := by
      rw [show (4 : NNReal) = 2 ^ (2 : Nat) by norm_num, ← pow_mul]
    simpa [hden, mul_comm] using hcast
  have hstart :
      ((3 : NNReal) / 4) ^ ((12800 : Nat) : Real) ≤
        (2 : NNReal) ^ (-(centiBits : Real)) := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, NNReal.rpow_natCast]
    exact hbase
  have hmono := NNReal.rpow_le_rpow hstart (by norm_num : (0 : Real) ≤ 1 / 100)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul] at hmono
  rw [show ((12800 : Nat) : Real) * (1 / 100) = ((128 : Nat) : Real) by norm_num,
    show (-(centiBits : Real)) * (1 / 100) =
      -((centiBits : Real) / 100) by ring,
    NNReal.rpow_natCast] at hmono
  rw [ProximityPrize.Benchmark.claimedRadius,
    ProximityPrize.Benchmark.claimedError,
    ProximityPrize.Benchmark.IRSProfile.repetitions]
  rw [show (1 - ((1 : Nat) : NNReal) / ((4 : Nat) : NNReal)) =
      (3 : NNReal) / 4 by
    have hquarter :
        (((1 : Nat) : NNReal) / ((4 : Nat) : NNReal)) ≤ 1 :=
      (div_le_one (by norm_num)).2 (by norm_num)
    apply NNReal.eq
    rw [NNReal.coe_sub hquarter]
    norm_num]
  exact hmono

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem reduction :
    ToyProblem.Impl.IRS.certifiedGammaError
        ProximityPrize.Benchmark.IRSProfile.totalDimension
        ProximityPrize.Benchmark.IRSProfile.interleaving
        ProximityPrize.Benchmark.IRSProfile.domain
        (ProximityPrize.Benchmark.claimedRadius 1 4) ≤
      ProximityPrize.Benchmark.reductionTarget := by
  letI : NeZero ProximityPrize.Benchmark.IRSProfile.interleaving :=
    ⟨by norm_num [ProximityPrize.Benchmark.IRSProfile.interleaving]⟩
  letI : NeZero (ProximityPrize.Benchmark.IRSProfile.totalDimension /
      ProximityPrize.Benchmark.IRSProfile.interleaving) :=
    ⟨by norm_num [ProximityPrize.Benchmark.IRSProfile.totalDimension,
      ProximityPrize.Benchmark.IRSProfile.interleaving]⟩
  have hdim : ProximityPrize.Benchmark.IRSProfile.totalDimension /
      ProximityPrize.Benchmark.IRSProfile.interleaving ≤
        Fintype.card ProximityPrize.Benchmark.IRSProfile.Index := by
    rw [ProximityPrize.Benchmark.IRSProfile.card_index]
    norm_num [ProximityPrize.Benchmark.IRSProfile.totalDimension,
      ProximityPrize.Benchmark.IRSProfile.interleaving,
      ProximityPrize.Benchmark.IRSProfile.domainSize]
  have hdelta : ProximityPrize.Benchmark.claimedRadius 1 4 ≤
      Code.relativeUniqueDecodingRadius
        (ReedSolomon.code ProximityPrize.Benchmark.IRSProfile.domain
          (ProximityPrize.Benchmark.IRSProfile.totalDimension /
            ProximityPrize.Benchmark.IRSProfile.interleaving) :
              Set (ProximityPrize.Benchmark.IRSProfile.Index →
                ProximityPrize.Benchmark.IRSProfile.Field)) := by
    rw [ReedSolomon.relativeUniqueDecodingRadius_RS_eq hdim,
      ProximityPrize.Benchmark.IRSProfile.card_index]
    norm_num [ProximityPrize.Benchmark.claimedRadius,
      ProximityPrize.Benchmark.IRSProfile.totalDimension,
      ProximityPrize.Benchmark.IRSProfile.interleaving,
      ProximityPrize.Benchmark.IRSProfile.domainSize]
    rw [show ((1 : NNReal) - 1 / 2) / 2 = 1 / 4 by
      apply NNReal.eq
      norm_num [NNReal.coe_sub (by norm_num : (1 / 2 : NNReal) ≤ 1)]]
  have hgamma :
      ToyProblem.Impl.IRS.certifiedGammaError
          ProximityPrize.Benchmark.IRSProfile.totalDimension
          ProximityPrize.Benchmark.IRSProfile.interleaving
          ProximityPrize.Benchmark.IRSProfile.domain
          (ProximityPrize.Benchmark.claimedRadius 1 4) ≤
        ((Fintype.card ProximityPrize.Benchmark.IRSProfile.Index + 1 : Nat) : NNReal) /
          Fintype.card ProximityPrize.Benchmark.IRSProfile.Field :=
    UniqueDecoding.certifiedGammaError_le_of_uniqueDecoding
      (F := ProximityPrize.Benchmark.IRSProfile.Field)
    ProximityPrize.Benchmark.IRSProfile.domain
    ProximityPrize.Benchmark.IRSProfile.totalDimension
    ProximityPrize.Benchmark.IRSProfile.interleaving
    (ProximityPrize.Benchmark.claimedRadius 1 4)
    (by norm_num [ProximityPrize.Benchmark.IRSProfile.interleaving])
    (by norm_num [ProximityPrize.Benchmark.claimedRadius])
    (by norm_num [ProximityPrize.Benchmark.claimedRadius])
    hdelta
  calc
    ToyProblem.Impl.IRS.certifiedGammaError
          ProximityPrize.Benchmark.IRSProfile.totalDimension
          ProximityPrize.Benchmark.IRSProfile.interleaving
          ProximityPrize.Benchmark.IRSProfile.domain
          (ProximityPrize.Benchmark.claimedRadius 1 4)
        ≤ ((Fintype.card ProximityPrize.Benchmark.IRSProfile.Index + 1 : Nat) : NNReal) /
            Fintype.card ProximityPrize.Benchmark.IRSProfile.Field := hgamma
    _ ≤ ProximityPrize.Benchmark.reductionTarget := by
      rw [ProximityPrize.Benchmark.IRSProfile.card_index,
        ProximityPrize.Benchmark.BinaryField192.card_field]
      rw [show ProximityPrize.Benchmark.reductionTarget =
          1 / (2 : NNReal) ^ (128 : Nat) by
        norm_num [ProximityPrize.Benchmark.reductionTarget,
          ProximityGap.prizeThreshold]]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      norm_num [ProximityPrize.Benchmark.IRSProfile.domainSize]

/-- The initial half-rate benchmark certificate: 53.12 bits at radius `1/4`. -/
theorem certificate : ProximityPrize.Benchmark.ProtocolClaim centiBits 1 4 where
  admissible := by
    constructor <;>
      norm_num [ProximityPrize.Benchmark.claimedRadius,
        ProximityPrize.Benchmark.IRSProfile.minRelativeDistance]
  reduction := reduction
  score := score

end ProximityPrize.Baselines.InitialLower
