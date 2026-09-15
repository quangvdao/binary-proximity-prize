/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.QuarterTargetLower
import ProximityPrize.Baselines.UniqueDecoding

/-!
# Initial quarter-rate lower certificate

This is the axiom-clean unique-decoding baseline at radius `3/8`.  It bounds
the complete MCA-plus-list combination-round error and certifies 43.39 bits
for the profile's 64 spot checks.
-/

namespace ProximityPrize.Baselines.QuarterInitialLower

open Code ProximityGap ToyProblem
open scoped NNReal

def centiBits : Nat := 4339

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
theorem score_nat :
    (5 : Nat) ^ 6400 * 2 ^ centiBits ≤ 2 ^ 19200 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem score :
    (1 - ProximityPrize.Benchmark.Quarter.claimedRadius 3 8) ^
        ProximityPrize.Benchmark.QuarterRateProfile.repetitions ≤
      ProximityPrize.Benchmark.Quarter.claimedError centiBits := by
  have hbase :
      ((5 : NNReal) / 8) ^ (6400 : Nat) ≤
        ((2 : NNReal) ^ centiBits)⁻¹ := by
    rw [div_pow, show ((2 : NNReal) ^ centiBits)⁻¹ =
      1 / (2 : NNReal) ^ centiBits by rw [one_div],
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hcast :
        (((5 : Nat) ^ 6400 * 2 ^ centiBits : Nat) : NNReal) ≤
          ((2 : Nat) ^ 19200 : NNReal) := by
      exact_mod_cast score_nat
    push_cast at hcast
    have hden : (8 : NNReal) ^ (6400 : Nat) = 2 ^ (19200 : Nat) := by
      rw [show (8 : NNReal) = 2 ^ (3 : Nat) by norm_num, ← pow_mul]
    simpa [hden, mul_comm] using hcast
  have hstart :
      ((5 : NNReal) / 8) ^ ((6400 : Nat) : Real) ≤
        (2 : NNReal) ^ (-(centiBits : Real)) := by
    rw [NNReal.rpow_neg, NNReal.rpow_natCast, NNReal.rpow_natCast]
    exact hbase
  have hmono := NNReal.rpow_le_rpow hstart (by norm_num : (0 : Real) ≤ 1 / 100)
  rw [← NNReal.rpow_mul, ← NNReal.rpow_mul] at hmono
  rw [show ((6400 : Nat) : Real) * (1 / 100) = ((64 : Nat) : Real) by norm_num,
    show (-(centiBits : Real)) * (1 / 100) =
      -((centiBits : Real) / 100) by ring,
    NNReal.rpow_natCast] at hmono
  rw [ProximityPrize.Benchmark.Quarter.claimedRadius,
    ProximityPrize.Benchmark.Quarter.claimedError,
    ProximityPrize.Benchmark.QuarterRateProfile.repetitions]
  rw [show (1 - ((3 : Nat) : NNReal) / ((8 : Nat) : NNReal)) =
      (5 : NNReal) / 8 by
    have hthreeEighths :
        (((3 : Nat) : NNReal) / ((8 : Nat) : NNReal)) ≤ 1 :=
      (div_le_one (by norm_num)).2 (by norm_num)
    apply NNReal.eq
    rw [NNReal.coe_sub hthreeEighths]
    norm_num]
  exact hmono

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem reduction :
    ToyProblem.Impl.IRS.certifiedGammaError
        ProximityPrize.Benchmark.QuarterRateProfile.totalDimension
        ProximityPrize.Benchmark.QuarterRateProfile.interleaving
        ProximityPrize.Benchmark.QuarterRateProfile.domain
        (ProximityPrize.Benchmark.Quarter.claimedRadius 3 8) ≤
      ProximityPrize.Benchmark.Quarter.reductionTarget := by
  letI : NeZero ProximityPrize.Benchmark.QuarterRateProfile.interleaving :=
    ⟨by norm_num [ProximityPrize.Benchmark.QuarterRateProfile.interleaving]⟩
  letI : NeZero (ProximityPrize.Benchmark.QuarterRateProfile.totalDimension /
      ProximityPrize.Benchmark.QuarterRateProfile.interleaving) :=
    ⟨by norm_num [ProximityPrize.Benchmark.QuarterRateProfile.totalDimension,
      ProximityPrize.Benchmark.QuarterRateProfile.interleaving]⟩
  have hdim : ProximityPrize.Benchmark.QuarterRateProfile.totalDimension /
      ProximityPrize.Benchmark.QuarterRateProfile.interleaving ≤
        Fintype.card ProximityPrize.Benchmark.QuarterRateProfile.Index := by
    rw [ProximityPrize.Benchmark.QuarterRateProfile.card_index]
    norm_num [ProximityPrize.Benchmark.QuarterRateProfile.totalDimension,
      ProximityPrize.Benchmark.QuarterRateProfile.interleaving,
      ProximityPrize.Benchmark.QuarterRateProfile.domainSize]
  have hdelta : ProximityPrize.Benchmark.Quarter.claimedRadius 3 8 ≤
      Code.relativeUniqueDecodingRadius
        (ReedSolomon.code ProximityPrize.Benchmark.QuarterRateProfile.domain
          (ProximityPrize.Benchmark.QuarterRateProfile.totalDimension /
            ProximityPrize.Benchmark.QuarterRateProfile.interleaving) :
              Set (ProximityPrize.Benchmark.QuarterRateProfile.Index →
                ProximityPrize.Benchmark.QuarterRateProfile.Field)) := by
    rw [ReedSolomon.relativeUniqueDecodingRadius_RS_eq hdim,
      ProximityPrize.Benchmark.QuarterRateProfile.card_index]
    norm_num [ProximityPrize.Benchmark.Quarter.claimedRadius,
      ProximityPrize.Benchmark.QuarterRateProfile.totalDimension,
      ProximityPrize.Benchmark.QuarterRateProfile.interleaving,
      ProximityPrize.Benchmark.QuarterRateProfile.domainSize]
    rw [show ((1 : NNReal) - 1 / 4) / 2 = 3 / 8 by
      have hquarter : ((1 / 4 : NNReal) ≤ 1) :=
        (div_le_one (by norm_num)).2 (by norm_num)
      apply NNReal.eq
      rw [NNReal.coe_div, NNReal.coe_sub hquarter]
      norm_num]
  have hgamma :
      ToyProblem.Impl.IRS.certifiedGammaError
          ProximityPrize.Benchmark.QuarterRateProfile.totalDimension
          ProximityPrize.Benchmark.QuarterRateProfile.interleaving
          ProximityPrize.Benchmark.QuarterRateProfile.domain
          (ProximityPrize.Benchmark.Quarter.claimedRadius 3 8) ≤
        ((Fintype.card ProximityPrize.Benchmark.QuarterRateProfile.Index + 1 : Nat) : NNReal) /
          Fintype.card ProximityPrize.Benchmark.QuarterRateProfile.Field :=
    UniqueDecoding.certifiedGammaError_le_of_uniqueDecoding
      (F := ProximityPrize.Benchmark.QuarterRateProfile.Field)
    ProximityPrize.Benchmark.QuarterRateProfile.domain
    ProximityPrize.Benchmark.QuarterRateProfile.totalDimension
    ProximityPrize.Benchmark.QuarterRateProfile.interleaving
    (ProximityPrize.Benchmark.Quarter.claimedRadius 3 8)
    (by norm_num [ProximityPrize.Benchmark.QuarterRateProfile.interleaving])
    (by norm_num [ProximityPrize.Benchmark.Quarter.claimedRadius])
    (by norm_num [ProximityPrize.Benchmark.Quarter.claimedRadius])
    hdelta
  calc
    ToyProblem.Impl.IRS.certifiedGammaError
          ProximityPrize.Benchmark.QuarterRateProfile.totalDimension
          ProximityPrize.Benchmark.QuarterRateProfile.interleaving
          ProximityPrize.Benchmark.QuarterRateProfile.domain
          (ProximityPrize.Benchmark.Quarter.claimedRadius 3 8)
        ≤ ((Fintype.card ProximityPrize.Benchmark.QuarterRateProfile.Index + 1 : Nat) : NNReal) /
            Fintype.card ProximityPrize.Benchmark.QuarterRateProfile.Field := hgamma
    _ ≤ ProximityPrize.Benchmark.Quarter.reductionTarget := by
      rw [ProximityPrize.Benchmark.QuarterRateProfile.card_index,
        ProximityPrize.Benchmark.BinaryField192.card_field]
      rw [show ProximityPrize.Benchmark.Quarter.reductionTarget =
          1 / (2 : NNReal) ^ (128 : Nat) by
        norm_num [ProximityPrize.Benchmark.Quarter.reductionTarget,
          ProximityGap.prizeThreshold]]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      norm_num [ProximityPrize.Benchmark.QuarterRateProfile.domainSize]

/-- The initial quarter-rate benchmark certificate: 43.39 bits at radius `3/8`. -/
theorem certificate :
    ProximityPrize.Benchmark.Quarter.ProtocolClaim centiBits 3 8 where
  admissible := by
    constructor <;>
      norm_num [ProximityPrize.Benchmark.Quarter.claimedRadius,
        ProximityPrize.Benchmark.QuarterRateProfile.minRelativeDistance]
  reduction := reduction
  score := score

end ProximityPrize.Baselines.QuarterInitialLower
