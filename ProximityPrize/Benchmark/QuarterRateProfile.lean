/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.ProofSystem.ToyProblem.Codegen
import ArkLib.ProofSystem.ToyProblem.Leaderboard
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineLines.UniqueDecoding
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ProximityPrize.Benchmark.BinaryDomain

/-! # The quarter-rate binary interleaved-RS challenge profile -/

namespace ProximityPrize.Benchmark.QuarterRateProfile

open Code ToyProblem ToyProblem.Impl.IRS
open scoped NNReal

abbrev Field := BinaryField192.Field
abbrev Index := BinaryDomain.Index 21

def totalDimension : Nat := 2 ^ 25
def interleaving : Nat := 64
def baseDimension : Nat := 2 ^ 19
def domainSize : Nat := 2 ^ 21
def repetitions : Nat := 64

theorem card_index : Fintype.card Index = domainSize := by
  norm_num [Index, domainSize, BinaryDomain.card_index]

theorem interleaving_dvd_totalDimension : interleaving ∣ totalDimension := by
  norm_num [interleaving, totalDimension]

theorem totalDimension_div_interleaving :
    totalDimension / interleaving = baseDimension := by
  norm_num [totalDimension, interleaving, baseDimension]

local instance : NeZero interleaving := ⟨by norm_num [interleaving]⟩
local instance : NeZero baseDimension := ⟨by norm_num [baseDimension]⟩

/-- The exact `D_21 = span_{GF(2)} {1,u,...,u^20}` domain. -/
def domain : Index ↪ Field := BinaryDomain.domain 21 (by norm_num)

theorem domain_range :
    Set.range domain = CompPoly.Extension.Ext.ofBase ''
      (BinaryDomain.subspace 21 : Set BinaryField64.Field) :=
  BinaryDomain.range_domain 21 (by norm_num)

def encoder :
    (Fin totalDimension → Field) →ₗ[Field]
      (Index → Fin interleaving → Field) :=
  ToyProblem.Impl.IRS.encoder totalDimension interleaving
    interleaving_dvd_totalDimension domain

noncomputable def code : ModuleCode Index Field (Fin interleaving → Field) :=
  ReedSolomon.Interleaved.irsCode domain totalDimension interleaving

noncomputable def baseCode : ModuleCode Index Field Field :=
  ReedSolomon.code domain baseDimension

theorem encoder_injective : Function.Injective encoder := by
  exact ToyProblem.Impl.IRS.encoder_injective totalDimension interleaving
    interleaving_dvd_totalDimension domain (by
      rw [card_index]
      norm_num [totalDimension, interleaving, domainSize])

theorem encoder_range : Set.range encoder = (code : Set _) := by
  exact ToyProblem.Impl.IRS.encoder_range totalDimension interleaving
    interleaving_dvd_totalDimension domain

theorem dimension : Module.finrank Field code = totalDimension := by
  exact ReedSolomon.Interleaved.dim_irsCode_of_dvd domain totalDimension
    interleaving interleaving_dvd_totalDimension (by
      rw [card_index]
      norm_num [totalDimension, interleaving, domainSize])

theorem alphabetRate : (LinearCode.alphabetRate code : ℝ) = 1 / 4 := by
  unfold code
  rw [ReedSolomon.Interleaved.alphabetRate_irsCode domain totalDimension
    interleaving (by
      rw [card_index]
      norm_num [totalDimension, interleaving, domainSize]),
    totalDimension_div_interleaving]
  norm_num [baseDimension]

set_option maxRecDepth 20000 in
theorem minDistance :
    Code.minDist (code : Set (Index → Fin interleaving → Field)) = 1572865 := by
  unfold code
  rw [ReedSolomon.Interleaved.minDist_irsCode domain totalDimension interleaving
    (by
      all_goals norm_num [totalDimension, interleaving, domainSize])]
  norm_num [totalDimension, interleaving]

set_option maxRecDepth 20000 in
theorem baseMinDistance :
    Code.minDist (baseCode : Set (Index → Field)) = 1572865 := by
  unfold baseCode
  rw [ReedSolomon.minDist_eq_card_sub_min_add_1, card_index]
  norm_num [baseDimension, domainSize]

/-- The exact relative distance `(3 * 2^19 + 1) / 2^21`. -/
noncomputable def minRelativeDistance : ℝ≥0 := (1572865 : ℝ≥0) / 2097152

theorem base_minRelativeDistance :
    (Code.minRelHammingDistCode (baseCode : Set (Index → Field)) : ℝ≥0) =
      minRelativeDistance := by
  have hbridge := Code.minDist_div_card_eq_minRelHammingDistCode
    (baseCode : Set (Index → Field))
  rw [baseMinDistance, card_index] at hbridge
  norm_num [domainSize] at hbridge
  have hQ :
      ((Code.minRelHammingDistCode (baseCode : Set (Index → Field)) : ℚ≥0) : ℚ) =
        (((1572865 : ℚ≥0) / 2097152 : ℚ≥0) : ℚ) := by
    rw [← hbridge]
    norm_num
  have hN :
      Code.minRelHammingDistCode (baseCode : Set (Index → Field)) =
        (1572865 : ℚ≥0) / 2097152 := by
    exact_mod_cast hQ
  unfold minRelativeDistance
  rw [hN]
  norm_num

theorem minRelativeDistance_eq :
    (Code.minRelHammingDistCode
      (code : Set (Index → Fin interleaving → Field)) : ℝ≥0) =
      minRelativeDistance := by
  have hbridge := Code.minDist_div_card_eq_minRelHammingDistCode
    (code : Set (Index → Fin interleaving → Field))
  rw [minDistance, card_index] at hbridge
  norm_num [domainSize] at hbridge
  have hQ :
      ((Code.minRelHammingDistCode
        (code : Set (Index → Fin interleaving → Field)) : ℚ≥0) : ℚ) =
        (((1572865 : ℚ≥0) / 2097152 : ℚ≥0) : ℚ) := by
    rw [← hbridge]
    norm_num
  have hN :
      Code.minRelHammingDistCode
        (code : Set (Index → Fin interleaving → Field)) =
          (1572865 : ℚ≥0) / 2097152 := by
    exact_mod_cast hQ
  unfold minRelativeDistance
  rw [hN]
  norm_num

noncomputable def parameters :
    ToyProblem.FixedRadiusParameters (ι := Index) (F := Field)
      (A := Fin interleaving → Field) where
  k := totalDimension
  t := repetitions
  code := code
  encoder := encoder
  encoder_injective := encoder_injective
  encoder_range := encoder_range

def merkleOpeningEstimateBits : Nat :=
  repetitions * (256 * 21 + 192 * interleaving)

theorem merkleOpeningEstimateBits_eq : merkleOpeningEstimateBits = 1130496 := by
  norm_num [merkleOpeningEstimateBits, repetitions, interleaving]

def merkleOpeningEstimateBytes : Nat := merkleOpeningEstimateBits / 8

theorem merkleOpeningEstimateBytes_eq : merkleOpeningEstimateBytes = 141312 := by
  norm_num [merkleOpeningEstimateBytes, merkleOpeningEstimateBits,
    repetitions, interleaving]

end ProximityPrize.Benchmark.QuarterRateProfile
