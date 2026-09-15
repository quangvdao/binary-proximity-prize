/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.ProofSystem.ToyProblem.Codegen
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.EpsCa

/-!
# Axiom-clean unique-decoding baseline

The generic theorem in this module bounds the complete MCA-plus-list
`certifiedGammaError` used by the benchmark.  The MCA term uses BCIKS20's
proved Reed--Solomon unique-decoding theorem and invariance under nonempty
row-wise interleaving.  The list term uses ordinary unique decoding of the
twice-interleaved code.  No capacity-regime admit is used.
-/

namespace ProximityPrize.Baselines.UniqueDecoding

open Code ProximityGap ToyProblem CoreDefinitions
open scoped NNReal ENNReal

variable {ι F : Type} [Fintype ι] [Nonempty ι]
variable [Field F] [Fintype F] [DecidableEq F]

/-- In the unique-decoding range, the full IRS combination-round certificate
is at most `(n + 1) / q`: `n/q` for MCA and `1/q` for the point list. -/
theorem certifiedGammaError_le_of_uniqueDecoding
    (domain : ι ↪ F) (k s : Nat) [NeZero s] (δ : NNReal)
    (hs : 0 < s) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (ReedSolomon.code domain (k / s) : Set (ι → F))) :
    ToyProblem.Impl.IRS.certifiedGammaError k s domain δ ≤
      ((Fintype.card ι + 1 : Nat) : NNReal) / Fintype.card F := by
  let Cbase : ModuleCode ι F F := ReedSolomon.code domain (k / s)
  let Cirs : ModuleCode ι F (Fin s → F) :=
    ReedSolomon.Interleaved.irsCode domain k s
  let Ctwo : ModuleCode ι F (Fin 2 → Fin s → F) := Cirs ^⋈ (Fin 2)
  have hmca :
      mcaError (AffineLineGenerator F) Cirs (δ : Real) ≤
        ((Fintype.card ι / Fintype.card F : NNReal) : ENNReal) := by
    calc
      mcaError (AffineLineGenerator F) Cirs (δ : Real) =
          mcaError (AffineLineGenerator F) Cbase (δ : Real) := by
        dsimp only [Cirs, Cbase]
        unfold ReedSolomon.Interleaved.irsCode
        exact ProximityGap.mcaError_interleaved_eq
          (ReedSolomon.code domain (k / s)) s δ hs hδ_pos hδ_lt_one
      _ ≤ ((Fintype.card ι / Fintype.card F : NNReal) : ENNReal) :=
        ProximityGap.rs_mcaError_le_of_le_relUDR hδ_pos hδ
  have hdistTwo : Code.minDist (Ctwo : Set (ι → Fin 2 → Fin s → F)) =
      Code.minDist (Cbase : Set (ι → F)) := by
    dsimp only [Ctwo, Cirs, Cbase]
    rw [Code.interleavedCode_eq_interleavedCodeSet_of_moduleCode,
      Code.minDist_interleavedCodeSet]
    unfold ReedSolomon.Interleaved.irsCode
    rw [Code.interleavedCode_eq_interleavedCodeSet_of_moduleCode,
      Code.minDist_interleavedCodeSet]
  have hδtwo : δ ≤ Code.relativeUniqueDecodingRadius
      (Ctwo : Set (ι → Fin 2 → Fin s → F)) := by
    rw [Code.relativeUniqueDecodingRadius, Code.dist_eq_minDist] at hδ ⊢
    rw [hdistTwo]
    simpa only [Cbase] using hδ
  have hLambda : Code.Lambda (Ctwo : Set (ι → Fin 2 → Fin s → F)) (δ : Real) ≤ 1 := by
    rw [← Code.isUniquelyDecodable_iff_Lambda_le]
    exact (Code.isUniquelyDecodable_relativeUniqueDecodingRadius
      (Ctwo : Set (ι → Fin 2 → Fin s → F))).anti_radius (by exact_mod_cast hδtwo)
  have hLambdaNat :
      (Code.Lambda (Ctwo : Set (ι → Fin 2 → Fin s → F)) (δ : Real)).toNat ≤ 1 :=
    ENat.toNat_le_of_le_coe hLambda
  rw [← ENNReal.coe_le_coe, ToyProblem.Impl.IRS.coe_certifiedGammaError]
  calc
    mcaError (AffineLineGenerator F) Cirs (δ : Real) +
          ((Code.Lambda (Ctwo : Set (ι → Fin 2 → Fin s → F))
            (δ : Real)).toNat : ENNReal) / (Fintype.card F : ENNReal)
        ≤ ((Fintype.card ι / Fintype.card F : NNReal) : ENNReal) +
            ((1 / Fintype.card F : NNReal) : ENNReal) := by
          refine add_le_add ?_ ?_
          · exact hmca
          · rw [ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
              ENNReal.coe_one, ENNReal.coe_natCast]
            have hLambdaENN :
                ((Code.Lambda (Ctwo : Set (ι → Fin 2 → Fin s → F))
                  (δ : Real)).toNat : ENNReal) ≤ (1 : ENNReal) := by
              exact_mod_cast hLambdaNat
            exact ENNReal.div_le_div_right hLambdaENN _
    _ = ((((Fintype.card ι + 1 : Nat) : NNReal) /
          Fintype.card F : NNReal) : ENNReal) := by
      rw [← ENNReal.coe_add]
      congr 1
      rw [← add_div]
      norm_num

omit [Nonempty ι] [DecidableEq F] in
/-- The sharp extractor mixture is bounded by the spot-check term plus any
upper bound on the combination-round certificate. -/
theorem certifiedExtractorError_le_add_of_gamma_le
    (domain : ι ↪ F) (k s queries : Nat) (δ gammaBound : NNReal)
    (hgamma : ToyProblem.Impl.IRS.certifiedGammaError k s domain δ ≤ gammaBound) :
    ToyProblem.Impl.IRS.certifiedExtractorError k s queries domain δ ≤
      (1 - δ) ^ queries + gammaBound := by
  unfold ToyProblem.Impl.IRS.certifiedExtractorError ToyProblem.certifiedExtractorError
  calc
    (1 - δ) ^ queries +
          ToyProblem.Impl.IRS.certifiedGammaError k s domain δ *
            (1 - (1 - δ) ^ queries)
        ≤ (1 - δ) ^ queries +
            ToyProblem.Impl.IRS.certifiedGammaError k s domain δ := by
          gcongr
          exact mul_le_of_le_one_right (by positivity) tsub_le_self
    _ ≤ (1 - δ) ^ queries + gammaBound := by gcongr

end ProximityPrize.Baselines.UniqueDecoding
