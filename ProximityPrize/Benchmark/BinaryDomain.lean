/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProximityPrize.Benchmark.BinaryField192

/-!
# Binary affine evaluation domains

For `d ≤ 64`, `D_d` is exactly the `ZMod 2`-linear span of
`1, u, ..., u^(d-1)` inside `GF(2^64)`, embedded in the cubic tower field.
-/

@[expose] public section

namespace ProximityPrize.Benchmark.BinaryDomain

open CompPoly.Extension

abbrev Scalar := ZMod 2
abbrev Base := BinaryField64.Field
abbrev Field := BinaryField192.Field

/-- Coefficient vectors for the first `d` polynomial-basis powers. -/
abbrev Index (d : Nat) := Fin d → Scalar

/-- The first `d` powers of the concrete polynomial-basis generator `u`. -/
def powers (d : Nat) : Fin d → Base := fun i => BinaryField64.u ^ (i : Nat)

theorem powers_linearIndependent (d : Nat) (hd : d ≤ 64) :
    LinearIndependent Scalar (powers d) := by
  let castIndex : Fin d → Fin BinaryField64.powerBasis.dim :=
    fun i => Fin.castLE (by simpa using hd) i
  have hcast : Function.Injective castIndex := by
    intro i j hij
    have hv : (castIndex i).val = (castIndex j).val :=
      congrArg (fun z : Fin BinaryField64.powerBasis.dim => z.val) hij
    apply Fin.ext
    exact hv
  have hli := BinaryField64.powerBasis.basis.linearIndependent.comp castIndex hcast
  have heq : (BinaryField64.powerBasis.basis ∘ castIndex) = powers d := by
    funext i
    simp only [Function.comp_apply, PowerBasis.basis_eq_pow,
      BinaryField64.powerBasis_gen, castIndex, Fin.val_castLE, powers]
  rw [heq] at hli
  exact hli

/-- Interpret a coefficient vector as its polynomial in `u`. -/
def basePoint (d : Nat) (a : Index d) : Base :=
  Fintype.linearCombination Scalar (powers d) a

theorem basePoint_injective (d : Nat) (hd : d ≤ 64) :
    Function.Injective (basePoint d) :=
  (powers_linearIndependent d hd).fintypeLinearCombination_injective

/-- The actual base-field subspace `D_d = span_{GF(2)} {u^0, ..., u^(d-1)}`. -/
def subspace (d : Nat) : Submodule Scalar Base :=
  Submodule.span Scalar (Set.range (powers d))

theorem range_basePoint (d : Nat) : Set.range (basePoint d) = (subspace d : Set Base) := by
  change (LinearMap.range (Fintype.linearCombination Scalar (powers d)) : Set Base) = _
  rw [Fintype.range_linearCombination]
  rfl

/-- Embed `D_d` into the cubic tower field used by the Reed–Solomon code. -/
def domain (d : Nat) (hd : d ≤ 64) : Index d ↪ Field where
  toFun a := Ext.ofBase (basePoint d a)
  inj' := by
    intro a b h
    apply basePoint_injective d hd
    have hc := congrArg (fun z : Field => Ext.coeff z (0 : Fin 3)) h
    simpa only [Ext.coeff_ofBase, Fin.val_zero, if_pos] using hc

@[simp] theorem card_index (d : Nat) : Fintype.card (Index d) = 2 ^ d := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- The domain image is precisely the tower embedding of the advertised span. -/
theorem range_domain (d : Nat) (hd : d ≤ 64) :
    Set.range (domain d hd) = Ext.ofBase '' (subspace d : Set Base) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨basePoint d a, ?_, rfl⟩
    rw [← range_basePoint d]
    exact ⟨a, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.range (basePoint d) := by
      rw [range_basePoint d]
      exact hx
    obtain ⟨a, rfl⟩ := hx'
    exact ⟨a, rfl⟩

end ProximityPrize.Benchmark.BinaryDomain
