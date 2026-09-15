/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProximityPrize.Benchmark.BinaryField64
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# The concrete cubic tower `GF(2^192)`

This is the degree-three extension of `BinaryField64.Field` cut out by the exact
polynomial `Y^3 + Y + 1`.
-/

@[expose] public section

namespace ProximityPrize.Benchmark.BinaryField192

open Polynomial CompPoly.Extension

abbrev Base := BinaryField64.Field

/-- The exact tower polynomial `Y^3 + Y + 1` over `GF(2^64)`. -/
noncomputable def cubic : Base[X] := X ^ 3 + X + 1

theorem cubic_natDegree : cubic.natDegree = 3 := by
  rw [cubic]
  compute_degree!

theorem cubic_monic : cubic.Monic := by
  rw [cubic]
  monicity!

private theorem cubic_no_root_generic {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (hcardF : Fintype.card F = 2 ^ 64) (x : F) :
    ¬(X ^ 3 + X + 1 : F[X]).IsRoot x := by
  intro hx
  have h : x ^ 3 + x + 1 = 0 := by
    simpa [IsRoot] using hx
  have hx0 : x ≠ 0 := by
    intro hx0
    subst x
    simp at h
  have h3 : x ^ 3 = x + 1 := by
    have h' : x ^ 3 + x = 1 :=
      (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq _)
    calc
      x ^ 3 = (x ^ 3 + x) + x := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 1 + x := by rw [h']
      _ = x + 1 := add_comm _ _
  have h6 : x ^ 6 = x ^ 2 + 1 := by
    calc
      x ^ 6 = (x ^ 3) ^ 2 := by ring
      _ = (x + 1) ^ 2 := by rw [h3]
      _ = x ^ 2 + 1 := by
        rw [add_sq]
        simp only [one_pow, mul_one, two_mul, CharTwo.add_self_eq_zero]
        simp
  have h7 : x ^ 7 = 1 := by
    calc
      x ^ 7 = x * x ^ 6 := by ring
      _ = x ^ 3 + x := by rw [h6]; ring
      _ = 1 := by
        rw [h3, add_comm x 1, add_assoc, CharTwo.add_self_eq_zero]
        simp
  have hcard := FiniteField.pow_card_sub_one_eq_one x hx0
  rw [hcardF] at hcard
  have hreduce : x ^ (2 ^ 64 - 1) = x := by
    rw [show 2 ^ 64 - 1 = 7 * 2635249153387078802 + 1 by norm_num,
      pow_add, pow_mul, h7]
    simp
  have hx1 : x = 1 := hreduce.symm.trans hcard
  subst x
  simp only [one_pow, CharTwo.add_self_eq_zero, zero_add] at h
  exact one_ne_zero h

/-- `Y^3 + Y + 1` stays irreducible over `GF(2^64)`. -/
theorem cubic_irreducible : Irreducible cubic := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [cubic_natDegree]
    norm_num
  · simpa only [cubic] using cubic_no_root_generic BinaryField64.card_field

/-- Parameters for the cubic tower representation. -/
def params : ExtensionParams Base where
  d := 3
  two_le := by norm_num
  lower := Vector.ofFn fun i => if (i : Nat) = 0 ∨ (i : Nat) = 1 then 1 else 0
  q := 2 ^ 64
  card_eq := BinaryField64.card_field

@[simp] theorem params_d : params.d = 3 := rfl
@[simp] theorem params_q : params.q = 2 ^ 64 := rfl

theorem params_poly : params.poly = cubic := by
  rw [ExtensionParams.poly, cubic]
  unfold params ExtensionParams.lowerCoeff
  simp only [Vector.getElem_ofFn]
  change X ^ 3 + (∑ i : Fin 3,
    C (if (i : Nat) = 0 ∨ (i : Nat) = 1 then 1 else 0) * X ^ (i : Nat)) =
    X ^ 3 + X + 1
  rw [Fin.sum_univ_three]
  norm_num
  ring

instance : Fact (Irreducible params.poly) := ⟨params_poly ▸ cubic_irreducible⟩

/-- `GF(2^192) = GF(2^64)[Y]/(Y^3 + Y + 1)`, with VM-computable arithmetic. -/
abbrev Field : Type := Ext params

instance : CharP Field 2 := by
  apply charP_of_injective_algebraMap' Base 2

/-- The cubic tower generator, the class of `Y`. -/
def y : Field := Ext.gen

@[simp] theorem card_field : Fintype.card Field = 2 ^ 192 := by
  rw [Ext.card_ext]
  norm_num [params]

theorem y_pow_three : y ^ 3 = y + 1 := by
  have h := Ext.aeval_gen_poly (P := params)
  rw [params_poly, cubic] at h
  simp only [map_add, map_pow, aeval_X, aeval_one] at h
  have h' : Ext.gen ^ 3 + Ext.gen = 1 :=
    (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq _)
  calc
    y ^ 3 = (Ext.gen ^ 3 + Ext.gen) + Ext.gen := by
      simp only [y, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = 1 + Ext.gen := by rw [h']
    _ = y + 1 := by rw [add_comm]; rfl

end ProximityPrize.Benchmark.BinaryField192
