import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! A direct finite upper bound for block-constant nonnegative permanents.
Each target-block assignment has at most `(m!)^d` compatible permutations.
Discarding the target-capacity restriction then factorizes into row sums.
This proves the estimate directly, with no Brégman inequality as an input. -/

open Matrix Equiv
open scoped BigOperators

namespace Wormald

noncomputable section

def blockConstantMatrix {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (m : ℕ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℝ :=
  Matrix.of fun v w => B v.1 w.1

private theorem firstProjectionFiber_card (d m : ℕ) (i : Fin d) :
    Fintype.card {v : Fin d × Fin m // v.1 = i} = m := by
  let e : {v : Fin d × Fin m // v.1 = i} ≃ Fin m :=
    { toFun := fun v => v.1.2
      invFun := fun k => ⟨(i, k), rfl⟩
      left_inv := by
        intro v
        apply Subtype.ext
        exact Prod.ext v.2.symm rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin m)

/-- A fixed assignment of target blocks admits at most the number of
permutations internal to the target blocks. -/
theorem blockPermutationFiber_card_le (d m : ℕ) (f : Fin d × Fin m → Fin d) :
    Fintype.card {σ : Equiv.Perm (Fin d × Fin m) // (fun v => (σ v).1) = f} ≤
      Nat.factorial m ^ d := by
  classical
  let F := {σ : Equiv.Perm (Fin d × Fin m) // (fun v => (σ v).1) = f}
  let S := {σ : Equiv.Perm (Fin d × Fin m) // Prod.fst ∘ σ = Prod.fst}
  have hS : Fintype.card S = Nat.factorial m ^ d := by
    rw [show Fintype.card S =
      Fintype.card {σ : Equiv.Perm (Fin d × Fin m) // Prod.fst ∘ σ = Prod.fst} from rfl,
      DomMulAct.stabilizer_card]
    simp only [firstProjectionFiber_card, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  by_cases hF : Nonempty F
  · obtain ⟨σ₀⟩ := hF
    let emb : F → S := fun σ =>
      ⟨σ.1 * σ₀.1⁻¹, by
        funext v
        change (σ.1 (σ₀.1.symm v)).1 = v.1
        calc
          (σ.1 (σ₀.1.symm v)).1 = f (σ₀.1.symm v) := congrFun σ.2 _
          _ = (σ₀.1 (σ₀.1.symm v)).1 := (congrFun σ₀.2 _).symm
          _ = v.1 := by rw [Equiv.apply_symm_apply]⟩
    have hinj : Function.Injective emb := by
      intro σ τ h
      apply Subtype.ext
      have hh := congrArg Subtype.val h
      change σ.1 * σ₀.1⁻¹ = τ.1 * σ₀.1⁻¹ at hh
      exact mul_right_cancel hh
    exact (Fintype.card_le_of_injective emb hinj).trans_eq hS
  · have : IsEmpty F := not_nonempty_iff.mp hF
    change Fintype.card F ≤ _
    simp

/-- The block-constant permanent bound needed for nonregular independent
random blow-ups. It applies to every nonnegative base matrix. -/
theorem blockConstantMatrix_permanent_le {d : ℕ}
    (B : Matrix (Fin d) (Fin d) ℝ) (hB : ∀ i j, 0 ≤ B i j) (m : ℕ) :
    (blockConstantMatrix B m).permanent ≤
      (Nat.factorial m : ℝ) ^ d * ∏ i : Fin d, (∑ j : Fin d, B i j) ^ m := by
  classical
  let π : Equiv.Perm (Fin d × Fin m) → (Fin d × Fin m → Fin d) :=
    fun σ v => (σ v).1
  let weight : (Fin d × Fin m → Fin d) → ℝ := fun f => ∏ v, B v.1 (f v)
  have hweight (f : Fin d × Fin m → Fin d) : 0 ≤ weight f :=
    Finset.prod_nonneg fun v _ => hB v.1 (f v)
  have hfiber (f : Fin d × Fin m → Fin d) :
      (∑ _σ : {σ : Equiv.Perm (Fin d × Fin m) // π σ = f}, weight f) ≤
        (Nat.factorial m : ℝ) ^ d * weight f := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (hweight f)
    exact_mod_cast blockPermutationFiber_card_le d m f
  calc
    (blockConstantMatrix B m).permanent = ∑ σ, weight (π σ) := by
      rw [← Matrix.permanent_transpose]
      rfl
    _ = ∑ f, ∑ _σ : {σ : Equiv.Perm (Fin d × Fin m) // π σ = f}, weight f :=
      (Fintype.sum_fiberwise' π weight).symm
    _ ≤ ∑ f, (Nat.factorial m : ℝ) ^ d * weight f :=
      Finset.sum_le_sum fun f _ => hfiber f
    _ = (Nat.factorial m : ℝ) ^ d * ∑ f, weight f := (Finset.mul_sum _ _ _).symm
    _ = (Nat.factorial m : ℝ) ^ d * ∏ i : Fin d, (∑ j : Fin d, B i j) ^ m := by
      congr 1
      change (∑ f : Fin d × Fin m → Fin d, ∏ v, B v.1 (f v)) = _
      rw [← Fintype.prod_sum]
      simp [Fintype.prod_prod_type]

end
end Wormald
