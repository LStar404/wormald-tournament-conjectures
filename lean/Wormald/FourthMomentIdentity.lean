import Wormald.CarouselSwitching
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# A finite fourth-moment identity

The four-index Pfaffian sum is proved by expanding a square and permuting finite
sums. This avoids characteristic polynomials, eigenvalues, and power series.
-/

namespace Wormald
noncomputable section
open scoped BigOperators
open Matrix

def pfaffianFour {ι : Type*} (A : Matrix ι ι ℝ) (a b c d : ι) : ℝ :=
  A a b * A c d - A a c * A b d + A a d * A b c

private def quadSum {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) : ℝ :=
  ∑ v : ι × ι × ι × ι, f v.1 v.2.1 v.2.2.1 v.2.2.2

private theorem quadSum_swap23 {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    quadSum f = quadSum (fun a b c d => f a c b d) := by
  let e : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) :=
    ⟨fun v => (v.1, v.2.2.1, v.2.1, v.2.2.2),
      fun v => (v.1, v.2.2.1, v.2.1, v.2.2.2),
      fun ⟨a,b,c,d⟩ => rfl, fun ⟨a,b,c,d⟩ => rfl⟩
  exact (Equiv.sum_comp e (fun v => f v.1 v.2.1 v.2.2.1 v.2.2.2)).symm

private theorem quadSum_swap24 {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    quadSum f = quadSum (fun a b c d => f a d c b) := by
  let e : (ι × ι × ι × ι) ≃ (ι × ι × ι × ι) :=
    ⟨fun v => (v.1, v.2.2.2, v.2.2.1, v.2.1),
      fun v => (v.1, v.2.2.2, v.2.2.1, v.2.1),
      fun ⟨a,b,c,d⟩ => rfl, fun ⟨a,b,c,d⟩ => rfl⟩
  exact (Equiv.sum_comp e (fun v => f v.1 v.2.1 v.2.2.1 v.2.2.2)).symm

private theorem quadSum_congr {ι : Type*} [Fintype ι]
    {f g : ι → ι → ι → ι → ℝ} (h : ∀ a b c d, f a b c d = g a b c d) :
    quadSum f = quadSum g := Finset.sum_congr rfl (fun _v _ => h _ _ _ _)

/-- The ordered four-index Pfaffian squares determine the fourth trace. -/
theorem pfaffianFour_sum_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hskew : ∀ i j, A j i = -A i j) :
    (∑ v : ι × ι × ι × ι, pfaffianFour A v.1 v.2.1 v.2.2.1 v.2.2.2 ^ 2) =
      3 * (∑ a, ∑ b, A a b ^ 2) ^ 2 - 6 * (A ^ 4).trace := by
  let E := (∑ a, ∑ b, A a b ^ 2) ^ 2
  let T := (A ^ 4).trace
  have hsq : quadSum (fun a b c d => (A a b * A c d) ^ 2) = E := by
    simp only [quadSum, Fintype.sum_prod_type, E, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hsq' : quadSum (fun a b c d => (A a c * A b d) ^ 2) = E := by
    rw [← quadSum_swap23 (fun a b c d => (A a b * A c d) ^ 2)]
    exact hsq
  have hsq'' : quadSum (fun a b c d => (A a d * A b c) ^ 2) = E := by
    calc
      _ = quadSum (fun a b c d => (A a d * A c b) ^ 2) := by
        apply quadSum_congr
        intro a b c d
        rw [hskew b c]
        ring
      _ = _ := by rw [← quadSum_swap24]; exact hsq
  have htr : quadSum (fun a b c d => A a c * A b d * A a d * A b c) = T := by
    have hp : A ^ 4 = (A * A) * (A * A) := by noncomm_ring
    dsimp [T]
    rw [hp]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Finset.sum_mul, Finset.mul_sum, quadSum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [hskew b d, hskew a c]
    ring
  have hcross₁ : quadSum (fun a b c d => A a b * A c d * A a c * A b d) = T := by
    rw [quadSum_swap24]
    calc
      _ = quadSum (fun a b c d => A a c * A b d * A a d * A b c) := by
        apply quadSum_congr
        intro a b c d
        rw [hskew b c, hskew b d]
        ring
      _ = T := htr
  have hcross₂ : quadSum (fun a b c d => A a b * A c d * A a d * A b c) = -T := by
    rw [quadSum_swap23]
    calc
      _ = quadSum (fun a b c d => -(A a c * A b d * A a d * A b c)) := by
        apply quadSum_congr
        intro a b c d
        rw [hskew b c]
        ring
      _ = -T := by simp only [quadSum, Finset.sum_neg_distrib] at htr ⊢; rw [htr]
  have hexpand : quadSum (fun a b c d => pfaffianFour A a b c d ^ 2) =
      quadSum (fun a b c d => (A a b * A c d) ^ 2) +
      quadSum (fun a b c d => (A a c * A b d) ^ 2) +
      quadSum (fun a b c d => (A a d * A b c) ^ 2) -
      2 * quadSum (fun a b c d => A a b * A c d * A a c * A b d) +
      2 * quadSum (fun a b c d => A a b * A c d * A a d * A b c) -
      2 * quadSum (fun a b c d => A a c * A b d * A a d * A b c) := by
    simp only [quadSum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [pfaffianFour]
    ring
  change quadSum (fun a b c d => pfaffianFour A a b c d ^ 2) = _
  rw [hexpand, hsq, hsq', hsq'', hcross₁, hcross₂, htr]
  dsimp [E, T]
  ring

end
end Wormald
