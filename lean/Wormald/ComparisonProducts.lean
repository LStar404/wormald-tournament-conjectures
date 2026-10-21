import Wormald.ComparisonEquality

namespace Wormald

noncomputable section
open Matrix Finset

/-- A₀ A₁ ... Aₘ₋₁, so dropping initial factors corresponds literally to
the suffix products in Fang–Huang Corollary 3.4. -/
def matrixProduct {n : ℕ} (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := match m with
  | 0 => 1
  | m + 1 => A 0 * matrixProduct (fun k => A (k + 1)) m

/-- The complete product version of the source's Corollary 3.4. -/
theorem sortedAbs_matrixProduct_prefixDominated {n : ℕ}
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ k i j, A k j i = -A k i j)
    (hbound : ∀ k i j, |A k i j| ≤ 1) (x : Fin n → ℝ) (m : ℕ) :
    PrefixDominated (sortedAbs (matrixProduct A m *ᵥ x))
      (comparisonMatrix n ^ m *ᵥ sortedAbs x) := by
  induction m generalizing A with
  | zero => simp only [matrixProduct, pow_zero, Matrix.one_mulVec]; exact fun r _ => le_rfl
  | succ m ih =>
    have hprev := ih (fun k => A (k + 1)) (fun k => hskew (k + 1)) (fun k => hbound (k + 1))
    have hstep := sortedAbs_mulVec_prefixDominated (A 0) (hskew 0) (hbound 0)
      (matrixProduct (fun k => A (k + 1)) m *ᵥ x)
    have hK := comparisonMatrix_preserves_prefixDominated _ _ hprev
    simpa only [matrixProduct, pow_succ', ← Matrix.mulVec_mulVec] using hstep.trans hK

theorem sortedAbs_matrixProduct_eq_of_succ {n : ℕ} (hn : 2 ≤ n)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ k i j, A k j i = -A k i j)
    (hbound : ∀ k i j, |A k i j| ≤ 1) (x : Fin n → ℝ) (m : ℕ)
    (heq : sortedAbs (matrixProduct A (m + 1) *ᵥ x) =
      comparisonMatrix n ^ (m + 1) *ᵥ sortedAbs x) :
    sortedAbs (matrixProduct (fun k => A (k + 1)) m *ᵥ x) =
      comparisonMatrix n ^ m *ᵥ sortedAbs x := by
  have hprev := sortedAbs_matrixProduct_prefixDominated (fun k => A (k + 1))
    (fun k => hskew (k + 1)) (fun k => hbound (k + 1)) x m
  have hstep := sortedAbs_mulVec_prefixDominated (A 0) (hskew 0) (hbound 0)
    (matrixProduct (fun k => A (k + 1)) m *ᵥ x)
  rw [matrixProduct, pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at heq
  rw [heq] at hstep
  have hK := comparisonMatrix_preserves_prefixDominated _ _ hprev
  exact comparisonMatrix_eq_of_prefixDominated hn _ _ hprev (hK.antisymm hstep)

/-- Equality in a full product forces equality in every literal suffix product. -/
theorem sortedAbs_matrixProduct_eq_suffix {n : ℕ} (hn : 2 ≤ n)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ k i j, A k j i = -A k i j)
    (hbound : ∀ k i j, |A k i j| ≤ 1) (x : Fin n → ℝ) (p q : ℕ)
    (heq : sortedAbs (matrixProduct A (p + q) *ᵥ x) =
      comparisonMatrix n ^ (p + q) *ᵥ sortedAbs x) :
    sortedAbs (matrixProduct (fun k => A (k + p)) q *ᵥ x) =
      comparisonMatrix n ^ q *ᵥ sortedAbs x := by
  induction p generalizing A with
  | zero => simpa using heq
  | succ p ih =>
    have hm : p + 1 + q = (p + q) + 1 := by omega
    rw [hm] at heq
    have hprev := sortedAbs_matrixProduct_eq_of_succ hn A hskew hbound x (p + q) heq
    have htail := ih (fun k => A (k + 1)) (fun k => hskew (k + 1)) (fun k => hbound (k + 1)) hprev
    simpa only [Nat.add_assoc] using htail

end
end Wormald
