import Wormald.ComparisonCone

namespace Wormald

noncomputable section
open Matrix Finset

theorem PrefixDominated.trans {n : ℕ} {x y z : Fin n → ℝ}
    (hxy : PrefixDominated x y) (hyz : PrefixDominated y z) : PrefixDominated x z :=
  fun r hr => (hxy r hr).trans (hyz r hr)

/-- Fang–Huang Corollary 3.4 for every power and every real skew matrix in
[-1,1]. This is an iteration of the proved one-step inequality. -/
theorem sortedAbs_pow_mulVec_prefixDominated {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (x : Fin n → ℝ) (p : ℕ) :
    PrefixDominated (sortedAbs (A ^ p *ᵥ x))
      (comparisonMatrix n ^ p *ᵥ sortedAbs x) := by
  induction p with
  | zero => simp only [pow_zero, Matrix.one_mulVec]; exact fun r _ => le_rfl
  | succ p ih =>
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact (sortedAbs_mulVec_prefixDominated A hskew hbound (A ^ p *ᵥ x)).trans
      (comparisonMatrix_preserves_prefixDominated _ _ ih)

/-- Every comparison iterate remains in the decreasing nonnegative cone. -/
theorem comparisonMatrix_pow_mulVec_cone {n : ℕ} (x : Fin n → ℝ)
    (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i) (p : ℕ) :
    Antitone (comparisonMatrix n ^ p *ᵥ x) ∧
      (∀ i, 0 ≤ (comparisonMatrix n ^ p *ᵥ x) i) := by
  induction p with
  | zero => simpa using And.intro hx hx0
  | succ p ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact ⟨comparisonMatrix_mulVec_antitone _ ih.1 ih.2,
      comparisonMatrix_mulVec_nonneg _ ih.1 ih.2⟩

theorem sum_sortedAbs_sq {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, sortedAbs x i ^ 2) = ∑ i, x i ^ 2 := by
  unfold sortedAbs
  simp only [sq_abs]
  exact Equiv.sum_comp _ (fun i => x i ^ 2)

/-- The actual Euclidean moment comparison, for arbitrary exponent and input.
The right side is the explicit comparison matrix; the transitive bridge is separate. -/
theorem pow_mulVec_sum_sq_le_comparison {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (x : Fin n → ℝ) (p : ℕ) :
    (∑ i, (A ^ p *ᵥ x) i ^ 2) ≤
      ∑ i, (comparisonMatrix n ^ p *ᵥ sortedAbs x) i ^ 2 := by
  have h := sortedAbs_pow_mulVec_prefixDominated A hskew hbound x p
  have hcone := comparisonMatrix_pow_mulVec_cone (sortedAbs x)
    (sortedAbs_antitone x) (fun i => abs_nonneg _) p
  have hnorm := h.sum_sq_le _ _ (sortedAbs_antitone _) hcone.1
    (fun i => abs_nonneg _) hcone.2
  rwa [sum_sortedAbs_sq] at hnorm

end
end Wormald
