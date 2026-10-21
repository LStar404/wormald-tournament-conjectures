import Wormald.ComparisonPowers
import Wormald.ComparisonStrictness

namespace Wormald

noncomputable section
open Matrix Finset

theorem PrefixDominated.antisymm {n : ℕ} {x y : Fin n → ℝ}
    (hxy : PrefixDominated x y) (hyx : PrefixDominated y x) : x = y := by
  have hprefix : ∀ r, r ≤ n → prefixSum x r = prefixSum y r :=
    fun r hr => le_antisymm (hxy r hr) (hyx r hr)
  funext i
  have hi := i.isLt
  have hnext := hprefix (i.val + 1) (by omega)
  rw [prefixSum_succ _ _ hi, prefixSum_succ _ _ hi,
    hprefix i.val (by omega)] at hnext
  exact add_left_cancel hnext

/-- Equality after one additional factor forces equality before that factor.
The dimension condition avoids the source's false n=1 injectivity claim. -/
theorem sortedAbs_pow_mulVec_eq_of_succ {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (x : Fin n → ℝ) (p : ℕ)
    (heq : sortedAbs (A ^ (p + 1) *ᵥ x) =
      comparisonMatrix n ^ (p + 1) *ᵥ sortedAbs x) :
    sortedAbs (A ^ p *ᵥ x) = comparisonMatrix n ^ p *ᵥ sortedAbs x := by
  have hprevious := sortedAbs_pow_mulVec_prefixDominated A hskew hbound x p
  have hstep := sortedAbs_mulVec_prefixDominated A hskew hbound (A ^ p *ᵥ x)
  rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at heq
  rw [heq] at hstep
  have hK := comparisonMatrix_preserves_prefixDominated _ _ hprevious
  exact comparisonMatrix_eq_of_prefixDominated hn _ _ hprevious (hK.antisymm hstep)

/-- The equality descent in Fang–Huang Corollary 3.4, for all smaller powers. -/
theorem sortedAbs_pow_mulVec_eq_descends {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (x : Fin n → ℝ) (p q : ℕ) (hqp : q ≤ p)
    (heq : sortedAbs (A ^ p *ᵥ x) = comparisonMatrix n ^ p *ᵥ sortedAbs x) :
    sortedAbs (A ^ q *ᵥ x) = comparisonMatrix n ^ q *ᵥ sortedAbs x := by
  induction p generalizing q with
  | zero =>
    have hq : q = 0 := by omega
    subst q
    exact heq
  | succ p ih =>
    by_cases hq : q = p + 1
    · subst q
      exact heq
    · exact ih q (by omega)
        (sortedAbs_pow_mulVec_eq_of_succ hn A hskew hbound x p heq)

/-- Equal Euclidean moments force the full sorted-vector equality, so the
equality analysis is a proved consequence of weak majorization. -/
theorem sortedAbs_pow_mulVec_eq_of_sum_sq_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (x : Fin n → ℝ) (p : ℕ)
    (heq : (∑ i, (A ^ p *ᵥ x) i ^ 2) =
      ∑ i, (comparisonMatrix n ^ p *ᵥ sortedAbs x) i ^ 2) :
    sortedAbs (A ^ p *ᵥ x) = comparisonMatrix n ^ p *ᵥ sortedAbs x := by
  have h := sortedAbs_pow_mulVec_prefixDominated A hskew hbound x p
  apply h.eq_of_sum_sq_eq _ _ (sortedAbs_antitone _) (fun i => abs_nonneg _)
  rwa [sum_sortedAbs_sq]

end
end Wormald
