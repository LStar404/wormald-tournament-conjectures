import Wormald.CentralGaussianRadius
import Wormald.RegularScaledExpansion

/-! The explicit central radius applied to the genuine regular-tournament
Fourier integrand. The error bound is independent of the prescribed arcs. -/

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators

theorem card_Edge_le_square (m : ℕ) : Fintype.card (Edge m) ≤ m ^ 2 := by
  have h := Fintype.card_le_of_injective
    (Subtype.val : Edge m → Fin m × Fin m) Subtype.val_injective
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using h

theorem exists_scaledRegularFactor_central_error {m : ℕ} (hm : 1 ≤ m)
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hloop : ∀ e ∈ D, e.1 ≠ e.2)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (x : Fin m → ℝ)
    (hx : ∀ i j, |(Real.sqrt (m : ℝ))⁻¹ * x i -
      (Real.sqrt (m : ℝ))⁻¹ * x j| ≤ centralGaussianRadius m) :
    ∃ e : ℝ, |e| ≤ centralGaussianError m ∧
      scaledRegularFactor D x =
        graphGaussianWeight (partialPermutationGaussianGraphData D hloop hs ht)
          (1 / (m : ℝ)) x * (gaussianQuarticFactor m x : ℂ) * (Real.exp e : ℂ) := by
  obtain ⟨e, he, hprod⟩ := exists_scaledRegularFactor_error D hD hloop hs ht x
    (centralGaussianRadius m) (centralGaussianRadius_nonneg m)
    (centralGaussianRadius_le_one hm) hx
  exact ⟨e, he.trans (centralGaussian_card_error_le m (Fintype.card (Edge m)) D.card
    (card_Edge_le_square m) (partialPermutation_edges_le D hs)), hprod⟩

end
end Wormald.FiniteModel
