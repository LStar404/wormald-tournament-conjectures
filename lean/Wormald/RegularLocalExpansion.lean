import Wormald.RegularLocalPhase
import Wormald.DeletedCosineApproximation

/-! The actual regular containment integrand has a uniform quartic local
expansion. The quadratic correction is the true prescribed-edge Laplacian,
and its imaginary phase is the true endpoint imbalance. -/

namespace Wormald.FiniteModel
noncomputable section
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem exists_normalizedRegularIntegrand_local_error {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (θ : Fin m → ℝ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hθ : ∀ i j, |θ i - θ j| ≤ r) :
    ∃ e : ℝ, |e| ≤ Fintype.card (Edge m) * r ^ 6 + 2 * D.card * r ^ 4 ∧
      normalizedRegularIntegrand D (fun i => θ i / Real.pi) =
        Complex.exp (((partialImbalance D ⬝ᵥ θ : ℝ) : ℂ) * Complex.I) *
          (Real.exp (-completeSquareEnergy θ / 2 - completeQuarticEnergy θ / 12 +
            (θ ⬝ᵥ (partialLaplacian D *ᵥ θ)) / 2 + e) : ℂ) := by
  obtain ⟨e, he, hprod⟩ := exists_deleted_cosine_product_error
    Finset.univ (forcedUnorderedEdges D) (Finset.subset_univ _)
    (fun e : Edge m => θ e.1.1 - θ e.1.2) r hr hr1 (fun _ _ => hθ _ _)
  rw [Finset.card_univ, forcedUnorderedEdges_card D hD] at he
  refine ⟨e, he, ?_⟩
  rw [freeCosineEdges_eq_sdiff, sum_edges_square_eq_completeSquareEnergy,
    sum_edges_quartic_eq_completeQuarticEnergy, sum_forced_square_eq_partialLaplacian D hD] at hprod
  rw [normalizedRegularIntegrand_radians D hD]
  congr 1
  rw [← Complex.ofReal_prod, hprod]

/-- A common translation has no effect on the complete energies. -/
theorem completeSquareEnergy_translate {m : ℕ} (x : Fin m → ℝ) (c : ℝ) :
    completeSquareEnergy (fun i => x i + c) = completeSquareEnergy x := by
  simp only [completeSquareEnergy, add_sub_add_right_eq_sub]

theorem completeQuarticEnergy_translate {m : ℕ} (x : Fin m → ℝ) (c : ℝ) :
    completeQuarticEnergy (fun i => x i + c) = completeQuarticEnergy x := by
  simp only [completeQuarticEnergy, add_sub_add_right_eq_sub]

theorem completeSquareEnergy_smul {m : ℕ} (x : Fin m → ℝ) (c : ℝ) :
    completeSquareEnergy (c • x) = c ^ 2 * completeSquareEnergy x := by
  simp only [completeSquareEnergy, Pi.smul_apply, smul_eq_mul, ← mul_sub,
    mul_pow, ← Finset.mul_sum]
  ring

theorem completeQuarticEnergy_smul {m : ℕ} (x : Fin m → ℝ) (c : ℝ) :
    completeQuarticEnergy (c • x) = c ^ 4 * completeQuarticEnergy x := by
  simp only [completeQuarticEnergy, Pi.smul_apply, smul_eq_mul, ← mul_sub,
    mul_pow, ← Finset.mul_sum]
  ring

end
end Wormald.FiniteModel
