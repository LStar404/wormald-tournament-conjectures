import Wormald.PrescribedEdgeStatistics

/-! The actual normalized regular Fourier integrand: every prescribed arc
retains its directed phase and each free unordered edge contributes a cosine. -/

namespace Wormald.FiniteModel
noncomputable section
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem normalizedForestCosineFactor_prescribed {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (x : Fin m → ℝ) (p : {p // p ∈ D}) :
    normalizedForestCosineFactor D x (prescribedArcToEdge D hD p) =
      Complex.exp (((Real.pi * (x p.1.1 - x p.1.2) : ℝ) : ℂ) * Complex.I) := by
  have hp : (p.1.1, p.1.2) ∈ D := p.2
  have hr : (p.1.2, p.1.1) ∉ D := hD _ _ hp
  by_cases hlt : p.1.1 < p.1.2
  · simp [prescribedArcToEdge, canonicalEdge, hlt, normalizedForestCosineFactor,
      freeCosineEdges, forestCosineEdgeFactor, hp, hr]
  · simp [prescribedArcToEdge, canonicalEdge, hlt, normalizedForestCosineFactor,
      freeCosineEdges, forestCosineEdgeFactor, hp, hr]
    congr 1
    ring

theorem freeCosineEdges_eq_sdiff {m : ℕ} (D : Finset (Fin m × Fin m)) :
    Finset.univ \ forcedUnorderedEdges D = freeCosineEdges D := by
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, forcedUnorderedEdges,
    freeCosineEdges, Finset.mem_filter, not_or]

theorem normalizedRegularIntegrand_eq_phase_product {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (x : Fin m → ℝ) :
    normalizedRegularIntegrand D x =
      Complex.exp (((Real.pi * (partialImbalance D ⬝ᵥ x) : ℝ) : ℂ) * Complex.I) *
        ∏ e ∈ freeCosineEdges D, (Real.cos (Real.pi * (x e.1.1 - x e.1.2)) : ℂ) := by
  have hsplit := Finset.prod_sdiff (f := normalizedForestCosineFactor D x)
    (Finset.subset_univ (forcedUnorderedEdges D))
  rw [freeCosineEdges_eq_sdiff] at hsplit
  have hfree : (∏ e ∈ freeCosineEdges D, normalizedForestCosineFactor D x e) =
      ∏ e ∈ freeCosineEdges D, (Real.cos (Real.pi * (x e.1.1 - x e.1.2)) : ℂ) :=
    Finset.prod_congr rfl fun e he => by simp only [normalizedForestCosineFactor, ite_eq_left he]
  have hforced : (∏ e ∈ forcedUnorderedEdges D, normalizedForestCosineFactor D x e) =
      Complex.exp (((Real.pi * (partialImbalance D ⬝ᵥ x) : ℝ) : ℂ) * Complex.I) := by
    rw [← prescribedArcToEdge_image D hD,
      Finset.prod_image (prescribedArcToEdge_injective D hD).injOn]
    simp_rw [normalizedForestCosineFactor_prescribed]
    rw [← Complex.exp_sum]
    congr 1
    rw [partialImbalance_dot_eq_sum]
    simp only [← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.mul_sum]
    rw [Finset.sum_attach D (fun p => x p.1 - x p.2)]
  rw [normalizedRegularIntegrand, ← hsplit, hfree, hforced, mul_comm]

/-- Physical angles are measured in radians. The factor π in the original
unit-torus coordinates is explicitly canceled here. -/
theorem normalizedRegularIntegrand_radians {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (θ : Fin m → ℝ) :
    normalizedRegularIntegrand D (fun i => θ i / Real.pi) =
      Complex.exp (((partialImbalance D ⬝ᵥ θ : ℝ) : ℂ) * Complex.I) *
        ∏ e ∈ freeCosineEdges D, (Real.cos (θ e.1.1 - θ e.1.2) : ℂ) := by
  rw [normalizedRegularIntegrand_eq_phase_product D hD]
  have hphase : Real.pi * (partialImbalance D ⬝ᵥ (fun i => θ i / Real.pi)) =
      partialImbalance D ⬝ᵥ θ := by
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hdiff (e : Edge m) : Real.pi * (θ e.1.1 / Real.pi - θ e.1.2 / Real.pi) =
      θ e.1.1 - θ e.1.2 := by field_simp
  simp only [hphase, hdiff]

end
end Wormald.FiniteModel
