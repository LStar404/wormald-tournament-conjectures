import Wormald.RegularLocalExpansion
import Wormald.GaussianQuarticCancellation

namespace Wormald.FiniteModel
noncomputable section
open Matrix
open scoped BigOperators

def scaledRegularFactor {m : ℕ} (D : Finset (Fin m × Fin m)) (x : Fin m → ℝ) : ℂ :=
  let θ := (Real.sqrt (m : ℝ))⁻¹ • x
  (Real.exp (completeSquareEnergy θ / 2) : ℂ) *
    normalizedRegularIntegrand D (fun i => θ i / Real.pi)

/-- At the genuine growing-dimensional Gaussian scale, the actual cosine
integrand equals the graph tilt times the common quartic factor and a
uniformly bounded Taylor error. No integral approximation is assumed. -/
theorem exists_scaledRegularFactor_error {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hloop : ∀ e ∈ D, e.1 ≠ e.2)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D)
    (x : Fin m → ℝ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : ∀ i j, |(Real.sqrt (m : ℝ))⁻¹ * x i - (Real.sqrt (m : ℝ))⁻¹ * x j| ≤ r) :
    ∃ e : ℝ, |e| ≤ Fintype.card (Edge m) * r ^ 6 + 2 * D.card * r ^ 4 ∧
      scaledRegularFactor D x =
        graphGaussianWeight (partialPermutationGaussianGraphData D hloop hs ht)
          (1 / (m : ℝ)) x * (gaussianQuarticFactor m x : ℂ) * (Real.exp e : ℂ) := by
  let c : ℝ := (Real.sqrt (m : ℝ))⁻¹
  let θ : Fin m → ℝ := c • x
  obtain ⟨e, he, hprod⟩ := exists_normalizedRegularIntegrand_local_error D hD θ r hr hr1 hx
  refine ⟨e, he, ?_⟩
  have hc2 : c ^ 2 = 1 / (m : ℝ) := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg m), one_div]
  have hc4 : c ^ 4 = 1 / (m : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hc2]
    ring
  have hq4 : completeQuarticEnergy θ / 12 = completeQuarticEnergy x / (12 * (m : ℝ) ^ 2) := by
    rw [show θ = c • x from rfl, completeQuarticEnergy_smul, hc4]
    ring
  have hquad : θ ⬝ᵥ (partialLaplacian D *ᵥ θ) =
      (1 / (m : ℝ)) * (x ⬝ᵥ (partialLaplacian D *ᵥ x)) := by
    dsimp [θ]
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← mul_assoc, ← pow_two, hc2]
  have hphase : partialImbalance D ⬝ᵥ θ =
      Real.sqrt (1 / (m : ℝ)) * (partialImbalance D ⬝ᵥ x) := by
    simp only [θ, dotProduct_smul, smul_eq_mul, one_div, Real.sqrt_inv, c]
  have hexp : Real.exp (completeSquareEnergy θ / 2) *
      Real.exp (-completeSquareEnergy θ / 2 - completeQuarticEnergy θ / 12 +
        (θ ⬝ᵥ (partialLaplacian D *ᵥ θ)) / 2 + e) =
      Real.exp ((1 / (m : ℝ)) / 2 * (x ⬝ᵥ (partialLaplacian D *ᵥ x))) *
        gaussianQuarticFactor m x * Real.exp e := by
    rw [gaussianQuarticFactor, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hq4, hquad]
    ring
  change (Real.exp (completeSquareEnergy θ / 2) : ℂ) *
    normalizedRegularIntegrand D (fun i => θ i / Real.pi) = _
  rw [hprod, hphase]
  change _ =
    ((Real.exp ((1 / (m : ℝ)) / 2 * (x ⬝ᵥ (partialLaplacian D *ᵥ x))) : ℝ) : ℂ) *
      Complex.exp (((Real.sqrt (1 / (m : ℝ)) * (partialImbalance D ⬝ᵥ x) : ℝ) : ℂ) * Complex.I) *
        (gaussianQuarticFactor m x : ℂ) * (Real.exp e : ℂ)
  have hcast := congrArg Complex.ofReal hexp
  simp only [Complex.ofReal_mul] at hcast
  calc
    _ = Complex.exp (((Real.sqrt (1 / (m : ℝ)) * (partialImbalance D ⬝ᵥ x) : ℝ) : ℂ) * Complex.I) *
        ((Real.exp (completeSquareEnergy θ / 2) : ℂ) *
          (Real.exp (-completeSquareEnergy θ / 2 - completeQuarticEnergy θ / 12 +
            (θ ⬝ᵥ (partialLaplacian D *ᵥ θ)) / 2 + e) : ℂ)) := by ring
    _ = _ := by rw [hcast]; ring

end
end Wormald.FiniteModel
