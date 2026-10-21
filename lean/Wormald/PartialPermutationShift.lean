import Wormald.PartialPermutationLaplacian

namespace Wormald

noncomputable section
open Matrix
open scoped BigOperators

/-- Incidence Laplacians annihilate constants, before imposing any degree
or partial-permutation condition. -/
theorem partialLaplacian_mulVec_one {m : ℕ} (D : Finset (Fin m × Fin m)) :
    partialLaplacian D *ᵥ (fun _ => 1) = 0 := by
  simp [partialLaplacian, Matrix.sum_mulVec, Matrix.vecMulVec_mulVec]

theorem partialImbalance_dot_one {m : ℕ} (D : Finset (Fin m × Fin m)) :
    partialImbalance D ⬝ᵥ (fun _ => 1) = 0 := by
  simp [dotProduct]

theorem partialLaplacian_quadratic_add_const {m : ℕ} (D : Finset (Fin m × Fin m))
    (x : Fin m → ℝ) (c : ℝ) :
    (x + fun _ => c) ⬝ᵥ (partialLaplacian D *ᵥ (x + fun _ => c)) =
      x ⬝ᵥ (partialLaplacian D *ᵥ x) := by
  simp only [partialLaplacian_quadratic, Pi.add_apply, add_sub_add_right_eq_sub]

theorem partialImbalance_dot_add_const {m : ℕ} (D : Finset (Fin m × Fin m))
    (x : Fin m → ℝ) (c : ℝ) :
    partialImbalance D ⬝ᵥ (x + fun _ => c) = partialImbalance D ⬝ᵥ x := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, sum_partialImbalance]
  simp

theorem FiniteModel.internalCycleGaussianGraphData_mulVec_one {d m : ℕ}
    (σ : Equiv.Perm (Fin d × Fin m)) (hN : 3 ≤ d * m) (hσ : SingleOrbit σ) (i : Fin d) :
    (internalCycleGaussianGraphData σ hN hσ i).laplacian *ᵥ (fun _ => 1) = 0 :=
  partialLaplacian_mulVec_one _

end
end Wormald
