import Wormald.CircleLiftIntegration
import Wormald.GoodClusterGaussianVolume
import Wormald.RegularLocalExpansion

/-! The good-cluster Gaussian estimate for the actual unprescribed edges of
a directed partial permutation, including exact circle-to-cube transport. -/

namespace Wormald.FiniteModel
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance goodKernelCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance goodKernelCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem no_opposite_arc_ne {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) : ∀ e ∈ D, e.1 ≠ e.2 := by
  rintro ⟨a, b⟩ he h
  change a = b at h
  subst b
  exact hD a a he he

def freeEdgeGaussian {m : ℕ} (D : Finset (Fin m × Fin m)) (x : Fin m → ℝ) : ℝ :=
  Real.exp (-(∑ e ∈ freeCosineEdges D, (Real.pi * (x e.1.1 - x e.1.2)) ^ 2) / 2)

theorem continuous_freeEdgeGaussian {m : ℕ} (D : Finset (Fin m × Fin m)) :
    Continuous (freeEdgeGaussian D) := by
  unfold freeEdgeGaussian
  fun_prop

theorem freeEdgeGaussian_nonneg {m : ℕ} (D : Finset (Fin m × Fin m)) (x : Fin m → ℝ) :
    0 ≤ freeEdgeGaussian D x := (Real.exp_pos _).le

theorem freeEdgeGaussian_le_one {m : ℕ} (D : Finset (Fin m × Fin m)) (x : Fin m → ℝ) :
    freeEdgeGaussian D x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    (by norm_num)

theorem freeCosineEdges_energy {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) (x : Fin m → ℝ) :
    (∑ e ∈ freeCosineEdges D, (x e.1.1 - x e.1.2) ^ 2) =
      completeSquareEnergy x - x ⬝ᵥ (partialLaplacian D *ᵥ x) := by
  have h := Finset.sum_sdiff (f := fun e : Edge m => (x e.1.1 - x e.1.2) ^ 2)
    (Finset.subset_univ (forcedUnorderedEdges D))
  rw [freeCosineEdges_eq_sdiff, sum_edges_square_eq_completeSquareEnergy x,
    sum_forced_square_eq_partialLaplacian D hD x] at h
  linarith

theorem freeEdgeGaussian_eq_anchored {n : ℕ} (D : Finset (Fin (n + 2) × Fin (n + 2)))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hs : Set.InjOn (Prod.fst : Fin (n + 2) × Fin (n + 2) → Fin (n + 2)) D)
    (ht : Set.InjOn (Prod.snd : Fin (n + 2) × Fin (n + 2) → Fin (n + 2)) D)
    (x : Fin (n + 2) → ℝ) :
    freeEdgeGaussian D x =
      matrixGaussian (anchoredGraphPrecision (partialPermutationGaussianGraphData D
        (no_opposite_arc_ne D hD) hs ht))
        (Real.pi • anchorDifference x) := by
  let G := partialPermutationGaussianGraphData D
    (no_opposite_arc_ne D hD) hs ht
  have h1 : G.laplacian *ᵥ (fun _ => 1) = 0 := partialLaplacian_mulVec_one D
  have hembed : Fin.snoc (Real.pi • anchorDifference x) 0 =
      Real.pi • x + fun _ => -(Real.pi * x (Fin.last (n + 1))) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [anchorDifference, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg, mul_add, mul_neg]
  have henergy : completeSquareEnergy
      (Real.pi • x + fun _ => -(Real.pi * x (Fin.last (n + 1)))) =
      completeSquareEnergy (Real.pi • x) :=
    completeSquareEnergy_translate (Real.pi • x) (-(Real.pi * x (Fin.last (n + 1))))
  have hsum := freeCosineEdges_energy D hD (Real.pi • x)
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub] at hsum
  change _ = matrixGaussian (anchoredGraphPrecision G) (Real.pi • anchorDifference x)
  rw [freeEdgeGaussian, matrixGaussian, anchoredGraphPrecision_quadratic, hembed,
    graph_quadratic_add_const G h1, henergy]
  rw [hsum]
  rfl

theorem integral_freeEdgeGaussian_cube_le {m : ℕ} (hm : 16 ≤ m)
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) :
    (∫ x : Fin m → ℝ in Metric.closedBall 0 (3 / 16 : ℝ), freeEdgeGaussian D x) ≤
      (3 / 8 : ℝ) * Real.exp 2 * quotientGaussianVolume m / Real.pi ^ (m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  simp_rw [freeEdgeGaussian_eq_anchored D hD hs ht]
  simpa only [show n + 2 - 1 = n + 1 by omega] using goodClusterGaussian_cube_le hm
    (partialPermutationGaussianGraphData D
      (no_opposite_arc_ne D hD) hs ht)
    (partialLaplacian_mulVec_one D)

theorem integral_circleWindow_freeEdgeGaussian_le {m : ℕ} (hm : 16 ≤ m)
    (D : Finset (Fin m × Fin m)) (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D)
    (hs : Set.InjOn (Prod.fst : Fin m × Fin m → Fin m) D)
    (ht : Set.InjOn (Prod.snd : Fin m × Fin m → Fin m) D) (j : Fin 16) :
    (∫ x : UnitAddTorus (Fin m) in circleClusterWindow j (3 / 16 : ℝ),
      freeEdgeGaussian D (fun i => circleCenteredLift j (x i))) ≤
      (3 / 8 : ℝ) * Real.exp 2 * quotientGaussianVolume m / Real.pi ^ (m - 1) := by
  rw [integral_circleClusterWindow_lift j (3 / 16 : ℝ) (by norm_num) (by norm_num)]
  exact integral_freeEdgeGaussian_cube_le hm D hD hs ht

end
end Wormald.FiniteModel
