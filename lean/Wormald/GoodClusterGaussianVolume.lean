import Wormald.GaussianGraphIntegral
import Wormald.GaussianBoxAnchor
import Wormald.GaussianQuarticIdentity

/-! The Gaussian volume of a good cluster after deleting degree-two edges.
The bound retains the exact dimension-dependent complete-graph volume. -/

namespace Wormald
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem graph_quadratic_add_const {m : ℕ} (G : GaussianGraphData m)
    (h1 : G.laplacian *ᵥ (fun _ => 1) = 0) (x : Fin m → ℝ) (c : ℝ) :
    (x + fun _ => c) ⬝ᵥ (G.laplacian *ᵥ (x + fun _ => c)) =
      x ⬝ᵥ (G.laplacian *ᵥ x) := by
  have hc : (fun _ : Fin m => c) = c • (fun _ => (1 : ℝ)) := by ext i; simp
  have hleft : (fun _ : Fin m => (1 : ℝ)) ⬝ᵥ (G.laplacian *ᵥ x) = 0 := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, graphLaplacian_symmetric G, h1,
      zero_dotProduct]
  rw [hc, Matrix.mulVec_add, Matrix.mulVec_smul, h1, smul_zero, add_zero,
    add_dotProduct, smul_dotProduct, hleft]
  simp

def anchoredGraphPrecision {n : ℕ} (G : GaussianGraphData (n + 2)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  completeQuotientPrecision n - G.laplacian.submatrix Fin.castSucc Fin.castSucc

theorem anchoredGraphPrecision_quadratic {n : ℕ} (G : GaussianGraphData (n + 2))
    (y : Fin (n + 1) → ℝ) :
    y ⬝ᵥ (anchoredGraphPrecision G *ᵥ y) =
      completeSquareEnergy (Fin.snoc y 0) -
        (Fin.snoc y 0) ⬝ᵥ (G.laplacian *ᵥ (Fin.snoc y 0)) := by
  have htop : y ⬝ᵥ (G.laplacian.submatrix Fin.castSucc Fin.castSucc *ᵥ y) =
      (Fin.snoc y 0) ⬝ᵥ (G.laplacian *ᵥ (Fin.snoc y 0)) := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_castSucc]
  rw [anchoredGraphPrecision, Matrix.sub_mulVec, dotProduct_sub, htop,
    completeQuotientPrecision_quadratic, completeSquareEnergy_eq]
  simp only [Fintype.card_fin, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    zero_pow (by norm_num : 2 ≠ 0), add_zero]

theorem anchoredGraphPrecision_posDef {n : ℕ} (hn : 4 < n + 2)
    (G : GaussianGraphData (n + 2)) (h1 : G.laplacian *ᵥ (fun _ => 1) = 0) :
    (anchoredGraphPrecision G).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    change (anchoredGraphPrecision G).transpose = anchoredGraphPrecision G
    simp [anchoredGraphPrecision, Matrix.transpose_sub, Matrix.transpose_submatrix,
      graphLaplacian_symmetric, completeQuotientPrecision]
  · intro y hy
    simp only [star_trivial]
    rw [anchoredGraphPrecision_quadratic]
    let v : Fin (n + 2) → ℝ := Fin.snoc y 0
    let c : ℝ := (∑ i, v i) / ((n + 2 : ℕ) : ℝ)
    let w : Fin (n + 2) → ℝ := fun i => v i - c
    have hm : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hwSum : ∑ i, w i = 0 := by
      simp only [w, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, c]
      field_simp
      ring
    have hw : w ≠ 0 := by
      intro hw
      have hc0 : c = 0 := by
        have h := congrFun hw (Fin.last (n + 1))
        simp only [w, v, Fin.snoc_last, Pi.zero_apply, zero_sub, neg_eq_zero] at h
        exact h
      apply hy
      ext j
      have h := congrFun hw j.castSucc
      simpa [w, v, hc0] using h
    have henergy : completeSquareEnergy v = ((n + 2 : ℕ) : ℝ) * (w ⬝ᵥ w) := by
      rw [← completeSquareEnergy_sub_const v c, completeSquareEnergy_eq]
      rw [hwSum]
      simp [dotProduct, pow_two, w]
    have hquad : w ⬝ᵥ (G.laplacian *ᵥ w) = v ⬝ᵥ (G.laplacian *ᵥ v) :=
      graph_quadratic_add_const G h1 v (-c)
    have hp : 0 < w ⬝ᵥ w := by
      simpa only [star_trivial] using (dotProduct_star_self_pos_iff (v := w)).mpr hw
    have hbound := G.quadratic_le w
    have hmR : (4 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hn
    change 0 < completeSquareEnergy v - v ⬝ᵥ (G.laplacian *ᵥ v)
    rw [henergy]
    nlinarith [mul_pos (sub_pos.mpr hmR) hp]

def anchoredGraphQuadraticFactor {n : ℕ} (G : GaussianGraphData (n + 2))
    (y : Fin (n + 1) → ℝ) : ℝ :=
  Real.exp ((Fin.snoc y 0) ⬝ᵥ (G.laplacian *ᵥ (Fin.snoc y 0)) / 2)

theorem graphQuadraticFactor_scaledAnchor {n : ℕ} (G : GaussianGraphData (n + 2))
    (h1 : G.laplacian *ᵥ (fun _ => 1) = 0) (x : Fin (n + 2) → ℝ) :
    anchoredGraphQuadraticFactor G (scaledAnchorDifference x) =
      graphQuadraticWeight G (1 / ((n + 2 : ℕ) : ℝ)) x := by
  have hembed : Fin.snoc (scaledAnchorDifference x) 0 =
      (Real.sqrt ((n + 2 : ℕ) : ℝ))⁻¹ • (x + fun _ => -x (Fin.last (n + 1))) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [scaledAnchorDifference, anchorDifference, sub_eq_add_neg, add_assoc]
  rw [anchoredGraphQuadraticFactor, hembed]
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n + 2 : ℕ)),
    graph_quadratic_add_const G h1]
  rw [graphQuadraticWeight]
  congr 1
  ring

theorem graphQuadraticWeight_mean_le_exp_two {m : ℕ} (hm : 16 ≤ m)
    (G : GaussianGraphData m) :
    (∫ x, graphQuadraticWeight G (1 / (m : ℝ)) x
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤ Real.exp 2 := by
  have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hw := memLp_graphGaussianWeight G (1 / (m : ℝ)) (by positivity) (by
    rw [show 8 * (1 / (m : ℝ)) = 8 / m by ring]
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < m)).mpr
    linarith)
  have hreal : MemLp (graphQuadraticWeight G (1 / (m : ℝ))) 2
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
    simpa only [norm_graphGaussianWeight] using hw.norm
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hreal)
    (by simpa using (memLp_const (1 : ℝ) :
      MemLp (fun _ : Fin m → ℝ => (1 : ℝ)) 2 (Measure.pi (fun _ => gaussianReal 0 1))))
  have hmean : (∫ x, graphQuadraticWeight G (1 / (m : ℝ)) x
      ∂Measure.pi (fun _ => gaussianReal 0 1)) ≤
      Real.sqrt (∫ x, graphQuadraticWeight G (1 / (m : ℝ)) x ^ 2
        ∂Measure.pi (fun _ => gaussianReal 0 1)) := by
    rw [Real.sqrt_eq_rpow]
    simpa [graphQuadraticWeight, Real.norm_eq_abs, Real.rpow_two, one_div] using hh
  have hL2 := graphGaussianWeight_L2_le hm G
  simp only [norm_graphGaussianWeight] at hL2
  have hsqrt : Real.sqrt (Real.exp 4) = Real.exp 2 := by
    have heq : Real.exp 4 = Real.exp 2 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hmean.trans ((Real.sqrt_le_sqrt hL2).trans_eq hsqrt)

theorem matrixGaussian_anchoredGraphPrecision {n : ℕ} (G : GaussianGraphData (n + 2))
    (y : Fin (n + 1) → ℝ) :
    matrixGaussian (anchoredGraphPrecision G) y =
      matrixGaussian (completeQuotientPrecision n) y * anchoredGraphQuadraticFactor G y := by
  rw [matrixGaussian, anchoredGraphPrecision_quadratic, matrixGaussian,
    anchoredGraphQuadraticFactor, ← Real.exp_add, completeSquareEnergy_eq]
  congr 1
  rw [completeQuotientPrecision_quadratic]
  simp only [Fintype.card_fin, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    zero_pow (by norm_num : 2 ≠ 0), add_zero]
  push_cast
  ring

/-- Deleting a degree-two graph changes the good cluster's anchored Gaussian
volume by at most exp(2), uniformly in its size and shape. -/
theorem integral_anchoredGraphGaussian_le {n : ℕ} (hn : 16 ≤ n + 2)
    (G : GaussianGraphData (n + 2)) (h1 : G.laplacian *ᵥ (fun _ => 1) = 0) :
    (∫ y : Fin (n + 1) → ℝ, matrixGaussian (anchoredGraphPrecision G) y) ≤
      Real.exp 2 * quotientGaussianVolume (n + 2) := by
  have hmR : (16 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hn
  have hw := memLp_graphGaussianWeight G (1 / ((n + 2 : ℕ) : ℝ)) (by positivity) (by
    rw [show 8 * (1 / ((n + 2 : ℕ) : ℝ)) = 8 / ((n + 2 : ℕ) : ℝ) by ring]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n + 2 : ℕ))).mpr
    linarith)
  have hreal : MemLp (graphQuadraticWeight G (1 / ((n + 2 : ℕ) : ℝ))) 2
      (Measure.pi (fun _ => gaussianReal 0 1)) := by
    simpa only [norm_graphGaussianWeight] using hw.norm
  have hi : Integrable (fun x : Fin (n + 2) → ℝ =>
      anchoredGraphQuadraticFactor G (scaledAnchorDifference x))
        (Measure.pi (fun _ => gaussianReal 0 1)) := by
    simpa only [graphQuadraticFactor_scaledAnchor G h1] using hreal.integrable (by norm_num)
  have ht := integral_standardNormalProduct_scaledAnchorDifference (anchoredGraphQuadraticFactor G) hi
  simp_rw [graphQuadraticFactor_scaledAnchor G h1, smul_eq_mul,
    ← matrixGaussian_anchoredGraphPrecision] at ht
  have hbound := graphQuadraticWeight_mean_le_exp_two hn G
  rw [ht] at hbound
  have hV := quotientGaussianVolume_pos (show 2 ≤ n + 2 by omega)
  have h := mul_le_mul_of_nonneg_left hbound hV.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul, mul_comm] using h

theorem goodClusterGaussian_cube_le {n : ℕ} (hn : 16 ≤ n + 2)
    (G : GaussianGraphData (n + 2)) (h1 : G.laplacian *ᵥ (fun _ => 1) = 0) :
    (∫ x : Fin (n + 2) → ℝ in Metric.closedBall 0 (3 / 16 : ℝ),
      matrixGaussian (anchoredGraphPrecision G) (Real.pi • anchorDifference x)) ≤
      (3 / 8 : ℝ) * Real.exp 2 * quotientGaussianVolume (n + 2) / Real.pi ^ (n + 1) := by
  have hp := anchoredGraphPrecision_posDef (by omega) G h1
  have hc : Continuous (matrixGaussian (anchoredGraphPrecision G)) := by
    unfold matrixGaussian dotProduct Matrix.mulVec
    fun_prop
  have h := integral_closedBall_radian_anchorDifference_le (3 / 16 : ℝ) (by norm_num)
    (matrixGaussian (anchoredGraphPrecision G)) hc (fun _ => (Real.exp_pos _).le)
    (integrable_matrixGaussian _ hp)
  exact h.trans (by
    have hh := mul_le_mul_of_nonneg_left (integral_anchoredGraphGaussian_le hn G h1)
      (show 0 ≤ 2 * (3 / 16 : ℝ) / Real.pi ^ (n + 1) by positivity)
    convert hh using 1; ring)

end
end Wormald
