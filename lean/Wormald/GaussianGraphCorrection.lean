import Wormald.MatrixMomentSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Gaussian correction for any directed partial permutation, expressed using
only its Laplacian bound, trace and imbalance identity. Path-forest relabeling
is unnecessary; the same finite matrix argument also covers cycle components. -/

namespace Wormald
noncomputable section
open Matrix
open scoped BigOperators

structure GaussianGraphData (m : ℕ) where
  laplacian : Matrix (Fin m) (Fin m) ℝ
  imbalance : Fin m → ℝ
  edgeCount : ℕ
  joinCount : ℕ
  positive : laplacian.PosSemidef
  quadratic_le : ∀ x, x ⬝ᵥ (laplacian *ᵥ x) ≤ 4 * (x ⬝ᵥ x)
  trace_eq : laplacian.trace = 2 * edgeCount
  imbalance_square : imbalance ⬝ᵥ imbalance = 2 * (edgeCount : ℝ) - 2 * joinCount
  imbalance_sum : ∑ i, imbalance i = 0
  edges_le : edgeCount ≤ m

theorem graphLaplacian_symmetric {m : ℕ} (G : GaussianGraphData m) :
    G.laplacian.transpose = G.laplacian := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using G.positive.isHermitian.eq

theorem graphLaplacian_quadratic_nonneg {m : ℕ} (G : GaussianGraphData m)
    (x : Fin m → ℝ) : 0 ≤ x ⬝ᵥ (G.laplacian *ᵥ x) := by
  simpa only [star_trivial] using G.positive.dotProduct_mulVec_nonneg x

theorem graphLaplacian_quadratic_le_four {m : ℕ} (G : GaussianGraphData m)
    (x : Fin m → ℝ) : x ⬝ᵥ (G.laplacian *ᵥ x) ≤ 4 * (x ⬝ᵥ x) := G.quadratic_le x

@[simp] theorem graphLaplacian_trace {m : ℕ} (G : GaussianGraphData m) :
    G.laplacian.trace = 2 * G.edgeCount := G.trace_eq

@[simp] theorem graphImbalance_square {m : ℕ} (G : GaussianGraphData m) :
    G.imbalance ⬝ᵥ G.imbalance = 2 * (G.edgeCount : ℝ) - 2 * G.joinCount := G.imbalance_square

theorem posDef_one_sub_smul_graphLaplacian {m : ℕ} (G : GaussianGraphData m)
    (r : ℝ) (hr : 0 ≤ r) (hr4 : 4 * r < 1) : (1 - r • G.laplacian).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    change (1 - r • G.laplacian).transpose = 1 - r • G.laplacian
    simp [Matrix.transpose_sub, Matrix.transpose_smul, graphLaplacian_symmetric]
  · intro x hx
    have hp : 0 < x ⬝ᵥ x := by
      simpa only [star_trivial] using (dotProduct_star_self_pos_iff (v := x)).mpr hx
    have hmul := mul_le_mul_of_nonneg_left (G.quadratic_le x) hr
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul]
    nlinarith [mul_pos (sub_pos.mpr hr4) hp]

private theorem real_dot_self_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- Completing a square bounds the inverse quadratic form without any
dimension-dependent matrix norm estimate. -/
theorem graph_inverse_quadratic_bounds {m : ℕ} (G : GaussianGraphData m)
    (r : ℝ) (hr : 0 ≤ r) (hr4 : 4 * r < 1) (b : Fin m → ℝ) :
    0 ≤ b ⬝ᵥ ((1 - r • G.laplacian)⁻¹ *ᵥ b) - b ⬝ᵥ b ∧
    b ⬝ᵥ ((1 - r • G.laplacian)⁻¹ *ᵥ b) - b ⬝ᵥ b ≤
      (4 * r / (1 - 4 * r)) * (b ⬝ᵥ b) := by
  let M : Matrix (Fin m) (Fin m) ℝ := 1 - r • G.laplacian
  let y := M⁻¹ *ᵥ b
  let c : ℝ := 1 - 4 * r
  have hc : 0 < c := sub_pos.mpr hr4
  have hM := posDef_one_sub_smul_graphLaplacian G r hr hr4
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hMy : M *ᵥ y = b := by
    rw [show y = M⁻¹ *ᵥ b from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv M hunit, Matrix.one_mulVec]
  have hsym : M.transpose = M := by
    dsimp [M]
    simp [Matrix.transpose_sub, Matrix.transpose_smul, graphLaplacian_symmetric]
  have hyb : y ⬝ᵥ (M *ᵥ y) = b ⬝ᵥ y := by rw [hMy, dotProduct_comm]
  have hcross : y ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ b := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hMy]
  have hMb : b ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ b - r * (b ⬝ᵥ (G.laplacian *ᵥ b)) := by
    simp [M, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
  have hlow : c * (y ⬝ᵥ y) ≤ b ⬝ᵥ y := by
    have hh := mul_le_mul_of_nonneg_left (graphLaplacian_quadratic_le_four G y) hr
    have he : y ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ y - r * (y ⬝ᵥ (G.laplacian *ᵥ y)) := by
      simp [M, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
    rw [hyb] at he
    dsimp [c]
    linarith
  have hnorm := real_dot_self_nonneg (b - c • y)
  have hnormeq : (b - c • y) ⬝ᵥ (b - c • y) =
      b ⬝ᵥ b - 2 * c * (b ⬝ᵥ y) + c ^ 2 * (y ⬝ᵥ y) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, dotProduct_comm y b]
    ring
  rw [hnormeq] at hnorm
  have hupper : c * (b ⬝ᵥ y) ≤ b ⬝ᵥ b := by
    have hh := mul_le_mul_of_nonneg_left hlow hc.le
    nlinarith
  have hvar := hM.posSemidef.dotProduct_mulVec_nonneg (b - y)
  change 0 ≤ (b - y) ⬝ᵥ (M *ᵥ (b - y)) at hvar
  simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
    hMy, hcross, hMb, dotProduct_comm y b] at hvar
  have henergy : 0 ≤ r * (b ⬝ᵥ (G.laplacian *ᵥ b)) :=
    mul_nonneg hr (graphLaplacian_quadratic_nonneg G b)
  change 0 ≤ b ⬝ᵥ y - b ⬝ᵥ b ∧
    b ⬝ᵥ y - b ⬝ᵥ b ≤ (4 * r / c) * (b ⬝ᵥ b)
  constructor
  · linarith
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    dsimp [c] at hupper ⊢
    nlinarith

theorem graphLaplacian_posSemidef {m : ℕ} (G : GaussianGraphData m) :
    (G.laplacian).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    exact graphLaplacian_symmetric G
  · intro x
    simpa only [star_trivial] using graphLaplacian_quadratic_nonneg G x

private theorem eigenvalues_le_of_smul_one_sub_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Matrix ι ι ℝ) (hD : D.IsHermitian) (c : ℝ)
    (hbound : (c • (1 : Matrix ι ι ℝ) - D).PosSemidef) (i : ι) :
    hD.eigenvalues i ≤ c := by
  let U := hD.eigenvectorUnitary
  have hp := hbound.conjTranspose_mul_mul_same (U : Matrix ι ι ℝ)
  have hdiag : Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star U) D =
      Matrix.diagonal hD.eigenvalues := by
    simpa [U] using hD.conjStarAlgAut_star_eigenvectorUnitary
  have htrans : (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star U)
      (c • (1 : Matrix ι ι ℝ) - D)).PosSemidef := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using hp
  rw [map_sub, map_smul, map_one, hdiag] at htrans
  have hsub : c • (1 : Matrix ι ι ℝ) - Matrix.diagonal hD.eigenvalues =
      Matrix.diagonal (fun j => c - hD.eigenvalues j) := by
    ext j k
    by_cases hjk : j = k <;> simp [hjk]
  rw [hsub] at htrans
  exact sub_nonneg.mp ((Matrix.posSemidef_diagonal_iff.mp htrans) i)

theorem graph_scaled_eigenvalues_bounds {m : ℕ} (G : GaussianGraphData m)
    (r : ℝ) (hr : 0 ≤ r)
    (hD : (r • G.laplacian).IsHermitian) (i : Fin m) :
    0 ≤ hD.eigenvalues i ∧ hD.eigenvalues i ≤ 4 * r := by
  have hpos := (graphLaplacian_posSemidef G).smul hr
  have hbound : ((4 * r) • (1 : Matrix (Fin m) (Fin m) ℝ) -
      r • G.laplacian).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [Matrix.isHermitian_iff_isSymm]
      change _ᵀ = _
      simp [Matrix.transpose_sub, Matrix.transpose_smul, graphLaplacian_symmetric]
    · intro x
      have h := mul_le_mul_of_nonneg_left (graphLaplacian_quadratic_le_four G x) hr
      simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul]
      nlinarith
  exact ⟨hpos.eigenvalues_nonneg i,
    eigenvalues_le_of_smul_one_sub_posSemidef _ hD _ hbound i⟩

/-- The logarithm of the determinant has a uniform second-order error.
For r=1/m and at most m forest edges this error is O(1/m). -/
theorem graph_logdet_quadratic_error {m : ℕ} (G : GaussianGraphData m)
    (r : ℝ) (hr : 0 ≤ r) (hr8 : r ≤ 1 / 8) :
    |Real.log (1 - r • G.laplacian).det + 2 * r * G.edgeCount| ≤
      16 * r ^ 2 * G.edgeCount := by
  let D := r • G.laplacian
  have hpos : D.PosSemidef := (graphLaplacian_posSemidef G).smul hr
  let μ := hpos.1.eigenvalues
  have hμ0 (i) : 0 ≤ μ i := (graph_scaled_eigenvalues_bounds G r hr hpos.1 i).1
  have hμr (i) : μ i ≤ 4 * r := (graph_scaled_eigenvalues_bounds G r hr hpos.1 i).2
  have hμhalf (i) : μ i ≤ 1 / 2 := by linarith [hμr i]
  have hμ1 (i) : μ i < 1 := by linarith [hμhalf i]
  have hlog : Real.log (1 - D).det = ∑ i, Real.log (1 - μ i) := by
    rw [det_one_sub_eq_prod_eigenvalues D hpos.1,
      Real.log_prod (fun i _ => (sub_pos.mpr (hμ1 i)).ne')]
  have htrace : ∑ i, μ i = 2 * r * G.edgeCount := by
    have h := trace_pow_eq_sum_eigenvalues D hpos.1 1
    simpa [D, Matrix.trace_smul, graphLaplacian_trace, mul_comm, mul_left_comm,
      mul_assoc] using h.symm
  have hscalar (i) : |Real.log (1 - μ i) + μ i| ≤ 8 * r * μ i := by
    have h := Real.abs_log_sub_add_sum_range_le (x := μ i)
      (by rw [abs_of_nonneg (hμ0 i)]; exact hμ1 i) 1
    norm_num [Finset.sum_range_succ, abs_of_nonneg (hμ0 i)] at h
    have hfrac : μ i ^ 2 / (1 - μ i) ≤ 8 * r * μ i := by
      apply (div_le_iff₀ (sub_pos.mpr (hμ1 i))).mpr
      have hsq : μ i ^ 2 ≤ 4 * r * μ i := by nlinarith [mul_nonneg (hμ0 i) (sub_nonneg.mpr (hμr i))]
      nlinarith [mul_nonneg (show 0 ≤ 8 * r * μ i from
          mul_nonneg (mul_nonneg (by norm_num) hr) (hμ0 i))
        (show 0 ≤ 1 / 2 - μ i by linarith [hμhalf i])]
    simpa only [add_comm] using h.trans hfrac
  rw [hlog, ← htrace, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ i, |Real.log (1 - μ i) + μ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 8 * r * μ i := Finset.sum_le_sum fun i _ => hscalar i
    _ = _ := by rw [← Finset.mul_sum, htrace]; ring

def graphGaussianLogFactor {m : ℕ} (G : GaussianGraphData m) (r : ℝ) : ℝ :=
  -Real.log (1 - r • G.laplacian).det / 2 - r / 2 *
    (G.imbalance ⬝ᵥ ((1 - r • G.laplacian)⁻¹ *ᵥ G.imbalance))

/-- The Gaussian determinant correction and endpoint phase combine to the
number of consecutive selected edges. The error is uniform over all forests. -/
theorem graphGaussianLogFactor_error {m : ℕ} (G : GaussianGraphData m)
    (r : ℝ) (hr : 0 ≤ r) (hr8 : r ≤ 1 / 8) :
    |graphGaussianLogFactor G r - r * G.joinCount| ≤ 16 * r ^ 2 * G.edgeCount := by
  let b := G.imbalance
  let v := b ⬝ᵥ ((1 - r • G.laplacian)⁻¹ *ᵥ b)
  have hdet := graph_logdet_quadratic_error G r hr hr8
  have hgap := graph_inverse_quadratic_bounds G r hr (by linarith) b
  have hb : b ⬝ᵥ b ≤ 2 * G.edgeCount := by
    dsimp [b]
    rw [graphImbalance_square]
    linarith [show (0 : ℝ) ≤ G.joinCount by positivity]
  have hc : 0 < 1 - 4 * r := by linarith
  have hcoef : 4 * r / (1 - 4 * r) ≤ 8 * r := by
    apply (div_le_iff₀ hc).mpr
    nlinarith [mul_nonneg hr (show 0 ≤ 1 - 8 * r by linarith)]
  have hgap' : 0 ≤ v - b ⬝ᵥ b ∧ v - b ⬝ᵥ b ≤ 16 * r * G.edgeCount := by
    refine ⟨hgap.1, ?_⟩
    calc
      _ ≤ (4 * r / (1 - 4 * r)) * (b ⬝ᵥ b) := hgap.2
      _ ≤ (8 * r) * (2 * G.edgeCount) :=
        mul_le_mul hcoef hb (real_dot_self_nonneg b) (by positivity)
      _ = _ := by ring
  have heq : graphGaussianLogFactor G r - r * G.joinCount =
      -(Real.log (1 - r • G.laplacian).det + 2 * r * G.edgeCount) / 2 -
        r / 2 * (v - b ⬝ᵥ b) := by
    dsimp [graphGaussianLogFactor, v, b]
    rw [graphImbalance_square]
    ring
  rw [heq]
  calc
    _ ≤ |-(Real.log (1 - r • G.laplacian).det + 2 * r * G.edgeCount) / 2| +
        |r / 2 * (v - b ⬝ᵥ b)| := abs_sub _ _
    _ = |Real.log (1 - r • G.laplacian).det + 2 * r * G.edgeCount| / 2 +
        r / 2 * (v - b ⬝ᵥ b) := by
      rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg (mul_nonneg (div_nonneg hr (by norm_num)) hgap'.1)]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hgap'.2 (div_nonneg hr (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith


end
end Wormald
