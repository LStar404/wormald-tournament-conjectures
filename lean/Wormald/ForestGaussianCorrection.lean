import Wormald.ForestLaplacian
import Wormald.MatrixMomentSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Uniform finite-matrix estimates for the Gaussian tilt produced by forcing
a path forest. The estimates retain their constants as the dimension grows. -/

namespace Wormald
noncomputable section
open Matrix
open scoped BigOperators

private theorem real_dot_self_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- Completing a square bounds the inverse quadratic form without any
dimension-dependent matrix norm estimate. -/
theorem forest_inverse_quadratic_bounds {n : ℕ} (S : Finset (Fin n))
    (r : ℝ) (hr : 0 ≤ r) (hr4 : 4 * r < 1) (b : Fin (n + 1) → ℝ) :
    0 ≤ b ⬝ᵥ ((1 - r • forestLaplacian S)⁻¹ *ᵥ b) - b ⬝ᵥ b ∧
    b ⬝ᵥ ((1 - r • forestLaplacian S)⁻¹ *ᵥ b) - b ⬝ᵥ b ≤
      (4 * r / (1 - 4 * r)) * (b ⬝ᵥ b) := by
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := 1 - r • forestLaplacian S
  let y := M⁻¹ *ᵥ b
  let c : ℝ := 1 - 4 * r
  have hc : 0 < c := sub_pos.mpr hr4
  have hM := posDef_one_sub_smul_forestLaplacian S r hr hr4
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hMy : M *ᵥ y = b := by
    rw [show y = M⁻¹ *ᵥ b from rfl, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv M hunit, Matrix.one_mulVec]
  have hsym : M.transpose = M := by
    dsimp [M]
    simp [Matrix.transpose_sub, Matrix.transpose_smul, forestLaplacian_symmetric]
  have hyb : y ⬝ᵥ (M *ᵥ y) = b ⬝ᵥ y := by rw [hMy, dotProduct_comm]
  have hcross : y ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ b := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hMy]
  have hMb : b ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ b - r * (b ⬝ᵥ (forestLaplacian S *ᵥ b)) := by
    simp [M, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
  have hlow : c * (y ⬝ᵥ y) ≤ b ⬝ᵥ y := by
    have hh := mul_le_mul_of_nonneg_left (forestLaplacian_quadratic_le_four S y) hr
    have he : y ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ y - r * (y ⬝ᵥ (forestLaplacian S *ᵥ y)) := by
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
  have henergy : 0 ≤ r * (b ⬝ᵥ (forestLaplacian S *ᵥ b)) :=
    mul_nonneg hr (forestLaplacian_quadratic_nonneg S b)
  change 0 ≤ b ⬝ᵥ y - b ⬝ᵥ b ∧
    b ⬝ᵥ y - b ⬝ᵥ b ≤ (4 * r / c) * (b ⬝ᵥ b)
  constructor
  · linarith
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    dsimp [c] at hupper ⊢
    nlinarith

theorem forestLaplacian_posSemidef {n : ℕ} (S : Finset (Fin n)) :
    (forestLaplacian S).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    exact forestLaplacian_symmetric S
  · intro x
    simpa only [star_trivial] using forestLaplacian_quadratic_nonneg S x

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

theorem forest_scaled_eigenvalues_bounds {n : ℕ} (S : Finset (Fin n))
    (r : ℝ) (hr : 0 ≤ r)
    (hD : (r • forestLaplacian S).IsHermitian) (i : Fin (n + 1)) :
    0 ≤ hD.eigenvalues i ∧ hD.eigenvalues i ≤ 4 * r := by
  have hpos := (forestLaplacian_posSemidef S).smul hr
  have hbound : ((4 * r) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) -
      r • forestLaplacian S).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [Matrix.isHermitian_iff_isSymm]
      change _ᵀ = _
      simp [Matrix.transpose_sub, Matrix.transpose_smul, forestLaplacian_symmetric]
    · intro x
      have h := mul_le_mul_of_nonneg_left (forestLaplacian_quadratic_le_four S x) hr
      simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul]
      nlinarith
  exact ⟨hpos.eigenvalues_nonneg i,
    eigenvalues_le_of_smul_one_sub_posSemidef _ hD _ hbound i⟩

/-- The logarithm of the determinant has a uniform second-order error.
For r=1/m and at most m forest edges this error is O(1/m). -/
theorem forest_logdet_quadratic_error {n : ℕ} (S : Finset (Fin n))
    (r : ℝ) (hr : 0 ≤ r) (hr8 : r ≤ 1 / 8) :
    |Real.log (1 - r • forestLaplacian S).det + 2 * r * S.card| ≤
      16 * r ^ 2 * S.card := by
  let D := r • forestLaplacian S
  have hpos : D.PosSemidef := (forestLaplacian_posSemidef S).smul hr
  let μ := hpos.1.eigenvalues
  have hμ0 (i) : 0 ≤ μ i := (forest_scaled_eigenvalues_bounds S r hr hpos.1 i).1
  have hμr (i) : μ i ≤ 4 * r := (forest_scaled_eigenvalues_bounds S r hr hpos.1 i).2
  have hμhalf (i) : μ i ≤ 1 / 2 := by linarith [hμr i]
  have hμ1 (i) : μ i < 1 := by linarith [hμhalf i]
  have hlog : Real.log (1 - D).det = ∑ i, Real.log (1 - μ i) := by
    rw [det_one_sub_eq_prod_eigenvalues D hpos.1,
      Real.log_prod (fun i _ => (sub_pos.mpr (hμ1 i)).ne')]
  have htrace : ∑ i, μ i = 2 * r * S.card := by
    have h := trace_pow_eq_sum_eigenvalues D hpos.1 1
    simpa [D, Matrix.trace_smul, trace_forestLaplacian, mul_comm, mul_left_comm,
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

def forestGaussianLogFactor {n : ℕ} (S : Finset (Fin n)) (r : ℝ) : ℝ :=
  -Real.log (1 - r • forestLaplacian S).det / 2 - r / 2 *
    (forestImbalance S ⬝ᵥ ((1 - r • forestLaplacian S)⁻¹ *ᵥ forestImbalance S))

/-- The Gaussian determinant correction and endpoint phase combine to the
number of consecutive selected edges. The error is uniform over all forests. -/
theorem forestGaussianLogFactor_error {n : ℕ} (S : Finset (Fin n))
    (r : ℝ) (hr : 0 ≤ r) (hr8 : r ≤ 1 / 8) :
    |forestGaussianLogFactor S r - r * forestJoinCount S| ≤ 16 * r ^ 2 * S.card := by
  let b := forestImbalance S
  let v := b ⬝ᵥ ((1 - r • forestLaplacian S)⁻¹ *ᵥ b)
  have hdet := forest_logdet_quadratic_error S r hr hr8
  have hgap := forest_inverse_quadratic_bounds S r hr (by linarith) b
  have hb : b ⬝ᵥ b ≤ 2 * S.card := by
    dsimp [b]
    rw [forestImbalance_square]
    linarith [show (0 : ℝ) ≤ forestJoinCount S by positivity]
  have hc : 0 < 1 - 4 * r := by linarith
  have hcoef : 4 * r / (1 - 4 * r) ≤ 8 * r := by
    apply (div_le_iff₀ hc).mpr
    nlinarith [mul_nonneg hr (show 0 ≤ 1 - 8 * r by linarith)]
  have hgap' : 0 ≤ v - b ⬝ᵥ b ∧ v - b ⬝ᵥ b ≤ 16 * r * S.card := by
    refine ⟨hgap.1, ?_⟩
    calc
      _ ≤ (4 * r / (1 - 4 * r)) * (b ⬝ᵥ b) := hgap.2
      _ ≤ (8 * r) * (2 * S.card) :=
        mul_le_mul hcoef hb (real_dot_self_nonneg b) (by positivity)
      _ = _ := by ring
  have heq : forestGaussianLogFactor S r - r * forestJoinCount S =
      -(Real.log (1 - r • forestLaplacian S).det + 2 * r * S.card) / 2 -
        r / 2 * (v - b ⬝ᵥ b) := by
    dsimp [forestGaussianLogFactor, v, b]
    rw [forestImbalance_square]
    ring
  rw [heq]
  calc
    _ ≤ |-(Real.log (1 - r • forestLaplacian S).det + 2 * r * S.card) / 2| +
        |r / 2 * (v - b ⬝ᵥ b)| := abs_sub _ _
    _ = |Real.log (1 - r • forestLaplacian S).det + 2 * r * S.card| / 2 +
        r / 2 * (v - b ⬝ᵥ b) := by
      rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg (mul_nonneg (div_nonneg hr (by norm_num)) hgap'.1)]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hgap'.2 (div_nonneg hr (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith

/-- At the true central scale r=1/m, the Gaussian part of the containment
ratio has a relative error bounded by 32/m, for every path edge subset. -/
theorem forestGaussian_relative_error_le {n : ℕ} (hn : 16 ≤ n + 1)
    (S : Finset (Fin n)) :
    |Real.exp (forestGaussianLogFactor S (1 / ((n + 1 : ℕ) : ℝ)) -
      forestJoinCount S / ((n + 1 : ℕ) : ℝ)) - 1| ≤ 32 / ((n + 1 : ℕ) : ℝ) := by
  let m : ℝ := ((n + 1 : ℕ) : ℝ)
  have hm16 : 16 ≤ m := by dsimp [m]; exact_mod_cast hn
  have hm : 0 < m := by linarith
  have hr : 0 ≤ 1 / m := le_of_lt (one_div_pos.mpr hm)
  have hr8 : 1 / m ≤ 1 / 8 := (div_le_div_iff₀ hm (by norm_num)).mpr (by linarith)
  have hc : (S.card : ℝ) ≤ m := by
    have h := S.card_le_univ
    simp only [Fintype.card_fin] at h
    have hcast : (S.card : ℝ) ≤ n := by exact_mod_cast h
    dsimp [m]
    push_cast
    linarith
  have he := forestGaussianLogFactor_error S (1 / m) hr hr8
  have hbound : |forestGaussianLogFactor S (1 / m) - forestJoinCount S / m| ≤ 16 / m := by
    calc
      _ = |forestGaussianLogFactor S (1 / m) - (1 / m) * forestJoinCount S| := by congr 1; ring
      _ ≤ 16 * (1 / m) ^ 2 * S.card := he
      _ ≤ 16 * (1 / m) ^ 2 * m := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 16 / m := by field_simp
  have hone : 16 / m ≤ 1 := (div_le_iff₀ hm).mpr (by linarith)
  have hexp := Real.abs_exp_sub_one_le (hbound.trans hone)
  change _ ≤ 32 / m
  calc
    _ ≤ 2 * |forestGaussianLogFactor S (1 / m) - forestJoinCount S / m| := hexp
    _ ≤ 2 * (16 / m) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = _ := by ring

end
end Wormald
