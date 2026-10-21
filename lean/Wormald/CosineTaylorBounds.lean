import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Uniform scalar estimates for the growing-dimensional regular-tournament
Fourier integral. Constants do not depend on the number of vertices or edges. -/

namespace Wormald
noncomputable section
open scoped BigOperators
open Set

theorem abs_cos_quartic_remainder (x : ℝ) (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)| ≤ |x| ^ 6 / 120 := by
  have hbound := taylor_mean_remainder_bound (f := Real.cos) (n := 5)
    (C := 1) (a := 0) (b := 1) (x := |x|) (by norm_num)
    Real.contDiff_cos.contDiffOn ⟨abs_nonneg x, hx⟩
    (fun y hy => by
      rw [Real.iteratedDerivWithin_cos_Icc 6 (by norm_num) hy, Real.norm_eq_abs]
      exact Real.abs_iteratedDeriv_cos_le_one 6 y)
  have ht : taylorWithinEval Real.cos 5 (Icc 0 1) 0 |x| =
      1 - |x| ^ 2 / 2 + |x| ^ 4 / 24 := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, Real.iteratedDerivWithin_cos_Icc _ (by norm_num)
      (show (0 : ℝ) ∈ Icc 0 1 by norm_num), Real.iteratedDeriv_add_one_cos,
      Real.iteratedDeriv_add_one_sin, iteratedDeriv_zero, smul_eq_mul]
    ring
  rw [ht] at hbound
  have hfour : |x| ^ 4 = x ^ 4 := by
    calc
      |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
      _ = (x ^ 2) ^ 2 := by rw [sq_abs]
      _ = x ^ 4 := by ring
  norm_num [Real.cos_abs, Real.norm_eq_abs, sq_abs, hfour] at hbound
  exact hbound

theorem abs_log_cos_quartic_remainder (x : ℝ) (hx : |x| ≤ 1) :
    |Real.log (Real.cos x) + x ^ 2 / 2 + x ^ 4 / 12| ≤ |x| ^ 6 := by
  let u : ℝ := 1 - Real.cos x
  have hu0 : 0 ≤ u := sub_nonneg.mpr (Real.cos_le_one x)
  have hu2 : u ≤ x ^ 2 / 2 := by
    dsimp [u]
    linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hu1 : u ≤ 1 / 2 := by linarith
  have hlog := Real.abs_log_sub_add_sum_range_le
    (x := u) (by rw [abs_of_nonneg hu0]; linarith) 2
  norm_num [Finset.sum_range_succ, abs_of_nonneg hu0, show 1 - u = Real.cos x by dsimp [u]; ring] at hlog
  have hlog' : |Real.log (Real.cos x) + u + u ^ 2 / 2| ≤ 2 * u ^ 3 := by
    have hden : 0 < 1 - u := by linarith
    have hfrac : u ^ 3 / (1 - u) ≤ 2 * u ^ 3 := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg (pow_nonneg hu0 3) (show 0 ≤ 1 - 2 * u by linarith)]
    rw [show 1 - u = Real.cos x by dsimp [u]; ring] at hfrac
    convert hlog.trans hfrac using 1
    congr 1
    ring
  have hx6 : |x| ^ 6 = (x ^ 2) ^ 3 := by
    calc
      |x| ^ 6 = (|x| ^ 2) ^ 3 := by ring
      _ = (x ^ 2) ^ 3 := by rw [sq_abs]
  have he := abs_cos_quartic_remainder x hx
  rw [hx6] at he
  have heu : |u - x ^ 2 / 2| ≤ x ^ 4 := by
    rw [abs_of_nonpos (by linarith : u - x ^ 2 / 2 ≤ 0)]
    have hE := (abs_le.mp he).2
    dsimp [u] at *
    nlinarith [mul_nonneg (sq_nonneg (x ^ 2)) (show 0 ≤ 1 - x ^ 2 by linarith)]
  have hsum : |u + x ^ 2 / 2| ≤ x ^ 2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ u + x ^ 2 / 2)]
    linarith
  have hpoly : |u + u ^ 2 / 2 - (x ^ 2 / 2 + x ^ 4 / 12)| ≤
      (x ^ 2) ^ 3 / 120 + (x ^ 2) ^ 3 / 2 := by
    have he' : |u - (x ^ 2 / 2 - x ^ 4 / 24)| ≤ (x ^ 2) ^ 3 / 120 := by
      convert he using 1
      rw [show u - (x ^ 2 / 2 - x ^ 4 / 24) =
        -(Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)) by dsimp [u]; ring,
        abs_neg]
    calc
      _ = |(u - (x ^ 2 / 2 - x ^ 4 / 24)) +
          (u - x ^ 2 / 2) * (u + x ^ 2 / 2) / 2| := by congr 1; ring
      _ ≤ |u - (x ^ 2 / 2 - x ^ 4 / 24)| +
          |(u - x ^ 2 / 2) * (u + x ^ 2 / 2) / 2| := abs_add_le _ _
      _ ≤ (x ^ 2) ^ 3 / 120 + (x ^ 2) ^ 3 / 2 := by
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
        calc
          |u - x ^ 2 / 2| * |u + x ^ 2 / 2| ≤ x ^ 4 * x ^ 2 := mul_le_mul heu hsum (abs_nonneg _) (by positivity)
          _ = (x ^ 2) ^ 3 := by ring
  have hu3 : 2 * u ^ 3 ≤ (x ^ 2) ^ 3 / 4 := by
    have hp := pow_le_pow_left₀ hu0 hu2 3
    nlinarith [hp]
  calc
    _ = |(Real.log (Real.cos x) + u + u ^ 2 / 2) -
        (u + u ^ 2 / 2 - (x ^ 2 / 2 + x ^ 4 / 12))| := by congr 1; ring
    _ ≤ |Real.log (Real.cos x) + u + u ^ 2 / 2| +
        |u + u ^ 2 / 2 - (x ^ 2 / 2 + x ^ 4 / 12)| := abs_sub _ _
    _ ≤ |x| ^ 6 := by rw [hx6]; nlinarith [hlog', hpoly, hu3, pow_nonneg (sq_nonneg x) 3]

theorem cos_pos_of_abs_le_one (x : ℝ) (hx : |x| ≤ 1) : 0 < Real.cos x := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

theorem abs_log_cos_quadratic_remainder (x : ℝ) (hx : |x| ≤ 1) :
    |Real.log (Real.cos x) + x ^ 2 / 2| ≤ 2 * |x| ^ 4 := by
  have h6 : |x| ^ 6 ≤ |x| ^ 4 := by
    have hp : |x| ^ 2 ≤ 1 := by nlinarith [abs_nonneg x]
    nlinarith [mul_nonneg (pow_nonneg (abs_nonneg x) 4) (sub_nonneg.mpr hp)]
  have h4 : x ^ 4 = |x| ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
  calc
    _ = |(Real.log (Real.cos x) + x ^ 2 / 2 + x ^ 4 / 12) - x ^ 4 / 12| := by congr 1; ring
    _ ≤ |Real.log (Real.cos x) + x ^ 2 / 2 + x ^ 4 / 12| + |x ^ 4 / 12| := abs_sub _ _
    _ ≤ 2 * |x| ^ 4 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ x ^ 4 / 12), h4]
      have hq := abs_log_cos_quartic_remainder x hx
      rw [h4] at hq
      nlinarith [hq, pow_nonneg (abs_nonneg x) 4]

theorem log_cos_le_neg_quarter_sq (x : ℝ) (hx : |x| ≤ 1) :
    Real.log (Real.cos x) ≤ -(x ^ 2 / 4) := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have h4 : x ^ 4 ≤ x ^ 2 := by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2)]
  have h6 : |x| ^ 6 ≤ x ^ 2 := by
    have hh : |x| ^ 6 = x ^ 4 * x ^ 2 := by
      calc
        |x| ^ 6 = (|x| ^ 2) ^ 3 := by ring
        _ = x ^ 4 * x ^ 2 := by rw [sq_abs]; ring
    rw [hh]
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - x ^ 4 by linarith)]
  have hc := (abs_le.mp (abs_cos_quartic_remainder x hx)).2
  have hl := Real.log_le_sub_one_of_pos (cos_pos_of_abs_le_one x hx)
  linarith [sq_nonneg x]

/-- The sharp quadratic coefficient is needed for growing-dimensional tails:
a weaker Gaussian coefficient would introduce an exponential volume loss. -/
theorem log_cos_le_neg_half_sq (x : ℝ) (hx : |x| < Real.pi / 2) :
    Real.log (Real.cos x) ≤ -(x ^ 2 / 2) := by
  let f : ℝ → ℝ := fun y => Real.log (Real.cos y) + y ^ 2 / 2
  have hd : ∀ y ∈ Icc 0 |x|, HasDerivAt f (-Real.tan y + y) y := by
    intro y hy
    have hc : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hy.1, Real.pi_pos], hy.2.trans_lt hx⟩
    have hl : HasDerivAt (fun t => Real.log (Real.cos t)) (-Real.tan y) y := by
      simpa only [Real.tan_eq_sin_div_cos, neg_div] using (Real.hasDerivAt_cos y).log hc.ne'
    convert hl.add ((hasDerivAt_pow 2 y).div_const 2) using 1
    norm_num
  have hm : AntitoneOn f (Icc 0 |x|) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => by
        have hy' := interior_subset hy
        linarith [Real.le_tan hy'.1 (hy'.2.trans_lt hx)])
  have hh := hm ⟨le_rfl, abs_nonneg x⟩ ⟨abs_nonneg x, le_rfl⟩ (abs_nonneg x)
  simp only [f, Real.cos_zero, Real.log_one, zero_pow (by norm_num : 2 ≠ 0), zero_div,
    add_zero, Real.cos_abs, sq_abs] at hh
  linarith

theorem abs_cos_le_exp_neg_half_sq (x : ℝ) (hx : |x| ≤ Real.pi / 2) :
    |Real.cos x| ≤ Real.exp (-(x ^ 2 / 2)) := by
  by_cases hlt : |x| < Real.pi / 2
  · have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo (abs_lt.mp hlt)
    rw [abs_of_pos hc, ← Real.exp_log hc]
    exact Real.exp_le_exp.mpr (log_cos_le_neg_half_sq x hlt)
  · have heq : |x| = Real.pi / 2 := le_antisymm hx (le_of_not_gt hlt)
    have hc : Real.cos x = 0 := by rw [← Real.cos_abs, heq, Real.cos_pi_div_two]
    rw [hc, abs_zero]
    exact (Real.exp_pos _).le

variable {ι : Type*}

/-- The quartic approximation is uniform over every finite edge family. -/
theorem exists_cosine_product_quartic_error (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, |x i| ≤ 1) :
    ∃ e : ℝ, |e| ≤ ∑ i ∈ s, |x i| ^ 6 ∧
      (∏ i ∈ s, Real.cos (x i)) = Real.exp
        (-(∑ i ∈ s, x i ^ 2) / 2 - (∑ i ∈ s, x i ^ 4) / 12 + e) := by
  refine ⟨∑ i ∈ s, (Real.log (Real.cos (x i)) + x i ^ 2 / 2 + x i ^ 4 / 12), ?_, ?_⟩
  · exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i hi => abs_log_cos_quartic_remainder (x i) (hx i hi))
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    rw [show -(∑ i ∈ s, x i ^ 2) / 2 - (∑ i ∈ s, x i ^ 4) / 12 +
        ((∑ i ∈ s, Real.log (Real.cos (x i))) +
          (∑ i ∈ s, x i ^ 2) / 2 + (∑ i ∈ s, x i ^ 4) / 12) =
        ∑ i ∈ s, Real.log (Real.cos (x i)) by ring, Real.exp_sum]
    exact Finset.prod_congr rfl fun i hi => (Real.exp_log (cos_pos_of_abs_le_one (x i) (hx i hi))).symm

/-- A cardinality bound turns the local scalar error into an explicit bound
valid even when the number of variables and edges grow. -/
theorem cosine_quartic_error_le_card_mul_radius (s : Finset ι) (x : ι → ℝ)
    (r : ℝ) (_hr : 0 ≤ r) (hr1 : r ≤ 1) (hx : ∀ i ∈ s, |x i| ≤ r) :
    |∑ i ∈ s, (Real.log (Real.cos (x i)) + x i ^ 2 / 2 + x i ^ 4 / 12)| ≤
      s.card * r ^ 6 := by
  calc
    _ ≤ ∑ i ∈ s, |Real.log (Real.cos (x i)) + x i ^ 2 / 2 + x i ^ 4 / 12| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, r ^ 6 := Finset.sum_le_sum fun i hi =>
      (abs_log_cos_quartic_remainder (x i) ((hx i hi).trans hr1)).trans
        (pow_le_pow_left₀ (abs_nonneg _) (hx i hi) 6)
    _ = _ := by simp [nsmul_eq_mul]

/-- Deleting a forest edge contributes a quadratic correction with a uniform
fourth-order error; at central scale the error is O(|F| r⁴). -/
theorem cosine_quadratic_error_le_card_mul_radius (s : Finset ι) (x : ι → ℝ)
    (r : ℝ) (_hr : 0 ≤ r) (hr1 : r ≤ 1) (hx : ∀ i ∈ s, |x i| ≤ r) :
    |∑ i ∈ s, (Real.log (Real.cos (x i)) + x i ^ 2 / 2)| ≤
      2 * s.card * r ^ 4 := by
  calc
    _ ≤ ∑ i ∈ s, |Real.log (Real.cos (x i)) + x i ^ 2 / 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, 2 * r ^ 4 := Finset.sum_le_sum fun i hi =>
      (abs_log_cos_quadratic_remainder (x i) ((hx i hi).trans hr1)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hx i hi) 4) (by norm_num))
    _ = _ := by simp [nsmul_eq_mul]; ring

end
end Wormald
