import Wormald.CircleCosineKernel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Data.Nat.Choose.Bounds

/-! The geometric decay needed after sorting configurations by their number
of outliers.  The dimension-dependent polynomial cost is dominated by the
cross-cluster cosine loss, uniformly in the number of outliers. -/

namespace Wormald
noncomputable section
open Filter Finset
open scoped Topology BigOperators

/-- A fixed polynomial does not offset geometric decay, even when the
exponent is the integer quotient minus a fixed number. -/
theorem tendsto_nat_pow_mul_floor_pow {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (p b c : ℕ) (hb : 0 < b) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ p * q ^ (m / b - c)) atTop (𝓝 0) := by
  have ht : Tendsto (fun m : ℕ => m / b) atTop atTop :=
    Nat.tendsto_div_const_atTop hb.ne'
  have hlim := ((tendsto_pow_const_mul_const_pow_of_lt_one p hq.le hq1).comp ht).const_mul
    (((2 * b : ℕ) : ℝ) ^ p / q ^ c)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun m => mul_nonneg (by positivity) (by positivity))
    _ hlim
  filter_upwards [ht.eventually (eventually_ge_atTop (max c 1))] with m hm
  have hc : c ≤ m / b := le_trans (le_max_left _ _) hm
  have hdiv : 1 ≤ m / b := le_trans (le_max_right _ _) hm
  have hsize : m ≤ 2 * b * (m / b) := by
    have hmod := Nat.mod_lt m hb
    have hdecomp := Nat.mod_add_div m b
    nlinarith
  have hsizeR : (m : ℝ) ≤ ((2 * b : ℕ) : ℝ) * (m / b : ℕ) := by exact_mod_cast hsize
  have hpow : (m : ℝ) ^ p ≤ (((2 * b : ℕ) : ℝ) * (m / b : ℕ)) ^ p :=
    pow_le_pow_left₀ (by positivity) hsizeR _
  have heq : q ^ (m / b - c) = q ^ (m / b) / q ^ c := by
    apply (eq_div_iff (pow_ne_zero _ hq.ne')).mpr
    rw [← pow_add, Nat.sub_add_cancel hc]
  rw [heq]
  calc
    _ ≤ ((((2 * b : ℕ) : ℝ) * (m / b : ℕ)) ^ p) *
        (q ^ (m / b) / q ^ c) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by simp only [Function.comp_apply, mul_pow]; ring

/-- In particular the actual bin separation beats the m^(3/2) cost per
outlier.  The constant may include all fixed Jacobian and counting costs. -/
theorem tendsto_cluster_geometric_base {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (C : ℝ) :
    Tendsto (fun m : ℕ => C * (m : ℝ) ^ (3 / 2 : ℝ) * q ^ (m / 16 - 2))
      atTop (𝓝 0) := by
  have hlim := (tendsto_nat_pow_mul_floor_pow hq hq1 2 16 2 (by norm_num)).const_mul |C|
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (m : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hmR (by norm_num : (3 / 2 : ℝ) ≤ 2)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    abs_of_nonneg (pow_nonneg hq.le _)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (abs_nonneg C))
      (pow_nonneg hq.le (m / 16 - 2))

/-- The outlier sum starts at one, so its bound tends to zero with its base. -/
theorem sum_outlier_powers_le {B : ℝ} (hB : 0 ≤ B) (hB1 : B < 1) (m : ℕ) :
    (∑ r ∈ Icc 1 m, B ^ r) ≤ B / (1 - B) := by
  simpa only [Finset.Ico_add_one_right_eq_Icc, pow_one] using
    (geom_sum_Ico_le_of_lt_one (m := 1) (n := m + 1) hB hB1)

/-- The number of possible outliers may grow with the dimension.  Once
the common base tends to zero, the whole finite geometric tail does too. -/
theorem tendsto_sum_outlier_powers {B : ℕ → ℝ}
    (hB : ∀ᶠ m in atTop, 0 ≤ B m) (hlim : Tendsto B atTop (𝓝 0)) :
    Tendsto (fun m => ∑ r ∈ Icc 1 m, B m ^ r) atTop (𝓝 0) := by
  have hquot := hlim.div (tendsto_const_nhds.sub hlim) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  simp only [sub_zero, zero_div] at hquot
  apply squeeze_zero' _ _ hquot
  · filter_upwards [hB] with m hm
    exact sum_nonneg fun r _ => pow_nonneg hm r
  · filter_upwards [hB, hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with m hm hm1
    exact sum_outlier_powers_le hm hm1 m

theorem tendsto_cluster_outlier_sum {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun m : ℕ => ∑ r ∈ Icc 1 m,
      (C * (m : ℝ) ^ (3 / 2 : ℝ) * q ^ (m / 16 - 2)) ^ r) atTop (𝓝 0) := by
  apply tendsto_sum_outlier_powers
    (Eventually.of_forall fun m => mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
      (pow_nonneg hq.le _))
  exact tendsto_cluster_geometric_base hq hq1 C

/-- Choosing the exceptional vertices costs at most m^r. -/
theorem binomial_outlier_sum_le {A : ℝ} (hA : 0 ≤ A) (m : ℕ) :
    (∑ r ∈ Icc 1 m, (m.choose r : ℝ) * A ^ r) ≤
      ∑ r ∈ Icc 1 m, ((m : ℝ) * A) ^ r := by
  apply sum_le_sum
  intro r _
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hA r)
  exact_mod_cast Nat.choose_le_pow m r

theorem binomial_outlier_sum_le_div {A : ℝ} (hA : 0 ≤ A) (m : ℕ)
    (hmA : (m : ℝ) * A < 1) :
    (∑ r ∈ Icc 1 m, (m.choose r : ℝ) * A ^ r) ≤
      ((m : ℝ) * A) / (1 - (m : ℝ) * A) :=
  (binomial_outlier_sum_le hA m).trans
    (sum_outlier_powers_le (mul_nonneg (Nat.cast_nonneg m) hA) hmA m)

/-- The dense-core counting inequality yields a common decay base that is
independent of the configuration and its number of exceptional vertices. -/
theorem cluster_separation_power_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (m c r : ℕ) (hc : m ≤ 16 * c) :
    q ^ (r * (c - 2)) ≤ (q ^ (m / 16 - 2)) ^ r := by
  have hdiv : m / 16 ≤ c := by omega
  have he : r * (m / 16 - 2) ≤ r * (c - 2) :=
    Nat.mul_le_mul_left r (Nat.sub_le_sub_right hdiv 2)
  simpa only [← pow_mul, Nat.mul_comm r] using pow_le_pow_of_le_one hq hq1 he

theorem tendsto_binomial_outlier_sum {A : ℕ → ℝ}
    (hA : ∀ᶠ m in atTop, 0 ≤ A m)
    (hlim : Tendsto (fun m : ℕ => (m : ℝ) * A m) atTop (𝓝 0)) :
    Tendsto (fun m => ∑ r ∈ Icc 1 m, (m.choose r : ℝ) * A m ^ r)
      atTop (𝓝 0) := by
  have hB : ∀ᶠ m : ℕ in atTop, 0 ≤ (m : ℝ) * A m :=
    hA.mono fun m hm => mul_nonneg (Nat.cast_nonneg m) hm
  apply squeeze_zero' _ _ (tendsto_sum_outlier_powers hB hlim)
  · filter_upwards [hA] with m hm
    exact sum_nonneg fun r _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hm r)
  · exact hA.mono fun m hm => binomial_outlier_sum_le hm m

/-- This is the form used by the actual cluster decomposition: the Gaussian
volume costs sqrt(m) per removed vertex and the choice of those vertices
is accounted for by the binomial coefficient. -/
theorem tendsto_cluster_binomial_tail {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun m : ℕ => ∑ r ∈ Icc 1 m,
      (m.choose r : ℝ) *
        (C * Real.sqrt (m : ℝ) * q ^ (m / 16 - 2)) ^ r)
      atTop (𝓝 0) := by
  apply tendsto_binomial_outlier_sum
    (Eventually.of_forall fun m => mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))
      (pow_nonneg hq.le _))
  have hlim := (tendsto_nat_pow_mul_floor_pow hq hq1 2 16 2 (by norm_num)).const_mul C
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun m => by positivity) _ hlim
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsqrt : Real.sqrt (m : ℝ) ≤ m :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
  have hpow : 0 ≤ q ^ (m / 16 - 2) := pow_nonneg hq.le _
  calc
    _ = C * ((m : ℝ) * Real.sqrt (m : ℝ)) * q ^ (m / 16 - 2) := by ring
    _ ≤ C * ((m : ℝ) * m) * q ^ (m / 16 - 2) := by gcongr
    _ = _ := by ring

/-- The constants in the circle decomposition are fixed rather than
dimension-dependent; a final factor of sixteen, or any other fixed
nonnegative factor, therefore preserves the vanishing tail. -/
theorem tendsto_actual_circle_cluster_tail (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun m : ℕ => ∑ r ∈ Icc 1 m,
      (m.choose r : ℝ) *
        (C * Real.sqrt (m : ℝ) * circleSeparationRatio ^ (m / 16 - 2)) ^ r)
      atTop (𝓝 0) :=
  tendsto_cluster_binomial_tail circleSeparationRatio_pos circleSeparationRatio_lt_one C hC

end
end Wormald
