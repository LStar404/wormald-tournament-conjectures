import Wormald.CosineTaylorBounds
import Wormald.GaussianProductTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! An explicit central window for the growing-dimensional Fourier integral.
At this scale all sixth-order cosine errors and all Gaussian tails vanish
uniformly in the prescribed partial permutation. -/

namespace Wormald
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

def centralGaussianRadius (m : ℕ) : ℝ := (m : ℝ) ^ (-3 / 8 : ℝ)

def centralGaussianError (m : ℕ) : ℝ :=
  (m : ℝ) ^ 2 * centralGaussianRadius m ^ 6 +
    2 * m * centralGaussianRadius m ^ 4

def centralGaussianTail (m : ℕ) : ℝ :=
  2 * m * Real.exp (-(m : ℝ) * centralGaussianRadius m ^ 2 / 32)

theorem centralGaussianRadius_nonneg (m : ℕ) : 0 ≤ centralGaussianRadius m :=
  Real.rpow_nonneg (Nat.cast_nonneg m) _

theorem centralGaussianRadius_pos {m : ℕ} (hm : 0 < m) : 0 < centralGaussianRadius m :=
  Real.rpow_pos_of_pos (by exact_mod_cast hm) _

theorem centralGaussianRadius_le_one {m : ℕ} (hm : 1 ≤ m) : centralGaussianRadius m ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by norm_num)

theorem eventually_centralGaussianRadius_le_one :
    ∀ᶠ m in atTop, centralGaussianRadius m ≤ 1 :=
  (eventually_ge_atTop 1).mono fun _ hm => centralGaussianRadius_le_one hm

theorem centralGaussianRadius_pow (m k : ℕ) :
    centralGaussianRadius m ^ k = (m : ℝ) ^ ((-3 / 8 : ℝ) * k) :=
  (Real.rpow_mul_natCast (Nat.cast_nonneg m) (-3 / 8) k).symm

theorem centralGaussianError_eq {m : ℕ} (hm : 0 < m) :
    centralGaussianError m = (m : ℝ) ^ (-1 / 4 : ℝ) + 2 * (m : ℝ) ^ (-1 / 2 : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h6 : (m : ℝ) ^ 2 * centralGaussianRadius m ^ 6 = (m : ℝ) ^ (-1 / 4 : ℝ) := by
    rw [centralGaussianRadius_pow, ← Real.rpow_natCast, ← Real.rpow_add hmR]
    norm_num
  have h4 : (m : ℝ) * centralGaussianRadius m ^ 4 = (m : ℝ) ^ (-1 / 2 : ℝ) := by
    rw [centralGaussianRadius_pow]
    calc
      _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ ((-3 / 8 : ℝ) * 4) := by norm_num
      _ = _ := by rw [← Real.rpow_add hmR]; norm_num
  rw [centralGaussianError, h6, mul_assoc, h4]

theorem tendsto_centralGaussianError :
    Tendsto centralGaussianError atTop (𝓝 0) := by
  have h1 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h2 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := h1.add (h2.const_mul 2)
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  simpa only [Function.comp_apply, neg_div] using
    (centralGaussianError_eq (show 0 < m by omega)).symm

theorem centralGaussianRadius_square_scale {m : ℕ} (hm : 0 < m) :
    (m : ℝ) * centralGaussianRadius m ^ 2 = (m : ℝ) ^ (1 / 4 : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [centralGaussianRadius_pow]
  calc
    _ = (m : ℝ) ^ (1 : ℝ) * (m : ℝ) ^ ((-3 / 8 : ℝ) * 2) := by norm_num
    _ = _ := by rw [← Real.rpow_add hmR]; norm_num

theorem tendsto_centralGaussianTail : Tendsto centralGaussianTail atTop (𝓝 0) := by
  have ht : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 (1 / 32)
    (by norm_num)).comp ht).const_mul 2
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpow : ((m : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = m := by
    rw [← Real.rpow_mul hmR.le]
    norm_num
  change 2 * (((m : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) *
    Real.exp (-(1 / 32) * (m : ℝ) ^ (1 / 4 : ℝ))) = centralGaussianTail m
  rw [hpow, centralGaussianTail]
  have he : -(m : ℝ) * centralGaussianRadius m ^ 2 / 32 =
      -(1 / 32) * (m : ℝ) ^ (1 / 4 : ℝ) := by
    rw [neg_mul, centralGaussianRadius_square_scale (show 0 < m by omega)]
    ring
  rw [he]
  ring

/-- The local Taylor bound uses only the actual edge cardinalities. -/
theorem centralGaussian_card_error_le (m a b : ℕ) (ha : a ≤ m ^ 2) (hb : b ≤ m) :
    (a : ℝ) * centralGaussianRadius m ^ 6 +
      2 * b * centralGaussianRadius m ^ 4 ≤ centralGaussianError m := by
  have haR : (a : ℝ) ≤ (m : ℝ) ^ 2 := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ m := by exact_mod_cast hb
  unfold centralGaussianError
  gcongr

/-- Using half the stated radius for the anchored coordinates ensures
that all pairwise angular differences lie within the stated radius. -/
theorem centralGaussian_pair_difference_le {m : ℕ} (j : Fin m) (x : Fin m → ℝ)
    (hx : ∀ i, |x i - x j| ≤ centralGaussianRadius m / 2) (u v : Fin m) :
    |x u - x v| ≤ centralGaussianRadius m := by
  calc
    _ = |(x u - x j) - (x v - x j)| := by congr 1; ring
    _ ≤ |x u - x j| + |x v - x j| := abs_sub _ _
    _ ≤ centralGaussianRadius m := by linarith [hx u, hx v]

theorem finiteGaussian_central_outside_le {m : ℕ} (j : Fin m) :
    (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).real
      {x | ∃ i : Fin m, Real.sqrt (m : ℝ) * (centralGaussianRadius m / 2) ≤
        |x i - x j|} ≤ centralGaussianTail m := by
  have h := finiteGaussian_scaled_anchor_tail_le j (centralGaussianRadius m / 2)
    (by positivity [centralGaussianRadius_nonneg m])
  convert h using 1
  unfold centralGaussianTail
  congr 2
  ring

end
end Wormald
