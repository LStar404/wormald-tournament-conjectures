import Wormald.AnchoredRealFourier

namespace Wormald

noncomputable section
open Matrix MeasureTheory Filter
open scoped Topology BigOperators

def complexFrobeniusSq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

theorem complexFrobeniusSq_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ complexFrobeniusSq M :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg (M i j)))

theorem continuous_complexFrobeniusSq (n : ℕ) : Continuous (@complexFrobeniusSq n) := by
  unfold complexFrobeniusSq
  fun_prop

theorem complex_mulVec_energy_le_frobenius {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (x : Fin n → ℂ) : complexEnergy (M *ᵥ x) ≤ complexFrobeniusSq M * complexEnergy x := by
  have hrow (i : Fin n) : ‖∑ j, M i j * x j‖ ^ 2 ≤
      (∑ j, ‖M i j‖ ^ 2) * (∑ j, ‖x j‖ ^ 2) := by
    have hnorm := norm_sum_le Finset.univ (fun j => M i j * x j)
    simp only [norm_mul] at hnorm
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖M i j‖) (fun j => ‖x j‖))
  calc
    _ = ∑ i, ‖∑ j, M i j * x j‖ ^ 2 := by
      simp only [complexEnergy, Complex.normSq_eq_norm_sq, Matrix.mulVec, dotProduct]
    _ ≤ ∑ i, (∑ j, ‖M i j‖ ^ 2) * (∑ j, ‖x j‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by
      simp only [complexFrobeniusSq, complexEnergy, Complex.normSq_eq_norm_sq, Finset.sum_mul]

theorem Tournament.complexNormalizedSign_frobenius_lt_one {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) : complexFrobeniusSq T.complexNormalizedSign < 1 := by
  have hentry (i j : Fin n) : Complex.normSq (T.complexNormalizedSign i j) = T.realNormalizedSign i j ^ 2 := by
    change Complex.normSq (T.normalizedSign i j : ℂ) = (T.normalizedSign i j : ℝ) ^ 2
    rw [Complex.normSq_ratCast]
    ring
  simpa only [complexFrobeniusSq, hentry] using T.realNormalizedSign_energy_lt_one hn

theorem matrix_power_energy_le_of_one_step {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hM : ∀ x, complexEnergy (M *ᵥ x) ≤ r * complexEnergy x)
    (N : ℕ) (x : Fin n → ℂ) : complexEnergy (M ^ N *ᵥ x) ≤ r ^ N * complexEnergy x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    exact (hM _).trans ((mul_le_mul_of_nonneg_left ih hr).trans_eq (by rw [pow_succ']; ring))

theorem matrix_power_trace_norm_le_of_one_step {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hM : ∀ x, complexEnergy (M *ᵥ x) ≤ r * complexEnergy x)
    (N : ℕ) : ‖(M ^ N).trace‖ ≤ (n : ℝ) * Real.sqrt r ^ N := by
  have hdiag (j : Fin n) : ‖(M ^ N) j j‖ ≤ Real.sqrt r ^ N := by
    have hcol := matrix_power_energy_le_of_one_step M r hr hM N (Pi.single j 1)
    have hbasis : complexEnergy (Pi.single j (1 : ℂ)) = 1 := by simp [complexEnergy, Pi.single_apply]
    rw [Matrix.mulVec_single_one, hbasis, mul_one] at hcol
    have hj : Complex.normSq ((M ^ N) j j) ≤ complexEnergy ((M ^ N).col j) :=
      Finset.single_le_sum (fun i _ => Complex.normSq_nonneg ((M ^ N) i j)) (Finset.mem_univ j)
    have hsq := hj.trans hcol
    rw [Complex.normSq_eq_norm_sq] at hsq
    have hsqrt : (Real.sqrt r ^ N) ^ 2 = r ^ N := by rw [pow_right_comm, Real.sq_sqrt hr]
    nlinarith [norm_nonneg ((M ^ N) j j), pow_nonneg (Real.sqrt_nonneg r) N]
  calc
    _ = ‖∑ j, (M ^ N) j j‖ := rfl
    _ ≤ ∑ j, ‖(M ^ N) j j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, Real.sqrt r ^ N := Finset.sum_le_sum (fun j _ => hdiag j)
    _ = _ := by simp [nsmul_eq_mul]

/-- Continuity and an actual center Frobenius bound give a common local
power-trace decay rate. There is no eigenvalue-continuity assumption. -/
theorem exists_local_residual_power_trace_decay {E : Type*} [NormedAddCommGroup E]
    {n : ℕ} (R : E → Matrix (Fin n) (Fin n) ℂ)
    (hR : ContinuousAt R 0) (hcenter : complexFrobeniusSq (R 0) < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ θ : E, ‖θ‖ < δ → ∀ N : ℕ,
      ‖(R θ ^ N).trace‖ ≤ (n : ℝ) * q ^ N := by
  let r := (complexFrobeniusSq (R 0) + 1) / 2
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [complexFrobeniusSq_nonneg (R 0)]
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hmid : complexFrobeniusSq (R 0) < r := by dsimp [r]; linarith
  have hcont := (continuous_complexFrobeniusSq n).continuousAt.comp hR
  have hevent : ∀ᶠ θ in 𝓝 (0 : E), complexFrobeniusSq (R θ) < r :=
    hcont.tendsto.eventually (eventually_lt_nhds hmid)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hq1 : Real.sqrt r < 1 := by nlinarith [Real.sq_sqrt hr0, Real.sqrt_nonneg r]
  refine ⟨δ, hδ, Real.sqrt r, Real.sqrt_nonneg r, hq1, ?_⟩
  intro θ hθ N
  apply matrix_power_trace_norm_le_of_one_step _ r hr0 _ N
  intro x
  exact (complex_mulVec_energy_le_frobenius _ x).trans
    (mul_le_mul_of_nonneg_right (hball (by simpa only [Metric.mem_ball, dist_zero_right] using hθ)).le
      (complexEnergy_nonneg x))

theorem Tournament.exists_residual_family_power_trace_decay {E : Type*} [NormedAddCommGroup E]
    {n : ℕ} (T : Tournament n) (hn : n ≠ 0) (R : E → Matrix (Fin n) (Fin n) ℂ)
    (hR : ContinuousAt R 0) (hzero : R 0 = T.complexNormalizedSign) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ θ : E, ‖θ‖ < δ → ∀ N : ℕ,
      ‖(R θ ^ N).trace‖ ≤ (n : ℝ) * q ^ N := by
  apply exists_local_residual_power_trace_decay R hR
  rw [hzero]
  exact T.complexNormalizedSign_frobenius_lt_one hn

/-- A uniform finite-dimensional power bound controls every bounded Fourier
weight. Polynomial Gaussian normalization is dominated by geometric decay. -/
theorem residual_integral_sqrt_normalized_tendsto_zero_of_trace_bound
    {d n : ℕ} (R : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (S : Set (Fin d → ℝ)) (hfinite : volume S < ⊤)
    (w : ℕ → (Fin d → ℝ) → ℂ) (hw : ∀ m t, t ∈ S → ‖w m t‖ ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (htrace : ∀ t ∈ S, ∀ N : ℕ, ‖(R t ^ N).trace‖ ≤ (n : ℝ) * q ^ N)
    (D : ℕ) (hD : 1 ≤ D) (k : ℕ) :
    Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ) : ℂ) ^ k *
      ∫ t in S, w m t * (R t ^ (D * m)).trace) atTop (𝓝 0) := by
  let C : ℝ := (n : ℝ) * volume.real S
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg
  have hnorm (m : ℕ) : ‖∫ t in S, w m t * (R t ^ (D * m)).trace‖ ≤ C * q ^ m := by
    have hpower : q ^ (D * m) ≤ q ^ m :=
      pow_le_pow_of_le_one hq0 hq1.le (by simpa using Nat.mul_le_mul_right m hD)
    have hpoint (t : Fin d → ℝ) (ht : t ∈ S) :
        ‖w m t * (R t ^ (D * m)).trace‖ ≤ (n : ℝ) * q ^ m := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hw m t ht)).trans
        ((htrace t ht _).trans (mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg _)))
    have hb := norm_setIntegral_le_of_norm_le_const_ae' hfinite
      (Filter.Eventually.of_forall hpoint)
    convert hb using 1
    dsimp [C]
    ring
  have hlim : Tendsto (fun m : ℕ => C * ((m : ℝ) ^ k * q ^ m)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_const_mul_const_pow_of_lt_one k hq0 hq1)
  have hweighted : Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ)) ^ k *
      ‖∫ t in S, w m t * (R t ^ (D * m)).trace‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun m =>
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _))) _ hlim
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hsqrt : Real.sqrt (m : ℝ) ≤ m := Real.sqrt_le_self_iff.mpr (Or.inr hmR)
    have hsqrtpow := pow_le_pow_left₀ (Real.sqrt_nonneg (m : ℝ)) hsqrt k
    calc
      _ ≤ (Real.sqrt (m : ℝ)) ^ k * (C * q ^ m) :=
        mul_le_mul_of_nonneg_left (hnorm m) (pow_nonneg (Real.sqrt_nonneg _) _)
      _ ≤ (m : ℝ) ^ k * (C * q ^ m) :=
        mul_le_mul_of_nonneg_right hsqrtpow (mul_nonneg hC (pow_nonneg hq0 _))
      _ = _ := by ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using hweighted

/-- Continuity at the center and its strict Frobenius energy bound suffice for
all local residual Fourier integrals to vanish after Gaussian normalization. -/
theorem exists_local_residual_integral_decay {d n : ℕ}
    (R : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ)
    (hR : ContinuousAt R 0) (hcenter : complexFrobeniusSq (R 0) < 1)
    (w : ℕ → (Fin d → ℝ) → ℂ) (hw : ∀ m t, ‖w m t‖ ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, 0 < a → a ≤ δ → ∀ D : ℕ, 1 ≤ D → ∀ k : ℕ,
      Tendsto (fun m : ℕ => (Real.sqrt (m : ℝ) : ℂ) ^ k *
        ∫ t in Metric.ball 0 a, w m t * (R t ^ (D * m)).trace) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, q, hq0, hq1, htrace⟩ := exists_local_residual_power_trace_decay R hR hcenter
  refine ⟨δ, hδ, ?_⟩
  intro a ha haδ D hD k
  apply residual_integral_sqrt_normalized_tendsto_zero_of_trace_bound R
    (Metric.ball 0 a) ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : Fin d → ℝ) a).measure_lt_top) w (fun m t _ => hw m t)
      q hq0 hq1 _ D hD k
  intro t ht N
  apply htrace t _ N
  exact (by simpa only [Metric.mem_ball, dist_zero_right] using ht : ‖t‖ < a).trans_le haδ

end
end Wormald
