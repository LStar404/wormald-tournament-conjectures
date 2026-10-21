import Wormald.FiniteWeightedChernoff

namespace Wormald

noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

def finiteWeightedAverage {Ω : Type*} [Fintype Ω] (w F : Ω → ℝ) : ℝ :=
  (∑ ω, w ω * F ω) / ∑ ω, w ω

theorem finiteWeightedAverage_error_le {Ω : Type*} [Fintype Ω]
    (w F : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hW : 0 < ∑ ω, w ω)
    (c η B : ℝ) (hη : 0 ≤ η) (bad : Ω → Prop)
    (hgood : ∀ ω, ¬bad ω → |F ω - c| ≤ η) (hall : ∀ ω, |F ω - c| ≤ B) :
    |finiteWeightedAverage w F - c| ≤
      η + B * ((∑ ω, if bad ω then w ω else 0) / ∑ ω, w ω) := by
  have heq : finiteWeightedAverage w F - c =
      (∑ ω, w ω * (F ω - c)) / ∑ ω, w ω := by
    unfold finiteWeightedAverage
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    field_simp [hW.ne']
  have hnum : |∑ ω, w ω * (F ω - c)| ≤
      η * (∑ ω, w ω) + B * ∑ ω, if bad ω then w ω else 0 := by
    calc
      _ ≤ ∑ ω, |w ω * (F ω - c)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ ω, w ω * |F ω - c| := by simp only [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ ∑ ω, (η * w ω + B * (if bad ω then w ω else 0)) := by
        apply Finset.sum_le_sum
        intro ω _
        by_cases h : bad ω
        · rw [ite_eq_left h]
          have hh := mul_le_mul_of_nonneg_left (hall ω) (hw ω)
          have h0 := mul_nonneg hη (hw ω)
          nlinarith
        · rw [ite_eq_right h]
          have hh := mul_le_mul_of_nonneg_left (hgood ω h) (hw ω)
          nlinarith
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [heq, abs_div, abs_of_pos hW]
  apply (div_le_div_of_nonneg_right hnum hW.le).trans_eq
  field_simp [hW.ne']

/-- Bounded continuous observables converge under finite weighted
concentration, even when the finite sample space changes with the index. -/
theorem tendsto_finiteWeightedAverage_of_concentration
    {Ω : ℕ → Type*} [∀ m, Fintype (Ω m)] (w X : (m : ℕ) → Ω m → ℝ)
    (c : ℝ) (φ : ℝ → ℝ) (B : ℝ)
    (hw : ∀ m ω, 0 ≤ w m ω) (hW : ∀ᶠ m in atTop, 0 < ∑ ω, w m ω)
    (hbound : ∀ᶠ m in atTop, ∀ ω, |φ (X m ω) - φ c| ≤ B)
    (hφ : ContinuousAt φ c)
    (hconcentration : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun m : ℕ => finiteAbsTailMass (w m) (fun ω => X m ω - c) δ / ∑ ω, w m ω)
        atTop (𝓝 0)) :
    Tendsto (fun m : ℕ => finiteWeightedAverage (w m) (fun ω => φ (X m ω))) atTop (𝓝 (φ c)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hφ (ε / 2) (by linarith)
  have hlim := (hconcentration δ hδ).const_mul B
  simp only [mul_zero] at hlim
  have hsmall : ∀ᶠ m : ℕ in atTop,
      B * (finiteAbsTailMass (w m) (fun ω => X m ω - c) δ / ∑ ω, w m ω) < ε / 2 :=
    hlim.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε / 2))
  filter_upwards [hW, hbound, hsmall] with m hmW hmB hmSmall
  have hgood (ω : Ω m) (hω : ¬δ ≤ |X m ω - c|) : |φ (X m ω) - φ c| ≤ ε / 2 := by
    have hh : dist (X m ω) c < δ := by simpa only [Real.dist_eq] using lt_of_not_ge hω
    simpa only [Real.dist_eq] using (hclose hh).le
  have hh := finiteWeightedAverage_error_le (w m) (fun ω => φ (X m ω)) (hw m) hmW
    (φ c) (ε / 2) B (by linarith) (fun ω => δ ≤ |X m ω - c|) hgood hmB
  change |finiteWeightedAverage (w m) (fun ω => φ (X m ω)) - φ c| < ε
  change _ ≤ ε / 2 + B * (finiteAbsTailMass (w m) (fun ω => X m ω - c) δ / ∑ ω, w m ω) at hh
  linarith

end
end Wormald
