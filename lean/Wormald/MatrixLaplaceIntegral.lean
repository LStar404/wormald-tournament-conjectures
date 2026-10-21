import Wormald.QuadraticPeakIntegral
import Wormald.QuadraticRemainderBound
import Wormald.GaussianNormBound

/-! A local Laplace theorem with the exact determinant constant, deduced
from a positive actual quadratic Taylor term rather than from a limit premise. -/

namespace Wormald
noncomputable section
open Matrix MeasureTheory Filter Topology
open scoped BigOperators

def matrixHalfQuadratic {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (x : Fin k → ℝ) : ℝ := (x ⬝ᵥ (S *ᵥ x)) / 2

theorem continuous_matrixHalfQuadratic {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) :
    Continuous (matrixHalfQuadratic S) := by
  unfold matrixHalfQuadratic Matrix.mulVec dotProduct
  fun_prop

theorem matrixHalfQuadratic_smul {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (a : ℝ) (x : Fin k → ℝ) :
    matrixHalfQuadratic S (a • x) = a ^ 2 * matrixHalfQuadratic S x := by
  simp only [matrixHalfQuadratic, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  ring

theorem matrixHalfQuadratic_pos {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ)
    (hS : S.PosDef) (x : Fin k → ℝ) (hx : x ≠ 0) :
    0 < matrixHalfQuadratic S x := by
  have h := hS.dotProduct_mulVec_pos hx
  simpa only [matrixHalfQuadratic, star_trivial, div_pos_iff_of_pos_right (by norm_num :
    (0 : ℝ) < 2)] using h

theorem integral_cexp_neg_matrixHalfQuadratic {k : ℕ}
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.PosDef) :
    (∫ x : Fin k → ℝ, Complex.exp (-(matrixHalfQuadratic S x : ℂ))) =
      (Real.sqrt (2 * Real.pi) ^ k / Real.sqrt S.det : ℝ) := by
  have hfun : (fun x : Fin k → ℝ => Complex.exp (-(matrixHalfQuadratic S x : ℂ))) =
      (fun x => (matrixGaussian S x : ℂ)) := by
    funext x
    simp only [matrixHalfQuadratic, matrixGaussian, ← Complex.ofReal_neg,
      ← Complex.ofReal_exp]
    congr 2
    ring
  rw [hfun, integral_complex_ofReal, integral_matrixGaussian S hS]

/-- Positive quadratic Taylor data imply a local complex Laplace limit on
every sufficiently small ball. No integral limit is among the hypotheses. -/
theorem exists_matrixLaplace_radius {k : ℕ} (hk : 0 < k)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.PosDef)
    (phase : (Fin k → ℝ) → ℂ) (r : ℝ) (hr : 0 < r)
    (hphase : ContinuousOn phase {x | ‖x‖ < r})
    (hsmall : (fun x => phase x + (matrixHalfQuadratic S x : ℂ)) =o[𝓝 0]
      (fun x => ((‖x‖ ^ 2 : ℝ) : ℂ))) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      Tendsto (fun m : ℕ => Real.sqrt (m : ℝ) ^ k •
        ∫ x : Fin k → ℝ, localComplexPeak phase δ m x) atTop
          (𝓝 ((Real.sqrt (2 * Real.pi) ^ k / Real.sqrt S.det : ℝ) : ℂ)) := by
  obtain ⟨a, ha, hlower⟩ := exists_pos_mul_norm_sq_le (matrixHalfQuadratic S)
    (continuous_matrixHalfQuadratic S) (matrixHalfQuadratic_smul S)
    (matrixHalfQuadratic_pos S hS)
  obtain ⟨err, herr, heq⟩ := exists_quadratic_phase_error phase (matrixHalfQuadratic S) hsmall
  have hdecay := eventually_re_le_neg_norm_sq phase (matrixHalfQuadratic S) err
    a ha hlower herr heq
  obtain ⟨ε, hε, hεbound⟩ := Metric.mem_nhds_iff.mp hdecay
  refine ⟨min r ε, lt_min hr hε, ?_⟩
  intro δ hδ hδsmall
  have hδr : δ ≤ r := hδsmall.trans (min_le_left _ _)
  have hδε : δ ≤ ε := hδsmall.trans (min_le_right _ _)
  have hcont : ContinuousOn phase {x | ‖x‖ < δ} := hphase.mono fun x hx =>
    hx.trans_le hδr
  have hbound : ∀ x, ‖x‖ < δ → (phase x).re ≤ -(a / 2) * ‖x‖ ^ 2 := by
    intro x hx
    apply hεbound
    simpa only [Metric.mem_ball, dist_zero_right] using hx.trans_le hδε
  have hlim := tendsto_localComplexPeak_integral phase (matrixHalfQuadratic S)
    δ (a / 2) hδ hcont
    (tendsto_nat_mul_phase_invSqrt_of_isLittleO phase (matrixHalfQuadratic S)
      (matrixHalfQuadratic_smul S) hsmall)
    hbound (integrable_exp_neg_norm_sq_pi hk (half_pos ha))
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    integral_cexp_neg_matrixHalfQuadratic S hS] using hlim

end
end Wormald
