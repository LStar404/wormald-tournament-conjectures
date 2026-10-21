import Wormald.AnalyticJetBridge
import Wormald.CriticalGradient
import Wormald.ConjectureSixReduction
import Wormald.SpectralConstant

/-!
# Wormald's original Conjecture 6

The theorem below starts with the original determinant, explicitly eliminated
function and actual real angular Fréchet Hessian. The analytic correspondence
is proved, rather than passed as a hypothesis. No counting asymptotic theorem
or conjectural spectral comparison is used.
-/

namespace Wormald
noncomputable section
open Matrix

/-- The actual original analytic function has precisely the polynomial jet. -/
theorem Tournament.analyticJetBridge {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) : AnalyticJetBridge T := by
  apply analyticJetBridge_of_critical T
  · exact originalDeterminant_critical T hT
  · exact eliminatedCoefficient_critical_ne_zero T hT
  · intro a
    exact eval_first_pderiv_critical_uniform T hT (Nat.succ_ne_zero n) a (Fin.last n)
  · exact eval_first_pderiv_critical_ne_zero T hT (Nat.succ_ne_zero n) (Fin.last n)

/-- Identification of the original angular Hessian, with no analytic premise. -/
theorem originalAngularHessian_eq_candidate {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) :
    originalAngularHessian T = Complex.ofRealHom.mapMatrix T.candidateHessian := by
  apply Matrix.ext
  intro j k
  rw [T.analyticJetBridge hT j k, angularHessianJet_eq_candidate T hT j k]

/-- The formerly open correspondence is now an unconditional theorem. -/
theorem analyticCandidateCorrespondence : AnalyticCandidateCorrespondence := by
  intro n _ T hT
  exact originalAngularHessian_eq_candidate T hT

/-- Wormald's literal original Conjecture 6, for all regular base tournaments. -/
theorem conjectureSix : ConjectureSix :=
  conjectureSix_of_analytic_correspondence analyticCandidateCorrespondence

/-- The actual analytic determinant has a strictly positive real value. -/
theorem originalAngularHessian_det_positive {n : ℕ} (T : Tournament (n + 1))
    (hT : T.Regular) :
    ∃ h : ℝ, 0 < h ∧ (originalAngularHessian T).det = (h : ℂ) := by
  refine ⟨T.candidateHessian.det, T.candidateHessian_det_pos, ?_⟩
  rw [originalAngularHessian_eq_candidate T hT]
  exact (Complex.ofRealHom.map_det T.candidateHessian).symm

/-- The literal determinant ratio is the positive rational square root in the
original analytic conjecture, strengthening the existence-of-a-square target. -/
theorem originalAngularHessian_positive_rational_root {n : ℕ}
    (T : Tournament (n + 1)) (hT : T.Regular) :
    ∃ q : ℚ, 0 < q ∧ T.spectralRatio = (q : ℂ) ∧
      ((n + 1 : ℕ) : ℂ) / (originalAngularHessian T).det = (q : ℂ) ^ 2 := by
  obtain ⟨q, hq, heq⟩ := T.spectralRatio_positive_rational (Nat.succ_ne_zero n)
  refine ⟨q, hq, heq, ?_⟩
  have hdet : (originalAngularHessian T).det = (T.candidateHessian.det : ℂ) := by
    rw [originalAngularHessian_eq_candidate T hT]
    exact (Complex.ofRealHom.map_det T.candidateHessian).symm
  rw [hdet, ← heq, T.spectralRatio_sq_eq_candidate hT]
  norm_num

#print axioms conjectureSix

end
end Wormald
