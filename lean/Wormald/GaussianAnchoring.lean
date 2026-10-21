import Wormald.GaussianProductDensity
import Wormald.CompleteGaussianQuotient
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact removal of the common Gaussian translation coordinate. The map
to anchored differences is treated by an actual Lebesgue change of variables. -/

namespace Wormald
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators

def anchorShear (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) where
  toFun x := Fin.snoc (fun j => x j.castSucc + x (Fin.last n)) (x (Fin.last n))
  invFun x := Fin.snoc (fun j => x j.castSucc - x (Fin.last n)) (x (Fin.last n))
  left_inv x := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv x := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  measurable_toFun := by
    change Measurable (fun x : Fin (n + 1) → ℝ =>
      Fin.snoc (α := fun _ => ℝ) (fun j => x j.castSucc + x (Fin.last n)) (x (Fin.last n)))
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc] <;> fun_prop
  measurable_invFun := by
    change Measurable (fun x : Fin (n + 1) → ℝ =>
      Fin.snoc (α := fun _ => ℝ) (fun j => x j.castSucc - x (Fin.last n)) (x (Fin.last n)))
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc] <;> fun_prop

def anchorShearMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  1 + Matrix.vecMulVec (Fin.snoc (fun _ => 1) 0) (Pi.single (Fin.last n) 1)

theorem det_anchorShearMatrix (n : ℕ) : (anchorShearMatrix n).det = 1 := by
  rw [anchorShearMatrix, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp

theorem anchorShearMatrix_mulVec (n : ℕ) (x : Fin (n + 1) → ℝ) :
    anchorShearMatrix n *ᵥ x = anchorShear n x := by
  rw [anchorShearMatrix, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [anchorShear]

theorem measurePreserving_anchorShear (n : ℕ) : MeasurePreserving (anchorShear n) := by
  refine ⟨(anchorShear n).measurable, ?_⟩
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (show (anchorShearMatrix n).det ≠ 0 by rw [det_anchorShearMatrix]; norm_num)
  have hfun : (Matrix.toLin' (anchorShearMatrix n) : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) =
      anchorShear n := funext (anchorShearMatrix_mulVec n)
  rw [hfun, det_anchorShearMatrix] at hmap
  simpa using hmap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_anchorShear_split {n : ℕ} (H : (Fin (n + 1) → ℝ) → E)
    (hH : Integrable H) :
    (∫ x, H x) = ∫ y : Fin n → ℝ, ∫ t : ℝ,
      H (Fin.snoc (fun j => y j + t) t) := by
  have hp := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have hs : Integrable (H ∘ anchorShear n) :=
    (measurePreserving_anchorShear n).integrable_comp_of_integrable hH
  have hi := hp.integrable_comp_of_integrable hs
  rw [← (measurePreserving_anchorShear n).integral_comp' H]
  change (∫ x, (H ∘ anchorShear n) x) = _
  rw [← hp.integral_comp' (H ∘ anchorShear n)]
  change (∫ z : ℝ × (Fin n → ℝ), ((H ∘ anchorShear n) ∘
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm) z
      ∂(volume.prod volume)) = _
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_last', anchorShear]
      congr 1
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

end
end Wormald
