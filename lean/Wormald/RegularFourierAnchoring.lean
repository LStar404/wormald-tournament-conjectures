import Wormald.RegularKernelNormalization
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! The exact removal of the common angular translation from the genuine
regular-degree Fourier integral. Periodicity is encoded by the circle domain;
the simultaneous translation invariance follows from its proved centered
formula. Fubini and Haar translation then anchor the final coordinate at zero. -/

namespace Wormald
noncomputable section
open MeasureTheory
open scoped BigOperators Pointwise

local instance regularAnchorCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance regularAnchorCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance regularAnchorCircleAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

theorem integral_torus_eq_anchored_last {n : ℕ} (f : UnitAddTorus (Fin (n + 1)) → ℂ)
    (hf : Continuous f) (hinv : ∀ x c, f (fun i => x i + c) = f x) :
    (∫ x : UnitAddTorus (Fin (n + 1)), f x) =
      ∫ y : UnitAddTorus (Fin n), f (Fin.snoc y 0) := by
  have hsnoc : Continuous (fun p : UnitAddCircle × UnitAddTorus (Fin n) => f (Fin.snoc p.2 p.1)) := by
    apply hf.comp
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using continuous_fst
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (continuous_apply j : Continuous (fun y : UnitAddTorus (Fin n) => y j)).comp
          (continuous_snd : Continuous (fun p : UnitAddCircle × UnitAddTorus (Fin n) => p.2))
  have hints : Integrable (fun p : UnitAddCircle × UnitAddTorus (Fin n) =>
      f (Fin.snoc p.2 p.1)) :=
    hsnoc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hinner (t : UnitAddCircle) :
      (∫ y : UnitAddTorus (Fin n), f (Fin.snoc y t)) =
        ∫ y : UnitAddTorus (Fin n), f (Fin.snoc y 0) := by
    have hpoint (y : UnitAddTorus (Fin n)) :
        f (Fin.snoc y t) = f (Fin.snoc (fun i => y i + -t) 0) := by
      have heq : (fun i => (Fin.snoc y t : Fin (n + 1) → UnitAddCircle) i + -t) =
          Fin.snoc (fun i => y i + -t) 0 := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      simpa only [heq] using (hinv (Fin.snoc y t) (-t)).symm
    calc
      _ = ∫ y : UnitAddTorus (Fin n), f (Fin.snoc (fun i => y i + -t) 0) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = _ := integral_add_right_eq_self (fun y : UnitAddTorus (Fin n) => f (Fin.snoc y 0))
        (fun _ => -t)
  calc
    _ = ∫ p : UnitAddCircle × UnitAddTorus (Fin n), f (Fin.snoc p.2 p.1) := by
      rw [← ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle)
        (Fin.last n)).symm).integral_comp']
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_last]
      rfl
    _ = ∫ t : UnitAddCircle, ∫ y : UnitAddTorus (Fin n), f (Fin.snoc y t) := integral_prod _ hints
    _ = _ := by simp_rw [hinner]; simp

def centeredUnitCube (n : ℕ) : Set (Fin n → ℝ) :=
  {y | ∀ i, y i ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)}

def centeredPiCube (n : ℕ) : Set (Fin n → ℝ) :=
  {θ | ∀ i, θ i ∈ Set.Ioc (-(Real.pi / 2)) (Real.pi / 2)}

theorem pi_smul_centeredUnitCube (n : ℕ) :
    Real.pi • centeredUnitCube n = centeredPiCube n := by
  ext θ
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ Real.pi_ne_zero]
  simp only [centeredUnitCube, centeredPiCube, Set.mem_ofPred_eq, Set.mem_Ioc,
    Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
  constructor
  · intro h i
    have hlo := (lt_div_iff₀ Real.pi_pos).mp (h i).1
    have hhi := (div_le_iff₀ Real.pi_pos).mp (h i).2
    constructor <;> linarith
  · intro h i
    constructor
    · apply (lt_div_iff₀ Real.pi_pos).mpr
      linarith [(h i).1]
    · apply (div_le_iff₀ Real.pi_pos).mpr
      linarith [(h i).2]

/-- The explicit π Jacobian for physical angle coordinates. -/
theorem integral_unitCube_eq_physicalCube {n : ℕ} (f : (Fin n → ℝ) → ℂ) :
    (∫ y in centeredUnitCube n, f y) = (Real.pi ^ n)⁻¹ •
      ∫ θ in centeredPiCube n, f (Real.pi⁻¹ • θ) := by
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Fin n → ℝ))
    (fun θ => f (Real.pi⁻¹ • θ)) (centeredUnitCube n) Real.pi_pos
  simpa only [smul_smul, inv_mul_cancel₀ Real.pi_ne_zero, one_smul,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, pi_smul_centeredUnitCube] using h

namespace FiniteModel

theorem centeredDegreeIntegrand_add_const {m : ℕ} (w : Edge m → Bool → ℚ)
    (x : Fin m → ℝ) (t : ℝ) :
    centeredDegreeIntegrand w (fun i => x i + t) = centeredDegreeIntegrand w x := by
  unfold centeredDegreeIntegrand
  simp only [add_sub_add_right_eq_sub]

theorem degreeFourierIntegrand_add_const {m : ℕ} (w : Edge m → Bool → ℚ)
    (hm : Odd m) (x : UnitAddTorus (Fin m)) (c : UnitAddCircle) :
    degreeFourierIntegrand w (fun i => x i + c) = degreeFourierIntegrand w x := by
  obtain ⟨t, _, rfl⟩ := AddCircle.eq_coe_Ico c
  let y : Fin m → ℝ := fun i => (AddCircle.equivIco 1 0 (x i)).1
  have hy : (fun i => (y i : UnitAddCircle)) = x := by
    funext i
    exact AddCircle.coe_equivIco
  rw [← hy]
  simp only [← QuotientAddGroup.mk_add]
  rw [degreeFourierIntegrand_eq_centered w hm, degreeFourierIntegrand_eq_centered w hm]
  exact centeredDegreeIntegrand_add_const w y t

theorem normalizedRegularTorusIntegrand_add_const {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m)
    (x : UnitAddTorus (Fin m)) (c : UnitAddCircle) :
    normalizedRegularTorusIntegrand D (fun i => x i + c) = normalizedRegularTorusIntegrand D x := by
  unfold normalizedRegularTorusIntegrand
  rw [degreeFourierIntegrand_add_const _ hm]

theorem integral_normalizedRegularTorus_eq_anchored {n : ℕ}
    (D : Finset (Fin (n + 1) × Fin (n + 1))) (hm : Odd (n + 1)) :
    (∫ x : UnitAddTorus (Fin (n + 1)), normalizedRegularTorusIntegrand D x) =
      ∫ y : UnitAddTorus (Fin n), normalizedRegularTorusIntegrand D (Fin.snoc y 0) :=
  integral_torus_eq_anchored_last _ (continuous_normalizedRegularTorusIntegrand D)
    (normalizedRegularTorusIntegrand_add_const D hm)

theorem integral_normalizedRegularTorus_eq_anchored_cube {n : ℕ}
    (D : Finset (Fin (n + 1) × Fin (n + 1))) (hm : Odd (n + 1)) (a : Fin n → ℝ) :
    (∫ x : UnitAddTorus (Fin (n + 1)), normalizedRegularTorusIntegrand D x) =
      ∫ y : Fin n → ℝ in {y | ∀ i, y i ∈ Set.Ioc (a i) (a i + 1)},
        normalizedRegularIntegrand D (Fin.snoc y 0) := by
  rw [integral_normalizedRegularTorus_eq_anchored D hm, UnitAddTorus.integral_preimage _ a]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun (y : Fin n → ℝ) => by
    dsimp only
    have hcoe : Fin.snoc (fun i => (y i : UnitAddCircle)) 0 =
        fun i => (((Fin.snoc y (0 : ℝ) : Fin (n + 1) → ℝ) i) : UnitAddCircle) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    rw [hcoe, normalizedRegularTorusIntegrand_coe D hm]

def normalizedRegularPhysicalIntegrand {m : ℕ} (D : Finset (Fin m × Fin m))
    (θ : Fin m → ℝ) : ℂ := normalizedRegularIntegrand D (fun i => θ i / Real.pi)

/-- The original full-dimensional Haar integral, anchored and expressed in
physical angles θ=πx. Its Jacobian is exactly π^{−(m−1)}. -/
theorem integral_normalizedRegularTorus_eq_physical_anchored {n : ℕ}
    (D : Finset (Fin (n + 1) × Fin (n + 1))) (hm : Odd (n + 1)) :
    (∫ x : UnitAddTorus (Fin (n + 1)), normalizedRegularTorusIntegrand D x) =
      (Real.pi ^ n)⁻¹ • ∫ θ in centeredPiCube n,
        normalizedRegularPhysicalIntegrand D (Fin.snoc θ 0) := by
  rw [integral_normalizedRegularTorus_eq_anchored_cube D hm (fun _ => -(1 / 2 : ℝ))]
  have hcube : {y : Fin n → ℝ | ∀ i, y i ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)} =
      centeredUnitCube n := by norm_num [centeredUnitCube]
  rw [hcube, integral_unitCube_eq_physicalCube]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    dsimp only
    unfold normalizedRegularPhysicalIntegrand
    congr 1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;>
      simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

end FiniteModel
end
end Wormald
