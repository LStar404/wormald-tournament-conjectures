import Wormald.RegularForestCosine
import Wormald.CircleCosineKernel

/-! Exact normalization of the true regular containment Fourier integral.
Each prescribed edge removes one factor two. The remaining normalized
integrand is bounded by the circle cosine product used in the tail proof. -/

namespace Wormald.FiniteModel
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def forcedUnorderedEdges {m : ℕ} (D : Finset (Fin m × Fin m)) : Finset (Edge m) :=
  Finset.univ.filter (fun e => (e.1.1, e.1.2) ∈ D ∨ (e.1.2, e.1.1) ∈ D)

private theorem prescribed_ne {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) (p : {p // p ∈ D}) : p.1.1 ≠ p.1.2 := by
  intro h
  have hp : (p.1.1, p.1.2) ∈ D := p.2
  have hr : (p.1.2, p.1.1) ∈ D := by simpa only [h] using hp
  exact hD _ _ hp hr

private def prescribedToEdge {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) (p : {p // p ∈ D}) : Edge m :=
  canonicalEdge p.1.1 p.1.2 (prescribed_ne D hD p)

private theorem prescribedToEdge_injective {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) : Function.Injective (prescribedToEdge D hD) := by
  intro p q h
  have hv := congrArg Subtype.val h
  unfold prescribedToEdge canonicalEdge at hv
  split_ifs at hv <;> simp only [Prod.mk.injEq] at hv
  · exact Subtype.ext (Prod.ext hv.1 hv.2)
  · exact False.elim (hD _ _ p.2 (by simpa only [hv.1, hv.2] using q.2))
  · exact False.elim (hD _ _ p.2 (by simpa only [hv.1, hv.2] using q.2))
  · exact Subtype.ext (Prod.ext hv.2 hv.1)

theorem forcedUnorderedEdges_card {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) : (forcedUnorderedEdges D).card = D.card := by
  have himage : D.attach.image (prescribedToEdge D hD) = forcedUnorderedEdges D := by
    ext e
    constructor
    · intro he
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp he
      have hpair := canonicalEdge_pair p.1.1 p.1.2 (prescribed_ne D hD p)
      change (prescribedToEdge D hD p).1 = p.1 ∨
        (prescribedToEdge D hD p).1 = (p.1.2, p.1.1) at hpair
      rw [hp] at hpair
      simp only [forcedUnorderedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hpair with h | h
      · exact Or.inl (by change e.1 ∈ D; rw [h]; exact p.2)
      · exact Or.inr (by rw [h]; exact p.2)
    · intro he
      rcases (Finset.mem_filter.mp he).2 with hf | hr
      · let p : {p // p ∈ D} := ⟨(e.1.1, e.1.2), hf⟩
        refine Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, ?_⟩
        simp only [prescribedToEdge, p, canonicalEdge, dite_eq_left e.2]
      · let p : {p // p ∈ D} := ⟨(e.1.2, e.1.1), hr⟩
        refine Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, ?_⟩
        simp only [prescribedToEdge, p, canonicalEdge, dite_eq_right (not_lt_of_gt e.2)]
  rw [← himage, Finset.card_image_of_injective _ (prescribedToEdge_injective D hD), Finset.card_attach]

theorem freeCosineEdges_card_add {m : ℕ} (D : Finset (Fin m × Fin m))
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) :
    (freeCosineEdges D).card + D.card = Fintype.card (Edge m) := by
  have hcompl : (freeCosineEdges D)ᶜ = forcedUnorderedEdges D := by
    ext e
    simp only [Finset.mem_compl, freeCosineEdges, forcedUnorderedEdges,
      Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not]
  simpa only [hcompl, forcedUnorderedEdges_card D hD] using Finset.card_add_card_compl (freeCosineEdges D)

def normalizedForestCosineFactor {m : ℕ} (D : Finset (Fin m × Fin m))
    (x : Fin m → ℝ) (e : Edge m) : ℂ :=
  if e ∈ freeCosineEdges D then (Real.cos (Real.pi * (x e.1.1 - x e.1.2)) : ℂ)
  else forestCosineEdgeFactor D x e

def normalizedRegularIntegrand {m : ℕ} (D : Finset (Fin m × Fin m)) (x : Fin m → ℝ) : ℂ :=
  ∏ e : Edge m, normalizedForestCosineFactor D x e

theorem forestCosineProduct_eq_normalized {m : ℕ} (D : Finset (Fin m × Fin m))
    (x : Fin m → ℝ) :
    (∏ e : Edge m, forestCosineEdgeFactor D x e) =
      (2 : ℂ) ^ (freeCosineEdges D).card * normalizedRegularIntegrand D x := by
  have hfactor (e : Edge m) : forestCosineEdgeFactor D x e =
      (if e ∈ freeCosineEdges D then (2 : ℂ) else 1) * normalizedForestCosineFactor D x e := by
    by_cases he : e ∈ freeCosineEdges D
    · have hd := (Finset.mem_filter.mp he).2
      simp only [normalizedForestCosineFactor, ite_eq_left he, forestCosineEdgeFactor,
        ite_eq_right hd.1, ite_eq_right hd.2]
    · simp only [normalizedForestCosineFactor, ite_eq_right he, one_mul]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter]
  simp

theorem norm_normalizedForestCosineFactor_le {m : ℕ} (D : Finset (Fin m × Fin m))
    (x : Fin m → ℝ) (e : Edge m) :
    ‖normalizedForestCosineFactor D x e‖ ≤
      if e ∈ freeCosineEdges D then circleCosineKernel (x e.1.1 : UnitAddCircle) (x e.1.2 : UnitAddCircle)
      else 1 := by
  by_cases he : e ∈ freeCosineEdges D
  · simp only [normalizedForestCosineFactor, ite_eq_left he, Complex.norm_real, Real.norm_eq_abs,
      abs_cos_pi_sub_eq_circleKernel, le_refl]
  · simp only [normalizedForestCosineFactor, ite_eq_right he]
    unfold forestCosineEdgeFactor
    split
    · split
      · simp
      · simp [Complex.norm_exp]
    · rename_i hf
      have hr : (e.1.2, e.1.1) ∈ D := by
        by_contra hr
        exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf, hr⟩)
      simp only [ite_eq_left hr, Complex.norm_exp]
      simp

theorem norm_normalizedRegularIntegrand_le {m : ℕ} (D : Finset (Fin m × Fin m))
    (x : Fin m → ℝ) :
    ‖normalizedRegularIntegrand D x‖ ≤ ∏ e ∈ freeCosineEdges D,
      circleCosineKernel (x e.1.1 : UnitAddCircle) (x e.1.2 : UnitAddCircle) := by
  unfold normalizedRegularIntegrand
  rw [norm_prod]
  calc
    _ ≤ ∏ e : Edge m, if e ∈ freeCosineEdges D then
        circleCosineKernel (x e.1.1 : UnitAddCircle) (x e.1.2 : UnitAddCircle) else 1 :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun e _ => norm_normalizedForestCosineFactor_le D x e)
    _ = _ := by rw [← Finset.prod_filter]; simp

theorem regularContainmentProbability_eq_normalized_cube_ratio {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m)
    (hD : ∀ u v, (u, v) ∈ D → (v, u) ∉ D) (a : Fin m → ℝ) :
    (regularContainmentProbability D hm : ℂ) = ((2 : ℂ) ^ D.card)⁻¹ *
      ((∫ x : Fin m → ℝ in {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)}, normalizedRegularIntegrand D x) /
        (∫ x : Fin m → ℝ in {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
          ∏ e : Edge m, (Real.cos (Real.pi * (x e.1.1 - x e.1.2)) : ℂ))) := by
  have hloop : ∀ i, (i, i) ∉ D := fun i h => hD i i h h
  rw [regularContainmentProbability_eq_centered_cube_ratio D hm hloop a]
  simp_rw [forestCosineProduct_eq_normalized]
  rw [integral_const_mul, ← freeCosineEdges_card_add D hD, pow_add]
  rw [mul_assoc, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def normalizedRegularTorusIntegrand {m : ℕ} (D : Finset (Fin m × Fin m))
    (x : UnitAddTorus (Fin m)) : ℂ :=
  degreeFourierIntegrand (arcSetWeight D) x / (2 : ℂ) ^ (freeCosineEdges D).card

theorem normalizedRegularTorusIntegrand_coe {m : ℕ} (D : Finset (Fin m × Fin m))
    (hm : Odd m) (x : Fin m → ℝ) :
    normalizedRegularTorusIntegrand D (fun i => (x i : UnitAddCircle)) =
      normalizedRegularIntegrand D x := by
  unfold normalizedRegularTorusIntegrand
  rw [degreeFourierIntegrand_eq_centered _ hm, centeredDegreeIntegrand_forced,
    forestCosineProduct_eq_normalized]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0))

theorem norm_normalizedRegularTorusIntegrand_le {m : ℕ} (D : Finset (Fin m × Fin m))
    (hm : Odd m) (x : UnitAddTorus (Fin m)) :
    ‖normalizedRegularTorusIntegrand D x‖ ≤
      ∏ e ∈ freeCosineEdges D, circleCosineKernel (x e.1.1) (x e.1.2) := by
  let y : Fin m → ℝ := fun i => (AddCircle.equivIco 1 0 (x i)).1
  have hy : (fun i => (y i : UnitAddCircle)) = x := by
    funext i
    exact AddCircle.coe_equivIco
  rw [← hy, normalizedRegularTorusIntegrand_coe D hm y]
  exact norm_normalizedRegularIntegrand_le D y

theorem continuous_normalizedRegularTorusIntegrand {m : ℕ} (D : Finset (Fin m × Fin m)) :
    Continuous (normalizedRegularTorusIntegrand D) := by
  unfold normalizedRegularTorusIntegrand degreeFourierIntegrand
  fun_prop

theorem normalizedRegularTorusIntegrand_cluster_bound {m : ℕ} (D : Finset (Fin m × Fin m))
    (hm : Odd m) (x : UnitAddTorus (Fin m)) (j : Fin 16)
    (hdeleted : ∀ u ∈ circleOutliers x j,
      ((circleCore x j).filter (fun v => (u, v) ∈ D ∨ (v, u) ∈ D)).card ≤ 2) :
    ‖normalizedRegularTorusIntegrand D x‖ ≤
      circleSeparationRatio ^ ((circleOutliers x j).card * ((circleCore x j).card - 2)) *
        Real.exp (-(∑ e ∈ goodFreeCosineEdges D (circleGood x j),
          (Real.pi * (circleCenteredLift j (x e.1.1) - circleCenteredLift j (x e.1.2))) ^ 2) / 2) :=
  (norm_normalizedRegularTorusIntegrand_le D hm x).trans
    (freeCosineProduct_cluster_gaussian_bound D x j hdeleted)

end
end Wormald.FiniteModel
