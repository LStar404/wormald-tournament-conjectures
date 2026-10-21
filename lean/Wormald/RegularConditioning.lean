import Wormald.CarouselRegular
import Wormald.PermanentBound

/-! The original uniform regular-block law is exactly the independent law
conditioned on all internal degree constraints. All normalizing probabilities
are strictly positive at odd block orders. -/

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem uniformMean_equiv {Ω Ω' : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype Ω'] [Nonempty Ω'] (e : Ω ≃ Ω') (f : Ω' → ℕ) :
    uniformMean (fun ω => f (e ω)) = uniformMean f := by
  unfold uniformMean
  rw [Fintype.sum_equiv e (fun ω => (f (e ω) : ℚ)) (fun ω => (f ω : ℚ)) (fun _ => rfl),
    Fintype.card_congr e]

private theorem sum_restricted_eq_subtype {Ω : Type*} [Fintype Ω]
    (p : Ω → Prop) (f : Ω → ℕ) :
    (∑ ω, ((if p ω then f ω else 0 : ℕ) : ℚ)) = ∑ ω : {ω // p ω}, (f ω : ℚ) := by
  simp only [Nat.cast_ite, Nat.cast_zero]
  simpa only [Finset.sum_filter] using
    (Finset.sum_subtype (Finset.univ.filter p) (by simp) (fun ω => (f ω : ℚ)))

theorem uniformMean_event_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : Ω → Prop) [Nonempty {ω // p ω}] :
    0 < uniformMean (fun ω => if p ω then 1 else 0) := by
  unfold uniformMean
  rw [sum_restricted_eq_subtype p (fun _ => 1)]
  simp only [Nat.cast_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  exact div_pos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card {ω // p ω}))
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω))

/-- The finite conditional-mean identity, with the actual event probability
in its denominator. -/
theorem uniformMean_subtype_eq_conditional {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p : Ω → Prop) [Nonempty {ω // p ω}] (f : Ω → ℕ) :
    uniformMean (fun ω : {ω // p ω} => f ω) =
      uniformMean (fun ω => if p ω then f ω else 0) /
        uniformMean (fun ω => if p ω then 1 else 0) := by
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Ω))
  have hsub : (Fintype.card {ω // p ω} : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card {ω // p ω}))
  unfold uniformMean
  rw [sum_restricted_eq_subtype p f, sum_restricted_eq_subtype p (fun _ => 1)]
  simp only [Nat.cast_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp

theorem uniformMean_product {I Ω : Type*} [Fintype I] [Fintype Ω] [Nonempty Ω]
    [DecidableEq I] [DecidableEq Ω]
    (f : I → Ω → ℕ) :
    uniformMean (fun ω : I → Ω => ∏ i, f i (ω i)) = ∏ i, uniformMean (f i) := by
  unfold uniformMean
  simp only [Nat.cast_prod]
  rw [← Fintype.prod_sum (f := fun i ω => (f i ω : ℚ))]
  simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow]

def AllRegularBlocks {d m : ℕ} (blocks : IndependentSample d m) : Prop :=
  ∀ i, RegularBlock (blocks i)

def regularSampleEquiv (d m : ℕ) : RegularSample d m ≃
    {blocks : IndependentSample d m // AllRegularBlocks blocks} where
  toFun blocks := ⟨fun i => (blocks i).1, fun i => (blocks i).2⟩
  invFun blocks i := ⟨blocks.1 i, blocks.2 i⟩
  left_inv _ := rfl
  right_inv _ := rfl

def regularEventProbability (d m : ℕ) : ℚ :=
  uniformMean (fun blocks : IndependentSample d m => if AllRegularBlocks blocks then 1 else 0)

def regularIndicator {m : ℕ} (T : Orientation m) : ℕ :=
  if RegularBlock T then 1 else 0

def singleRegularProbability (m : ℕ) : ℚ :=
  uniformMean (regularIndicator (m := m))

theorem regularEventProbability_eq_pow (d m : ℕ) :
    regularEventProbability d m = singleRegularProbability m ^ d := by
  have hfun : (fun blocks : IndependentSample d m => if AllRegularBlocks blocks then 1 else 0) =
      (fun blocks => ∏ i, regularIndicator (blocks i) : IndependentSample d m → ℕ) := by
    funext blocks
    simp only [regularIndicator]
    rw [Fintype.prod_boole]
    split <;> split <;> simp_all [AllRegularBlocks]
  have hconstant : (∏ _i : Fin d,
      uniformMean (regularIndicator (m := m))) =
      singleRegularProbability m ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  unfold regularEventProbability
  rw [hfun]
  exact (uniformMean_product (I := Fin d) (Ω := Orientation m)
    (fun _ => regularIndicator)).trans hconstant

theorem regularEventProbability_pos (d m : ℕ) (hm : Odd m) :
    0 < regularEventProbability d m := by
  have : Nonempty (RegularSample d m) := regularSample_nonempty d m hm
  have : Nonempty {blocks : IndependentSample d m // AllRegularBlocks blocks} :=
    ⟨regularSampleEquiv d m (Classical.choice (regularSample_nonempty d m hm))⟩
  exact uniformMean_event_pos AllRegularBlocks

theorem regularMean_eq_conditional {d m : ℕ} (hlegal : LegalRegularOrder d m)
    (f : IndependentSample d m → ℕ) :
    @uniformMean (RegularSample d m) (Fintype.ofFinite _) hlegal.2
      (fun blocks => f (fun i => (blocks i).1)) =
      uniformMean (fun blocks => if AllRegularBlocks blocks then f blocks else 0) /
        regularEventProbability d m := by
  let : Fintype (RegularSample d m) := Fintype.ofFinite _
  have : Nonempty (RegularSample d m) := hlegal.2
  have : Nonempty {blocks : IndependentSample d m // AllRegularBlocks blocks} :=
    ⟨regularSampleEquiv d m (Classical.choice hlegal.2)⟩
  have heq := uniformMean_equiv (regularSampleEquiv d m)
    (fun blocks => f blocks.1)
  exact heq.trans (uniformMean_subtype_eq_conditional AllRegularBlocks f)

/-- The actual cycle expectation in the uniform regular-block model is the
conditional independent expectation, with no asymptotic premise. -/
theorem expectedRegularCycles_eq_conditional {d m : ℕ} (base : Orientation d)
    (hlegal : LegalRegularOrder d m) :
    expectedRegularCycles base m hlegal =
      uniformMean (fun blocks : IndependentSample d m =>
        if AllRegularBlocks blocks then hamiltonCycleCount (blowupArc base blocks) else 0) /
        regularEventProbability d m :=
  regularMean_eq_conditional hlegal (fun blocks => hamiltonCycleCount (blowupArc base blocks))

theorem expectedRegularPaths_eq_conditional {d m : ℕ} (base : Orientation d)
    (hlegal : LegalRegularOrder d m) :
    expectedRegularPaths base m hlegal =
      uniformMean (fun blocks : IndependentSample d m =>
        if AllRegularBlocks blocks then hamiltonPathCount (blowupArc base blocks) else 0) /
        regularEventProbability d m :=
  regularMean_eq_conditional hlegal (fun blocks => hamiltonPathCount (blowupArc base blocks))

def ContainsArcSet {m : ℕ} (D : Finset (Fin m × Fin m)) (T : Orientation m) : Prop :=
  ∀ e ∈ D, arc T e.1 e.2 = true

def independentContainmentProbability {m : ℕ} (D : Finset (Fin m × Fin m)) : ℚ :=
  uniformMean (fun T : Orientation m => if ContainsArcSet D T then 1 else 0)

def regularContainmentProbability {m : ℕ} (D : Finset (Fin m × Fin m))
    (hm : Odd m) : ℚ := by
  have : Nonempty {T : Orientation m // RegularBlock T} := ⟨⟨carousel m, carousel_regular hm⟩⟩
  exact uniformMean (fun T : {T : Orientation m // RegularBlock T} =>
    if ContainsArcSet D T.1 then 1 else 0)

/-- The exact finite probability whose uniform path-forest asymptotic is
Wormald's Lemma 3. This declaration proves conditioning only. -/
theorem regularContainmentProbability_eq_conditional {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m) :
    regularContainmentProbability D hm =
      uniformMean (fun T : Orientation m =>
        if RegularBlock T ∧ ContainsArcSet D T then 1 else 0) / singleRegularProbability m := by
  have : Nonempty {T : Orientation m // RegularBlock T} := ⟨⟨carousel m, carousel_regular hm⟩⟩
  have h := uniformMean_subtype_eq_conditional RegularBlock
    (fun T : Orientation m => if ContainsArcSet D T then 1 else 0)
  have hfun : (fun T : Orientation m => if RegularBlock T ∧ ContainsArcSet D T then 1 else 0) =
      (fun T => if RegularBlock T then if ContainsArcSet D T then 1 else 0 else 0 : Orientation m → ℕ) := by
    funext T
    by_cases hr : RegularBlock T <;> by_cases hc : ContainsArcSet D T <;> simp [hr, hc]
  change uniformMean (fun T : {T : Orientation m // RegularBlock T} =>
      if ContainsArcSet D T.1 then 1 else 0) =
    uniformMean (fun T : Orientation m => if RegularBlock T ∧ ContainsArcSet D T then 1 else 0) /
      uniformMean (fun T : Orientation m => if RegularBlock T then 1 else 0)
  rw [hfun]
  exact h

end
end Wormald.FiniteModel

namespace Wormald
open scoped BigOperators

theorem Tournament.regular_iff_sign_row_sum_zero {m : ℕ} (T : Tournament m) :
    T.Regular ↔ ∀ i, (∑ j, T.sign i j) = 0 := by
  constructor
  · exact T.sign_row_sum
  · intro h i
    have hi := h i
    simp only [Tournament.sign, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum] at hi
    simp at hi
    linarith

namespace FiniteModel
theorem allRegularBlocks_iff_sign_degree_zero {d m : ℕ} (blocks : IndependentSample d m) :
    AllRegularBlocks blocks ↔ ∀ i v, (∑ w, (toTournament (blocks i)).sign v w) = 0 := by
  simp only [AllRegularBlocks, RegularBlock, Tournament.regular_iff_sign_row_sum_zero]

end FiniteModel
end Wormald
