import Wormald.RegularConditioning
import Mathlib.Algebra.MvPolynomial.Basic

/-! Exact finite generating polynomials for regular tournaments. Choosing the
source endpoint of each unordered edge records its actual outdegree. This is
the finite coefficient identity needed before any growing-dimension estimate. -/

namespace Wormald.FiniteModel
noncomputable section
open scoped BigOperators
open MvPolynomial
attribute [local instance] Classical.propDecidable

def orientationTail {m : ℕ} (T : Orientation m) (e : Edge m) : Fin m :=
  if T e then e.1.1 else e.1.2

def orientationHead {m : ℕ} (T : Orientation m) (e : Edge m) : Fin m :=
  if T e then e.1.2 else e.1.1

theorem arc_orientationTail_head {m : ℕ} (T : Orientation m) (e : Edge m) :
    arc T (orientationTail T e) (orientationHead T e) = true := by
  have hlt := e.2
  cases hb : T e <;> simp [orientationTail, orientationHead, hb, arc, hlt,
    not_lt_of_gt hlt]

private theorem orientationTail_head_injective {m : ℕ} (T : Orientation m) :
    Function.Injective (fun e : Edge m => (orientationTail T e, orientationHead T e)) := by
  intro e f h
  have ht := congrArg Prod.fst h
  have hh := congrArg Prod.snd h
  have he := e.2
  have hf := f.2
  cases hb : T e <;> cases hc : T f <;>
    simp only [orientationTail, orientationHead, hb, hc, Bool.false_eq_true,
      ite_false, ite_true] at ht hh
  · exact Subtype.ext (Prod.ext hh ht)
  · exfalso
    rw [ht, hh] at he
    exact (not_lt_of_gt hf) he
  · exfalso
    rw [ht, hh] at he
    exact (not_lt_of_gt hf) he
  · exact Subtype.ext (Prod.ext ht hh)

private def outgoingEdgeMap {m : ℕ} (T : Orientation m) (i : Fin m)
    (e : {e : Edge m // orientationTail T e = i}) : {j : Fin m // arc T i j = true} :=
  ⟨orientationHead T e.1,
    (congrArg (fun a => arc T a (orientationHead T e.1)) e.2).symm.trans
      (arc_orientationTail_head T e.1)⟩

private def outgoingEdgeEquiv {m : ℕ} (T : Orientation m) (i : Fin m) :
    {e : Edge m // orientationTail T e = i} ≃ {j : Fin m // arc T i j = true} :=
  Equiv.ofBijective (outgoingEdgeMap T i) ⟨by
    intro e f h
    apply Subtype.ext
    apply orientationTail_head_injective T
    exact Prod.ext (e.2.trans f.2.symm) (congrArg Subtype.val h), by
    intro j
    have hne : i ≠ j.1 := by
      intro h
      have hj := j.2
      rw [← h, arc_self] at hj
      contradiction
    by_cases hij : i < j.1
    · let e : Edge m := ⟨(i, j.1), hij⟩
      have hb : T e = true := by simpa only [arc, dite_eq_left hij] using j.2
      refine ⟨⟨e, by simp [orientationTail, hb, e]⟩, ?_⟩
      apply Subtype.ext
      simp [outgoingEdgeMap, orientationHead, hb, e]
    · have hji : j.1 < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm hne)
      let e : Edge m := ⟨(j.1, i), hji⟩
      have hb : T e = false := by
        have hj := j.2
        simp only [arc, dite_eq_right hij, dite_eq_left hji] at hj
        cases h : T e <;> simp_all [e]
      refine ⟨⟨e, by simp [orientationTail, hb, e]⟩, ?_⟩
      apply Subtype.ext
      simp [outgoingEdgeMap, orientationHead, hb, e]⟩

def orientationDegreeExponent {m : ℕ} (T : Orientation m) : Fin m →₀ ℕ :=
  ∑ e : Edge m, Finsupp.single (orientationTail T e) 1

theorem orientationDegreeExponent_apply {m : ℕ} (T : Orientation m) (i : Fin m) :
    orientationDegreeExponent T i = ∑ j : Fin m, if arc T i j then 1 else 0 := by
  have hcard := Fintype.card_congr (outgoingEdgeEquiv T i)
  simp only [orientationDegreeExponent, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Fintype.card_subtype, Finset.card_filter] at hcard ⊢
  exact hcard

theorem orientationDegreeExponent_cast {m : ℕ} (T : Orientation m) (i : Fin m) :
    (orientationDegreeExponent T i : ℚ) = ∑ j, (toTournament T).adjacency i j := by
  rw [orientationDegreeExponent_apply]
  simp only [toTournament]
  push_cast
  rfl

def regularDegreeExponent (m : ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => m / 2)

@[simp] theorem regularDegreeExponent_apply (m : ℕ) (i : Fin m) :
    regularDegreeExponent m i = m / 2 := rfl

private theorem odd_half_rat {m : ℕ} (hm : Odd m) :
    ((m : ℚ) - 1) / 2 = (m / 2 : ℕ) := by
  rcases hm with ⟨k, hk⟩
  have hh : m / 2 = k := by omega
  rw [hh, hk]
  push_cast
  ring

theorem regularBlock_iff_degreeExponent {m : ℕ} (T : Orientation m) (hm : Odd m) :
    RegularBlock T ↔ orientationDegreeExponent T = regularDegreeExponent m := by
  constructor
  · intro hr
    ext i
    have h := (orientationDegreeExponent_cast T i).trans ((hr i).trans (odd_half_rat hm))
    exact_mod_cast h
  · intro h i
    rw [← orientationDegreeExponent_cast, h, regularDegreeExponent_apply]
    exact (odd_half_rat hm).symm

def degreeGeneratingPolynomial {m : ℕ} {R : Type*} [CommSemiring R]
    (w : Edge m → Bool → R) : MvPolynomial (Fin m) R :=
  ∏ e : Edge m, (C (w e true) * X e.1.1 + C (w e false) * X e.1.2)

theorem degreeGeneratingPolynomial_eq_sum {m : ℕ} {R : Type*} [CommSemiring R]
    (w : Edge m → Bool → R) :
    degreeGeneratingPolynomial w = ∑ T : Orientation m,
      monomial (orientationDegreeExponent T) (∏ e, w e (T e)) := by
  calc
    _ = ∏ e : Edge m, ∑ b : Bool,
        monomial (Finsupp.single (if b then e.1.1 else e.1.2) 1) (w e b) := by
      unfold degreeGeneratingPolynomial
      apply Finset.prod_congr rfl
      intro e _
      simp [X, C_mul_monomial]
    _ = ∑ T : Orientation m, ∏ e : Edge m,
        monomial (Finsupp.single (if T e then e.1.1 else e.1.2) 1) (w e (T e)) :=
      Fintype.prod_sum (f := fun (e : Edge m) (b : Bool) =>
        monomial (Finsupp.single (if b then e.1.1 else e.1.2) 1) (w e b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T _
      exact (monomial_sum_prod _ _ _).symm

theorem coeff_degreeGeneratingPolynomial_regular {m : ℕ} {R : Type*} [CommSemiring R]
    (w : Edge m → Bool → R) (hm : Odd m) :
    (degreeGeneratingPolynomial w).coeff (regularDegreeExponent m) =
      ∑ T : Orientation m, if RegularBlock T then ∏ e, w e (T e) else 0 := by
  rw [degreeGeneratingPolynomial_eq_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [MvPolynomial.coeff_monomial]
  by_cases hr : RegularBlock T
  · rw [(regularBlock_iff_degreeExponent T hm).mp hr]
    simp only [ite_eq_left hr, ite_true]
  · have hne := mt (regularBlock_iff_degreeExponent T hm).mpr hr
    simp only [ite_eq_right hr, ite_eq_right hne]

def edgeArcConstraints {m : ℕ} (D : Finset (Fin m × Fin m)) (T : Orientation m) : Prop :=
  ∀ e : Edge m, ((e.1.1, e.1.2) ∈ D → T e = true) ∧
    ((e.1.2, e.1.1) ∈ D → T e = false)

theorem edgeArcConstraints_iff_contains {m : ℕ} (D : Finset (Fin m × Fin m))
    (hloop : ∀ i, (i, i) ∉ D) (T : Orientation m) :
    edgeArcConstraints D T ↔ ContainsArcSet D T := by
  constructor
  · intro h p hp
    have hne : p.1 ≠ p.2 := by
      intro heq
      have hp' : (p.1, p.2) ∈ D := hp
      rw [← heq] at hp'
      exact hloop p.1 hp'
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hb := (h ⟨p, hij⟩).1 hp
      simpa only [arc, dite_eq_left hij] using hb
    · have hb := (h ⟨(p.2, p.1), hji⟩).2 hp
      simp [arc, hji, not_lt_of_gt hji, hb]
  · intro h e
    constructor
    · intro he
      simpa only [arc, dite_eq_left e.2] using h _ he
    · intro he
      have hh := h _ he
      simpa [arc, e.2, not_lt_of_gt e.2] using hh

/-- A forbidden choice has weight zero. Every prescribed orientation is
checked, including inconsistent pairs of opposite prescribed arcs. -/
def arcSetWeight {m : ℕ} (D : Finset (Fin m × Fin m)) (e : Edge m) (b : Bool) : ℚ :=
  if ((e.1.1, e.1.2) ∈ D → b = true) ∧ ((e.1.2, e.1.1) ∈ D → b = false)
  then 1 else 0

theorem prod_arcSetWeight {m : ℕ} (D : Finset (Fin m × Fin m))
    (hloop : ∀ i, (i, i) ∉ D) (T : Orientation m) :
    (∏ e, arcSetWeight D e (T e)) = if ContainsArcSet D T then 1 else 0 := by
  unfold arcSetWeight
  rw [Fintype.prod_boole]
  by_cases h : ContainsArcSet D T
  · have hall := (edgeArcConstraints_iff_contains D hloop T).mpr h
    unfold edgeArcConstraints at hall
    simp only [ite_eq_left h, ite_eq_left hall]
  · have hall := mt (edgeArcConstraints_iff_contains D hloop T).mp h
    unfold edgeArcConstraints at hall
    simp only [ite_eq_right h, ite_eq_right hall]

def tournamentDegreePolynomial (m : ℕ) : MvPolynomial (Fin m) ℚ :=
  degreeGeneratingPolynomial (fun _ _ => (1 : ℚ))

def forcedDegreePolynomial {m : ℕ} (D : Finset (Fin m × Fin m)) :
    MvPolynomial (Fin m) ℚ := degreeGeneratingPolynomial (arcSetWeight D)

theorem singleRegularProbability_eq_degreeCoeff (m : ℕ) (hm : Odd m) :
    singleRegularProbability m =
      (tournamentDegreePolynomial m).coeff (regularDegreeExponent m) /
        (Fintype.card (Orientation m) : ℚ) := by
  unfold singleRegularProbability regularIndicator uniformMean tournamentDegreePolynomial
  rw [coeff_degreeGeneratingPolynomial_regular _ hm]
  simp only [Finset.prod_const_one, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem jointRegularContainmentProbability_eq_degreeCoeff {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m) (hloop : ∀ i, (i, i) ∉ D) :
    uniformMean (fun T : Orientation m =>
      if RegularBlock T ∧ ContainsArcSet D T then 1 else 0) =
      (forcedDegreePolynomial D).coeff (regularDegreeExponent m) /
        (Fintype.card (Orientation m) : ℚ) := by
  unfold uniformMean forcedDegreePolynomial
  rw [coeff_degreeGeneratingPolynomial_regular _ hm]
  congr 1
  apply Finset.sum_congr rfl
  intro T _
  rw [prod_arcSetWeight D hloop T]
  by_cases hr : RegularBlock T <;> by_cases hc : ContainsArcSet D T <;> simp [hr, hc]

/-- The exact regular containment probability is a ratio of two genuine
outdegree coefficients; no forest or asymptotic assumption is required. -/
theorem regularContainmentProbability_eq_coeff_ratio {m : ℕ}
    (D : Finset (Fin m × Fin m)) (hm : Odd m) (hloop : ∀ i, (i, i) ∉ D) :
    regularContainmentProbability D hm =
      (forcedDegreePolynomial D).coeff (regularDegreeExponent m) /
        (tournamentDegreePolynomial m).coeff (regularDegreeExponent m) := by
  rw [regularContainmentProbability_eq_conditional,
    jointRegularContainmentProbability_eq_degreeCoeff D hm hloop,
    singleRegularProbability_eq_degreeCoeff m hm]
  exact div_div_div_cancel_right₀
    (by exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Orientation m)))) _ _

theorem regularDegreeCoeff_pos (m : ℕ) (hm : Odd m) :
    0 < (tournamentDegreePolynomial m).coeff (regularDegreeExponent m) := by
  have : Nonempty {T : Orientation m // RegularBlock T} :=
    ⟨⟨carousel m, carousel_regular hm⟩⟩
  have h := uniformMean_event_pos (RegularBlock (m := m))
  change 0 < singleRegularProbability m at h
  rw [singleRegularProbability_eq_degreeCoeff m hm] at h
  exact (div_pos_iff_of_pos_right (by exact_mod_cast
    (Fintype.card_pos : 0 < Fintype.card (Orientation m)))).mp h

end
end Wormald.FiniteModel
