import Wormald.Definitions
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card

/-!
# The original finite combinatorial model

A Boolean is assigned to each unordered labelled pair, so every tournament occurs
exactly once in the sample space. Hamilton cycles are counted as successor
permutations with one orbit; their cyclic starting points are already identified.
`conjectureOne` below is a statement of the original problem, not a theorem.
-/

namespace Wormald.FiniteModel

/-- The smaller label is listed first, so every unordered pair appears once. -/
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- `true` means that the edge points from the smaller label to the larger one. -/
abbrev Orientation (n : ℕ) := Edge n → Bool

/-- Directed adjacency determined by an assignment of the unordered edges. -/
def arc {n : ℕ} (T : Orientation n) (i j : Fin n) : Bool :=
  if h : i < j then T ⟨(i, j), h⟩
  else if h : j < i then !(T ⟨(j, i), h⟩) else false

@[simp] theorem arc_self {n : ℕ} (T : Orientation n) (i : Fin n) :
    arc T i i = false := by simp [arc]

theorem arc_reverse {n : ℕ} (T : Orientation n) (i j : Fin n) (h : i ≠ j) :
    arc T i j = !(arc T j i) := by
  rcases lt_or_gt_of_ne h with hij | hji
  · simp [arc, hij, not_lt_of_gt hij]
  · simp [arc, hji, not_lt_of_gt hji]

/-- The Boolean encoding realizes the manuscript's 0/1 rational adjacency matrix. -/
def toTournament {n : ℕ} (T : Orientation n) : Wormald.Tournament n where
  adjacency i j := if arc T i j then 1 else 0
  diagonal i := by simp
  zero_or_one i j := by cases arc T i j <;> simp
  orientation i j hij := by
    rw [arc_reverse T i j hij]
    cases arc T j i <;> simp

/-- Distinct edge assignments give distinct rational tournament objects. -/
theorem toTournament_injective {n : ℕ} :
    Function.Injective (@toTournament n) := by
  intro T U h
  funext e
  have hentry := congrArg (fun A : Wormald.Tournament n => A.adjacency e.1.1 e.1.2) h
  have hnot : ¬ e.1.2 < e.1.1 := not_lt_of_gt e.2
  simp only [toTournament, arc, dite_eq_left e.2] at hentry
  cases hT : T e <;> cases hU : U e <;> simp_all

/-- Recovering the independent Boolean coordinates of any rational tournament. -/
noncomputable def fromTournament {n : ℕ} (T : Wormald.Tournament n) : Orientation n :=
  fun e => decide (T.adjacency e.1.1 e.1.2 = 1)

private theorem rationalTournament_ext {n : ℕ} {T U : Wormald.Tournament n}
    (h : T.adjacency = U.adjacency) : T = U := by
  cases T
  cases U
  cases h
  rfl

/-- Every tournament from the manuscript is represented by the Boolean sample space. -/
theorem to_fromTournament {n : ℕ} (T : Wormald.Tournament n) :
    toTournament (fromTournament T) = T := by
  classical
  cases T with
  | mk A hd hz ho =>
    apply rationalTournament_ext
    funext i j
    by_cases hij : i < j
    · simp only [toTournament, arc, dite_eq_left hij, fromTournament, decide_eq_true_eq]
      rcases hz i j with h0 | h1
      · simp [h0]
      · simp [h1]
    · by_cases hji : j < i
      · have hne : i ≠ j := ne_of_gt hji
        have hsum := ho i j hne
        simp only [toTournament, arc, dite_eq_right hij, dite_eq_left hji, fromTournament]
        rcases hz j i with h0 | h1
        · have hA : A i j = 1 := by simpa [h0] using hsum
          simp [h0, hA]
        · have hA : A i j = 0 := by linarith
          simp [h1, hA]
      · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
        subst j
        simp [toTournament, hd]

/-- The sample encoding is a bijection with the manuscript's tournament structure. -/
noncomputable def orientationEquivTournament (n : ℕ) :
    Orientation n ≃ Wormald.Tournament n where
  toFun := toTournament
  invFun := fromTournament
  left_inv T := toTournament_injective (to_fromTournament (toTournament T))
  right_inv := to_fromTournament

/-- The circle convention: all vertices lie in a single orbit of the successor. -/
def IsHamiltonCycle {V : Type*} [Fintype V]
    (a : V → V → Bool) (σ : Equiv.Perm V) : Prop :=
  (∀ v w, ∃ k : Fin (Fintype.card V), (σ^[k.val]) v = w) ∧
    ∀ v, a v (σ v) = true

/-- Each successor permutation contributes one directed cycle, without rotations. -/
noncomputable def hamiltonCycleCount {V : Type*} [Fintype V]
    (a : V → V → Bool) : ℕ :=
  Nat.card {σ : Equiv.Perm V // IsHamiltonCycle a σ}

/-- A Hamilton path is a bijective ordered list whose consecutive arcs are directed. -/
def IsHamiltonPath {V : Type*} [Fintype V]
    (a : V → V → Bool) (e : Fin (Fintype.card V) ≃ V) : Prop :=
  ∀ i j, j.val = i.val + 1 → a (e i) (e j) = true

noncomputable def hamiltonPathCount {V : Type*} [Fintype V]
    (a : V → V → Bool) : ℕ :=
  Nat.card {e : Fin (Fintype.card V) ≃ V // IsHamiltonPath a e}

/-- All d labelled internal tournaments; the uniform law makes the blocks independent. -/
abbrev IndependentSample (d m : ℕ) := Fin d → Orientation m

/-- Blow-up vertices are the pairs (base label, internal label). -/
def blowupArc {d m : ℕ} (base : Orientation d) (blocks : IndependentSample d m)
    (v w : Fin d × Fin m) : Bool :=
  if v.1 = w.1 then arc (blocks v.1) v.2 w.2 else arc base v.1 w.1

@[simp] theorem blowupArc_self {d m : ℕ} (base : Orientation d)
    (blocks : IndependentSample d m) (v : Fin d × Fin m) :
    blowupArc base blocks v v = false := by simp [blowupArc]

/-- The finite sample construction always produces an actual tournament. -/
theorem blowupArc_reverse {d m : ℕ} (base : Orientation d)
    (blocks : IndependentSample d m) (v w : Fin d × Fin m) (h : v ≠ w) :
    blowupArc base blocks v w = !(blowupArc base blocks w v) := by
  by_cases hb : v.1 = w.1
  · have hi : v.2 ≠ w.2 := by
      intro hi
      exact h (Prod.ext hb hi)
    rw [blowupArc, ite_eq_left hb, blowupArc, ite_eq_left hb.symm]
    rw [hb]
    exact arc_reverse (blocks w.1) v.2 w.2 hi
  · simp only [blowupArc, ite_eq_right hb, ite_eq_right (Ne.symm hb)]
    exact arc_reverse base v.1 w.1 hb

/-- A finite uniform expectation, with exact rational arithmetic. -/
noncomputable def uniformMean {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℕ) : ℚ :=
  (∑ ω, (f ω : ℚ)) / (Fintype.card Ω : ℚ)

/-- This sample space is never empty, so its mean never divides by zero. -/
theorem independentSample_card_pos (d m : ℕ) :
    0 < Fintype.card (IndependentSample d m) := by
  exact Fintype.card_pos_iff.mpr ⟨fun _ _ => false⟩

theorem independentSample_denominator_ne_zero (d m : ℕ) :
    (Fintype.card (IndependentSample d m) : ℚ) ≠ 0 := by
  exact_mod_cast ne_of_gt (independentSample_card_pos d m)

noncomputable def expectedCycles {d : ℕ} (base : Orientation d) (m : ℕ) : ℚ :=
  uniformMean (fun blocks : IndependentSample d m =>
    hamiltonCycleCount (blowupArc base blocks))

noncomputable def expectedPaths {d : ℕ} (base : Orientation d) (m : ℕ) : ℚ :=
  uniformMean (fun blocks : IndependentSample d m =>
    hamiltonPathCount (blowupArc base blocks))

/-- Isomorphisms preserve edge directions; they do not perform sign switching. -/
def Isomorphic {n : ℕ} (T U : Orientation n) : Prop :=
  ∃ e : Equiv.Perm (Fin n), ∀ i j, arc T i j = arc U (e i) (e j)

theorem isomorphic_refl {n : ℕ} (T : Orientation n) : Isomorphic T T :=
  ⟨Equiv.refl _, fun _ _ => rfl⟩

/-- For odd n this is exactly i→j iff the clockwise distance lies in 1,…,(n−1)/2. -/
def carousel (n : ℕ) : Orientation n :=
  fun e => decide (e.1.2.val - e.1.1.val ≤ n / 2)

/-- Clockwise distance with labels in 0,…,n−1, written without modular notation. -/
def clockwiseDistance {n : ℕ} (i j : Fin n) : ℕ :=
  if i ≤ j then j.val - i.val else n + j.val - i.val

/-- The encoded reference really is the odd-order carousel from the original problem. -/
theorem carousel_arc_iff {n : ℕ} (hn : Odd n) (i j : Fin n) :
    arc (carousel n) i j = true ↔
      0 < clockwiseDistance i j ∧ clockwiseDistance i j ≤ n / 2 := by
  rcases lt_trichotomy i j with hij | heq | hji
  · have hle : i ≤ j := le_of_lt hij
    simp [arc, carousel, hij, clockwiseDistance, hle]
  · subst j
    simp [clockwiseDistance]
  · have hnot : ¬ i < j := not_lt_of_gt hji
    have hnle : ¬ i ≤ j := not_le_of_gt hji
    simp [arc, carousel, hnot, hji, clockwiseDistance, hnle]
    rcases hn with ⟨k, hk⟩
    omega

/-- Wormald's original Conjecture 1, with its fixed-d, then large-m quantifiers.
This definition is deliberately NOT accompanied by a proof. -/
def conjectureOne : Prop :=
  ∀ d : ℕ, 3 ≤ d → Odd d → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
    ∀ base : Orientation d, expectedCycles base m ≤ expectedCycles (carousel d) m

/-- The manuscript's stronger uniqueness claim, also an unproved target. -/
def uniqueClassConjectureOne : Prop :=
  ∀ d : ℕ, 3 ≤ d → Odd d → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
    ∀ base : Orientation d,
      expectedCycles base m ≤ expectedCycles (carousel d) m ∧
      (expectedCycles base m = expectedCycles (carousel d) m ↔
        Isomorphic base (carousel d))

/-- Uniform regular internal blocks are only considered at odd block orders.
The additional nonempty-support condition records that a uniform law exists. -/
def RegularBlock {m : ℕ} (T : Orientation m) : Prop := (toTournament T).Regular

abbrev RegularSample (d m : ℕ) := Fin d → {T : Orientation m // RegularBlock T}

def LegalRegularOrder (d m : ℕ) : Prop := Odd m ∧ Nonempty (RegularSample d m)

noncomputable def expectedRegularCycles {d : ℕ} (base : Orientation d) (m : ℕ)
    (hlegal : LegalRegularOrder d m) : ℚ := by
  classical
  letI : Fintype (RegularSample d m) := Fintype.ofFinite _
  letI : Nonempty (RegularSample d m) := hlegal.2
  exact uniformMean (fun blocks : RegularSample d m =>
    hamiltonCycleCount (blowupArc base (fun i => (blocks i).1)))

noncomputable def expectedRegularPaths {d : ℕ} (base : Orientation d) (m : ℕ)
    (hlegal : LegalRegularOrder d m) : ℚ := by
  classical
  letI : Fintype (RegularSample d m) := Fintype.ofFinite _
  letI : Nonempty (RegularSample d m) := hlegal.2
  exact uniformMean (fun blocks : RegularSample d m =>
    hamiltonPathCount (blowupArc base (fun i => (blocks i).1)))

end Wormald.FiniteModel
