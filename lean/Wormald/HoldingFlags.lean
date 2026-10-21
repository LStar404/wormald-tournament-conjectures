import Wormald.PositiveTransitionSquare

/-! A constant diagonal transition makes the holding indicators independent.
Everything is an exact finite sum over actual paths, so no infinite Markov
process or conditional probability is needed for this reduction. -/

namespace Wormald

noncomputable section
open Matrix
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def linearPathWeight (P : Matrix V V ℝ) {N : ℕ} (s : V) (w : Fin N → V) : ℝ :=
  ∏ t : Fin N, P (Fin.cons (α := fun _ => V) s w t.castSucc) (w t)

def linearHoldingPattern {N : ℕ} (s : V) (w : Fin N → V) : Fin N → Bool :=
  fun t => decide (Fin.cons (α := fun _ => V) s w t.castSucc = w t)

def holdingFlagMass (P : Matrix V V ℝ) {N : ℕ} (s : V) (b : Fin N → Bool) : ℝ :=
  ∑ w : Fin N → V, if linearHoldingPattern s w = b then linearPathWeight P s w else 0

omit [Fintype V] [DecidableEq V] in
theorem linearPathWeight_cons (P : Matrix V V ℝ) {N : ℕ}
    (s j : V) (w : Fin N → V) :
    linearPathWeight P s (Fin.cons j w) = P s j * linearPathWeight P j w := by
  unfold linearPathWeight
  rw [Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ]

omit [Fintype V] in
theorem linearHoldingPattern_cons {N : ℕ} (s j : V) (w : Fin N → V) :
    linearHoldingPattern s (Fin.cons j w) = Fin.cons (decide (s = j)) (linearHoldingPattern j w) := by
  ext t
  refine Fin.cases ?_ (fun i => ?_) t
  · simp [linearHoldingPattern]
  · simp [linearHoldingPattern, Fin.castSucc_succ]

omit [DecidableEq V] in
theorem sum_fin_succ_function {N : ℕ} (g : (Fin (N + 1) → V) → ℝ) :
    (∑ w, g w) = ∑ j, ∑ v : Fin N → V, g (Fin.cons j v) := by
  symm
  calc
    _ = ∑ p : V × (Fin N → V), g (Fin.cons p.1 p.2) := by rw [Fintype.sum_prod_type]
    _ = _ := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (N + 1) => V)) _ _ (fun _ => rfl)

theorem holdingFlagMass_cons (P : Matrix V V ℝ) {N : ℕ}
    (s : V) (b : Bool) (bs : Fin N → Bool) :
    holdingFlagMass P s (Fin.cons b bs) =
      ∑ j, (if decide (s = j) = b then P s j else 0) * holdingFlagMass P j bs := by
  unfold holdingFlagMass
  rw [sum_fin_succ_function]
  simp only [linearHoldingPattern_cons, Fin.cons_inj, linearPathWeight_cons]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : decide (s = j) = b
  · simp only [h, true_and, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : linearHoldingPattern j v = bs <;> simp [hv]
  · simp [h]

theorem holding_step_mass (P : Matrix V V ℝ) (p : ℝ)
    (hrow : ∀ i, (∑ j, P i j) = 1) (hdiag : ∀ i, P i i = p) (s : V) (b : Bool) :
    (∑ j, if decide (s = j) = b then P s j else 0) = if b then p else 1 - p := by
  cases b with
  | true => simp [hdiag]
  | false =>
    have hterm (j : V) :
        (if decide (s = j) = false then P s j else 0) =
          P s j - if s = j then P s j else 0 := by
      by_cases h : s = j <;> simp [h]
    simp only [hterm, Finset.sum_sub_distrib, hrow]
    simp [hdiag]

/-- Exact joint mass of every holding pattern. The right side is the product
of Bernoulli masses, independent of the starting state. -/
theorem holdingFlagMass_eq_product (P : Matrix V V ℝ) (p : ℝ)
    (hrow : ∀ i, (∑ j, P i j) = 1) (hdiag : ∀ i, P i i = p)
    (N : ℕ) (s : V) (b : Fin N → Bool) :
    holdingFlagMass P s b = ∏ t, if b t then p else 1 - p := by
  induction N generalizing s with
  | zero => simp [holdingFlagMass, linearPathWeight, linearHoldingPattern, funext_iff]
  | succ N ih =>
    rw [← Fin.cons_self_tail b, holdingFlagMass_cons]
    simp_rw [ih]
    rw [← Finset.sum_mul, holding_step_mass P p hrow hdiag]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    rfl

omit [DecidableEq V] in
theorem sum_linearPathWeight_eq_one (P : Matrix V V ℝ)
    (hrow : ∀ i, (∑ j, P i j) = 1) (N : ℕ) (s : V) :
    (∑ w : Fin N → V, linearPathWeight P s w) = 1 := by
  induction N generalizing s with
  | zero => simp [linearPathWeight]
  | succ N ih =>
    rw [sum_fin_succ_function]
    simp only [linearPathWeight_cons, ← Finset.mul_sum, ih, mul_one, hrow]

/-- Exact push-forward of every finite path observable depending only on the
holding flags. This includes tail events and exponential moments. -/
theorem sum_holding_observable_eq_product (P : Matrix V V ℝ) (p : ℝ)
    (hrow : ∀ i, (∑ j, P i j) = 1) (hdiag : ∀ i, P i i = p)
    {N : ℕ} (s : V) (F : (Fin N → Bool) → ℝ) :
    (∑ w : Fin N → V, linearPathWeight P s w * F (linearHoldingPattern s w)) =
      ∑ b : Fin N → Bool, (∏ t, if b t then p else 1 - p) * F b := by
  calc
    _ = ∑ w : Fin N → V, ∑ b : Fin N → Bool,
        (if linearHoldingPattern s w = b then linearPathWeight P s w else 0) * F b := by
      apply Finset.sum_congr rfl
      intro w _
      simp only [ite_mul, zero_mul]
      simp
    _ = ∑ b : Fin N → Bool, holdingFlagMass P s b * F b := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, holdingFlagMass]
    _ = _ := by simp_rw [holdingFlagMass_eq_product P p hrow hdiag N s]

@[simp] theorem Tournament.realCriticalTransition_diagonal {n : ℕ} (T : Tournament n)
    (i : Fin n) : T.realCriticalTransition i i = 1 / (n : ℝ) := by
  simp [Tournament.realCriticalTransition]

/-- The actual regular tournament has IID Bernoulli(1/n) holding flags. -/
theorem Tournament.holdingFlagMass_eq_product {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (N : ℕ) (s : Fin n) (b : Fin N → Bool) :
    holdingFlagMass T.realCriticalTransition s b =
      ∏ t, if b t then 1 / (n : ℝ) else 1 - 1 / (n : ℝ) :=
  Wormald.holdingFlagMass_eq_product T.realCriticalTransition (1 / (n : ℝ))
    (T.realCriticalTransition_row_sum hn hT) T.realCriticalTransition_diagonal N s b

end
end Wormald
