import Wormald.AdjacentHoldingConcentration

namespace Wormald

noncomputable section
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

def cyclicTripleIndicator {N : ℕ} (f : Fin N → V) (t : Fin N) : ℕ :=
  if f t = f (finRotate N t) ∧ f (finRotate N t) = f (finRotate N (finRotate N t)) then 1 else 0

def cyclicTripleCount {N : ℕ} (f : Fin N → V) : ℕ := ∑ t, cyclicTripleIndicator f t

def linearTripleCount {N : ℕ} (f : Fin (N + 1) → V) : ℕ :=
  adjacentSuccessCount (linearHoldingPattern (f 0) (Fin.tail f))

theorem adjacentSuccessCount_eq_sum {N : ℕ} (b : Fin (N + 1) → Bool) :
    adjacentSuccessCount b = ∑ t : Fin N, if b t.castSucc && b t.succ then 1 else 0 := by
  induction N with
  | zero => simp [adjacentSuccessCount]
  | succ N ih =>
    rw [adjacentSuccessCount, Fin.sum_univ_succ, ih (Fin.tail b)]
    simp [Fin.tail, Fin.castSucc_succ]

theorem linearHoldingPattern_eq_successive {N : ℕ} (f : Fin (N + 1) → V) :
    linearHoldingPattern (f 0) (Fin.tail f) = fun t => decide (f t.castSucc = f t.succ) := by
  ext t
  simp only [linearHoldingPattern, Fin.cons_self_tail, Fin.tail]

theorem linearTripleCount_eq_sum {N : ℕ} (f : Fin (N + 3) → V) :
    linearTripleCount f = ∑ t : Fin (N + 1),
      if f t.castSucc.castSucc = f t.succ.castSucc ∧ f t.succ.castSucc = f t.succ.succ
      then 1 else 0 := by
  rw [linearTripleCount, linearHoldingPattern_eq_successive, adjacentSuccessCount_eq_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp [Fin.castSucc_succ]

theorem finRotate_two_castSucc {N : ℕ} (t : Fin (N + 1)) :
    finRotate (N + 3) t.castSucc.castSucc = t.succ.castSucc := by
  exact finRotate_of_lt (n := N + 2) (k := t.val) (by omega)

theorem finRotate_succ_castSucc {N : ℕ} (t : Fin (N + 1)) :
    finRotate (N + 3) t.succ.castSucc = t.succ.succ := by
  exact finRotate_of_lt (n := N + 2) (k := t.val + 1) (by omega)

def cyclicEndTripleCount {N : ℕ} (f : Fin (N + 3) → V) : ℕ :=
  cyclicTripleIndicator f (Fin.last (N + 1)).castSucc + cyclicTripleIndicator f (Fin.last (N + 2))

/-- Opening a cyclic word removes precisely the two triples crossing the cut. -/
theorem cyclicTripleCount_eq_linear_add_end {N : ℕ} (f : Fin (N + 3) → V) :
    cyclicTripleCount f = linearTripleCount f + cyclicEndTripleCount f := by
  unfold cyclicTripleCount
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, linearTripleCount_eq_sum]
  unfold cyclicEndTripleCount
  simp only [cyclicTripleIndicator, finRotate_two_castSucc, finRotate_succ_castSucc]
  omega

theorem cyclicEndTripleCount_le_two {N : ℕ} (f : Fin (N + 3) → V) :
    cyclicEndTripleCount f ≤ 2 := by
  unfold cyclicEndTripleCount cyclicTripleIndicator
  split_ifs <;> omega

/-- Centering at the exact numbers of cyclic/open positions preserves the
same two-position error bound, since the missing expected contribution lies
in the interval [0,2] as well. -/
theorem cyclicTriple_centered_cut_error {N : ℕ} (f : Fin (N + 3) → V)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |((cyclicTripleCount f : ℝ) - ((N + 3 : ℕ) : ℝ) * p ^ 2) -
      ((linearTripleCount f : ℝ) - ((N + 1 : ℕ) : ℝ) * p ^ 2)| ≤ 2 := by
  have he : ((cyclicTripleCount f : ℝ) - ((N + 3 : ℕ) : ℝ) * p ^ 2) -
      ((linearTripleCount f : ℝ) - ((N + 1 : ℕ) : ℝ) * p ^ 2) =
      (cyclicEndTripleCount f : ℝ) - 2 * p ^ 2 := by
    rw [cyclicTripleCount_eq_linear_add_end]
    push_cast
    ring
  rw [he]
  have hbound : (cyclicEndTripleCount f : ℝ) ≤ 2 := by exact_mod_cast cyclicEndTripleCount_le_two f
  have hnonneg : (0 : ℝ) ≤ cyclicEndTripleCount f := Nat.cast_nonneg _
  have hp2 : p ^ 2 ≤ 1 := by nlinarith
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg p], by nlinarith [sq_nonneg p]⟩

theorem FiniteModel.cyclicWordWeight_cons {n N : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (s : Fin n) (w : Fin (N + 1) → Fin n) :
    FiniteModel.cyclicWordWeight P (Fin.cons s w) =
      linearPathWeight P s w * P (w (Fin.last N)) s := by
  unfold FiniteModel.cyclicWordWeight
  have hnext (t : Fin (N + 2)) :
      Fin.cons (α := fun _ => Fin n) s w (finRotate (N + 2) t) =
        Fin.snoc (α := fun _ => Fin n) w s t :=
    congrFun (Fin.snoc_eq_cons_rotate w s).symm t
  simp_rw [hnext]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.cons_last]
  rfl

theorem Tournament.realCriticalTransition_le_two_div {n : ℕ} (T : Tournament n) (i j : Fin n) :
    T.realCriticalTransition i j ≤ 2 / (n : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  nlinarith [T.real_sign_sq_le_one i j]

theorem Tournament.cyclicWordWeight_cons_le {n N : ℕ} (T : Tournament n)
    (s : Fin n) (w : Fin (N + 1) → Fin n) :
    FiniteModel.cyclicWordWeight T.realCriticalTransition (Fin.cons s w) ≤
      (2 / (n : ℝ)) * linearPathWeight T.realCriticalTransition s w := by
  rw [FiniteModel.cyclicWordWeight_cons]
  have hweight : 0 ≤ linearPathWeight T.realCriticalTransition s w :=
    Finset.prod_nonneg (fun _ _ => T.realCriticalTransition_nonneg _ _)
  exact (mul_le_mul_of_nonneg_left (T.realCriticalTransition_le_two_div _ _) hweight).trans_eq (mul_comm ..)

end
end Wormald
