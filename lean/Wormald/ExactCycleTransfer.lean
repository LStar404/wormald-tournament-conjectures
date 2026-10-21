import Wormald.MeanPermanent

/-!
# Exact independent Hamilton-cycle transfer

The actual sample mean equals the weighted sum over single-orbit successor
permutations. Opposite arc indicators remain coupled throughout this proof.
The order assumption excludes the only obstruction: a two-cycle using both
directions of the same unordered edge.
-/

namespace Wormald.FiniteModel
noncomputable section
open Matrix
open scoped BigOperators

def SingleOrbit {V : Type*} [Fintype V] (σ : Equiv.Perm V) : Prop :=
  ∀ v w, ∃ k : Fin (Fintype.card V), (σ^[k.val]) v = w

def weightedHamiltonianCycleSum {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) : ℝ := by
  classical
  exact ∑ σ : Equiv.Perm V, if SingleOrbit σ then ∏ v, A v (σ v) else 0

theorem singleOrbit_no_twoCycle {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 3 ≤ Fintype.card V) (σ : Equiv.Perm V) (hσ : SingleOrbit σ) (u v : V) :
    ¬ (σ u = v ∧ σ v = u) := by
  rintro ⟨hu, hv⟩
  have horbit (k : ℕ) : (σ^[k]) u = u ∨ (σ^[k]) u = v := by
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        rcases ih with h | h
        · rw [h, hu]
          exact Or.inr rfl
        · rw [h, hv]
          exact Or.inl rfl
  have hcover : (Finset.univ : Finset V) ⊆ {u, v} := by
    intro w _
    obtain ⟨k, hk⟩ := hσ u w
    rcases horbit k.val with h | h
    · simp [← hk, h]
    · simp [← hk, h]
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_le_two (a := u) (b := v))
  simp only [Finset.card_univ] at hcard
  omega

theorem singleOrbit_no_fixedPoint {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 3 ≤ Fintype.card V) (σ : Equiv.Perm V) (hσ : SingleOrbit σ) (v : V) :
    σ v ≠ v := by
  intro h
  exact singleOrbit_no_twoCycle hV σ hσ v v ⟨h, h⟩

/-- The existing successor-permutation convention agrees exactly with its
0/1 weighted sum, without a cyclic rotation factor. -/
theorem hamiltonCycleCount_eq_weightedSum {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → V → Bool) : (hamiltonCycleCount a : ℝ) =
      weightedHamiltonianCycleSum (fun v w => if a v w = true then 1 else 0) := by
  classical
  rw [hamiltonCycleCount_eq_sum]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, weightedHamiltonianCycleSum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases horbit : SingleOrbit σ
  · by_cases harcs : ∀ v, a v (σ v) = true
    · have hham : IsHamiltonCycle a σ := ⟨horbit, harcs⟩
      simp [horbit, hham, harcs]
    · have hham : ¬ IsHamiltonCycle a σ := fun h => harcs h.2
      obtain ⟨v, hv⟩ := not_forall.mp harcs
      simp only [horbit, hham, ite_true, ite_false]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])
  · have hham : ¬ IsHamiltonCycle a σ := fun h => horbit h.1
    simp [horbit, hham]

private theorem oppositePair_rowProduct {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (u v : V) (huv : u ≠ v) (σ : Equiv.Perm V) (x : ℝ) :
    (∏ a, replaceOppositePair A u v x a (σ a)) =
      (if σ u = v then x else A u (σ u)) *
      (if σ v = u then 1 - x else A v (σ v)) *
      ∏ a ∈ (Finset.univ.erase u).erase v, A a (σ a) := by
  have hv : v ∈ Finset.univ.erase u := by simp [Ne.symm huv]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ u),
    ← Finset.mul_prod_erase _ _ hv]
  have hrest : (∏ a ∈ (Finset.univ.erase u).erase v,
      replaceOppositePair A u v x a (σ a)) =
      ∏ a ∈ (Finset.univ.erase u).erase v, A a (σ a) := by
    apply Finset.prod_congr rfl
    intro a ha
    have hav : a ≠ v := (Finset.mem_erase.mp ha).1
    have hau : a ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    simp [replaceOppositePair, hau, hav]
  rw [hrest]
  simp [replaceOppositePair, huv, Ne.symm huv, mul_assoc]

/-- A single orbit on at least three vertices uses an unordered edge at most
once. Consequently its exact orientation average equals the midpoint value. -/
theorem weightedHamiltonianCycleSum_oppositePair_average {V : Type*}
    [Fintype V] [DecidableEq V] (hV : 3 ≤ Fintype.card V)
    (A : Matrix V V ℝ) (u v : V) (huv : u ≠ v) :
    (weightedHamiltonianCycleSum (replaceOppositePair A u v 0) +
      weightedHamiltonianCycleSum (replaceOppositePair A u v 1)) / 2 =
      weightedHamiltonianCycleSum (replaceOppositePair A u v (1 / 2)) := by
  classical
  have hterm (σ : Equiv.Perm V) :
      ((if SingleOrbit σ then ∏ a, replaceOppositePair A u v 0 a (σ a) else 0) +
        (if SingleOrbit σ then ∏ a, replaceOppositePair A u v 1 a (σ a) else 0)) / 2 =
        if SingleOrbit σ then ∏ a, replaceOppositePair A u v (1 / 2) a (σ a) else 0 := by
    by_cases horbit : SingleOrbit σ
    · simp only [horbit, ite_true]
      rw [oppositePair_rowProduct A u v huv σ 0, oppositePair_rowProduct A u v huv σ 1,
        oppositePair_rowProduct A u v huv σ (1 / 2)]
      have hnot := singleOrbit_no_twoCycle hV σ horbit u v
      by_cases h₁ : σ u = v <;> by_cases h₂ : σ v = u <;>
        simp_all <;> ring
    · simp [horbit]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Equiv.Perm V))) rfl
    (fun σ _ => hterm σ)
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hsum
  exact hsum

theorem weightedHamiltonianCycleSum_internal_midpoint {d m : ℕ}
    (hN : 3 ≤ d * m) (base : Orientation d) (p : InternalEdge d m → ℝ)
    (e : InternalEdge d m) :
    (weightedHamiltonianCycleSum (internalProbabilityMatrix base (Function.update p e 0)) +
      weightedHamiltonianCycleSum (internalProbabilityMatrix base (Function.update p e 1))) / 2 =
      weightedHamiltonianCycleSum (internalProbabilityMatrix base (Function.update p e (1 / 2))) := by
  rw [internalProbabilityMatrix_update, internalProbabilityMatrix_update,
    internalProbabilityMatrix_update]
  apply weightedHamiltonianCycleSum_oppositePair_average
  · simpa using hN
  · exact internalTail_ne_head e

private theorem boolCube_average_eq_midpoint {K : Type*} [Fintype K] [DecidableEq K]
    (F : (K → ℝ) → ℝ)
    (hF : ∀ p : K → ℝ, ∀ k : K,
      (F (Function.update p k 0) + F (Function.update p k 1)) / 2 =
        F (Function.update p k (1 / 2))) :
    (∑ b : K → Bool, F (fun k => if b k then 1 else 0)) /
      (Fintype.card (K → Bool) : ℝ) = F (fun _ => 1 / 2) := by
  apply le_antisymm
  · exact boolCube_average_le_midpoint F (fun p _ k => (hF p k).le)
  · have hminus := boolCube_average_le_midpoint (fun p => -F p) (by
      intro p _ k
      have h := hF p k
      linarith)
    simp only [Finset.sum_neg_distrib, neg_div] at hminus
    exact neg_le_neg_iff.mp hminus

/-- Exact transfer from the actual independent finite sample space to a
weighted single-orbit sum. No independence of opposite arcs is assumed. -/
theorem expectedCycles_eq_internalWeightedSum {d : ℕ} (base : Orientation d)
    (m : ℕ) (hN : 3 ≤ d * m) :
    (expectedCycles base m : ℝ) =
      weightedHamiltonianCycleSum (internalProbabilityMatrix base (fun _ : InternalEdge d m => 1 / 2)) := by
  have hmean := boolCube_average_eq_midpoint
    (fun p : InternalEdge d m → ℝ => weightedHamiltonianCycleSum (internalProbabilityMatrix base p))
    (weightedHamiltonianCycleSum_internal_midpoint hN base)
  have hterms (b : InternalEdge d m → Bool) :
      weightedHamiltonianCycleSum (internalProbabilityMatrix base (fun e => if b e then 1 else 0)) =
        (hamiltonCycleCount (blowupArc base ((independentSampleEquiv d m).symm b)) : ℝ) := by
    rw [internalProbabilityMatrix_endpoint, hamiltonCycleCount_eq_weightedSum]
    congr 1
    funext v w
    simp [arcMatrix]
  simp only [hterms] at hmean
  have hsum := Fintype.sum_equiv (independentSampleEquiv d m)
    (fun blocks : IndependentSample d m =>
      (hamiltonCycleCount (blowupArc base blocks) : ℝ))
    (fun b : InternalEdge d m → Bool =>
      (hamiltonCycleCount (blowupArc base ((independentSampleEquiv d m).symm b)) : ℝ))
    (by intro blocks; simp)
  rw [← hsum, ← Fintype.card_congr (independentSampleEquiv d m)] at hmean
  convert hmean using 1
  simp only [expectedCycles, uniformMean, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]

theorem weightedHamiltonianCycleSum_congr_offDiagonal {V : Type*}
    [Fintype V] [DecidableEq V] (hV : 3 ≤ Fintype.card V)
    (A B : Matrix V V ℝ) (hAB : ∀ v w, v ≠ w → A v w = B v w) :
    weightedHamiltonianCycleSum A = weightedHamiltonianCycleSum B := by
  classical
  unfold weightedHamiltonianCycleSum
  apply Finset.sum_congr rfl
  intro σ _
  by_cases horbit : SingleOrbit σ
  · simp only [horbit, ite_true]
    apply Finset.prod_congr rfl
    intro v _
    exact hAB v (σ v) (singleOrbit_no_fixedPoint hV σ horbit v).symm
  · simp [horbit]

theorem internalMidpoint_eq_blockConstant_offDiagonal {d m : ℕ}
    (base : Orientation d) (v w : Fin d × Fin m) (hvw : v ≠ w) :
    internalProbabilityMatrix base (fun _ => 1 / 2) v w =
      blockConstantMatrix (weightedBase base) m v w := by
  by_cases hb : v.1 = w.1
  · have hi : v.2 ≠ w.2 := fun h => hvw (Prod.ext hb h)
    rcases lt_or_gt_of_ne hi with h | h
    · simp [internalProbabilityMatrix, blockConstantMatrix, weightedBase, hb, h]
    · simp [internalProbabilityMatrix, blockConstantMatrix, weightedBase, hb, h, not_lt_of_gt h]
      norm_num
  · simp [internalProbabilityMatrix, blockConstantMatrix, weightedBase, hb]

/-- The exact weighted Hamilton-cycle formula for the original independent
model. The diagonal 1/2 in the block matrix is never visited by a Hamilton cycle. -/
theorem expectedCycles_eq_weightedHamiltonianCycleSum {d : ℕ} (base : Orientation d)
    (m : ℕ) (hN : 3 ≤ d * m) :
    (expectedCycles base m : ℝ) =
      weightedHamiltonianCycleSum (blockConstantMatrix (weightedBase base) m) := by
  rw [expectedCycles_eq_internalWeightedSum base m hN]
  apply weightedHamiltonianCycleSum_congr_offDiagonal
  · simpa using hN
  · exact internalMidpoint_eq_blockConstant_offDiagonal base

end
end Wormald.FiniteModel
