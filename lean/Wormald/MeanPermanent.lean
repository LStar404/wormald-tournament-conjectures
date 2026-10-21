import Wormald.PermanentBound
import Wormald.BlockPermanent
import Wormald.BoolCubeAverage

/-!
# Independent internal edges and the weighted permanent

Only the independent internal-block law is used here. Complementary arc
indicators on one unordered edge are averaged together; their product is
zero, so replacing them by their two means increases the permanent.
-/

namespace Wormald.FiniteModel

noncomputable section
open Matrix
open scoped BigOperators

def replaceOppositePair {V : Type*} [DecidableEq V]
    (A : Matrix V V ℝ) (u v : V) (x : ℝ) : Matrix V V ℝ :=
  fun a b => if a = u ∧ b = v then x else
    if a = v ∧ b = u then 1 - x else A a b

private theorem oppositePair_product {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (u v : V) (huv : u ≠ v) (σ : Equiv.Perm V) (x : ℝ) :
    (∏ a, replaceOppositePair A u v x (σ a) a) =
      (if σ u = v then 1 - x else A (σ u) u) *
      (if σ v = u then x else A (σ v) v) *
      ∏ a ∈ (Finset.univ.erase u).erase v, A (σ a) a := by
  have hv : v ∈ Finset.univ.erase u := by simp [Ne.symm huv]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ u),
    ← Finset.mul_prod_erase _ _ hv]
  have hrest : (∏ a ∈ (Finset.univ.erase u).erase v,
      replaceOppositePair A u v x (σ a) a) =
      ∏ a ∈ (Finset.univ.erase u).erase v, A (σ a) a := by
    apply Finset.prod_congr rfl
    intro a ha
    have hav : a ≠ v := (Finset.mem_erase.mp ha).1
    have hau : a ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    simp [replaceOppositePair, hau, hav]
  rw [hrest]
  simp [replaceOppositePair, huv, Ne.symm huv, mul_assoc]

/-- A fair orientation of a single unordered edge is bounded by replacing
both opposite arc indicators by 1/2. This is valid despite their dependence. -/
theorem permanent_oppositePair_average_le {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : ∀ a b, 0 ≤ A a b) (u v : V) (huv : u ≠ v) :
    ((replaceOppositePair A u v 0).permanent +
      (replaceOppositePair A u v 1).permanent) / 2 ≤
      (replaceOppositePair A u v (1 / 2)).permanent := by
  have hterm (σ : Equiv.Perm V) :
      ((∏ a, replaceOppositePair A u v 0 (σ a) a) +
        (∏ a, replaceOppositePair A u v 1 (σ a) a)) / 2 ≤
        ∏ a, replaceOppositePair A u v (1 / 2) (σ a) a := by
    rw [oppositePair_product A u v huv σ 0, oppositePair_product A u v huv σ 1,
      oppositePair_product A u v huv σ (1 / 2)]
    have hP : 0 ≤ ∏ a ∈ (Finset.univ.erase u).erase v, A (σ a) a :=
      Finset.prod_nonneg (fun a _ => hA (σ a) a)
    by_cases h₁ : σ u = v <;> by_cases h₂ : σ v = u <;>
      simp [h₁, h₂] <;> nlinarith
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Equiv.Perm V)))
    (fun σ _ => hterm σ)
  rw [← Finset.sum_div, Finset.sum_add_distrib] at hsum
  exact hsum

abbrev InternalEdge (d m : ℕ) := Fin d × Edge m

def internalTail {d m : ℕ} (e : InternalEdge d m) : Fin d × Fin m := (e.1, e.2.1.1)

def internalHead {d m : ℕ} (e : InternalEdge d m) : Fin d × Fin m := (e.1, e.2.1.2)

theorem internalTail_ne_head {d m : ℕ} (e : InternalEdge d m) :
    internalTail e ≠ internalHead e := by
  intro h
  exact e.2.2.ne (congrArg Prod.snd h)

/-- The independent-edge matrix at arbitrary internal edge probabilities.
Its diagonal is zero; probabilities are assigned to unordered edges once. -/
def internalProbabilityMatrix {d m : ℕ} (base : Orientation d)
    (p : InternalEdge d m → ℝ) : Matrix (Fin d × Fin m) (Fin d × Fin m) ℝ :=
  fun v w => if v.1 = w.1 then
    if h : v.2 < w.2 then p (v.1, ⟨(v.2, w.2), h⟩) else
      if h : w.2 < v.2 then 1 - p (v.1, ⟨(w.2, v.2), h⟩) else 0
    else if arc base v.1 w.1 = true then 1 else 0

theorem internalProbabilityMatrix_nonneg {d m : ℕ} (base : Orientation d)
    (p : InternalEdge d m → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
    ∀ v w, 0 ≤ internalProbabilityMatrix base p v w := by
  intro v w
  unfold internalProbabilityMatrix
  split_ifs
  · exact (hp _).1
  · exact sub_nonneg.mpr (hp _).2
  · norm_num
  · norm_num
  · norm_num

theorem internalProbabilityMatrix_update {d m : ℕ} (base : Orientation d)
    (p : InternalEdge d m → ℝ) (e : InternalEdge d m) (x : ℝ) :
    internalProbabilityMatrix base (Function.update p e x) =
      replaceOppositePair (internalProbabilityMatrix base p) (internalTail e) (internalHead e) x := by
  ext v w
  have hlt := e.2.2
  by_cases hforward : v = internalTail e ∧ w = internalHead e
  · rcases hforward with ⟨rfl, rfl⟩
    simp [internalProbabilityMatrix, replaceOppositePair, internalTail, internalHead, hlt]
  by_cases hreverse : v = internalHead e ∧ w = internalTail e
  · rcases hreverse with ⟨rfl, rfl⟩
    simp [internalProbabilityMatrix, replaceOppositePair, internalTail, internalHead,
      hlt, not_lt_of_gt hlt, hlt.ne, hlt.ne']
  simp only [replaceOppositePair, hforward, hreverse, ite_false]
  by_cases hb : v.1 = w.1
  · by_cases hvw : v.2 < w.2
    · have hk : (v.1, (⟨(v.2, w.2), hvw⟩ : Edge m)) ≠ e := by
        intro h
        apply hforward
        have hbase := congrArg (fun a : InternalEdge d m => a.1) h
        have htail := congrArg (fun a : InternalEdge d m => a.2.1.1) h
        have hhead := congrArg (fun a : InternalEdge d m => a.2.1.2) h
        exact ⟨Prod.ext hbase htail, Prod.ext (hb.symm.trans hbase) hhead⟩
      have hk' : (w.1, (⟨(v.2, w.2), hvw⟩ : Edge m)) ≠ e := by
        simpa only [hb] using hk
      simp [internalProbabilityMatrix, hb, hvw, Function.update, hk']
    · by_cases hwv : w.2 < v.2
      · have hk : (v.1, (⟨(w.2, v.2), hwv⟩ : Edge m)) ≠ e := by
          intro h
          apply hreverse
          have hbase := congrArg (fun a : InternalEdge d m => a.1) h
          have htail := congrArg (fun a : InternalEdge d m => a.2.1.1) h
          have hhead := congrArg (fun a : InternalEdge d m => a.2.1.2) h
          exact ⟨Prod.ext hbase hhead, Prod.ext (hb.symm.trans hbase) htail⟩
        have hk' : (w.1, (⟨(w.2, v.2), hwv⟩ : Edge m)) ≠ e := by
          simpa only [hb] using hk
        simp [internalProbabilityMatrix, hb, hvw, hwv, Function.update, hk']
      · simp [internalProbabilityMatrix, hb, hvw, hwv]
  · simp [internalProbabilityMatrix, hb]

theorem internalProbabilityMatrix_permanent_midpoint {d m : ℕ} (base : Orientation d)
    (p : InternalEdge d m → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (e : InternalEdge d m) :
    ((internalProbabilityMatrix base (Function.update p e 0)).permanent +
      (internalProbabilityMatrix base (Function.update p e 1)).permanent) / 2 ≤
      (internalProbabilityMatrix base (Function.update p e (1 / 2))).permanent := by
  rw [internalProbabilityMatrix_update, internalProbabilityMatrix_update,
    internalProbabilityMatrix_update]
  exact permanent_oppositePair_average_le _ (internalProbabilityMatrix_nonneg base p hp)
    _ _ (internalTail_ne_head e)

/-- Flatten the independent block samples into their independent unordered edges. -/
def independentSampleEquiv (d m : ℕ) : IndependentSample d m ≃ (InternalEdge d m → Bool) where
  toFun blocks e := blocks e.1 e.2
  invFun b i e := b (i, e)
  left_inv _ := rfl
  right_inv _ := rfl

theorem internalProbabilityMatrix_endpoint {d m : ℕ} (base : Orientation d)
    (b : InternalEdge d m → Bool) :
    internalProbabilityMatrix base (fun e => if b e then 1 else 0) =
      fun v w => ((arcMatrix (blowupArc base ((independentSampleEquiv d m).symm b)) v w : ℕ) : ℝ) := by
  ext v w
  by_cases hb : v.1 = w.1
  · by_cases hvw : v.2 < w.2
    · simp [internalProbabilityMatrix, arcMatrix, blowupArc, arc, independentSampleEquiv,
        hb, hvw]
    · by_cases hwv : w.2 < v.2
      · simp only [internalProbabilityMatrix, hb, ite_true, hvw, dite_false, hwv, dite_true,
          arcMatrix, blowupArc, arc, independentSampleEquiv, Equiv.coe_fn_symm_mk]
        cases b (w.1, ⟨(w.2, v.2), hwv⟩) <;> simp
      · simp [internalProbabilityMatrix, arcMatrix, blowupArc, arc,
          hb, hvw, hwv]
  · simp [internalProbabilityMatrix, arcMatrix, blowupArc, hb]

theorem permanent_natCast_real {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℕ) : ((A.permanent : ℕ) : ℝ) =
      Matrix.permanent ((fun v w => (A v w : ℝ)) : Matrix V V ℝ) := by
  simp only [Matrix.permanent, Nat.cast_sum, Nat.cast_prod]

/-- The actual independent mean, before the diagonal is enlarged. -/
theorem expectedPermanent_le_internalMidpoint {d : ℕ} (base : Orientation d) (m : ℕ) :
    (expectedPermanent base m : ℝ) ≤
      (internalProbabilityMatrix base (fun _ => 1 / 2 : InternalEdge d m → ℝ)).permanent := by
  have hmean := boolCube_average_le_midpoint
    (fun p : InternalEdge d m → ℝ => (internalProbabilityMatrix base p).permanent)
    (fun p hp e => internalProbabilityMatrix_permanent_midpoint base p hp e)
  have hterms (b : InternalEdge d m → Bool) :
      (internalProbabilityMatrix base (fun e => if b e then 1 else 0)).permanent =
        (((arcMatrix (blowupArc base ((independentSampleEquiv d m).symm b))).permanent : ℕ) : ℝ) := by
    rw [internalProbabilityMatrix_endpoint, permanent_natCast_real]
  simp only [hterms] at hmean
  have hsum := Fintype.sum_equiv (independentSampleEquiv d m)
    (fun blocks : IndependentSample d m =>
      (((arcMatrix (blowupArc base blocks)).permanent : ℕ) : ℝ))
    (fun b : InternalEdge d m → Bool =>
      (((arcMatrix (blowupArc base ((independentSampleEquiv d m).symm b))).permanent : ℕ) : ℝ))
    (by intro blocks; simp)
  rw [← hsum, ← Fintype.card_congr (independentSampleEquiv d m)] at hmean
  convert hmean using 1
  simp only [expectedPermanent, uniformMean, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]

/-- Base weights including 1/2 on the block diagonal. These diagonal entries
are an upper bound; the underlying tournaments still have no loops. -/
def weightedBase {d : ℕ} (base : Orientation d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => if i = j then 1 / 2 else if arc base i j = true then 1 else 0

theorem weightedBase_nonneg {d : ℕ} (base : Orientation d) :
    ∀ i j, 0 ≤ weightedBase base i j := by
  intro i j
  unfold weightedBase
  split_ifs <;> norm_num

theorem internalMidpoint_le_blockConstant {d : ℕ} (base : Orientation d) (m : ℕ) :
    ∀ v w, internalProbabilityMatrix base (fun _ => 1 / 2) v w ≤
      blockConstantMatrix (weightedBase base) m v w := by
  intro v w
  unfold internalProbabilityMatrix blockConstantMatrix weightedBase
  simp only [Matrix.of_apply]
  split_ifs <;> norm_num

theorem permanent_mono_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Matrix V V ℝ) (hA : ∀ v w, 0 ≤ A v w) (hAB : ∀ v w, A v w ≤ B v w) :
    A.permanent ≤ B.permanent := by
  unfold Matrix.permanent
  apply Finset.sum_le_sum
  intro σ _
  exact Finset.prod_le_prod₀ (fun v _ => hA (σ v) v) (fun v _ => hAB (σ v) v)

/-- Averaging the actual independent model is bounded by its block-constant
weighted permanent. No assertion of this kind is made for regular blocks. -/
theorem expectedPermanent_le_blockConstant {d : ℕ} (base : Orientation d) (m : ℕ) :
    (expectedPermanent base m : ℝ) ≤ (blockConstantMatrix (weightedBase base) m).permanent := by
  apply (expectedPermanent_le_internalMidpoint base m).trans
  exact permanent_mono_nonneg _ _
    (internalProbabilityMatrix_nonneg base _ (by intro e; norm_num))
    (internalMidpoint_le_blockConstant base m)

theorem expectedCycles_le_blockConstant {d : ℕ} (base : Orientation d) (m : ℕ) :
    (expectedCycles base m : ℝ) ≤ (blockConstantMatrix (weightedBase base) m).permanent := by
  exact (show (expectedCycles base m : ℝ) ≤ (expectedPermanent base m : ℝ) by
    exact_mod_cast expectedCycles_le_expectedPermanent base m).trans
    (expectedPermanent_le_blockConstant base m)

theorem expectedCycles_le_factorial_rowSum {d : ℕ} (base : Orientation d) (m : ℕ) :
    (expectedCycles base m : ℝ) ≤
      (Nat.factorial m : ℝ) ^ d * ∏ i, (∑ j, weightedBase base i j) ^ m :=
  (expectedCycles_le_blockConstant base m).trans
    (blockConstantMatrix_permanent_le (weightedBase base) (weightedBase_nonneg base) m)

end
end Wormald.FiniteModel
