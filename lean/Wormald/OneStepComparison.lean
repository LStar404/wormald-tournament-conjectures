import Wormald.MomentComparison
import Wormald.MergeWeights

namespace Wormald

noncomputable section
open Matrix Finset

private def finsetComplEquiv {n : ℕ} (S : Finset (Fin n)) : ↥(Sᶜ : Finset (Fin n)) ⊕ ↥S ≃ Fin n where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun v := if hv : v ∈ S then Sum.inr ⟨v, hv⟩ else Sum.inl ⟨v, by simpa using hv⟩
  left_inv v := by
    rcases v with v | v
    · have hv : v.val ∉ S := Finset.mem_compl.mp v.property
      simp [hv]
    · simp [v.property]
  right_inv v := by dsimp; split_ifs <;> rfl

private theorem sum_finset_enum {n : ℕ} (S : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ i : Fin S.card, f ((S.equivFin.symm i).val)) = ∑ i ∈ S, f i := by
  calc
    _ = ∑ v : S, f v.val := Equiv.sum_comp S.equivFin.symm (fun v : S => f v.val)
    _ = _ := by simpa only [Finset.sum_coe_sort_eq_attach] using (Finset.sum_attach S f)

/-- The full sharp one-step signed-subset bound, with the source's explicit prefix
weights. Every hypothesis is an actual entry condition on A or sign condition on ε. -/
theorem signed_subset_mulVec_le_comparisonWeights {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (S : Finset (Fin n)) (ε x : Fin n → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hx : ∀ i, 0 ≤ x i) :
    (∑ i ∈ S, ε i * (A *ᵥ x) i) ≤
      ∑ j : Fin n, comparisonWeights n S.card j * sortedAbs x j := by
  let y : Fin S.card → ℝ := fun i => x ((S.equivFin.symm i).val)
  let η : Fin S.card → ℝ := fun i => ε ((S.equivFin.symm i).val)
  let p : Equiv.Perm (Fin S.card) := descendingPermutation (fun i => |y i|)
  let e : Fin (Sᶜ).card ⊕ Fin S.card ≃ Fin n :=
    (Equiv.sumCongr (Sᶜ).equivFin.symm (p.trans S.equivFin.symm)).trans (finsetComplEquiv S)
  have hcard : (Sᶜ).card + S.card = n := by
    simp
  have hselected : ∀ i : Fin S.card, sortedAbs y i = x (e (Sum.inr i)) := by
    intro i
    change |x ((S.equivFin.symm (p i)).val)| = x ((S.equivFin.symm (p i)).val)
    exact abs_of_nonneg (hx _)
  have hout : (∑ i : Fin (Sᶜ).card, x (e (Sum.inl i))) = ∑ i ∈ Sᶜ, x i := by
    change (∑ i : Fin (Sᶜ).card, x (((Sᶜ).equivFin.symm i).val)) = _
    exact sum_finset_enum Sᶜ x
  have hinternal := half_sum_abs_signed_cross_le η y
    (fun i => hε ((S.equivFin.symm i).val))
  have hinner_sum : (∑ i : Fin S.card, ∑ j : Fin S.card, |η i * y j - η j * y i|) =
      ∑ i ∈ S, ∑ j ∈ S, |ε i * x j - ε j * x i| := by
    change (∑ i : Fin S.card, ∑ j : Fin S.card,
      |ε ((S.equivFin.symm i).val) * x ((S.equivFin.symm j).val) -
        ε ((S.equivFin.symm j).val) * x ((S.equivFin.symm i).val)|) = _
    calc
      _ = ∑ i : Fin S.card, ∑ j ∈ S,
          |ε ((S.equivFin.symm i).val) * x j - ε j * x ((S.equivFin.symm i).val)| := by
        apply Finset.sum_congr rfl
        intro i hi
        exact sum_finset_enum S (fun j =>
          |ε ((S.equivFin.symm i).val) * x j - ε j * x ((S.equivFin.symm i).val)|)
      _ = _ := sum_finset_enum S (fun i => ∑ j ∈ S, |ε i * x j - ε j * x i|)
  rw [hinner_sum] at hinternal
  have hsignbound : ∀ i, |ε i| ≤ 1 := by
    intro i
    rcases hε i with hi | hi <;> simp [hi]
  have hsource := signed_subset_mulVec_le A hskew hbound S ε x hsignbound hx
  have hmerge := concat_pairCoefficients_le hcard e x
  rw [hout] at hmerge
  simp_rw [← hselected] at hmerge
  exact hsource.trans ((add_le_add_right hinternal _).trans (by linarith [hmerge]))

private def outputSign (y : ℝ) : ℝ := if 0 ≤ y then 1 else -1

private theorem outputSign_mul (y : ℝ) : outputSign y * y = |y| := by
  by_cases hy : 0 ≤ y
  · simp [outputSign, hy, abs_of_nonneg hy]
  · simp [outputSign, hy, abs_of_neg (lt_of_not_ge hy)]

/-- Fang–Huang's sharp one-step subset inequality for nonnegative inputs.
Taking S to be the positions of the r largest outputs gives the weak-majorization
form of Lemma 3.3. The inequality is proved for all real skew matrices in [-1,1]. -/
theorem subset_abs_mulVec_le_comparisonWeights_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (S : Finset (Fin n)) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ i ∈ S, |(A *ᵥ x) i|) ≤
      ∑ j : Fin n, comparisonWeights n S.card j * sortedAbs x j := by
  have hε : ∀ i, outputSign ((A *ᵥ x) i) = 1 ∨ outputSign ((A *ᵥ x) i) = -1 := by
    intro i
    unfold outputSign
    split_ifs <;> simp
  have h := signed_subset_mulVec_le_comparisonWeights A hskew hbound S
    (fun i => outputSign ((A *ᵥ x) i)) x hε hx
  simpa only [outputSign_mul] using h

private theorem outputSign_abs (y : ℝ) : outputSign y * |y| = y := by
  by_cases hy : 0 ≤ y
  · simp [outputSign, hy, abs_of_nonneg hy]
  · simp [outputSign, hy, abs_of_neg (lt_of_not_ge hy)]

private theorem abs_outputSign (y : ℝ) : |outputSign y| = 1 := by
  unfold outputSign
  split_ifs <;> norm_num

/-- The complete one-step bound for arbitrary real input. Diagonal switching
reduces to nonnegative input and preserves the actual skew and entry conditions. -/
theorem subset_abs_mulVec_le_comparisonWeights {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A j i = -A i j) (hbound : ∀ i j, |A i j| ≤ 1)
    (S : Finset (Fin n)) (x : Fin n → ℝ) :
    (∑ i ∈ S, |(A *ᵥ x) i|) ≤
      ∑ j : Fin n, comparisonWeights n S.card j * sortedAbs x j := by
  let B : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => outputSign (x i) * A i j * outputSign (x j)
  have hBskew : ∀ i j, B j i = -B i j := by
    intro i j
    dsimp [B]
    rw [hskew]
    ring
  have hBbound : ∀ i j, |B i j| ≤ 1 := by
    intro i j
    simpa only [B, abs_mul, abs_outputSign, one_mul, mul_one] using hbound i j
  have hBvalue : ∀ i, (B *ᵥ (fun j => |x j|)) i =
      outputSign (x i) * (A *ᵥ x) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [B]
    calc
      _ = outputSign (x i) * A i j * (outputSign (x j) * |x j|) := by ring
      _ = _ := by rw [outputSign_abs]; ring
  have hBabs : ∀ i, |(B *ᵥ (fun j => |x j|)) i| = |(A *ᵥ x) i| := by
    intro i
    rw [hBvalue, abs_mul, abs_outputSign, one_mul]
  have hsort : sortedAbs (fun j => |x j|) = sortedAbs x := by
    unfold sortedAbs
    simp only [abs_abs]
  have h := subset_abs_mulVec_le_comparisonWeights_nonneg B hBskew hBbound S
    (fun j => |x j|) (fun j => abs_nonneg _)
  simpa only [hBabs, hsort] using h

end
end Wormald


