import Wormald.BernoulliPairConcentration

namespace Wormald

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def adjacentSuccessCount : {N : ℕ} → (Fin N → Bool) → ℕ
  | 0, _ => 0
  | 1, _ => 0
  | _N + 2, b => (if b 0 && b 1 then 1 else 0) + adjacentSuccessCount (Fin.tail b)

def adjacentCenteredValue (p : ℝ) {N : ℕ} (b : Fin (N + 1) → Bool) : ℝ :=
  (adjacentSuccessCount b : ℝ) - (N : ℝ) * p ^ 2

theorem adjacentSuccessCount_eq_paired {N : ℕ} (b : Fin (N + 1) → Bool) :
    adjacentSuccessCount b = pairedSuccessCount b + pairedSuccessCount (Fin.tail b) := by
  induction N with
  | zero => simp [adjacentSuccessCount, pairedSuccessCount]
  | succ N ih =>
    rw [adjacentSuccessCount, pairedSuccessCount, ih (Fin.tail b)]
    omega

theorem adjacentCenteredValue_eq_paired (p : ℝ) {N : ℕ} (b : Fin (N + 1) → Bool) :
    adjacentCenteredValue p b = pairedCenteredValue p b + pairedCenteredValue p (Fin.tail b) := by
  rw [adjacentCenteredValue, adjacentSuccessCount_eq_paired]
  unfold pairedCenteredValue
  have hc : (N + 1) / 2 + N / 2 = N := by omega
  have hcR : (((N + 1) / 2 : ℕ) : ℝ) + ((N / 2 : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hc
  push_cast
  nlinarith

theorem bernoulli_tail_observable_sum (p : ℝ) (N : ℕ) (F : (Fin N → Bool) → ℝ) :
    (∑ b : Fin (N + 1) → Bool, bernoulliProductMass p b * F (Fin.tail b)) =
      ∑ b : Fin N → Bool, bernoulliProductMass p b * F b := by
  rw [sum_fin_succ_function]
  simp only [bernoulliProductMass_cons, Fin.tail_cons, mul_assoc]
  simp_rw [← Finset.mul_sum]
  simp [bernoulliMass]
  ring

theorem finiteAbsTailMass_add_le {Ω : Type*} [Fintype Ω] (w X Y : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (a b : ℝ) :
    finiteAbsTailMass w (fun ω => X ω + Y ω) (a + b) ≤
      finiteAbsTailMass w X a + finiteAbsTailMass w Y b := by
  unfold finiteAbsTailMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  have hx0 : 0 ≤ if a ≤ |X ω| then w ω else 0 := by split_ifs <;> linarith [hw ω]
  have hy0 : 0 ≤ if b ≤ |Y ω| then w ω else 0 := by split_ifs <;> linarith [hw ω]
  by_cases h : a + b ≤ |X ω + Y ω|
  · simp only [ite_eq_left h]
    by_cases hx : a ≤ |X ω|
    · simp only [ite_eq_left hx]
      linarith
    · have hy : b ≤ |Y ω| := by
        have hh := abs_add_le (X ω) (Y ω)
        have hhx := lt_of_not_ge hx
        linarith
      simp only [ite_eq_left hy]
      linarith
  · simp only [ite_eq_right h]
    exact add_nonneg hx0 hy0

/-- The adjacent holding-pair count splits into its even and odd starting
positions. A finite union bound gives its explicit exponential concentration. -/
theorem adjacentCentered_abs_tail_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    finiteAbsTailMass (fun b : Fin (N + 1) → Bool => bernoulliProductMass p b)
      (adjacentCenteredValue p) (δ * ((N + 1 : ℕ) : ℝ)) ≤
        4 * Real.exp (-δ ^ 2 * (N : ℝ) / 2) := by
  let A := δ / 2 * ((N + 1 : ℕ) : ℝ)
  have hfirst : finiteAbsTailMass (fun b : Fin (N + 1) → Bool => bernoulliProductMass p b)
      (pairedCenteredValue p) A ≤ 2 * Real.exp (-2 * (δ / 2) ^ 2 * (N : ℝ)) := by
    apply (pairedCentered_abs_tail_le p hp0 hp1 (N + 1) (δ / 2) (by positivity)).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
    push_cast
    nlinarith [sq_nonneg (δ / 2)]
  have hsecond : finiteAbsTailMass (fun b : Fin (N + 1) → Bool => bernoulliProductMass p b)
      (fun b => pairedCenteredValue p (Fin.tail b)) A ≤
        2 * Real.exp (-2 * (δ / 2) ^ 2 * (N : ℝ)) := by
    have hmarg := bernoulli_tail_observable_sum p N
      (fun b => if A ≤ |pairedCenteredValue p b| then (1 : ℝ) else 0)
    have heq : finiteAbsTailMass (fun b : Fin (N + 1) → Bool => bernoulliProductMass p b)
        (fun b => pairedCenteredValue p (Fin.tail b)) A =
        finiteAbsTailMass (fun b : Fin N → Bool => bernoulliProductMass p b) (pairedCenteredValue p) A := by
      simpa only [mul_ite, mul_one, mul_zero, finiteAbsTailMass] using hmarg
    rw [heq]
    apply (finiteTailMass_antitone (fun b : Fin N → Bool => bernoulliProductMass p b)
      (fun b => |pairedCenteredValue p b|) (bernoulliProductMass_nonneg p hp0 hp1)
        (δ / 2 * (N : ℝ)) A (by dsimp [A]; push_cast; nlinarith)).trans
    exact pairedCentered_abs_tail_le p hp0 hp1 N (δ / 2) (by positivity)
  have hsplit : finiteAbsTailMass (fun b : Fin (N + 1) → Bool => bernoulliProductMass p b)
      (adjacentCenteredValue p) (δ * ((N + 1 : ℕ) : ℝ)) ≤
      finiteAbsTailMass (fun b : Fin (N + 1) → Bool => bernoulliProductMass p b) (pairedCenteredValue p) A +
        finiteAbsTailMass (fun b : Fin (N + 1) → Bool => bernoulliProductMass p b)
          (fun b => pairedCenteredValue p (Fin.tail b)) A := by
    have hfun : (adjacentCenteredValue p : (Fin (N + 1) → Bool) → ℝ) =
        fun b => pairedCenteredValue p b + pairedCenteredValue p (Fin.tail b) :=
      funext (adjacentCenteredValue_eq_paired p)
    rw [hfun, show δ * ((N + 1 : ℕ) : ℝ) = A + A by dsimp [A]; ring]
    exact finiteAbsTailMass_add_le _ _ _ (bernoulliProductMass_nonneg p hp0 hp1) A A
  have he : -2 * (δ / 2) ^ 2 * (N : ℝ) = -δ ^ 2 * (N : ℝ) / 2 := by ring
  rw [he] at hfirst hsecond
  linarith

/-- The concrete open-path triple statistic under the actual tournament
transition has the proved finite exponential tail bound. -/
theorem Tournament.holding_adjacent_tail_le {n : ℕ} (T : Tournament n)
    (hn : n ≠ 0) (hT : T.Regular) (N : ℕ) (s : Fin n) (δ : ℝ) (hδ : 0 ≤ δ) :
    (∑ w : Fin (N + 1) → Fin n,
      if δ * ((N + 1 : ℕ) : ℝ) ≤ |adjacentCenteredValue (1 / (n : ℝ)) (linearHoldingPattern s w)|
      then linearPathWeight T.realCriticalTransition s w else 0) ≤
        4 * Real.exp (-δ ^ 2 * (N : ℝ) / 2) := by
  have hp0 : 0 ≤ 1 / (n : ℝ) := by positivity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hp1 : 1 / (n : ℝ) ≤ 1 := (div_le_one (lt_of_lt_of_le zero_lt_one hnR)).mpr hnR
  have hpush := sum_holding_observable_eq_product T.realCriticalTransition (1 / (n : ℝ))
    (T.realCriticalTransition_row_sum hn hT) T.realCriticalTransition_diagonal s
    (fun b : Fin (N + 1) → Bool =>
      if δ * ((N + 1 : ℕ) : ℝ) ≤ |adjacentCenteredValue (1 / (n : ℝ)) b| then (1 : ℝ) else 0)
  have heq : (∑ w : Fin (N + 1) → Fin n,
      if δ * ((N + 1 : ℕ) : ℝ) ≤ |adjacentCenteredValue (1 / (n : ℝ)) (linearHoldingPattern s w)|
      then linearPathWeight T.realCriticalTransition s w else 0) =
      finiteAbsTailMass (fun b : Fin (N + 1) → Bool => bernoulliProductMass (1 / (n : ℝ)) b)
        (adjacentCenteredValue (1 / (n : ℝ))) (δ * ((N + 1 : ℕ) : ℝ)) := by
    simpa only [finiteAbsTailMass, bernoulliProductMass, bernoulliMass, mul_ite, mul_one, mul_zero] using hpush
  rw [heq]
  exact adjacentCentered_abs_tail_le _ hp0 hp1 N δ hδ

end
end Wormald
