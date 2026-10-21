import Wormald.FourthMomentEquality

/-!
# Regular switched-transitive tournaments are carousels

Regularity makes the ordered switching vector a kernel vector of the transitive
sign matrix. Subtracting adjacent rows forces consecutive signs to alternate.
The explicit carousel parity shuffle then gives an ordinary isomorphism.
-/

namespace Wormald
noncomputable section
open scoped BigOperators
open Matrix FiniteModel

theorem orientationSign_row_sum_regular {n : ℕ} (T : Orientation n)
    (hT : (toTournament T).Regular) (i : Fin n) :
    (∑ j, orientationSign T ℝ i j) = 0 := by
  have hrat : (∑ j, orientationSign T ℚ i j) = 0 := by
    rw [orientationSign_rat_eq_sign]
    exact Tournament.sign_row_sum _ hT i
  rw [← orientationSign_map T (Rat.castHom ℝ)]
  change (∑ j, (Rat.castHom ℝ) (orientationSign T ℚ i j)) = 0
  simpa only [map_sum, map_zero] using congrArg (Rat.castHom ℝ) hrat

private theorem transitiveSign_mulVec_succ_sub {n : ℕ} (ε : Fin n → ℝ)
    (i : ℕ) (hi : i + 1 < n) :
    (transitiveSign n ℝ *ᵥ ε) ⟨i + 1, hi⟩ -
      (transitiveSign n ℝ *ᵥ ε) ⟨i, by omega⟩ =
      -ε ⟨i, by omega⟩ - ε ⟨i + 1, hi⟩ := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : Fin n,
        ((if j.val = i then -ε j else 0) + (if j.val = i + 1 then -ε j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [transitiveSign, Fin.lt_def]
      split_ifs <;> norm_num <;> omega
    _ = _ := by
      rw [Finset.sum_add_distrib]
      have h₁ : ∀ j : Fin n, j.val = i ↔ j = ⟨i, by omega⟩ := by
        intro j
        exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      have h₂ : ∀ j : Fin n, j.val = i + 1 ↔ j = ⟨i + 1, hi⟩ := by
        intro j
        exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simp only [h₁, h₂]
      simp [sub_eq_add_neg]

private theorem kernel_transitive_alternating {n : ℕ} (hn : 0 < n)
    (ε : Fin n → ℝ) (hker : transitiveSign n ℝ *ᵥ ε = 0) :
    ∀ i : Fin n, ε i = if i.val % 2 = 0 then ε ⟨0, hn⟩ else -ε ⟨0, hn⟩ := by
  have hadj : ∀ i (hi : i + 1 < n), ε ⟨i + 1, hi⟩ = -ε ⟨i, by omega⟩ := by
    intro i hi
    have h := transitiveSign_mulVec_succ_sub ε i hi
    rw [hker] at h
    simp only [Pi.zero_apply, sub_self] at h
    linarith
  have hseq : ∀ i (hi : i < n),
      ε ⟨i, hi⟩ = if i % 2 = 0 then ε ⟨0, hn⟩ else -ε ⟨0, hn⟩ := by
    intro i
    induction i with
    | zero => intro hi; simp
    | succ i ih =>
      intro hi
      rw [hadj i hi, ih (by omega)]
      split_ifs <;> first | omega | ring
  intro i
  exact hseq i.val i.isLt

/-- Regularity upgrades a signed transitive equivalence to ordinary carousel
isomorphism; switching is absent from the conclusion. -/
theorem isomorphic_carousel_of_signed_permutation {q : ℕ}
    (T : Orientation (2 * q + 1)) (hT : (toTournament T).Regular)
    (σ : Equiv.Perm (Fin (2 * q + 1))) (ε : Fin (2 * q + 1) → ℝ)
    (hε : ∀ i, ε i ^ 2 = 1)
    (hσ : ∀ i j, orientationSign T ℝ (σ i) (σ j) =
      ε i * transitiveSign (2 * q + 1) ℝ i j * ε j) :
    Isomorphic T (carousel (2 * q + 1)) := by
  have hker : transitiveSign (2 * q + 1) ℝ *ᵥ ε = 0 := by
    funext i
    have hεne : ε i ≠ 0 := by
      intro hz
      have h := hε i
      rw [hz] at h
      norm_num at h
    apply (mul_eq_zero.mp (show ε i * (transitiveSign (2 * q + 1) ℝ *ᵥ ε) i = 0 from ?_)).resolve_left hεne
    calc
      _ = ∑ j, ε i * transitiveSign (2 * q + 1) ℝ i j * ε j := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      _ = ∑ j, orientationSign T ℝ (σ i) (σ j) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hσ i j).symm
      _ = ∑ j, orientationSign T ℝ (σ i) j := Equiv.sum_comp σ _
      _ = 0 := orientationSign_row_sum_regular T hT (σ i)
  have hseq := kernel_transitive_alternating (by omega : 0 < 2 * q + 1) ε hker
  let alt : Fin (2 * q + 1) → ℝ := fun i => if i.val % 2 = 0 then 1 else -1
  have hprod : ∀ i j, ε i * ε j = alt i * alt j := by
    intro i j
    rw [hseq i, hseq j]
    dsimp [alt]
    have hsq : ε (0 : Fin (2 * q + 1)) ^ 2 = 1 := hε 0
    split_ifs <;> nlinarith
  have hsign : ∀ i j,
      orientationSign T ℝ (σ i) (σ j) =
        orientationSign (carousel (2 * q + 1)) ℝ (carouselShuffle q i) (carouselShuffle q j) := by
    intro i j
    have hc := congrArg (fun M : Matrix (Fin (2 * q + 1)) (Fin (2 * q + 1)) ℝ => M i j)
      (carouselSign_shuffle (K := ℝ) q)
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
    change orientationSign (carousel (2 * q + 1)) ℝ (carouselShuffle q i) (carouselShuffle q j) =
      (alt i * transitiveSign (2 * q + 1) ℝ i j) * alt j at hc
    rw [hσ, hc]
    calc
      ε i * transitiveSign (2 * q + 1) ℝ i j * ε j =
          (ε i * ε j) * transitiveSign (2 * q + 1) ℝ i j := by ring
      _ = _ := by rw [hprod]; ring
  refine ⟨σ.symm.trans (carouselShuffle q), ?_⟩
  intro i j
  have hs := hsign (σ.symm i) (σ.symm j)
  simp only [Equiv.apply_symm_apply] at hs
  by_cases hij : i = j
  · subst j; rw [arc_self, arc_self]
  · have hne : (carouselShuffle q) (σ.symm i) ≠ (carouselShuffle q) (σ.symm j) :=
      (carouselShuffle q).injective.ne (σ.symm.injective.ne hij)
    simp only [orientationSign, ite_eq_right hij, ite_eq_right hne] at hs
    change arc T i j = arc (carousel (2 * q + 1))
      (carouselShuffle q (σ.symm i)) (carouselShuffle q (σ.symm j))
    cases h₁ : arc T i j <;>
      cases h₂ : arc (carousel (2 * q + 1))
        (carouselShuffle q (σ.symm i)) (carouselShuffle q (σ.symm j)) <;>
      first | rfl | norm_num [h₁, h₂] at hs

/-- The complete regular equality classification for the actual fourth trace. -/
theorem isomorphic_carousel_of_fourth_trace_eq {n : ℕ} (hn : Odd n)
    (T : Orientation n) (hT : (toTournament T).Regular)
    (heq : ((orientationSign T ℝ) ^ 4).trace = ((transitiveSign n ℝ) ^ 4).trace) :
    Isomorphic T (carousel n) := by
  obtain ⟨q, hq⟩ := hn
  have hdim : n = 2 * q + 1 := by omega
  subst n
  obtain ⟨σ, ε, hε, hσ⟩ := signed_permutation_of_fourth_trace_eq T heq
  exact isomorphic_carousel_of_signed_permutation T hT σ ε hε hσ

end
end Wormald
