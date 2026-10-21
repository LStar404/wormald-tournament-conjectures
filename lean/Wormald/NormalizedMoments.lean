import Wormald.SwitchingMoments
import Wormald.MomentEquality
import Wormald.TournamentPositivity

namespace Wormald

noncomputable section
open Matrix Finset FiniteModel

theorem realNormalizedSign_toTournament {n : ℕ} (T : Orientation n) :
    (toTournament T).realNormalizedSign = (1 / (n : ℝ)) • orientationSign T ℝ := by
  have hs := orientationSign_map T (Rat.castHom ℝ)
  rw [orientationSign_rat_eq_sign] at hs
  ext i j
  have hentry := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hs
  simp only [Matrix.map_apply] at hentry
  change (((toTournament T).sign i j : ℚ) : ℝ) = orientationSign T ℝ i j at hentry
  simp only [Tournament.realNormalizedSign, Tournament.normalizedSign,
    Rat.cast_div, Rat.cast_natCast, Matrix.smul_apply, smul_eq_mul]
  rw [hentry]
  ring

theorem frobenius_sq_smul_pow {n : ℕ} (c : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (p : ℕ) :
    (∑ i, ∑ j, ((c • M) ^ p) i j ^ 2) =
      (c ^ p) ^ 2 * (∑ i, ∑ j, (M ^ p) i j ^ 2) := by
  simp only [smul_pow, Matrix.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]

/-- Every moment of the paper's actual real normalized sign C=S/n is bounded
by the actual odd carousel. No spectral-limit or majorization assumption remains. -/
theorem Tournament.normalized_moment_le_carousel {n : ℕ} (T : Tournament n)
    (hn : Odd n) (p : ℕ) :
    (∑ i, ∑ j, (T.realNormalizedSign ^ p) i j ^ 2) ≤
      ∑ i, ∑ j, ((toTournament (carousel n)).realNormalizedSign ^ p) i j ^ 2 := by
  have h := tournament_pow_frobenius_sq_le_carousel hn (fromTournament T) p
  have hs : T.realNormalizedSign = (1 / (n : ℝ)) • orientationSign (fromTournament T) ℝ := by
    simpa only [to_fromTournament] using realNormalizedSign_toTournament (fromTournament T)
  rw [hs, realNormalizedSign_toTournament, frobenius_sq_smul_pow, frobenius_sq_smul_pow]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- Equality in a genuine normalized moment is equivalent to equality in the
unscaled sign moment. The positive scale is cancelled explicitly. -/
theorem normalized_moment_eq_iff_sign_moment_eq {n : ℕ} (hn : 0 < n)
    (T : Orientation n) (p : ℕ) :
    ((∑ i, ∑ j, ((toTournament T).realNormalizedSign ^ p) i j ^ 2) =
      ∑ i, ∑ j, ((toTournament (carousel n)).realNormalizedSign ^ p) i j ^ 2) ↔
    ((∑ i, ∑ j, (orientationSign T ℝ ^ p) i j ^ 2) =
      ∑ i, ∑ j, (orientationSign (carousel n) ℝ ^ p) i j ^ 2) := by
  rw [realNormalizedSign_toTournament, realNormalizedSign_toTournament,
    frobenius_sq_smul_pow, frobenius_sq_smul_pow]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < ((1 / (n : ℝ)) ^ p) ^ 2 := by positivity
  constructor
  · exact mul_left_cancel₀ (ne_of_gt hpos)
  · intro h
    rw [h]

/-- The equality criterion needed for C1: any genuine normalized p≥2 moment
equality forces the exact fourth-trace equality of the original tournament sign. -/
theorem normalized_moment_eq_implies_trace_four_eq {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n)
    (T : Orientation n) (p : ℕ) (hp : 2 ≤ p)
    (heq : (∑ i, ∑ j, ((toTournament T).realNormalizedSign ^ p) i j ^ 2) =
      ∑ i, ∑ j, ((toTournament (carousel n)).realNormalizedSign ^ p) i j ^ 2) :
    (orientationSign T ℝ ^ 4).trace = (transitiveSign n ℝ ^ 4).trace := by
  have hraw := (normalized_moment_eq_iff_sign_moment_eq (by omega) T p).mp heq
  rw [carousel_pow_frobenius_sq_eq_transitive_odd n hodd p] at hraw
  exact trace_four_eq_of_pow_frobenius_sq_eq hn _ (orientationSign_skew T)
    (orientationSign_bound T) p hp hraw

end
end Wormald
