import Wormald.SkewMomentSeries
import Wormald.NormalizedMoments

/-!
# The actual spectral constant is maximized by the odd carousel

The positive moment-series coefficients turn the proved all-moment comparison
into an inequality of literal determinant ratios. Equality also yields the
fourth-trace equality needed for the separate structural classification.
-/

namespace Wormald
noncomputable section
open Matrix FiniteModel

theorem Tournament.spectralRatio_re_le_carousel {n : ℕ} (T : Tournament n)
    (hn : Odd n) (hpos : 0 < n) :
    T.spectralRatio.re ≤ (toTournament (carousel n)).spectralRatio.re := by
  have hd := Nat.ne_of_gt hpos
  have hT := T.hasSum_frobenius_odd_log_spectralRatio hd
  have hCar := (toTournament (carousel n)).hasSum_frobenius_odd_log_spectralRatio hd
  have hterm (r : ℕ) :
      frobeniusSq (T.realNormalizedSign ^ (2 * r + 1)) / ((2 * r + 1 : ℕ) : ℝ) ≤
      frobeniusSq ((toTournament (carousel n)).realNormalizedSign ^ (2 * r + 1)) /
        ((2 * r + 1 : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_right
    · exact T.normalized_moment_le_carousel hn _
    · positivity
  have hlog := hasSum_mono hT hCar hterm
  exact (Real.log_le_log_iff (T.spectralRatio_re_pos hd)
    ((toTournament (carousel n)).spectralRatio_re_pos hd)).mp hlog

/-- Equality of the literal determinant constants forces equality of every
positive odd-power moment, not merely equality of an upper bound. -/
theorem Tournament.odd_moments_eq_of_spectralRatio_re_eq {n : ℕ}
    (T : Tournament n) (hn : Odd n) (hpos : 0 < n)
    (heq : T.spectralRatio.re = (toTournament (carousel n)).spectralRatio.re) (r : ℕ) :
    frobeniusSq (T.realNormalizedSign ^ (2 * r + 1)) =
      frobeniusSq ((toTournament (carousel n)).realNormalizedSign ^ (2 * r + 1)) := by
  have hd := Nat.ne_of_gt hpos
  have hterm (k : ℕ) :
      frobeniusSq (T.realNormalizedSign ^ (2 * k + 1)) / ((2 * k + 1 : ℕ) : ℝ) ≤
      frobeniusSq ((toTournament (carousel n)).realNormalizedSign ^ (2 * k + 1)) /
        ((2 * k + 1 : ℕ) : ℝ) := by
    apply div_le_div_of_nonneg_right
    · exact T.normalized_moment_le_carousel hn _
    · positivity
  have h := eq_terms_of_hasSum_eq_of_le
    (T.hasSum_frobenius_odd_log_spectralRatio hd)
    ((toTournament (carousel n)).hasSum_frobenius_odd_log_spectralRatio hd)
    hterm (congrArg Real.log heq) r
  exact (div_left_inj' (by positivity : ((2 * r + 1 : ℕ) : ℝ) ≠ 0)).mp h

/-- The equality implication entering the ordinary-isomorphism classification. -/
theorem trace_four_eq_of_spectralRatio_re_eq {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n)
    (T : Orientation n)
    (heq : (toTournament T).spectralRatio.re = (toTournament (carousel n)).spectralRatio.re) :
    (orientationSign T ℝ ^ 4).trace = (transitiveSign n ℝ ^ 4).trace := by
  have hm := (toTournament T).odd_moments_eq_of_spectralRatio_re_eq hodd (by omega) heq 1
  norm_num at hm
  exact normalized_moment_eq_implies_trace_four_eq hn hodd T 3 (by omega) hm

end
end Wormald
