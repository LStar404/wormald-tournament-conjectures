import Wormald.SpectralExtremum
import Wormald.RegularSignClassification

/-! The strict spectral gap for every regular non-carousel base, with
ordinary graph isomorphism as the exact structural conclusion. -/

namespace Wormald
noncomputable section
open FiniteModel

theorem isomorphic_carousel_of_spectralRatio_re_eq {n : ℕ} (hn : 2 ≤ n)
    (hodd : Odd n) (T : Orientation n) (hT : (toTournament T).Regular)
    (heq : (toTournament T).spectralRatio.re = (toTournament (carousel n)).spectralRatio.re) :
    Isomorphic T (carousel n) :=
  isomorphic_carousel_of_fourth_trace_eq hodd T hT
    (trace_four_eq_of_spectralRatio_re_eq hn hodd T heq)

/-- This is the actual strict limiting-constant comparison used by C1.
No moment inequality, classification or spectral comparison is a hypothesis. -/
theorem spectralRatio_re_lt_carousel_of_not_isomorphic {n : ℕ} (hn : 2 ≤ n)
    (hodd : Odd n) (T : Orientation n) (hT : (toTournament T).Regular)
    (hnot : ¬ Isomorphic T (carousel n)) :
    (toTournament T).spectralRatio.re < (toTournament (carousel n)).spectralRatio.re := by
  have hle := (toTournament T).spectralRatio_re_le_carousel hodd (by omega)
  have hne : (toTournament T).spectralRatio.re ≠
      (toTournament (carousel n)).spectralRatio.re := by
    intro heq
    exact hnot (isomorphic_carousel_of_spectralRatio_re_eq hn hodd T hT heq)
  exact lt_of_le_of_ne hle hne

end
end Wormald
