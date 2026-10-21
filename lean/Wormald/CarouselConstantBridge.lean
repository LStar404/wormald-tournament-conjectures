import Wormald.CarouselSwitching
import Wormald.CarouselLimit

namespace Wormald

noncomputable section
open Matrix
open FiniteModel

/-- The spectral ratio of the actual normalized carousel tournament sign matrix. -/
def carouselSpectralRatio (n : ℕ) : ℂ :=
  let C := ((toTournament (carousel n)).normalizedSign).map (Rat.castHom ℂ)
  (1 + C).det / (1 + Complex.I • C).det

/-- The closed constant is exactly the actual carousel determinant ratio,
including the regular-block factor exp(1/n). This is a general odd-order identity. -/
theorem carouselClosedConstant_eq_determinant (n : ℕ) (hn : Odd n) :
    carouselClosedConstant n = Complex.exp (1 / (n : ℂ)) * carouselSpectralRatio n := by
  have hnum := det_one_add_smul_carouselNormalizedSign (K := ℂ) n hn (1 : ℂ)
  simp only [one_smul] at hnum
  have hden := det_one_add_smul_carouselNormalizedSign (K := ℂ) n hn Complex.I
  unfold carouselClosedConstant carouselSpectralRatio
  dsimp only
  rw [hnum, hden, div_div_div_cancel_right₀ (two_ne_zero : (2 : ℂ) ≠ 0)]

/-- The determinant-derived regular carousel constants have the exact odd-order limit. -/
theorem tendsto_carouselDeterminantConstant_odd :
    Filter.Tendsto (fun j : ℕ =>
      Complex.exp (1 / ((2 * j + 3 : ℕ) : ℂ)) * carouselSpectralRatio (2 * j + 3))
      Filter.atTop (nhds ((Real.cosh 1 / Real.cos 1 : ℝ) : ℂ)) := by
  have heq : (fun j : ℕ =>
      Complex.exp (1 / ((2 * j + 3 : ℕ) : ℂ)) * carouselSpectralRatio (2 * j + 3)) =
      (fun j : ℕ => carouselClosedConstant (2 * j + 3)) := by
    funext j
    exact (carouselClosedConstant_eq_determinant (2 * j + 3)
      ⟨j + 1, by omega⟩).symm
  rw [heq]
  exact tendsto_carouselClosedConstant_odd

end
end Wormald
