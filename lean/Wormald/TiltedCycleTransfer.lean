import Wormald.BalancedTripleExponential
import Wormald.InternalTripleStatistic

/-! Exact finite transfer of the positive internal-join tilt. This uses the
actual successor cycles, their rooted vertex orders, and their balanced block
words. No regular-containment asymptotic is used in this file. -/

namespace Wormald.FiniteModel
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

def internalJoinTilt {d m : ℕ} (σ : Equiv.Perm (Fin d × Fin m)) : ℝ :=
  Real.exp ((∑ i, internalInOutCount (internalCycleArcSet σ i) : ℕ) / (m : ℝ))

def tiltedIndependentCycleSum {d : ℕ} (base : Orientation d) (m : ℕ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin d × Fin m), if SingleOrbit σ then
    (∏ v, blockConstantMatrix (weightedBase base) m v (σ v)) * internalJoinTilt σ else 0

def normalizedTiltedIndependentCycles {d : ℕ} (base : Orientation d) (m : ℕ) : ℝ :=
  tiltedIndependentCycleSum base m / cycleNormalizer (d * m)

theorem internalJoinTilt_orderSuccessor {d m : ℕ}
    [Nonempty (Fin d × Fin m)]
    (e : Fin (Fintype.card (Fin d × Fin m)) ≃ (Fin d × Fin m)) :
    internalJoinTilt (orderSuccessor e) =
      Real.exp (normalizedTripleValue m (fun t => (e t).1)) := by
  unfold internalJoinTilt normalizedTripleValue
  rw [sum_internalInOutCount_orderSuccessor_eq_cyclicTripleCount]

theorem rootedOrder_sum_mul_successor_weight {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] (A : Matrix V V ℝ) (g : Equiv.Perm V → ℝ) :
    (∑ e : Fin (Fintype.card V) ≃ V, rootedOrderWeight A e * g (orderSuccessor e)) =
      (Fintype.card V : ℝ) *
        ∑ σ : Equiv.Perm V, if SingleOrbit σ then (∏ v, A v (σ v)) * g σ else 0 := by
  have hsum := Fintype.sum_equiv (rootedCycleEquivOrder (V := V))
    (fun p : {σ : Equiv.Perm V // SingleOrbit σ} × V =>
      (∏ v, A v (p.1.1 v)) * g p.1.1)
    (fun e => rootedOrderWeight A e * g (orderSuccessor e)) (by
      intro p
      simp only [rootedCycleEquivOrder, Equiv.coe_fn_mk,
        rootedOrderWeight_orbitOrder, orderSuccessor_orbitOrder])
  rw [← hsum]
  have hsub : (∑ σ : Equiv.Perm V,
      if SingleOrbit σ then (∏ v, A v (σ v)) * g σ else 0) =
      ∑ σ : {σ : Equiv.Perm V // SingleOrbit σ}, (∏ v, A v (σ.1 v)) * g σ.1 := by
    simpa only [Finset.sum_filter] using
      (Finset.sum_subtype (Finset.univ.filter SingleOrbit) (by simp)
        (fun σ => (∏ v, A v (σ v)) * g σ))
  rw [hsub]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum]

theorem rootedOrder_tilted_sum_blockConstant {d m : ℕ}
    [Nonempty (Fin d × Fin m)] (B : Matrix (Fin d) (Fin d) ℝ) :
    (∑ e : Fin (Fintype.card (Fin d × Fin m)) ≃ (Fin d × Fin m),
      rootedOrderWeight (blockConstantMatrix B m) e * internalJoinTilt (orderSuccessor e)) =
      (Nat.factorial m : ℝ) ^ d *
        ∑ f : Fin (Fintype.card (Fin d × Fin m)) → Fin d,
          (if BalancedBaseWord m f then cyclicWordWeight B f else 0) *
            Real.exp (normalizedTripleValue m f) := by
  simp_rw [rootedOrder_block_weight, internalJoinTilt_orderSuccessor]
  let π : (Fin (Fintype.card (Fin d × Fin m)) ≃ (Fin d × Fin m)) →
      (Fin (Fintype.card (Fin d × Fin m)) → Fin d) := fun e a => (e a).1
  rw [← Fintype.sum_fiberwise' π
    (fun f => cyclicWordWeight B f * Real.exp (normalizedTripleValue m f))]
  change (∑ f, ∑ _e : labelingFiber (m := m) f,
    cyclicWordWeight B f * Real.exp (normalizedTripleValue m f)) = _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    labelingFiber_card_eq_ite, Nat.cast_ite, Nat.cast_pow, Nat.cast_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  unfold BalancedBaseWord
  split_ifs <;> simp

theorem normalizedTiltedIndependentCycles_eq_prefactor {d : ℕ} (base : Orientation d)
    (m : ℕ) (hN : 3 ≤ d * m) :
    normalizedTiltedIndependentCycles base m = factorialPrefactor d m *
      ∑ f : Fin (Fintype.card (Fin d × Fin m)) → Fin d,
        balancedWordWeight base m f * Real.exp (normalizedTripleValue m f) := by
  have hd : d ≠ 0 := by intro h; simp [h] at hN
  have hm : m ≠ 0 := by intro h; simp [h] at hN
  let : Nonempty (Fin d × Fin m) := ⟨(⟨0, Nat.pos_of_ne_zero hd⟩,
    ⟨0, Nat.pos_of_ne_zero hm⟩)⟩
  have hroot := rootedOrder_sum_mul_successor_weight
    (blockConstantMatrix (weightedBase base) m) (internalJoinTilt (d := d) (m := m))
  change _ = (Fintype.card (Fin d × Fin m) : ℝ) * tiltedIndependentCycleSum base m at hroot
  rw [rootedOrder_tilted_sum_blockConstant] at hroot
  have hscale : (∑ f : Fin (Fintype.card (Fin d × Fin m)) → Fin d,
      (if BalancedBaseWord m f then cyclicWordWeight (weightedBase base) f else 0) *
        Real.exp (normalizedTripleValue m f)) = ((d : ℝ) / 2) ^ (d * m) *
      ∑ f, balancedWordWeight base m f * Real.exp (normalizedTripleValue m f) := by
    rw [weightedBase_eq_smul_markovBase base hd, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [cyclicWordWeight_smul]
    simp only [Fintype.card_prod, Fintype.card_fin]
    unfold balancedWordWeight
    rw [← markovBase_eq_realCriticalTransition]
    split_ifs <;> ring
  rw [hscale] at hroot
  have hNne : d * m ≠ 0 := by omega
  have hfac : ((d * m : ℕ) : ℝ) * (Nat.factorial (d * m - 1) : ℝ) =
      (Nat.factorial (d * m) : ℝ) := by exact_mod_cast Nat.mul_factorial_pred hNne
  have hNr : ((d * m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hNne
  have hpredfac : (Nat.factorial (d * m - 1) : ℝ) ≠ 0 := by positivity
  have hNfac : (Nat.factorial (d * m) : ℝ) ≠ 0 := by positivity
  simp only [Fintype.card_prod, Fintype.card_fin] at hroot
  rw [div_pow] at hroot
  field_simp at hroot
  unfold normalizedTiltedIndependentCycles cycleNormalizer factorialPrefactor
  field_simp
  rw [← hfac]
  nlinarith [hroot]

theorem normalizedTiltedIndependentCycles_eq_mean {d : ℕ} (base : Orientation d)
    (m : ℕ) (hN : 3 ≤ d * m) (hW : balancedOccupationMass base m ≠ 0) :
    normalizedTiltedIndependentCycles base m =
      normalizedExpectedCycles base m * balancedTripleExponentialMean base m := by
  rw [normalizedTiltedIndependentCycles_eq_prefactor base m hN,
    normalizedExpectedCycles_eq_prefactor_mul_occupation base m hN]
  unfold balancedTripleExponentialMean finiteWeightedAverage
  rw [sum_balancedWordWeight]
  field_simp

/-- The actual tilted independent cycle sum has the regular-block correction
limit. This theorem is unconditional for every fixed regular base. -/
theorem tendsto_normalizedTiltedIndependentCycles {d : ℕ} (hd : 3 ≤ d)
    (base : Orientation d) (hT : (toTournament base).Regular) :
    Tendsto (normalizedTiltedIndependentCycles base) atTop
      (𝓝 ((toTournament base).spectralRatio.re * Real.exp (1 / (d : ℝ)))) := by
  apply ((tendsto_normalizedExpectedCycles_regular hd base hT).mul
    (tendsto_balancedTripleExponentialMean hd base hT)).congr'
  filter_upwards [eventually_balancedOccupationMass_pos hd base hT,
    eventually_ge_atTop 3] with m hm hm3
  exact (normalizedTiltedIndependentCycles_eq_mean base m (by
    have h := Nat.mul_le_mul_right m hd
    omega) hm.ne').symm

end
end Wormald.FiniteModel
