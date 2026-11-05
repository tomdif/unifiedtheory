/- Actual weak-coupling collapse of the unscaled unitary plaquette defect,
uniform in arbitrary changing lattice period. No decay rate in lattice
spacing or renormalized curvature limit follows from this theorem. -/
import UnifiedTheory.Clay.YangMills.WilsonIdentityNeighborhood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonWeakCouplingDefect
noncomputable section
open MeasureTheory Filter RegulatedGauge PeriodicLattice4 WilsonCrossingKernel
open UnitaryCharacterObservables WilsonAverageDefect WilsonIdentityNeighborhood
open scoped Topology

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {d : Type*} [Fintype d] [DecidableEq d]

theorem average_expectation_tendsto_zero (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (beta : ℕ → ℝ) (hbeta : Tendsto beta atTop atTop) :
    Tendsto (fun k => ∫ U, averageDefect (period k) G ρ U
      ∂wilsonLaw (period k) G (unitaryCharacter ρ) (beta k) (Fintype.card d))
      atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    exact Eventually.of_forall (fun k => hl.trans_le
      (integral_nonneg (average_nonneg (period k) G ρ)))
  · intro u hu
    obtain ⟨q,hq,hbound⟩ := average_expectation_bound G ρ hρ (u/4) (by positivity)
    have he : Tendsto (fun k => Real.exp (-6 * beta k * (u/4))) atTop (𝓝 0) := by
      have ht : Tendsto (fun k => (-6 * (u/4)) * beta k) atTop atBot :=
        hbeta.const_mul_atTop_of_neg (by linarith)
      convert Real.tendsto_exp_atBot.comp ht using 1
      ext k
      congr 1
      ring
    have hr : Tendsto (fun k => Real.exp (-6 * beta k * (u/4)) / q^4) atTop (𝓝 0) := by
      simpa using he.div_const (q^4)
    have hrem : Tendsto (fun k => (2 * (Fintype.card d : ℝ)) *
        (Real.exp (-6 * beta k * (u/4)) / q^4)) atTop (𝓝 0) := by
      simpa using hr.const_mul (2 * (Fintype.card d : ℝ))
    have hsmall := (tendsto_order.mp hr).2 1 (by norm_num)
    have hremSmall := (tendsto_order.mp hrem).2 (u/2) (by positivity)
    have hb := hbeta.eventually (eventually_ge_atTop (0 : ℝ))
    filter_upwards [hsmall,hremSmall,hb] with k hk hremk hbk
    have hh := hbound (period k) inferInstance (beta k) hbk hk.le
    linarith

/-- Every plaquette, including one moving with the regulator, has vanishing
mean defect along beta to infinity; no fixed volume is assumed. -/
theorem plaquette_expectation_tendsto_zero (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (beta : ℕ → ℝ) (hbeta : Tendsto beta atTop atTop)
    (p : ∀ k, PlaquetteIndex (period k)) :
    Tendsto (fun k => ∫ U, plaquetteDefect (period k) G ρ (p k) U
      ∂wilsonLaw (period k) G (unitaryCharacter ρ) (beta k) (Fintype.card d))
      atTop (𝓝 0) := by
  have h := (average_expectation_tendsto_zero G ρ hρ period beta hbeta).const_mul 6
  simp only [mul_zero] at h
  exact squeeze_zero (fun k => integral_nonneg (plaquette_nonneg (period k) G ρ (p k)))
    (fun k => mean_plaquette_le_six_average (period k) G ρ hρ (beta k) (Fintype.card d) (p k)) h

end
end UnifiedTheory.Clay.YangMills.WilsonWeakCouplingDefect
