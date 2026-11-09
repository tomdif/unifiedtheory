/- The actual clock-dependent potential profiles, with independent
Gaussian widths and frequencies, have explicit narrow Fourier integrals
and convergent clock derivatives at each fixed transverse point. The
half-density term is kept. Full Hilbert derivative convergence is separate. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredShiftedNarrowJet
import UnifiedTheory.Audit.KFCausalMixedFieldPureClockDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialFourierClock
noncomputable section
open Filter
open scoped Topology FourierTransform
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalClockLimit (amplitudes)
open KFCausalCorrelatedClusteredNeutralPowers (fieldProfile)
open KFCausalShiftedNarrowFourierGeometry (reconstruct radius shifted_coefficient_positive)
open KFCausalCorrelatedClusteredShiftedNarrowProfiles
open KFCausalCorrelatedClusteredShiftedNarrowJet
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneClockGeometry (velocity scale_velocity)
open KFCausalShiftedGaussianLongitudinalDifferential (amplitudeSlope clockAmplitude_derivative)
open KFCausalShiftedGaussianPureDifferential (realInverse)
open KFCausalClockFloorPureClockDerivative (rate)

variable {m : ℕ} (f : Family m) (α β ε y z : ℝ) (a p : Fin m → ℝ) (k : ℕ)
local notation "c" => amplitudes ε y a p
local notation "r" => scale ε y
local notation "t" => scale ε z

def amplitudeDerivative (s : ℝ) (i : Fin m) : ℂ := amplitudeSlope ε (a i) (p i) y s*c s i

def fourierProfile (δ s : ℝ) (u : Block 2) (v : Block 4) : ℂ :=
  (𝓕 (fun x => fieldProfile f c α β ε y z k δ (s,reconstruct x v))) u

def fourierLimit (s : ℝ) (u : Block 2) (v : Block 4) : ℂ :=
  limitTransformed f (c s) α β (r s) (t s) k u v

def fourierJet (δ s : ℝ) (u : Block 2) (v : Block 4) : ℂ :=
  clockJet f (c s) (amplitudeDerivative ε y a p s) α β
    (r s) (velocity ε (Real.exp s) (r s)) (t s) (velocity ε (Real.exp s) (t s)) k δ u v

def fourierLimitJet (s : ℝ) (u : Block 2) (v : Block 4) : ℂ :=
  limitClockJet f (c s) (amplitudeDerivative ε y a p s) α β
    (r s) (velocity ε (Real.exp s) (r s)) (t s) (velocity ε (Real.exp s) (t s)) k u v

def jetEnvelope (s : ℝ) (u : Block 2) (v : Block 4) : ℝ :=
  envelope f (c s) (amplitudeDerivative ε y a p s) α β
    (r s) (velocity ε (Real.exp s) (r s)) (t s) (velocity ε (Real.exp s) (t s)) k u v

def profileEnvelope (s : ℝ) (u : Block 2) (v : Block 4) : ℝ :=
  ∑ i, ‖coefficient f (c s) α β (r s) (t s) k i v‖*
    (Real.exp (-(radius ((α:ℂ)*(r s)^2) u v).re)*‖radius ((α:ℂ)*(r s)^2) u v‖^(f.degree i))

def clockExpression (δ s : ℝ) (u : Block 2) (v : Block 4) : ℂ :=
  realInverse ε s*fourierJet f α β ε y z a p k δ s u v+
    (rate ε s:ℂ)*fourierProfile f α β ε y z a p k δ s u v

def clockLimitExpression (s : ℝ) (u : Block 2) (v : Block 4) : ℂ :=
  realInverse ε s*fourierLimitJet f α β ε y z a p k s u v+
    (rate ε s:ℂ)*fourierLimit f α β ε y z a p k s u v

variable (hα : 0 < α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3)

include hα hε hy in
theorem fourierProfile_eq (δ s : ℝ) (hδ : 0 < δ) (u : Block 2) (v : Block 4) :
    fourierProfile f α β ε y z a p k δ s u v =
      transformed f (c s) α β (r s) (t s) k δ u v := by
  unfold fourierProfile
  simp_rw [actual_slice]
  exact slice_fourier f (c s) α β (r s) (t s) k
    (shifted_coefficient_positive α ε y s hα hε hy) δ hδ u v

include hε hy in
theorem amplitude_derivative (s : ℝ) (i : Fin m) :
    HasDerivAt (fun x => c x i) (amplitudeDerivative ε y a p s i) s :=
  clockAmplitude_derivative ε (a i) (p i) y s hε hy

include hα hε hy hz in
theorem fourierProfile_derivative (δ s : ℝ) (hδ : 0 < δ) (u : Block 2) (v : Block 4) :
    HasDerivAt (fun x => fourierProfile f α β ε y z a p k δ x u v)
      (fourierJet f α β ε y z a p k δ s u v) s := by
  have hne : (α:ℂ)*(r s)^2 ≠ 0 := fun he => by
    have hp := shifted_coefficient_positive α ε y s hα hε hy
    rw [he] at hp
    exact (lt_irrefl 0 hp)
  rw [show (fun x => fourierProfile f α β ε y z a p k δ x u v) =
    (fun x => transformed f (c x) α β (r x) (t x) k δ u v) from
      funext (fun x => fourierProfile_eq f α β ε y z a p k hα hε hy δ x hδ u v)]
  exact transformed_derivative f α β k c (amplitudeDerivative ε y a p s) r t _ _ s δ hδ u v
    (amplitude_derivative ε y a p hε hy s) (scale_velocity ε y s hε hy) (scale_velocity ε z s hε hz) hne

include hα hε hy hz in
theorem fourierLimit_derivative (s : ℝ) (u : Block 2) (v : Block 4) :
    HasDerivAt (fun x => fourierLimit f α β ε y z a p k x u v)
      (fourierLimitJet f α β ε y z a p k s u v) s := by
  have hne : (α:ℂ)*(r s)^2 ≠ 0 := fun he => by
    have hp := shifted_coefficient_positive α ε y s hα hε hy
    rw [he] at hp
    exact (lt_irrefl 0 hp)
  exact limitTransformed_derivative f α β k c (amplitudeDerivative ε y a p s) r t _ _ s u v
    (amplitude_derivative ε y a p hε hy s) (scale_velocity ε y s hε hy) (scale_velocity ε z s hε hz) hne

include hα hε hy in
theorem fourierProfile_tendsto (s : ℝ) (u : Block 2) (v : Block 4) :
    Tendsto (fun δ => fourierProfile f α β ε y z a p k δ s u v) (𝓝[>] 0)
      (𝓝 (fourierLimit f α β ε y z a p k s u v)) := by
  apply Tendsto.congr' _ (transformed_tendsto f (c s) α β (r s) (t s) k u v)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (fourierProfile_eq f α β ε y z a p k hα hε hy δ s hδ u v).symm

theorem fourierJet_tendsto (s : ℝ) (u : Block 2) (v : Block 4) :
    Tendsto (fun δ => fourierJet f α β ε y z a p k δ s u v) (𝓝[>] 0)
      (𝓝 (fourierLimitJet f α β ε y z a p k s u v)) :=
  clockJet_tendsto f (c s) (amplitudeDerivative ε y a p s) α β
    (r s) _ (t s) _ k u v

include hα hε hy in
theorem fourierJet_bound (δ s : ℝ) (hδ : 0 < δ) (u : Block 2) (v : Block 4) :
    ‖fourierJet f α β ε y z a p k δ s u v‖ ≤ jetEnvelope f α β ε y z a p k s u v :=
  clockJet_bound f (c s) (amplitudeDerivative ε y a p s) α β
    (r s) _ (t s) _ k (shifted_coefficient_positive α ε y s hα hε hy).le δ hδ u v

include hα hε hy in
theorem fourierProfile_bound (δ s : ℝ) (hδ : 0 < δ) (u : Block 2) (v : Block 4) :
    ‖fourierProfile f α β ε y z a p k δ s u v‖ ≤ profileEnvelope f α β ε y z a p k s u v := by
  rw [fourierProfile_eq f α β ε y z a p k hα hε hy δ s hδ u v]
  exact transformed_bound f (c s) α β (r s) (t s) k
    (shifted_coefficient_positive α ε y s hα hε hy).le δ hδ u v

include hα hε hy in
theorem clockExpression_tendsto (s : ℝ) (u : Block 2) (v : Block 4) :
    Tendsto (fun δ => clockExpression f α β ε y z a p k δ s u v) (𝓝[>] 0)
      (𝓝 (clockLimitExpression f α β ε y z a p k s u v)) :=
  ((fourierJet_tendsto f α β ε y z a p k s u v).const_mul _).add
    ((fourierProfile_tendsto f α β ε y z a p k hα hε hy s u v).const_mul _)

include hα hε hy in
theorem clockExpression_bound (δ s : ℝ) (hδ : 0 < δ) (u : Block 2) (v : Block 4) :
    ‖clockExpression f α β ε y z a p k δ s u v‖ ≤
      ‖realInverse ε s‖*jetEnvelope f α β ε y z a p k s u v+
        |rate ε s| * profileEnvelope f α β ε y z a p k s u v := by
  apply (norm_add_le _ _).trans
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (fourierJet_bound f α β ε y z a p k hα hε hy δ s hδ u v) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (fourierProfile_bound f α β ε y z a p k hα hε hy δ s hδ u v) (abs_nonneg _))

#print axioms fourierProfile_eq
#print axioms amplitude_derivative
#print axioms fourierProfile_derivative
#print axioms fourierLimit_derivative
#print axioms fourierProfile_tendsto
#print axioms fourierJet_tendsto
#print axioms fourierJet_bound
#print axioms fourierProfile_bound
#print axioms clockExpression_tendsto
#print axioms clockExpression_bound
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialFourierClock
