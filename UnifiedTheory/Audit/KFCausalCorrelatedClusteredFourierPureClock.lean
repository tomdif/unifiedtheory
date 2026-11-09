/- The joint Fourier representatives have actual pure-clock generator
graphs, not merely pointwise derivatives. The half-density correction and
-I*h factor are retained. Transport back to the physical endpoints is separate. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierOperatorBridge
import UnifiedTheory.Audit.KFCausalClockFloorPureClockDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierPureClock
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalShiftedNarrowJointGaussian (narrow spectator N Z)
open KFCausalShiftedNarrowControlledFactors (F)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalClockLimit (amplitudes)
open KFCausalCorrelatedClusteredPotentialFourierClock
open KFCausalCorrelatedClusteredJointFourierL2Limit
open KFCausalClockFloorPureClockDerivative (differential)
open KFCausalCanonicalClockDerivative (clockDerivative)
open KFCausalClockFloorPureClockMomentum (pureMomentum)

variable (α β ε y z : ℝ) (hα : 0 < α) (hε : 0 < ε)
  (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3)

include hε hy in
theorem radius_smooth : ContDiff ℝ 1 (Z α ε y) := by
  have hr := (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy)
  have hn (s : ℝ) : scale ε y s ≠ 0 := fun he => by
    have hp := KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy
    rw [he] at hp
    exact lt_irrefl 0 hp
  have ho : ContDiff ℝ 1 (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  unfold Z
  simp only [KFCausalShiftedNarrowFourierClockBounds.radius_split,← Complex.ofReal_pow,
    KFCausalShiftedNarrowJointGaussian.narrow_square]
  dsimp [spectator,KFCausalShiftedNarrowFourierGeometry.broadRadius]
  fun_prop (disch := intro x; exact pow_ne_zero 2 (hn x.1))

variable {m : ℕ} (f : Family m) (a p : Fin m → ℝ) (k : ℕ)
local notation "c" => amplitudes ε y a p

theorem polynomial_eval_smooth (P : Polynomial ℂ) :
    ContDiff ℝ 1 (fun w : ℂ => P.eval w) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add] using hP.add hQ
  | monomial n b => simpa only [Polynomial.eval_monomial] using
      (contDiff_const.mul (contDiff_id.pow n) : ContDiff ℝ 1 (fun w : ℂ => b*w^n))

include hα hε hy hz in
theorem coefficient_smooth (i : Fin m) :
    ContDiff ℝ 1 (fun x : Configuration =>
      KFCausalCorrelatedClusteredShiftedNarrowProfiles.coefficient f (c x.1) α β
        (scale ε y x.1) (scale ε z x.1) k i (spectator x)) := by
  have hr := (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy)
  have ht := (KFCausalClockFloorRelativeShift.scale_smooth ε z hε hz)
  have hc := (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude_smooth ε (a i) (p i) y hε hy)
  have hn (s : ℝ) : (α:ℂ)*scale ε y s^2 ≠ 0 := fun he => by
    have hp := KFCausalShiftedNarrowFourierGeometry.shifted_coefficient_positive α ε y s hα hε hy
    rw [he] at hp
    exact lt_irrefl 0 hp
  have ho : ContDiff ℝ 1 (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  have hp := polynomial_eval_smooth (f.polynomial i)
  have hn0 : ContDiff ℝ 1 (fun x : Configuration =>
      KFCausalShiftedNarrowFourierGeometry.neutral (scale ε y x.1) (spectator x)) := by
    dsimp [KFCausalShiftedNarrowFourierGeometry.neutral,spectator]
    fun_prop
  have ht0 : ContDiff ℝ 1 (fun x : Configuration =>
      KFCausalShiftedNarrowFourierGeometry.mixedField (scale ε z x.1) (spectator x)) := by
    dsimp [KFCausalShiftedNarrowFourierGeometry.mixedField,spectator]
    fun_prop
  unfold KFCausalCorrelatedClusteredShiftedNarrowProfiles.coefficient
    KFCausalShiftedNarrowFourierSlices.neutralPacket
  apply ContDiff.mul
  · dsimp [amplitudes]
    simp only [div_eq_mul_inv]
    fun_prop (disch := intro x; exact hn x.1)
  · exact ((contDiff_const.mul (hn0.pow 2)).add (contDiff_const.mul hn0)).cexp.mul (hp.comp hn0)

def profile (δ : ℝ) (x : Configuration) : ℂ :=
  fourierProfile f α β ε y z a p k δ x.1 (narrow x) (spectator x)
def limitProfile (x : Configuration) : ℂ :=
  fourierLimit f α β ε y z a p k x.1 (narrow x) (spectator x)

include hα hε hy hz in
theorem profile_differentiable (δ : ℝ) (hδ : 0 < δ) :
    Differentiable ℝ (profile α β ε y z f a p k δ) := by
  have hr := radius_smooth α ε y hε hy
  have hc := coefficient_smooth α β ε y z hα hε hy hz f a p k
  have he : profile α β ε y z f a p k δ = fun x : Configuration =>
      ∑ i, KFCausalCorrelatedClusteredShiftedNarrowProfiles.coefficient f (c x.1) α β
        (scale ε y x.1) (scale ε z x.1) k i (spectator x)*
          (Complex.exp (-Z α ε y x)*KFCausalClusteredWidthProfiles.quotient δ (Z α ε y x)^(f.degree i)) := by
    funext x
    rw [profile,fourierProfile_eq f α β ε y z a p k hα hε hy δ x.1 hδ,
      KFCausalCorrelatedClusteredShiftedNarrowProfiles.transformed_exact _ _ _ _ _ _ _ δ hδ]
    rfl
  apply ContDiff.differentiable (n := 1) ?_ (by norm_num)
  rw [he]
  apply ContDiff.sum
  intro i _
  exact (hc i).mul (hr.neg.cexp.mul
    (((contDiff_const.sub (contDiff_const.mul hr).cexp).div_const (δ:ℂ)).pow (f.degree i)))

include hα hε hy hz in
theorem limitProfile_differentiable : Differentiable ℝ (limitProfile α β ε y z f a p k) := by
  have hr := radius_smooth α ε y hε hy
  have hc := coefficient_smooth α β ε y z hα hε hy hz f a p k
  apply ContDiff.differentiable (n := 1) ?_ (by norm_num)
  change ContDiff ℝ 1 (fun x : Configuration =>
    ∑ i, KFCausalCorrelatedClusteredShiftedNarrowProfiles.coefficient f (c x.1) α β
      (scale ε y x.1) (scale ε z x.1) k i (spectator x)*
        (Complex.exp (-Z α ε y x)*Z α ε y x^(f.degree i)))
  apply ContDiff.sum
  intro i _
  exact (hc i).mul (hr.neg.cexp.mul (hr.pow (f.degree i)))

include hα hε hy hz in
theorem profile_clockDerivative (δ : ℝ) (hδ : 0 < δ) (x : Configuration) :
    clockDerivative (profile α β ε y z f a p k δ) x =
      fourierJet f α β ε y z a p k δ x.1 (narrow x) (spectator x) := by
  have hp := (profile_differentiable α β ε y z hα hε hy hz f a p k δ hδ x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  change HasDerivAt (fun s => profile α β ε y z f a p k δ (s,x.2))
    (clockDerivative (profile α β ε y z f a p k δ) x) x.1 at hp
  exact hp.unique (fourierProfile_derivative f α β ε y z a p k hα hε hy hz δ x.1 hδ (narrow x) (spectator x))

include hα hε hy hz in
theorem limitProfile_clockDerivative (x : Configuration) :
    clockDerivative (limitProfile α β ε y z f a p k) x =
      fourierLimitJet f α β ε y z a p k x.1 (narrow x) (spectator x) := by
  have hp := (limitProfile_differentiable α β ε y z hα hε hy hz f a p k x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  change HasDerivAt (fun s => limitProfile α β ε y z f a p k (s,x.2))
    (clockDerivative (limitProfile α β ε y z f a p k) x) x.1 at hp
  exact hp.unique (fourierLimit_derivative f α β ε y z a p k hα hε hy hz x.1 (narrow x) (spectator x))

include hα hε hy hz in
theorem profile_differential (δ : ℝ) (hδ : 0 < δ) (x : Configuration) :
    differential ε (profile α β ε y z f a p k δ) x =
      clockExpression f α β ε y z a p k δ x.1 (narrow x) (spectator x) := by
  unfold differential
  rw [profile_clockDerivative α β ε y z hα hε hy hz f a p k δ hδ x]
  rfl

include hα hε hy hz in
theorem limitProfile_differential (x : Configuration) :
    differential ε (limitProfile α β ε y z f a p k) x =
      clockLimitExpression f α β ε y z a p k x.1 (narrow x) (spectator x) := by
  unfold differential
  rw [limitProfile_clockDerivative α β ε y z hα hε hy hz f a p k x]
  rfl

#print axioms polynomial_eval_smooth
#print axioms radius_smooth
#print axioms coefficient_smooth
#print axioms profile_differentiable
#print axioms limitProfile_differentiable
#print axioms profile_clockDerivative
#print axioms limitProfile_clockDerivative
#print axioms profile_differential
#print axioms limitProfile_differential
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredFourierPureClock
