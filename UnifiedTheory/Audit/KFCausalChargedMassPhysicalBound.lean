/- State-independent bound for the actual-clock corrected marginal.
All geometric coefficients are the original scale and its derivative;
the zero imaginary shift is covered without division by that shift. -/
import UnifiedTheory.Audit.KFCausalChargedMassCorrectedBound
import UnifiedTheory.Audit.KFCausalQuarticResponseClockCoefficients

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedMassPhysicalBound
noncomputable section
open MeasureTheory
open KFCausalChargedMassScoreIBP
open KFCausalChargedQuarticCorrectedBound (scoreHalf)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
open KFCausalJointClockCoolingCoercivity (imaginaryRate)
open KFCausalJointFourierDissipationClock
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalWedgeGeometry (gamma)

theorem global_bound : ∃ K : ℝ,0≤K ∧ ∀ (n : ℕ) (α β ε y s q mu : ℝ)
    (w : Fin n→ℝ) (c : Fin n→ℂ),0<α→0<β→0<ε→|y|≤Real.pi*ε/3→
    (∀i,0<w i)→(∀i,8*β*(scale ε y s).im^2<2*(gamma α (scale ε y s)).re*w i)→
    let r := scale ε y s;
    let t := fraction ε s;
    let ell := imaginaryRate t r;
    let delta := (deriv (scale ε y) s).re-ell*r.re;
    let E := (∫v,energyDensity (1/(4*β)) (8*β*r.im^2) q mu (fieldSlope r) n α r w c v);
    let F := (∫v,fieldDensity (1/(4*β)) (8*β*r.im^2) q mu (fieldSlope r) n α r w c v);
    let C := (∫v,coolingDensity (1/(4*β)) (8*β*r.im^2) q mu (fieldSlope r) n α r w c v);
    -4*ell*E-delta*C+(-2*delta-3*ell)*F≤K*t*E := by
  obtain ⟨C,hC,hbound⟩ := KFCausalChargedMassCorrectedBound.global_corrected_bound
  refine ⟨1200+25*C/4,by positivity,?_⟩
  intro n α β ε y s q mu w c hα hβ hε hy hw hd
  dsimp only
  let r := scale ε y s
  let t := fraction ε s
  have ht := KFCausalNeutralPlaneNormalizedGeometry.fraction_bounds ε s hε
  have ht0 : 0≤t := ht.1.le
  have ht' : t∈Set.Icc 0 1 := ⟨ht.1.le,ht.2.le⟩
  have ha := KFCausalNeutralPlaneClockGeometry.scale_re_positive ε y s hε hy
  have hA := KFCausalClockFloorExactScaleRegion.square_re_half_le ε y s hε hy
  have hr : |r.im|<r.re := by dsimp [r]; nlinarith [sq_abs (scale ε y s).im,abs_nonneg (scale ε y s).im]
  have hδ : 0≤t*normalizedRealCooling t r := mul_nonneg ht.1.le
    (by have hh := (real_cooling_bounds ε y s hε hy t ht').1; linarith)
  have hc := KFCausalQuarticResponseClockCoefficients.young_certificate ε y s hε hy t β ht' hβ
  have hb := hbound n α r (1/(4*β)) (8*β*r.im^2) q mu (fieldSlope r) w c
    (t*normalizedRealCooling t r) (t*normalizedFieldJet t r) ((9800/9:ℝ)*t)
    hα hr hw hd (by positivity) (by positivity) hδ (by positivity)
    (by simpa only [KFCausalQuarticResponseClockCoefficients.residual,scoreHalf] using hc)
  have hE : 0≤∫v,energyDensity (1/(4*β)) (8*β*r.im^2) q mu (fieldSlope r) n α r w c v := by
    apply integral_nonneg
    intro v
    unfold energyDensity KFCausalAngularMassGaussianSmoothing.weight
    have hm : 0≤KFCausalChargedCoolingMarginalScore.marginal n α r w c v :=
      integral_nonneg (fun _ => sq_nonneg _)
    positivity
  have hl := mul_le_mul_of_nonneg_right
    (KFCausalQuarticResponseClockCoefficients.loss_bound ε y s hε hy t C ht' hC) hE
  have hvel : (deriv (scale ε y) s).re-imaginaryRate t r*r.re=t*normalizedRealCooling t r := by
    rw [(KFCausalNeutralPlaneNormalizedGeometry.actual_normalized_velocity ε y s hε hy).deriv]
    exact real_cooling_identity t r
  have hfield : -2*(t*normalizedRealCooling t r)-3*imaginaryRate t r=t*normalizedFieldJet t r := by
    rw [dilation_identity]
    unfold normalizedFieldJet
    ring
  change -4*imaginaryRate t r*(∫v,energyDensity (1/(4*β)) (8*β*r.im^2) q mu (fieldSlope r) n α r w c v)-
    ((deriv (scale ε y) s).re-imaginaryRate t r*r.re)*(∫v,coolingDensity (1/(4*β)) (8*β*r.im^2) q mu (fieldSlope r) n α r w c v)+
    (-2*((deriv (scale ε y) s).re-imaginaryRate t r*r.re)-3*imaginaryRate t r)*
      (∫v,fieldDensity (1/(4*β)) (8*β*r.im^2) q mu (fieldSlope r) n α r w c v)≤_
  rw [hvel,hfield]
  unfold scoreHalf at hb
  nlinarith only [hb,hl]

#print axioms global_bound
end
end UnifiedTheory.Audit.KFCausalChargedMassPhysicalBound
