/- Pointwise density of the actual T B output for arbitrary sourced
Gaussians. The complex clock slope used in response transport is derived
from the existing operator graph, including its ordered correction. -/
import UnifiedTheory.Audit.KFCausalSourcedMomentumOutput
import UnifiedTheory.Audit.KFCausalClockResponseTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalSourcedMomentumDensity
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (weakSlope)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (argument scale)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude gaussianState_profile)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile)
open UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDifferential (inverseClock)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical (physicalSymbol)
open UnifiedTheory.Audit.KFCausalClockFloorOrderedMomentumCommutator (correction)
open UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction (reducedOutput)
open UnifiedTheory.Audit.KFCausalShiftedClockMomentOperator
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
  (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "G" => shiftedOutput ε a α β hε ha hα hβ hw C p b h hb
local notation "Ghalf" => shiftedOutput ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb
local notation "Φ" => profile (clockAmplitude ε a p (-h/2)) (scale ε (-h/2)) α β b

theorem shifted_density : G =ᵐ[volume] fun x => C*Φ x := by
  filter_upwards [Lp.coeFn_smul C
    (KFCausalClockFloorCoherentSpectral.gaussianState ε a α β p b (-h/2) hε ha hα hβ hw (shift_bound ε h hb)),
    gaussianState_profile ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb)] with x hs hp
  exact hs.trans (by simp only [Pi.smul_apply,smul_eq_mul,hp])

theorem correction_density (f : Hilbert) : correction ε hε h hb f =ᵐ[volume] fun x =>
    (Complex.I*(h:ℂ)/2)*(inverseClock ε (-h/2) x.1-
      (ε:ℂ)*(inverseClock ε (-h/2) x.1)^2)*f x := by
  let M := KFCausalClockFloorVacuumMomentumResponse.multiplier ε hε h hb
  filter_upwards [Lp.coeFn_smul (Complex.I*(h:ℂ)/(2*(ε:ℂ))) (M f),
    KFCausalClockFloorVacuumMomentumResponse.multiplier_coe ε hε h hb f] with x hs hm
  change ((Complex.I*(h:ℂ)/(2*(ε:ℂ))) • M f) x = _
  simp only [Pi.smul_apply,smul_eq_mul,M] at hs
  rw [hs,hm]
  have hz : physicalSymbol ε h x = (ε:ℂ)*inverseClock ε (-h/2) x.1 := by
    simp only [physicalSymbol,KFCausalClockFloorComplexDefect.complexDefect,
      inverseClock,argument,div_eq_mul_inv]
  rw [hz]
  field_simp [Complex.ofReal_ne_zero.mpr hε.ne']

theorem momentum_density : reducedOutput ε a h hε ha hb p G Ghalf =ᵐ[volume] fun x =>
    (-Complex.I*(h:ℂ))*weakSlope ε a p (-h/2) x.1*(C*Φ x) := by
  have hm : momentOperator ε a (-h/2) ha Ghalf =ᵐ[volume]
      fun x => argument ε (-h/2) x.1*(C*Φ x) := by
    change momentOperator ε a (-h/2) ha (C • _) =ᵐ[volume] _
    rw [map_smul]
    filter_upwards [Lp.coeFn_smul C (momentOperator ε a (-h/2) ha
      (KFCausalClockFloorCoherentSpectral.gaussianState ε (a/2) α β p b (-h/2)
        hε (by positivity) hα hβ hw (shift_bound ε h hb))),
      gaussian_moment_coe ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb)] with x hs hg
    simp only [Pi.smul_apply,smul_eq_mul] at hs
    rw [hs,hg]
    ring
  let Z := inverseOperator ε (-h/2) hε (shift_bound ε h hb)
  let M := momentOperator ε a (-h/2) ha
  filter_upwards [Lp.coeFn_sub ((-Complex.I*(h:ℂ)) • (((p:ℂ)*Complex.I-1) • Z G-(2*(a:ℂ)) • M Ghalf))
      (correction ε hε h hb G),
    Lp.coeFn_smul (-Complex.I*(h:ℂ)) (((p:ℂ)*Complex.I-1) • Z G-(2*(a:ℂ)) • M Ghalf),
    Lp.coeFn_sub (((p:ℂ)*Complex.I-1) • Z G) ((2*(a:ℂ)) • M Ghalf),
    Lp.coeFn_smul ((p:ℂ)*Complex.I-1) (Z G),Lp.coeFn_smul (2*(a:ℂ)) (M Ghalf),
    inverseOperator_coe ε (-h/2) hε (shift_bound ε h hb) G,hm,
    correction_density ε hε h hb G,shifted_density ε a α β hε ha hα hβ hw C p b h hb]
    with x ht hs hd hz hM hi hm hc hg
  change ((-Complex.I*(h:ℂ)) • (((p:ℂ)*Complex.I-1) • Z G-(2*(a:ℂ)) • M Ghalf)-
    correction ε hε h hb G) x = _
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at ht hs hd hz hM
  rw [ht,hs,hd,hz,hM]
  simp only [Z,M,hi,hm,hc,hg,weakSlope]
  ring

include hb in
theorem actual_composition_density (hh : h ≠ 0) :
    ∃ bf tbf : Hilbert,
      (KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw C p b,bf) ∈
        (KFCausalClockFloorPureClockMomentum.pureMomentum ε hε h).graph ∧
      (bf,tbf) ∈ (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph ∧
      tbf =ᵐ[volume] fun x => (-Complex.I*(h:ℂ))*weakSlope ε a p (-h/2) x.1*(C*Φ x) := by
  obtain ⟨bf,_,_,_,hB,_,_,_,_⟩ :=
    KFCausalSourcedPureClockCommutator.actual_compositions ε a α β hε ha hα hβ hw C p b h hh hb
  exact ⟨bf,_,hB,KFCausalSourcedMomentumOutput.reduced_graph ε a α β hε ha hα hβ hw C p b h hh hb bf hB,
    momentum_density ε a α β hε ha hα hβ hw C p b h hb⟩

#print axioms shifted_density
#print axioms correction_density
#print axioms momentum_density
#print axioms actual_composition_density
end
end UnifiedTheory.Audit.KFCausalSourcedMomentumDensity
