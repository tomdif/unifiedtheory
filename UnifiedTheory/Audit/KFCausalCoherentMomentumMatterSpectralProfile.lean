/- Clock-only reduced output maps preserve a common unbounded physical
multiplier. Thus the actual mixed spectral momentum endpoint is the same
field multiplier of the doubled-parameter momentum output, divided by two. -/
import UnifiedTheory.Audit.KFCausalCoherentMatterSpectralProfile
import UnifiedTheory.Audit.KFCausalCoherentMomentumMatterSquare
import UnifiedTheory.Audit.KFCausalSourcedMomentumDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCoherentMomentumMatterSpectralProfile
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalUnboundedMultiplierIntegral (relation relation_smul)
open KFCausalCoherentMomentumOutputReduction (reducedOutput)
open KFCausalShiftedClockMomentOperator
open KFCausalClockFloorShiftedOutput (shift_bound)
open KFCausalShiftedGaussianLongitudinalDifferential (inverseClock)
open KFCausalClockFloorOrderedMomentumCommutator (correction)
open KFCausalCoherentMatterSpectralProfile (multiplier multiplier_continuous spectral_relation)
open KFCausalGaussianVacuumSquare (double_strip)

section
variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hb : |h| ≤ 2*Real.pi*ε/3) (p : ℝ)

theorem reducedOutput_coe (f g : Hilbert) : reducedOutput ε a h hε ha hb p f g =ᵐ[volume] fun x =>
    (-Complex.I*(h:ℂ))*(((p:ℂ)*Complex.I-1)*inverseClock ε (-h/2) x.1*f x-
      (2*(a:ℂ))*momentMultiplier ε a (-h/2) x.1*g x)-
        (Complex.I*(h:ℂ)/2)*(inverseClock ε (-h/2) x.1-
          (ε:ℂ)*inverseClock ε (-h/2) x.1^2)*f x := by
  let Z := inverseOperator ε (-h/2) hε (shift_bound ε h hb)
  let M := momentOperator ε a (-h/2) ha
  filter_upwards [Lp.coeFn_sub ((-Complex.I*(h:ℂ)) • (((p:ℂ)*Complex.I-1) • Z f-(2*(a:ℂ)) • M g))
      (correction ε hε h hb f),
    Lp.coeFn_smul (-Complex.I*(h:ℂ)) (((p:ℂ)*Complex.I-1) • Z f-(2*(a:ℂ)) • M g),
    Lp.coeFn_sub (((p:ℂ)*Complex.I-1) • Z f) ((2*(a:ℂ)) • M g),
    Lp.coeFn_smul ((p:ℂ)*Complex.I-1) (Z f),Lp.coeFn_smul (2*(a:ℂ)) (M g),
    inverseOperator_coe ε (-h/2) hε (shift_bound ε h hb) f,
    momentOperator_coe ε a (-h/2) ha g,KFCausalSourcedMomentumDensity.correction_density ε hε h hb f]
    with x ht hs hd hz hm hi hM hc
  change ((-Complex.I*(h:ℂ)) • (((p:ℂ)*Complex.I-1) • Z f-(2*(a:ℂ)) • M g)-correction ε hε h hb f) x = _
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at ht hs hd hz hm
  rw [ht,hs,hd,hz,hm]
  simp only [Z,M,hi,hM,hc]
  ring

theorem reduced_relation (w : Configuration → ℂ) (f g u v : Hilbert)
    (hf : relation w f u) (hg : relation w g v) :
    relation w (reducedOutput ε a h hε ha hb p f g) (reducedOutput ε a h hε ha hb p u v) := by
  filter_upwards [reducedOutput_coe ε a h hε ha hb p f g,reducedOutput_coe ε a h hε ha hb p u v,hf,hg]
    with x hfg huv hfu hgv
  rw [hfg,huv,hfu,hgv]
  ring
end

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hb : |h| ≤ Real.pi*ε/3) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)

theorem spectral_relation (j : Fin 2) : relation (multiplier ε h j)
    ((1/2:ℂ) • KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw C p b
      (2*h) (double_strip ε h hb) KFCausalPhysicalEnergyFactors.modelDirections KFCausalMatterOrderedDomain.pointField 7)
    (KFCausalCoherentMomentumMatterSquare.spectralOutput ε a α β hε ha hα hβ hw h hb C p b j) := by
  have hr := reduced_relation ε a (2*h) hε ha (double_strip ε h hb) p (multiplier ε h j) _ _ _ _
    (KFCausalCoherentMatterSpectralProfile.spectral_relation ε a α β hε ha hα hβ hw h hb C p b j)
    (KFCausalCoherentMatterSpectralProfile.spectral_relation ε (a/2) α β hε (half_pos ha) hα hβ hw h hb C p b j)
  exact relation_smul _ (multiplier_continuous ε h hε hb j).measurable _ _ hr (1/2:ℂ)

#print axioms reducedOutput_coe
#print axioms reduced_relation
#print axioms spectral_relation
end
end UnifiedTheory.Audit.KFCausalCoherentMomentumMatterSpectralProfile
