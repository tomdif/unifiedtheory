/- Longitudinal momentum domains for the original coherent inputs. The
clock derivative and its weighted L2 estimate are derived explicitly;
the inverse-clock-weighted Gaussian is not substituted for the input. -/
import UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDomain
import UnifiedTheory.Audit.KFCausalCoherentShearDomain
import UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoherentLongitudinalDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (velocity)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chart_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (clockFunction realClock clockFunction_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments (sourcedPacket)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
open UnifiedTheory.Audit.KFCausalCoherentShearDifferential (sourcedPacket_contDiff shear_gradient_memLp)
open UnifiedTheory.Audit.KFCausalClockFloorDifferentialMomentum (differential differential_graph)
open UnifiedTheory.Audit.KFCausalClockFloorTransportDerivative (coupledVelocity_split)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative (clockDerivative)

def clockSlope (ε a s : ℝ) : ℝ := Real.exp s/(Real.exp s+ε)-1-2*a*chart ε s*(Real.exp s+ε)

theorem clockFunction_derivative (ε a s : ℝ) (hε : 0 < ε) :
    HasDerivAt (clockFunction ε a) ((clockSlope ε a s:ℂ)*clockFunction ε a s) s := by
  have he : clockFunction ε a = fun t =>
      (((Real.exp t+ε)*Real.exp (-t)*Real.exp (-a*(chart ε t)^2):ℝ):ℂ) := by
    funext t
    have hex : Real.exp t*Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    simp only [clockFunction,realClock,add_mul,hex,one_mul]
  rw [he]
  have hd := (((Real.hasDerivAt_exp s).add_const ε).mul (hasDerivAt_neg s).exp).mul
    (((chart_derivative ε s).pow 2).const_mul (-a)).exp
  convert hd.ofReal_comp using 1
  simp only [Nat.cast_ofNat,show 2-1=1 from rfl,pow_one,Pi.mul_apply,Pi.pow_apply]
  unfold clockSlope
  simp only [Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_neg,Complex.ofReal_ofNat,Complex.ofReal_one]
  have hc : (Real.exp s:ℂ)+(ε:ℂ) ≠ 0 := by exact_mod_cast (show Real.exp s+ε ≠ 0 by positivity)
  field_simp [hc]
  ring

theorem profile_smooth (ε a : ℝ) (C : ℂ) (p α β : ℝ) (b : Fin 5 → ℂ) :
    ContDiff ℝ 1 (physicalProfile C p α β b (clockFunction ε a)) := by
  have hg : ContDiff ℝ 1 (clockFunction ε a) := by
    have hr : ContDiff ℝ 1 (realClock ε a) := by unfold realClock chart; fun_prop
    exact Complex.ofRealCLM.contDiff.comp hr
  have hp : ContDiff ℝ 1 (clockMultiplier C p (clockFunction ε a)) := by
    unfold clockMultiplier clockPhase
    exact (contDiff_const.mul (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp).mul hg
  exact (hp.comp contDiff_fst).mul ((sourcedPacket_contDiff α β b).comp contDiff_snd)

theorem profile_clock_derivative (ε a : ℝ) (hε : 0 < ε) (C : ℂ) (p α β : ℝ)
    (b : Fin 5 → ℂ) (x : Configuration) :
    clockDerivative (physicalProfile C p α β b (clockFunction ε a)) x =
      ((clockSlope ε a x.1:ℂ)+(p:ℂ)*Complex.I)*physicalProfile C p α β b (clockFunction ε a) x := by
  have hp := (((hasDerivAt_id x.1).ofReal_comp.const_mul ((p:ℂ)*Complex.I)).cexp.const_mul C).mul
    (clockFunction_derivative ε a x.1 hε)
  have hd := hp.mul_const (sourcedPacket α β b x.2)
  have hf := (((profile_smooth ε a C p α β b).differentiable (by norm_num)) x).hasFDerivAt.comp_hasDerivAt
    x.1 ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  have he := hf.unique hd
  change clockDerivative (physicalProfile C p α β b (clockFunction ε a)) x = _ at he
  rw [he]
  simp only [Complex.ofReal_one,mul_one,id_eq]
  unfold physicalProfile clockMultiplier clockPhase
  ring

theorem profile_differential (ε a : ℝ) (hε : 0 < ε) (C : ℂ) (p α β : ℝ)
    (b : Fin 5 → ℂ) (x : Configuration) :
    differential ε (physicalProfile C p α β b (clockFunction ε a)) x =
      (-(KFCausalClockFloorPureClockDerivative.rate ε x.1:ℂ)+
        (p:ℂ)*Complex.I*((Real.exp x.1+ε:ℝ):ℂ)⁻¹-2*(a:ℂ)*(chart ε x.1:ℂ))*
        physicalProfile C p α β b (clockFunction ε a) x+
      ((Real.exp x.1+ε:ℝ):ℂ)⁻¹*(clockMultiplier C p (clockFunction ε a) x.1*
        gradient α β b (velocity x.2) x.2) := by
  have ht := ((sourcedPacket_hasLineDerivAt α β b (velocity x.2) x.2).const_mul
    (clockMultiplier C p (clockFunction ε a) x.1))
  have hl : HasLineDerivAt ℝ (physicalProfile C p α β b (clockFunction ε a))
      (clockMultiplier C p (clockFunction ε a) x.1*gradient α β b (velocity x.2) x.2)
      x ((0,velocity x.2):Configuration) := by
    change HasDerivAt (fun t : ℝ => physicalProfile C p α β b (clockFunction ε a)
      (x+t • (0,velocity x.2))) _ 0
    convert ht using 1
    funext t
    simp [physicalProfile]
  have hs := hl.unique (((profile_smooth ε a C p α β b).differentiable (by norm_num) x).hasFDerivAt.hasLineDerivAt
    ((0,velocity x.2):Configuration))
  unfold differential
  rw [coupledVelocity_split,map_add,map_smul,map_smul]
  change _+(((Real.exp x.1+ε)⁻¹:ℝ) • clockDerivative (physicalProfile C p α β b (clockFunction ε a)) x+
    ((Real.exp x.1+ε)⁻¹:ℝ) • _) = _
  rw [profile_clock_derivative ε a hε C p α β b x,← hs]
  simp only [Complex.real_smul,Complex.ofReal_inv]
  unfold KFCausalClockFloorTransportDerivative.rate KFCausalClockFloorPureClockDerivative.rate
    KFCausalClockFloorFlow.clock clockSlope
  simp only [Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_div,
    Complex.ofReal_neg,Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_one,Complex.ofReal_inv]
  have hc : (Real.exp x.1:ℂ)+(ε:ℂ) ≠ 0 := by exact_mod_cast (show Real.exp x.1+ε ≠ 0 by positivity)
  field_simp [hc]
  ring

theorem profile_differential_memLp (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (C : ℂ) (p α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ) :
    MemLp (differential ε (physicalProfile C p α β b (clockFunction ε a))) 2 volume := by
  let f := physicalProfile C p α β b (clockFunction ε a)
  have hf := physicalProfile_memLp C p α β hα hβ hw b _ (clockFunction_memLp ε a hε ha)
  have hi : Continuous (fun s : ℝ => ((Real.exp s+ε:ℝ):ℂ)⁻¹) := by
    fun_prop (disch := intro s; exact Complex.ofReal_ne_zero.mpr (by positivity))
  have hib (s : ℝ) : ‖((Real.exp s+ε:ℝ):ℂ)⁻¹‖ ≤ 1/ε := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < Real.exp s+ε)]
    simpa only [one_div] using
      (inv_le_inv₀ (show 0 < Real.exp s+ε by positivity) hε).mpr (by linarith [Real.exp_pos s])
  have hinv := KFCausalShearPolynomialMoments.clock_mul_memLp _ hi (1/ε) (by positivity) hib
  have hr : Continuous (fun s => (KFCausalClockFloorPureClockDerivative.rate ε s:ℂ)) := by
    unfold KFCausalClockFloorPureClockDerivative.rate KFCausalClockFloorFlow.clock
    fun_prop (disch := intro s; positivity)
  have hrate := KFCausalShearPolynomialMoments.clock_mul_memLp _ hr (1/(8*ε)) (by positivity)
    (fun s => by simpa only [Complex.norm_real,Real.norm_eq_abs] using
      KFCausalClockFloorPureClockCommonDomain.rate_bound ε hε s) f hf
  have hmoment : MemLp (fun x : Configuration => (chart ε x.1:ℂ)*f x) 2 volume := by
    convert physicalProfile_memLp C p α β hα hβ hw b _
      (KFCausalGaussianClockMoment.clockFunction_moment_memLp ε a hε ha) using 1
    funext x
    unfold f physicalProfile clockMultiplier
    ring
  have hgradient := KFCausalPhysicalGaussianDerivative.configuration_product_memLp _ _
    (clockMultiplier_memLp C p _ (clockFunction_memLp ε a hε ha))
    (shear_gradient_memLp α β hα hβ hw b)
  convert ((hrate.neg.add ((hinv f hf).const_mul ((p:ℂ)*Complex.I))).sub
    (hmoment.const_mul (2*(a:ℂ)))).add (hinv _ hgradient) using 1
  funext x
  rw [profile_differential ε a hε C p α β b x]
  simp only [Pi.add_apply,Pi.sub_apply,Pi.neg_apply]
  dsimp only [f]
  ring

theorem profile_domain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (C : ℂ) (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ) :
    (physicalProfile_memLp C p α β hα hβ hw b _ (clockFunction_memLp ε a hε ha)).toLp
      (physicalProfile C p α β b (clockFunction ε a)) ∈ (longitudinalMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (differential_graph ε hε h hh _ _
    (profile_differential_memLp ε a hε ha C p α β hα hβ hw b)
    ((profile_smooth ε a C p α β b).differentiable (by norm_num)))

theorem state_domain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (k : Joint 2 4) :
    KFCausalClockFloorCoherentStates.state ε a h hε ha hh k ∈ (longitudinalMomentum ε hε h).domain := by
  rw [KFCausalCoherentShearDomain.state_eq_toLp]
  exact profile_domain ε a h hε ha hh _ _ _ _
    (KFCausalChargeGaussianGeometry.groundWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_positive h hh)
    (KFCausalClockFloorInvariantTrial.neutralWidth_bound h) _

theorem coherentSpan_le_longitudinalDomain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) :
    KFCausalClockFloorCoherentCommonDomain.coherentSpan ε a h hε ha hh ≤
      (longitudinalMomentum ε hε h).domain := by
  apply Submodule.span_le.mpr
  rintro f ⟨k,rfl⟩
  exact state_domain ε a h hε ha hh k

#print axioms clockFunction_derivative
#print axioms profile_smooth
#print axioms profile_clock_derivative
#print axioms profile_differential
#print axioms profile_differential_memLp
#print axioms profile_domain
#print axioms state_domain
#print axioms coherentSpan_le_longitudinalDomain
end
end UnifiedTheory.Audit.KFCausalCoherentLongitudinalDomain
