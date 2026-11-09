/- Actual growing-factor representatives for joint neutral/reciprocal
packets. The neutral polynomial and source are evaluated at the same
complex sheared coordinate for every charged width. -/
import UnifiedTheory.Audit.KFCausalVariableWidthOrderedProfile
import UnifiedTheory.Audit.KFCausalVariableWidthOrderedMomentum
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPackets
import UnifiedTheory.Audit.KFCausalReciprocalGaussianOutputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralOrderedProfile
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalRelativeGaussianDifferential (position)
open KFCausalReciprocalGaussianCoordinates (exponent)
open KFCausalReciprocalSqueezeFlow (squeeze diagonal offDiagonal)
open KFCausalReciprocalSqueezeTransport
open KFCausalReciprocalSqueezeEnergy (factorScale)
open KFCausalReciprocalGaussianDomain (baseWidth baseWidth_positive baseWidth_bound)
open KFCausalNeutralExponentialProfiles (neutralSource neutralSource_exponent)
open KFCausalReciprocalNeutralPackets
  (rescaledPolynomial state output momentumOutput output_graph)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalSourcedResponseFactorBridge (index)
open KFCausalPolynomialOrderedMomentumDensity (clockSlope)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalOrderedOperatorComposition (composition_graph)
open KFCausalPhysicalField (physicalField_graph)
open KFCausalTransverseFieldSquare (fieldSquare_graph)

theorem position_squeeze (t : ℝ) (r : ℂ) (q : Transverse) :
    position r (squeeze t q) 4 = (Real.exp t:ℂ)*position r q 4 := by
  have hm : squeeze t q 2+squeeze t q 3 = Real.exp t*(q 2+q 3) := by
    dsimp [squeeze,diagonal,offDiagonal]
    ring
  simp only [position,ite_true,← Complex.ofReal_add,hm]
  change ((Real.exp t*q 4:ℝ):ℂ)+_ = _
  push_cast
  ring

theorem position_rescale (t : ℝ) (r : ℂ) (q : Transverse) :
    (Real.exp (-t):ℂ)*position r (squeeze t q) 4 = position r q 4 := by
  rw [position_squeeze,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  simp

theorem polynomial_rescale (t : ℝ) (P : Polynomial ℂ) (r : ℂ) (q : Transverse) :
    (rescaledPolynomial t P).eval (position r (squeeze t q) 4) =
      P.eval (position r q 4) := by
  simp only [rescaledPolynomial,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,position_rescale]

def shiftedProfile (ε a α β h w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (x : Configuration) : ℂ :=
  C*clockAmplitude ε a p (-h/2) x.1*
    Complex.exp (exponent α β w (scale ε (-h/2) x.1) x.2)*
    Complex.exp (b*position (scale ε (-h/2) x.1) x.2 4)*
    P.eval (position (scale ε (-h/2) x.1) x.2 4)

theorem profile_squeeze (ε a α β h t : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (x : Configuration) :
    KFCausalVariableWidthOrderedProfile.orderedProfile ε a α (β*Real.exp (-2*t)) h
      C p (neutralSource ((Real.exp (-t):ℂ)*b)) 4 (rescaledPolynomial t P)
      (x.1,squeeze t x.2) =
        shiftedProfile ε a α β h (Real.exp (2*t)) C p b P x := by
  simp only [KFCausalVariableWidthOrderedProfile.orderedProfile,polynomial_rescale,
    KFCausalVariableWidthOrderedProfile.gaussianProfile,
    KFCausalRelativeGaussianDifferential.profile,neutralSource_exponent,
    KFCausalReciprocalGaussianOutputs.exponent_squeeze]
  have hs : ((Real.exp (-t):ℂ)*b)*position (scale ε (-h/2) x.1) (squeeze t x.2) 4 =
      b*position (scale ε (-h/2) x.1) x.2 4 := by
    rw [mul_assoc,mul_comm b,← mul_assoc,position_rescale]
    ring
  rw [hs,Complex.exp_add]
  unfold shiftedProfile
  ring

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "τ" => Real.log w/2
local notation "hτ" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h τ
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh τ
local notation "hwidth" => baseWidth_bound h hh τ hτ
local notation "d" => neutralSource ((Real.exp (-τ):ℂ)*b)
local notation "Q" => rescaledPolynomial τ P
local notation "k" => (Real.exp (-τ/2):ℂ)
local notation "U" => output ε a h w hε ha hh hw C p b P hb
local notation "V" => momentumOutput ε a h w hε ha hh hw C p b P hb
local notation "S" => shiftedProfile ε a α (neutralWidth h) h w C p b P

theorem output_vacuum_coe : U 7 =ᵐ[volume] S := by
  let f := KFCausalVariableWidthPolynomialDomain.output ε a α β hε ha hα hβ hwidth h
    C p d 4 hb Q modelDirections pointField 7
  have hu : U 7 = k • transport (-τ) f := by
    change k • (factorScale (-τ) 7 • transport (-τ) f) = _
    have hs : factorScale (-τ) 7 = 1 := by
      change (Real.exp (0*(-τ)):ℂ) = 1
      simp
    rw [hs,one_smul]
  rw [hu]
  filter_upwards [Lp.coeFn_smul k (transport (-τ) f),transport_coe (-τ) f,
    (squeezeFlow_quasiMeasurePreserving (-τ)).ae
      (KFCausalVariableWidthOrderedProfile.output_vacuum_coe ε a α β hε ha hα hβ hwidth h hb
        C p d 4 Q modelDirections pointField)] with x hc ht hf
  rw [hc,Pi.smul_apply,smul_eq_mul,ht]
  change f (squeezeFlow (-τ) x) = _ at hf
  rw [hf]
  simp only [squeezeFlow_apply,neg_neg,baseWidth]
  rw [profile_squeeze]
  have he : Real.exp (2*τ) = w := by
    rw [show 2*τ=Real.log w by ring,Real.exp_log (by linarith)]
  rw [he,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add,
    show -τ/2+τ/2=0 by ring,Real.exp_zero,Complex.ofReal_one,one_mul]

theorem output_linear_coe : U 5 =ᵐ[volume] fun x => (pointField x.2:ℂ)*S x := by
  obtain ⟨Y,hY,hL⟩ := (composition_graph _ _ _ _).mp
    (output_graph ε a h w hε ha hh hw C p b P hb 5)
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hY
    (output_graph ε a h w hε ha hh hw C p b P hb 7) rfl
  dsimp only at he
  rw [he] at hL
  filter_upwards [(physicalField_graph pointField _ _).mp hL,
    output_vacuum_coe ε a h w hε ha hh hw C p b P hb] with x hx hy
  rw [hx,hy]

theorem output_quadratic_coe : U 6 =ᵐ[volume] fun x => (pointField x.2:ℂ)^2*S x := by
  obtain ⟨Y,hY,hL⟩ := (composition_graph _ _ _ _).mp
    (output_graph ε a h w hε ha hh hw C p b P hb 6)
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hY
    (output_graph ε a h w hε ha hh hw C p b P hb 7) rfl
  dsimp only at he
  rw [he] at hL
  filter_upwards [(fieldSquare_graph pointField _ _).mp hL,
    output_vacuum_coe ε a h w hε ha hh hw C p b P hb] with x hx hy
  rw [hx,hy]

theorem output_coe (n : Fin 3) : U (index n) =ᵐ[volume]
    fun x => (pointField x.2:ℂ)^n.val*S x := by
  fin_cases n
  · simpa only [index,Matrix.cons_val_zero,pow_zero,one_mul] using
      output_vacuum_coe ε a h w hε ha hh hw C p b P hb
  · simpa only [index,Matrix.cons_val_one,pow_one] using
      output_linear_coe ε a h w hε ha hh hw C p b P hb
  · exact output_quadratic_coe ε a h w hε ha hh hw C p b P hb

theorem momentum_relation (n : Fin 3) :
    KFCausalUnboundedMultiplierIntegral.relation (clockSlope ε a h p) (U (index n)) (V (index n)) := by
  let f := KFCausalVariableWidthPolynomialDomain.output ε a α β hε ha hα hβ hwidth h
    C p d 4 hb Q modelDirections pointField (index n)
  let g := KFCausalVariableWidthPolynomialMomentum.momentumFactor ε a α β hε ha hα hβ hwidth h
    p d 4 C hb Q modelDirections pointField (index n)
  have hr := KFCausalVariableWidthOrderedMomentum.polynomial_relation ε a α β hε ha hα hβ hwidth h hh hb
    C p d 4 Q modelDirections pointField n
  filter_upwards [Lp.coeFn_smul k (factorScale (-τ) (index n) • transport (-τ) f),
    Lp.coeFn_smul k (factorScale (-τ) (index n) • transport (-τ) g),
    Lp.coeFn_smul (factorScale (-τ) (index n)) (transport (-τ) f),
    Lp.coeFn_smul (factorScale (-τ) (index n)) (transport (-τ) g),
    transport_coe (-τ) f,transport_coe (-τ) g,
    (squeezeFlow_quasiMeasurePreserving (-τ)).ae hr] with x huf hug htf htg hf hg hr
  change g (squeezeFlow (-τ) x) = _ at hr
  change (k • (factorScale (-τ) (index n) • transport (-τ) g)) x =
    clockSlope ε a h p x*(k • (factorScale (-τ) (index n) • transport (-τ) f)) x
  rw [huf,hug]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [htf,htg]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hf,hg,hr]
  simp only [clockSlope,squeezeFlow_apply]
  ring

theorem momentumOutput_coe (n : Fin 3) : V (index n) =ᵐ[volume]
    fun x => clockSlope ε a h p x*((pointField x.2:ℂ)^n.val*S x) := by
  filter_upwards [momentum_relation ε a h w hε ha hh hw C p b P hb n,
    output_coe ε a h w hε ha hh hw C p b P hb n] with x hm hu
  rw [hm,hu]

#print axioms position_squeeze
#print axioms position_rescale
#print axioms polynomial_rescale
#print axioms profile_squeeze
#print axioms output_vacuum_coe
#print axioms output_linear_coe
#print axioms output_quadratic_coe
#print axioms output_coe
#print axioms momentum_relation
#print axioms momentumOutput_coe
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralOrderedProfile
