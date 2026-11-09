/- Identify the actual transported initial field with a single complex
polynomial multiplying the unweighted initial interpolation state. This
checks the polynomial used by the numerical probe against the intrinsic
operators; it does not certify its quadrature or assert an energy bound. -/
import UnifiedTheory.Audit.KFCausalTransportedChargeInitial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalTransportedInitialPolynomial
noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalFieldEigenpolynomials (constantField scaleField)
open UnifiedTheory.Audit.KFCausalTransportedInitialAssembly (Fields clock assemble)
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient (displacement coefficient coefficient_generator_identity)
open UnifiedTheory.Audit.KFCausalActualTransportedField (profile profile_apply)
open UnifiedTheory.Audit.KFCausalClockProfileCalculus (transport_coe)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower_graph)
open UnifiedTheory.Audit.KFCausalCoherentMatterPathOperator (input field field_graph)
open UnifiedTheory.Audit.KFCausalIntrinsicTransportedMatter (initialInput)
open UnifiedTheory.Audit.KFCausalTransportedChargeInitial (initialInput_assembly)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

def tilt (ε h s : ℝ) : ℂ := Complex.exp (-displacement ε h s/2)

def polynomial (ε h : ℝ) (l : Transverse →L[ℝ] ℝ) (x : Configuration) : ℂ :=
  (constantField l x.2:ℂ)+tilt ε h x.1*(scaleField l x.2:ℂ)

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)

theorem clock_coe (r : ℝ) (f : Hilbert) : clock ε h hε hb hh r f =ᵐ[volume]
    fun x => Complex.exp (-(r:ℂ)*displacement ε h x.1)*f x := by
  filter_upwards [transport_coe (((-Complex.I*(h:ℂ))*(r:ℂ)) • profile ε h hε hb hh) 0 f]
    with x hx
  change clock ε h hε hb hh r f x = _ at hx
  rw [hx]
  congr 2
  simp only [BoundedContinuousFunction.smul_apply,smul_eq_mul,profile_apply]
  calc
    _ = -(r:ℂ)*(coefficient ε h x.1*(-(h:ℂ)*Complex.I)) := by norm_num; ring
    _ = _ := by rw [coefficient_generator_identity ε h x.1 hh]

theorem clock_zero_coe (f : Hilbert) : clock ε h hε hb hh 0 f =ᵐ[volume] f := by
  simpa only [Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,one_mul]
    using clock_coe ε h hε hb hh 0 f

theorem clock_half_coe (f : Hilbert) : clock ε h hε hb hh (1/2) f =ᵐ[volume]
    fun x => tilt ε h x.1*f x := by
  filter_upwards [clock_coe ε h hε hb hh (1/2) f] with x hx
  rw [hx,tilt]
  congr 2
  push_cast
  ring

theorem clock_one_coe (f : Hilbert) : clock ε h hε hb hh 1 f =ᵐ[volume]
    fun x => (tilt ε h x.1)^2*f x := by
  filter_upwards [clock_coe ε h hε hb hh 1 f] with x hx
  rw [hx,tilt,← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem assemble_coe (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : Hilbert) (v : Fields)
    (hv : ∀ m j, v m j =ᵐ[volume] fun x : Configuration => (m x.2:ℂ)^(j.val+1)*f x) :
    assemble ε h hε hb hh l i v =ᵐ[volume] fun x => (polynomial ε h l x)^(i.val+1)*f x := by
  fin_cases i
  · change clock ε h hε hb hh 0 (v (constantField l) 0)+
      clock ε h hε hb hh (1/2) (v (scaleField l) 0) =ᵐ[volume] _
    filter_upwards [Lp.coeFn_add (clock ε h hε hb hh 0 (v (constantField l) 0))
        (clock ε h hε hb hh (1/2) (v (scaleField l) 0)),
      clock_zero_coe ε h hε hb hh (v (constantField l) 0),
      clock_half_coe ε h hε hb hh (v (scaleField l) 0),hv (constantField l) 0,hv (scaleField l) 0]
      with x ha h0 h1 hc hs
    simp only [Pi.add_apply] at ha
    rw [ha,h0,h1,hc,hs]
    simp only [polynomial,Fin.val_zero,zero_add,pow_one]
    ring
  · let u := v (constantField l) 1
    let w := v (scaleField l) 1
    let m := v (constantField l+scaleField l) 1-u-w
    change clock ε h hε hb hh 0 u+clock ε h hε hb hh (1/2) m+
      clock ε h hε hb hh 1 w =ᵐ[volume] _
    filter_upwards [Lp.coeFn_add (clock ε h hε hb hh 0 u+clock ε h hε hb hh (1/2) m)
        (clock ε h hε hb hh 1 w),
      Lp.coeFn_add (clock ε h hε hb hh 0 u) (clock ε h hε hb hh (1/2) m),
      clock_zero_coe ε h hε hb hh u,clock_half_coe ε h hε hb hh m,clock_one_coe ε h hε hb hh w,
      Lp.coeFn_sub (v (constantField l+scaleField l) 1-u) w,
      Lp.coeFn_sub (v (constantField l+scaleField l) 1) u,
      hv (constantField l+scaleField l) 1,hv (constantField l) 1,hv (scaleField l) 1]
      with x ha hb' h0 h1 h2 hm hn hc hu hw
    change m x = _ at hm
    change u x = _ at hu
    change w x = _ at hw
    simp only [Pi.add_apply] at ha hb'
    simp only [Pi.sub_apply] at hm hn
    rw [ha,hb',h0,h1,h2,hm,hn,hc,hu,hw]
    simp only [polynomial,Fin.val_one,ContinuousLinearMap.add_apply,Complex.ofReal_add]
    norm_num only
    ring

variable (a : ℝ) (ha : 0 < a)
local notation "S" => coherentSpan ε a h hε ha hh

theorem initial_coe (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : S) :
    initialInput ε a h hε ha hh hb l i f =ᵐ[volume]
      fun x => (polynomial ε h l x)^(i.val+1)*(input ε a h hε ha hh hb 0 f) x := by
  rw [initialInput_assembly]
  exact assemble_coe ε h hε hb hh l i (input ε a h hε ha hh hb 0 f) _
    (fun m j => (fieldPower_graph m j _ _).mp
      (field_graph ε a h hε ha hh hb m j f ⟨0,by constructor <;> norm_num⟩))

omit hε hb hh a ha in
theorem pointField_polynomial (x : Configuration) :
    polynomial ε h pointField x = (x.2 4:ℂ)+(3*tilt ε h x.1-2)*((x.2 2:ℂ)+(x.2 3:ℂ)) := by
  simp only [polynomial,constantField,scaleField,ContinuousLinearMap.comp_apply,
    KFCausalMatterOrderedDomain.pointField_apply,
    KFCausalFieldPolynomialPackets.constantPart,KFCausalFieldPolynomialPackets.scalePart]
  norm_num
  push_cast
  ring

theorem pointField_initial_coe (i : Fin 2) (f : S) :
    initialInput ε a h hε ha hh hb pointField i f =ᵐ[volume] fun x =>
      ((x.2 4:ℂ)+(3*Complex.exp (-displacement ε h x.1/2)-2)*((x.2 2:ℂ)+(x.2 3:ℂ)))^(i.val+1)*
        (input ε a h hε ha hh hb 0 f) x := by
  simpa only [pointField_polynomial,tilt] using initial_coe ε h hε hb hh a ha pointField i f

#print axioms clock_coe
#print axioms clock_zero_coe
#print axioms clock_half_coe
#print axioms clock_one_coe
#print axioms assemble_coe
#print axioms initial_coe
#print axioms pointField_polynomial
#print axioms pointField_initial_coe
end
end UnifiedTheory.Audit.KFCausalTransportedInitialPolynomial
