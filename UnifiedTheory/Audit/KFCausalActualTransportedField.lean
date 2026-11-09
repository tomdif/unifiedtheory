/- Apply exact field transport to the actual inverse-clock coefficient
and Gaussian paths. Strong derivatives and both shear graphs are derived,
including the finite polynomial components of the original matter fields. -/
import UnifiedTheory.Audit.KFCausalFieldEigenpolynomials

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalActualTransportedField
noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockProfileCalculus
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition (Seed)
open UnifiedTheory.Audit.KFCausalEigenfieldShearGraphs (EigenWeight scalar)
open UnifiedTheory.Audit.KFCausalFieldShearPathGraphs (state firstState secondState)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator coefficientOperator_coe)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)

def profile : Profiles := BoundedContinuousFunction.mkOfBound
  ⟨coefficient ε h,(coefficient_smooth ε h hε hb).continuous⟩ (1/(2*ε)+1/(2*ε)) (fun s t => by
    calc
      dist (coefficient ε h s) (coefficient ε h t) ≤ ‖coefficient ε h s‖+‖coefficient ε h t‖ :=
        by simpa only [dist_eq_norm] using norm_sub_le (coefficient ε h s) (coefficient ε h t)
      _ ≤ 1/(2*ε)+1/(2*ε) := add_le_add (coefficient_bound ε h s hε hh hb) (coefficient_bound ε h t hε hh hb))

theorem profile_apply (s : ℝ) : profile ε h hε hb hh s = coefficient ε h s := rfl

theorem profile_operator : multiply (profile ε h hε hb hh) = coefficientOperator ε h hε hb hh := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (multiply_coe (profile ε h hε hb hh) f).trans (coefficientOperator_coe ε h hε hb hh f).symm

variable (s : Seed) (P : EigenWeight)
local notation "c" => profile ε h hε hb hh
local notation "C" => multiply c
local notation "U" => state ε h hε hb s P.toWeight
local notation "V" => firstState ε h hε hb s P.toWeight
local notation "K" => secondState ε h hε hb s P.toWeight

def input : ℝ → Hilbert := KFCausalTransportedShearCurve.input c (scalar P h) U
def output : ℝ → Hilbert := KFCausalTransportedShearCurve.output c (scalar P h) U V
def output2 : Interval → Hilbert := KFCausalTransportedShearCurve.output2 c (scalar P h) U V K

theorem base_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt U (C (V t)) t := by
  rw [profile_operator]
  exact KFCausalActualPolynomialShearCurve.input_strong_derivative P.toWeight
    ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b hh t ht

theorem first_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt V (C (K ⟨t,ht.1.le,ht.2.le⟩)) t := by
  rw [profile_operator]
  exact KFCausalActualPolynomialShearCurve.weightedFirst_strong_derivative P.toWeight
    ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b hh t ht

theorem input_continuous : Continuous (input ε h hε hb hh s P) :=
  KFCausalTransportedShearCurve.transported_continuous _ _
    (KFCausalActualPolynomialShearCurve.input_continuous P.toWeight ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b)

theorem output_continuous : Continuous (output ε h hε hb hh s P) :=
  KFCausalTransportedShearCurve.transported_continuous _ _
    ((KFCausalActualPolynomialShearCurve.weightedFirst_continuous P.toWeight ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b).add
      ((KFCausalActualPolynomialShearCurve.input_continuous P.toWeight ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b).const_smul _))

theorem input_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (input ε h hε hb hh s P) (C (output ε h hε hb hh s P t)) t :=
  KFCausalTransportedShearCurve.input_derivative c (scalar P h) U V (base_derivative ε h hε hb hh s P) t ht

theorem output_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (output ε h hε hb hh s P) (C (output2 ε h hε hb hh s P ⟨t,ht.1.le,ht.2.le⟩)) t :=
  KFCausalTransportedShearCurve.output_derivative c (scalar P h) U V K
    (base_derivative ε h hε hb hh s P) (first_derivative ε h hε hb hh s P) t ht

theorem input_graph (t : Interval) :
    (input ε h hε hb hh s P t,output ε h hε hb hh s P t) ∈ (shearMomentum h).graph :=
  KFCausalTransportedShearCurve.input_graph c (scalar P h) h hh U V
    (KFCausalEigenfieldShearGraphs.state_graph ε h hε hb s P hh) t

theorem output_graph (t : Interval) :
    (output ε h hε hb hh s P t,output2 ε h hε hb hh s P t) ∈ (shearMomentum h).graph :=
  KFCausalTransportedShearCurve.output_graph c (scalar P h) h hh U V K
    (KFCausalEigenfieldShearGraphs.state_graph ε h hε hb s P hh)
    (KFCausalEigenfieldShearGraphs.first_graph ε h hε hb s P hh) t

theorem input_one : input ε h hε hb hh s P 1 = U 1 := transport_one _ _

theorem transport_symbol (t r : ℝ) :
    ((t-1:ℝ):ℂ)*((scalar P h • c) r) =
      ((t-1:ℝ):ℂ)*(P.degree:ℂ)*displacement ε h r := by
  have he := coefficient_generator_identity ε h r hh
  simp only [BoundedContinuousFunction.smul_apply,smul_eq_mul,profile_apply,scalar]
  calc
    _ = ((t-1:ℝ):ℂ)*(P.degree:ℂ)*(coefficient ε h r*(-(h:ℂ)*Complex.I)) := by ring
    _ = _ := by rw [he]

theorem input_coe (t : Interval) : input ε h hε hb hh s P t =ᵐ[volume] fun x =>
    Complex.exp (((t:ℝ)-1:ℝ)*(P.degree:ℂ)*displacement ε h x.1)*P.value x*
      KFCausalImaginaryShearInterpolation.actualPath ε s.a s.α s.β s.p h s.b t x := by
  filter_upwards [transport_coe (scalar P h • c) t (U t),
    KFCausalActualPolynomialShearCurve.input_coe P.toWeight ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t]
      with x ht hu
  change input ε h hε hb hh s P t x = _ at ht
  change U t x = _ at hu
  rw [ht,hu,transport_symbol ε h hε hb hh P]
  ring

#print axioms profile_apply
#print axioms profile_operator
#print axioms base_derivative
#print axioms first_derivative
#print axioms input_continuous
#print axioms output_continuous
#print axioms input_derivative
#print axioms output_derivative
#print axioms input_graph
#print axioms output_graph
#print axioms input_one
#print axioms transport_symbol
#print axioms input_coe
end
end UnifiedTheory.Audit.KFCausalActualTransportedField
