/- Finite complex superpositions retain the derived strong imaginary-shear
equations, actual second-shear domains and monotonicity. Their clock
frequencies and Gaussian widths may differ. Cross terms are retained. -/
import UnifiedTheory.Audit.KFCausalImaginaryShearMonotonicity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient (coefficient coefficient_re_positive)
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (expectation)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

structure Seed where
  a : ℝ
  p : ℝ
  α : ℝ
  β : ℝ
  b : Fin 5 → ℂ
  ha : 0 < a
  hα : 0 < α
  hβ : 0 < β
  hw : 32*β ≤ α

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3)
variable {n : ℕ} (seed : Fin n → Seed) (z : Fin n → ℂ)

def sumInput (t : ℝ) : Hilbert := ∑ i, z i •
  input ε (seed i).a (seed i).p h (seed i).α (seed i).β hε (seed i).ha
    (seed i).hα (seed i).hβ (seed i).hw hb (seed i).b t
def sumShear (t : ℝ) : Hilbert := ∑ i, z i •
  shear ε (seed i).a (seed i).p h (seed i).α (seed i).β hε (seed i).ha
    (seed i).hα (seed i).hβ (seed i).hw hb (seed i).b t
def sumSecond (t : Interval) : Hilbert := ∑ i, z i •
  secondShear ε (seed i).a (seed i).p h (seed i).α (seed i).β hε (seed i).ha
    (seed i).hα (seed i).hβ (seed i).hw hb (seed i).b t

local notation "F" => sumInput ε h hε hb seed z
local notation "J" => sumShear ε h hε hb seed z
local notation "K" => sumSecond ε h hε hb seed z

theorem input_continuous : Continuous F :=
  continuous_finset_sum _ (fun i _ =>
    (KFCausalActualImaginaryShearCurve.input_continuous ε (seed i).a (seed i).p h
      (seed i).α (seed i).β hε (seed i).ha (seed i).hα (seed i).hβ (seed i).hw hb (seed i).b).const_smul (z i))

theorem shear_continuous : Continuous J :=
  continuous_finset_sum _ (fun i _ =>
    (KFCausalActualImaginaryShearCurve.shear_continuous ε (seed i).a (seed i).p h
      (seed i).α (seed i).β hε (seed i).ha (seed i).hα (seed i).hβ (seed i).hw hb (seed i).b).const_smul (z i))

variable (hh : h ≠ 0)
local notation "C" => coefficientOperator ε h hε hb hh

theorem input_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt F (C (J t)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun (i : Fin n) _ =>
    (input_strong_derivative ε (seed i).a (seed i).p h (seed i).α (seed i).β hε
      (seed i).ha (seed i).hα (seed i).hβ (seed i).hw hb (seed i).b hh t ht).const_smul (z i))
  simpa only [sumInput,sumShear,map_sum,map_smul] using hd

theorem shear_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt J (C (K ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun (i : Fin n) _ =>
    (shear_strong_derivative ε (seed i).a (seed i).p h (seed i).α (seed i).β hε
      (seed i).ha (seed i).hα (seed i).hβ (seed i).hw hb (seed i).b hh t ht).const_smul (z i))
  simpa only [sumShear,sumSecond,map_sum,map_smul] using hd

theorem graph_sum (f j : Fin n → Hilbert)
    (hf : ∀ i, (f i,j i) ∈ (shearMomentum h).graph) :
    (∑ i, z i • f i,∑ i, z i • j i) ∈ (shearMomentum h).graph := by
  have hs := (shearMomentum h).graph.sum_mem (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    (shearMomentum h).graph.smul_mem (z i) (hf i))
  simpa only [Prod.smul_mk,← prod_mk_sum] using hs

include hh in
theorem input_graph (t : Interval) : (F t,J t) ∈ (shearMomentum h).graph :=
  graph_sum h z _ _ (fun i => input_shear_graph ε (seed i).a (seed i).p h (seed i).α
    (seed i).β hε (seed i).ha (seed i).hα (seed i).hβ (seed i).hw hb (seed i).b hh t)

include hh in
theorem shear_graph (t : Interval) : (J t,K t) ∈ (shearMomentum h).graph :=
  graph_sum h z _ _ (fun i => shear_second_graph ε (seed i).a (seed i).p h (seed i).α
    (seed i).β hε (seed i).ha (seed i).hα (seed i).hβ (seed i).hw hb (seed i).b hh t)

omit hh in
theorem input_one : F 1 = ∑ i, z i •
    KFCausalClockFloorCoherentSpectral.gaussianState ε (seed i).a (seed i).α (seed i).β
      (seed i).p (seed i).b (-h/2) hε (seed i).ha (seed i).hα (seed i).hβ (seed i).hw
      (KFCausalImaginaryShearCoefficient.half_shift_bound ε h hb) := by
  unfold sumInput
  apply Finset.sum_congr rfl
  intro i _
  rw [KFCausalActualImaginaryShearCurve.input_one]

variable (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
variable (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)

include hW hh in
theorem expectation_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (expectation W F J) (2*∫ x, (coefficient ε h x.1).re*‖W (J t) x‖^2) t := by
  rw [← KFCausalClockShearPositiveVariation.pairing_integral C (coefficient ε h)
    (coefficientOperator_coe ε h hε hb hh)]
  exact KFCausalClockShearPositiveVariation.expectation_derivative C W (coefficient ε h) w
    (coefficientOperator_coe ε h hε hb hh) hW h hh F J (K ⟨t,ht.1.le,ht.2.le⟩) t
    (input_derivative ε h hε hb seed z hh t ht) (shear_derivative ε h hε hb seed z hh t ht)
    (input_graph ε h hε hb seed z hh ⟨t,ht.1.le,ht.2.le⟩)
    (shear_graph ε h hε hb seed z hh ⟨t,ht.1.le,ht.2.le⟩)

include hW hh in
theorem expectation_monotone : MonotoneOn (expectation W F J) (Icc (0:ℝ) 1) :=
  KFCausalClockShearPositiveVariation.expectation_monotone C W (coefficient ε h) w
    (coefficientOperator_coe ε h hε hb hh) hW
    (fun s => (coefficient_re_positive ε h s hε hh hb).le) h hh F J K
    (input_continuous ε h hε hb seed z) (shear_continuous ε h hε hb seed z)
    (input_derivative ε h hε hb seed z hh) (shear_derivative ε h hε hb seed z hh)
    (input_graph ε h hε hb seed z hh) (shear_graph ε h hε hb seed z hh)

include hW hh in
theorem expectation_endpoints : expectation W F J 0 ≤ expectation W F J 1 :=
  expectation_monotone ε h hε hb seed z hh W w hW
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)

local notation "R" => KFCausalClockFloorShearWeight.root ε hε h hb hh

theorem physical_weight_monotone : MonotoneOn (expectation R F J) (Icc (0:ℝ) 1) :=
  expectation_monotone ε h hε hb seed z hh R
    (fun s => (KFCausalClockFloorShearWeight.rootValue ε h s:ℂ))
    (KFCausalClockFloorShearWeight.root_coe ε hε h hb hh)

theorem physical_weight_endpoints : expectation R F J 0 ≤ expectation R F J 1 :=
  expectation_endpoints ε h hε hb seed z hh R
    (fun s => (KFCausalClockFloorShearWeight.rootValue ε h s:ℂ))
    (KFCausalClockFloorShearWeight.root_coe ε hε h hb hh)

#print axioms input_continuous
#print axioms shear_continuous
#print axioms input_derivative
#print axioms shear_derivative
#print axioms graph_sum
#print axioms input_graph
#print axioms shear_graph
#print axioms input_one
#print axioms expectation_derivative
#print axioms expectation_monotone
#print axioms expectation_endpoints
#print axioms physical_weight_monotone
#print axioms physical_weight_endpoints
end
end UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition
