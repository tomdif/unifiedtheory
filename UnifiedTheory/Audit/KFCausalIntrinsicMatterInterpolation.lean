/- State-defined charge interpolation and its quadratic cost on the
coherent span. Finite representations evaluate these functions but do
not define different paths. Continuity here is in the path parameters,
not continuity of the algebraic operators in the Hilbert norm. -/
import UnifiedTheory.Audit.KFCausalCoherentMatterPathOperator
import UnifiedTheory.Audit.KFCausalAveragedMatterInterpolation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalIntrinsicMatterInterpolation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (state)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalCoherentSpanVacuumSign (finite_representation)
open UnifiedTheory.Audit.KFCausalCoherentMatterPathOperator
  (rotate rotate_representation field_of_representation shear_of_representation derivativeField_of_representation)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2)
local notation "S" => coherentSpan ε a h hε ha hh

def field (f : S) (θ t : ℝ) : Hilbert :=
  KFCausalCoherentMatterPathOperator.field ε a h hε ha hh hb l i t (rotate ε a h hε ha hh (2*Real.pi*θ) f)
def shear (f : S) (θ t : ℝ) : Hilbert :=
  KFCausalCoherentMatterPathOperator.shear ε a h hε ha hh hb l i t (rotate ε a h hε ha hh (2*Real.pi*θ) f)
def derivativeField (f : S) (θ t : ℝ) : Hilbert :=
  KFCausalCoherentMatterPathOperator.derivativeField ε a h hε ha hh hb l i t (rotate ε a h hε ha hh (2*Real.pi*θ) f)

theorem curves_of_representation (f : S) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
    (hf : (f:Hilbert) = ∑ r, z r • state ε a h hε ha hh (k r)) (θ t : ℝ) :
    field ε a h hε ha hh hb l i f θ t = KFCausalCoherentMatterInterpolationOrbit.field ε a h hε ha hh hb l i k z θ t ∧
    shear ε a h hε ha hh hb l i f θ t = KFCausalCoherentMatterInterpolationOrbit.shear ε a h hε ha hh hb l i k z θ t ∧
    derivativeField ε a h hε ha hh hb l i f θ t =
      KFCausalCoherentMatterInterpolationOrbit.derivativeField ε a h hε ha hh hb l i k z θ t := by
  have hr := rotate_representation ε a h hε ha hh f k z hf (2*Real.pi*θ)
  exact ⟨field_of_representation ε a h hε ha hh hb l i _ _ z hr t,
    shear_of_representation ε a h hε ha hh hb l i _ _ z hr t,
    derivativeField_of_representation ε a h hε ha hh hb l i _ _ z hr t⟩

theorem curves_joint_continuous (f : S) :
    Continuous (fun p : ℝ × ℝ => field ε a h hε ha hh hb l i f p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => shear ε a h hε ha hh hb l i f p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => derivativeField ε a h hε ha hh hb l i f p.1 p.2) := by
  obtain ⟨n,k,z,hf⟩ := finite_representation ε a h hε ha hh f f.property
  have he := curves_of_representation ε a h hε ha hh hb l i f k z hf
  have hc := KFCausalCoherentMatterInterpolationOrbit.curves_joint_continuous ε a h hε ha hh hb l i k z
  exact ⟨hc.1.congr (fun p => (he p.1 p.2).1.symm),
    hc.2.1.congr (fun p => (he p.1 p.2).2.1.symm),
    hc.2.2.congr (fun p => (he p.1 p.2).2.2.symm)⟩

variable (W : Hilbert →L[ℂ] Hilbert)

def expectation (f : S) (θ t : ℝ) : ℝ :=
  (inner ℂ (W (field ε a h hε ha hh hb l i f θ t)) (W (shear ε a h hε ha hh hb l i f θ t))).re
def pathCost (f : S) (θ : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, ‖W (derivativeField ε a h hε ha hh hb l i f θ t)‖^2

theorem expectation_of_representation (f : S) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
    (hf : (f:Hilbert) = ∑ r, z r • state ε a h hε ha hh (k r)) (θ t : ℝ) :
    expectation ε a h hε ha hh hb l i W f θ t =
      KFCausalCoherentMatterInterpolationOrbit.expectation ε a h hε ha hh hb l i k z W θ t := by
  have he := curves_of_representation ε a h hε ha hh hb l i f k z hf θ t
  unfold expectation KFCausalCoherentMatterInterpolationOrbit.expectation
  rw [he.1,he.2.1]

theorem pathCost_of_representation (f : S) {n : ℕ} (k : Fin n → Joint 2 4) (z : Fin n → ℂ)
    (hf : (f:Hilbert) = ∑ r, z r • state ε a h hε ha hh (k r)) (θ : ℝ) :
    pathCost ε a h hε ha hh hb l i W f θ =
      KFCausalCoherentMatterInterpolationOrbit.pathCost ε a h hε ha hh hb l i k z W θ := by
  unfold pathCost KFCausalCoherentMatterInterpolationOrbit.pathCost
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [(curves_of_representation ε a h hε ha hh hb l i f k z hf θ t).2.2]

theorem expectation_joint_continuous (f : S) :
    Continuous (fun p : ℝ × ℝ => expectation ε a h hε ha hh hb l i W f p.1 p.2) :=
  Complex.continuous_re.comp
    ((W.continuous.comp (curves_joint_continuous ε a h hε ha hh hb l i f).1).inner
      (W.continuous.comp (curves_joint_continuous ε a h hε ha hh hb l i f).2.1))

theorem pathCost_continuous (f : S) : Continuous (pathCost ε a h hε ha hh hb l i W f) := by
  obtain ⟨n,k,z,hf⟩ := finite_representation ε a h hε ha hh f f.property
  exact (KFCausalCoherentMatterInterpolationOrbit.pathCost_continuous ε a h hε ha hh hb l i k z W).congr
    (fun θ => (pathCost_of_representation ε a h hε ha hh hb l i W f k z hf θ).symm)

theorem expectation_angle_integrable (f : S) (t : ℝ) :
    Integrable (fun θ => expectation ε a h hε ha hh hb l i W f θ t) angleMeasure :=
  (continuous_angle_memLp _ ((expectation_joint_continuous ε a h hε ha hh hb l i W f).comp
    (continuous_id.prodMk continuous_const))).integrable (by norm_num)

theorem pathCost_angle_integrable (f : S) :
    Integrable (pathCost ε a h hε ha hh hb l i W f) angleMeasure :=
  (continuous_angle_memLp _ (pathCost_continuous ε a h hε ha hh hb l i W f)).integrable (by norm_num)

theorem pathCost_nonnegative (f : S) (θ : ℝ) : 0 ≤ pathCost ε a h hε ha hh hb l i W f θ :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)

theorem pathCost_smul (c : ℂ) (f : S) (θ : ℝ) :
    pathCost ε a h hε ha hh hb l i W (c • f) θ = ‖c‖^2*pathCost ε a h hε ha hh hb l i W f θ := by
  simp only [pathCost,derivativeField,map_smul,norm_smul,mul_pow,intervalIntegral.integral_const_mul]

theorem pathCost_parallelogram (f g : S) (θ : ℝ) :
    pathCost ε a h hε ha hh hb l i W (f+g) θ + pathCost ε a h hε ha hh hb l i W (f-g) θ =
      2*(pathCost ε a h hε ha hh hb l i W f θ + pathCost ε a h hε ha hh hb l i W g θ) := by
  let v : S → ℝ → Hilbert := fun u t => W (derivativeField ε a h hε ha hh hb l i u θ t)
  have hI (u : S) : IntervalIntegrable (fun t => ‖v u t‖^2) volume 0 1 :=
    ((W.continuous.comp ((curves_joint_continuous ε a h hε ha hh hb l i u).2.2.comp
      (continuous_const.prodMk continuous_id))).norm.pow 2).intervalIntegrable 0 1
  change (∫ t in (0:ℝ)..1, ‖v (f+g) t‖^2)+(∫ t in (0:ℝ)..1, ‖v (f-g) t‖^2) =
    2*((∫ t in (0:ℝ)..1, ‖v f t‖^2)+(∫ t in (0:ℝ)..1, ‖v g t‖^2))
  rw [← intervalIntegral.integral_add (hI (f+g)) (hI (f-g))]
  calc
    _ = ∫ t in (0:ℝ)..1, 2*(‖v f t‖^2+‖v g t‖^2) := by
      apply intervalIntegral.integral_congr
      intro t _
      simpa only [v,derivativeField,map_add,map_sub,pow_two] using
        parallelogram_law_with_norm ℂ (v f t) (v g t)
    _ = _ := by rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add (hI f) (hI g)]

theorem actual_average_lower (w : ℝ → ℂ)
    (hW : ∀ v : Hilbert, W v =ᵐ[volume] fun x => w x.1*v x) (f : S) (g u j : ℝ → Hilbert)
    (hg : ∀ θ, (action h hh (2*Real.pi*θ) (f:Hilbert),g θ) ∈ (orderedExponential ε hε h).graph)
    (hu : ∀ θ, (g θ,u θ) ∈ (fieldPower l i).graph)
    (hj : ∀ θ, (u θ,j θ) ∈ (shearMomentum h).graph) :
    (∫ θ, expectation ε a h hε ha hh hb l i W f θ 0 ∂angleMeasure)-
      (h^2/(4*ε))*(∫ θ, pathCost ε a h hε ha hh hb l i W f θ ∂angleMeasure) ≤
      ∫ θ, (inner ℂ (W (u θ)) (W (j θ))).re ∂angleMeasure := by
  obtain ⟨n,k,z,hf⟩ := finite_representation ε a h hε ha hh f f.property
  have hg' : ∀ θ, (action h hh (2*Real.pi*θ) (∑ r, z r • state ε a h hε ha hh (k r)),g θ) ∈
      (orderedExponential ε hε h).graph := by rw [← hf]; exact hg
  have he := (KFCausalAveragedMatterInterpolation.actual_average_lower ε a h hε ha hh hb l i k z
    W w hW g u j hg' hu hj).2.2.2
  simp_rw [expectation_of_representation ε a h hε ha hh hb l i W f k z hf,
    pathCost_of_representation ε a h hε ha hh hb l i W f k z hf]
  exact he

#print axioms curves_of_representation
#print axioms curves_joint_continuous
#print axioms expectation_of_representation
#print axioms pathCost_of_representation
#print axioms expectation_joint_continuous
#print axioms pathCost_continuous
#print axioms expectation_angle_integrable
#print axioms pathCost_angle_integrable
#print axioms pathCost_nonnegative
#print axioms pathCost_smul
#print axioms pathCost_parallelogram
#print axioms actual_average_lower
end
end UnifiedTheory.Audit.KFCausalIntrinsicMatterInterpolation
