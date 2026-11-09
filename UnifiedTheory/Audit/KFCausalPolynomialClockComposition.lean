/- The clock-half output of every polynomial Gaussian has an actual
pure-clock momentum. The composition is constructed from Gaussian
representatives, closed-graph circle integration and finite sums. -/
import UnifiedTheory.Audit.KFCausalPolynomialMomentumReduction
import UnifiedTheory.Audit.KFCausalClockHalfMomentumDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalPolynomialClockComposition
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockKinetic (correction)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalProjectedKineticResponse (integral_closed_graph)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (clockFunction neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalPolynomialGaussianStates
  (circleSource sourceBound circleSource_continuous circleSource_bound)
open UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
open UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain (powerOutput output)
open UnifiedTheory.Audit.KFCausalPolynomialMomentumDomain
  (factorCurve factorCurve_continuous powerMomentumFactor momentumFactor)

theorem sourced_composition_graph (ε a α β h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) :
    (KFCausalClockFloorSourcedClockMomentum.clockOutput ε a α β hε ha hα hβ hw C p b,
      KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw C p b h hb modelDirections pointField 0-
        correction ε hε h (KFCausalClockFloorSourcedClockMomentum.clockOutput ε a α β hε ha hα hβ hw C p b)) ∈
      (pureMomentum ε hε h).graph := by
  let u := KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw C p b
  let v := KFCausalSourcedMomentumFactors.pureOutput ε a α β hε ha hα hβ hw C p b h
  let g := KFCausalClockFloorSourcedClockMomentum.clockOutput ε a α β hε ha hα hβ hw C p b
  let k := KFCausalSourcedMomentumFactors.factorOutput ε a α β hε ha hα hβ hw C p b h hb modelDirections pointField 0
  have hv : v =ᵐ[volume] fun x : Configuration => (-Complex.I*(h:ℂ))*
      KFCausalClockFloorPureClockDerivative.differential ε
        (KFCausalClockFloorCoherentDerivative.physicalProfile C p α β b (clockFunction ε a)) x := by
    filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
      (KFCausalOriginalPureClockOutput.preOutput ε a hε ha C p α β hα hβ hw b),
      KFCausalOriginalPureClockOutput.preOutput_coe ε a hε ha C p α β hα hβ hw b] with x hs hd
    change ((-Complex.I*(h:ℂ)) • KFCausalOriginalPureClockOutput.preOutput ε a hε ha C p α β hα hβ hw b) x = _
    rw [hs]
    simp only [Pi.smul_apply,hd,smul_eq_mul]
  have hg : (u,g) ∈ (clockHalf ε).graph :=
    KFCausalClockFloorSourcedClockMomentum.clockOutput_graph ε a α β hε ha hα hβ hw C p b
  have hk : (v,k) ∈ (clockHalf ε).graph :=
    KFCausalSourcedMomentumFactors.factorOutput_graph ε a α β hε ha hα hβ hw C p b h hh hb modelDirections pointField 0
  have hu := KFCausalSourcedMomentumFactors.pureOutput_graph ε a α β hε ha hα hβ hw C p b h hh
  have hd := KFCausalClockHalfMomentumDifferential.half_momentum_domain ε hε h hh
    (KFCausalClockFloorCoherentDerivative.physicalProfile C p α β b (clockFunction ε a))
    ((KFCausalCoherentLongitudinalDomain.profile_smooth ε a C p α β b).differentiable (by norm_num))
    u v g k (KFCausalClockFloorSourcedClockMomentum.state_coe ε a α β hε ha hα hβ hw C p b) hv hg hk
  let bg := (pureMomentum ε hε h) ⟨g,hd⟩
  have hbg : (g,bg) ∈ (pureMomentum ε hε h).graph := (pureMomentum ε hε h).mem_graph ⟨g,hd⟩
  have he : bg = k-correction ε hε h g := by
    have hc := KFCausalClockFloorPureClockClockResponse.commutator ε hε h hh u g v k bg hg hu hk hbg
    simpa only [sub_eq_add_neg,add_comm] using sub_eq_iff_eq_add.mp hc
  exact (congrArg (fun z : Hilbert => (g,z) ∈ (pureMomentum ε hε h).graph) he).mp hbg

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h

theorem power_composition_graph (n : ℕ) :
    (powerOutput ε a h hε ha hh C p b i hb n modelDirections pointField 0,
      powerMomentumFactor ε a h hε ha hh p b i C hb n modelDirections pointField 0-
        correction ε hε h (powerOutput ε a h hε ha hh C p b i hb n modelDirections pointField 0)) ∈
      (pureMomentum ε hε h).graph := by
  let G : ℝ → Hilbert := fun θ => KFCausalClockFloorSourcedCommonDomain.factorOutput
    ε a α β hε ha hα hβ hw (weight n θ) p (circleSource b i θ) h hb modelDirections pointField 0
  let K := factorCurve ε a h hε ha hh p b i hb n modelDirections pointField 0
  have hG : Continuous G := KFCausalSourcedCurveDomain.factor_continuous ε a h hε ha hh hb
    |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
    (weight_continuous n) continuous_const (circleSource_continuous b i)
    (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i)
    modelDirections pointField 0
  have hK : Continuous K := factorCurve_continuous ε a h hε ha hh p b i hb n modelDirections pointField 0
  have hg (θ : ℝ) : (G θ,K θ-correction ε hε h (G θ)) ∈ (pureMomentum ε hε h).graph :=
    sourced_composition_graph ε a α β h hε ha hα hβ hw hh hb (weight n θ) p (circleSource b i θ)
  have hi := (continuous_angle_memLp _ hG).integrable (by norm_num)
  have hj := (continuous_angle_memLp _ hK).integrable (by norm_num)
  have he := integral_closed_graph _ (pure_closed ε hε h hh) G
    (fun θ => K θ-correction ε hε h (G θ)) hG
    (hK.sub ((correction ε hε h).continuous.comp hG)) hg
  rw [integral_sub hj ((correction ε hε h).integrable_comp hi),
    (correction ε hε h).integral_comp_comm hi] at he
  have hs := (pureMomentum ε hε h).graph.smul_mem (C*normalization n) he
  simpa only [powerOutput,powerMomentumFactor,KFCausalSourcedCurveDomain.meanFactor,
    Prod.smul_mk,smul_sub,map_smul,G,K] using hs

theorem polynomial_composition_graph (P : Polynomial ℂ) :
    (output ε a h hε ha hh C p b i hb P modelDirections pointField 0,
      momentumFactor ε a h hε ha hh p b i C hb P modelDirections pointField 0-
        correction ε hε h (output ε a h hε ha hh C p b i hb P modelDirections pointField 0)) ∈
      (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem
    (fun n (_ : n ∈ P.support) => (pureMomentum ε hε h).graph.smul_mem (P.coeff n)
      (power_composition_graph ε a h hε ha hh hb C p b i n))
  simpa only [output,momentumFactor,Prod.smul_mk,← prod_mk_sum,smul_sub,
    Finset.sum_sub_distrib,map_sum,map_smul] using hs

#print axioms sourced_composition_graph
#print axioms power_composition_graph
#print axioms polynomial_composition_graph
end
end UnifiedTheory.Audit.KFCausalPolynomialClockComposition
