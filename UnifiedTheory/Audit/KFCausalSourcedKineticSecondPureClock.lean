/- Sourced directional moments and the actual second transverse momentum
output have pure-clock graphs. The explicit graph outputs are continuous
along bounded source curves, permitting the later circle integral. -/
import UnifiedTheory.Audit.KFCausalWeightedShiftedPureClockGraphs
import UnifiedTheory.Audit.KFCausalSourcedSecondMomentum
import UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSourcedKineticSecondPureClock
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalDirectionalGaussianStates (linearForm)
open KFCausalGaussianSecondMomentum (direction)
open KFCausalClockFloorCoherentSources (linearSource)
open KFCausalRadialMultipliers
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalCanonicalClockDerivative (clockDerivative)
open KFCausalShiftedGaussianPureDifferential (realInverse)
open KFCausalClockFloorTrialClockEnergy (dampedClockFunction dampedClockFunction_memLp)
open KFCausalClockFloorCoherentBounds (sourceSize)

def multiplier (d : Transverse) (k : ℕ) (x : Configuration) : ℂ := (linearForm d x.2:ℂ)^k

theorem multiplier_controlled (d : Transverse) (k : ℕ) : Controlled (multiplier d k) := by
  have hl : Controlled (fun x : Configuration => (linearForm d x.2:ℂ)) := by
    simp only [linearForm,Complex.ofReal_sum,Complex.ofReal_mul]
    exact controlled_sum Finset.univ _ (fun i _ => controlled_mul _ _ (controlled_const (d i:ℂ))
      (controlled_coordinate i))
  exact controlled_pow _ hl k

theorem multiplier_differentiable (d : Transverse) (k : ℕ) : Differentiable ℝ (multiplier d k) := by
  have hl : Differentiable ℝ (fun x : Configuration => linearForm d x.2) := by
    unfold linearForm
    apply Differentiable.fun_sum
    intro i _
    fun_prop
  exact (Complex.ofRealCLM.differentiable.comp hl).pow k

theorem multiplier_rate (ε : ℝ) (d : Transverse) (k : ℕ) (x : Configuration) :
    realInverse ε x.1*clockDerivative (multiplier d k) x = 0 := by
  have hd := ((multiplier_differentiable d k) x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  change HasDerivAt (fun _ : ℝ => (linearForm d x.2:ℂ)^k) (clockDerivative (multiplier d k) x) x.1 at hd
  rw [hd.unique (hasDerivAt_const x.1 ((linearForm d x.2:ℂ)^k)),mul_zero]

private theorem zero_strip (ε : ℝ) (hε : 0 < ε) : |(0:ℝ)| ≤ Real.pi*ε/3 := by
  simp
  positivity

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (p : ℝ)
local notation "hy" => zero_strip ε hε
local notation "g" => dampedClockFunction ε a
local notation "hg" => dampedClockFunction_memLp ε a hε ha

def powerOutput (d : Transverse) (k : ℕ) (h : ℝ) (C : ℂ) (b : Fin 5 → ℂ) : Hilbert :=
  KFCausalWeightedShiftedPureClockGraphs.output ε a α β p 0 hε ha hα hβ hw hy
    (multiplier d k) (fun _ => 0) (multiplier_controlled d k) (controlled_const 0) h C b

theorem power_graph (d : Transverse) (k : ℕ) (h : ℝ) (hh : h ≠ 0) (C : ℂ) (b : Fin 5 → ℂ) :
    (KFCausalSourcedDirectionalMoments.state C p α β hα hβ hw b g hg d k,
      powerOutput ε a α β hε ha hα hβ hw p d k h C b) ∈ (pureMomentum ε hε h).graph := by
  have hd := KFCausalClockFloorSourcedClockMomentum.dampedState_coe ε a α β hε ha hα hβ hw C p b
  rw [KFCausalClockFloorSourcedSpectral.dampedState_gaussian ε a α β hε ha hα hβ hw C p b] at hd
  have hi : KFCausalWeightedShiftedPureClockGraphs.input ε a α β p 0 hε ha hα hβ hw hy
      (multiplier d k) (multiplier_controlled d k) C b =
      KFCausalSourcedDirectionalMoments.state C p α β hα hβ hw b g hg d k := by
    apply Lp.ext
    filter_upwards [KFCausalWeightedShiftedPureClockGraphs.input_coe ε a α β p 0 hε ha hα hβ hw hy
      (multiplier d k) (multiplier_controlled d k) C b,
      KFCausalSourcedDirectionalMoments.state_coe C p α β hα hβ hw b g hg d k,hd,
      Lp.coeFn_smul C (KFCausalClockFloorCoherentSpectral.gaussianState ε a α β p b 0 hε ha hα hβ hw hy),
      KFCausalShiftedGaussianPhysicalProfile.gaussianState_profile ε a α β p 0 b hε ha hα hβ hw hy]
      with x hin hstate hd hc hs
    simp only [Pi.smul_apply,smul_eq_mul] at hc
    rw [hc,hs] at hd
    rw [hin,hstate]
    unfold KFCausalSourcedDirectionalMoments.profile multiplier
    rw [← hd]
    ring
  rw [← hi]
  exact KFCausalWeightedShiftedPureClockGraphs.graph ε a α β p 0 hε ha hα hβ hw hy
    (multiplier d k) (fun _ => 0) (multiplier_controlled d k) (controlled_const 0)
    (multiplier_differentiable d k) (multiplier_rate ε d k) h hh C b

theorem powerOutput_continuous (B : ℝ) (C : ℝ → ℂ) (b : ℝ → Fin 5 → ℂ)
    (hCc : Continuous C) (hbc : Continuous b) (hbB : ∀ θ, sourceSize (b θ) ≤ B)
    (d : Transverse) (k : ℕ) (h : ℝ) :
    Continuous (fun θ => powerOutput ε a α β hε ha hα hβ hw p d k h (C θ) (b θ)) :=
  KFCausalWeightedShiftedPureClockGraphs.output_continuous ε a α β p 0 hε ha hα hβ hw hy
    (multiplier d k) (fun _ => 0) (multiplier_controlled d k) (controlled_const 0) B C b hCc hbc hbB h

def output (h : ℝ) (v : Transverse) (C : ℂ) (b : Fin 5 → ℂ) : Hilbert :=
  (-Complex.I*(h:ℂ))^2 •
    (powerOutput ε a α β hε ha hα hβ hw p (direction α β v) 2 h C b+
      (2*linearSource b v) • powerOutput ε a α β hε ha hα hβ hw p (direction α β v) 1 h C b+
      (linearSource b v^2+(linearForm (direction α β v) v:ℂ)) •
        powerOutput ε a α β hε ha hα hβ hw p (direction α β v) 0 h C b)

theorem graph (h : ℝ) (hh : h ≠ 0) (v : Transverse) (C : ℂ) (b : Fin 5 → ℂ) :
    (KFCausalSourcedSecondMomentum.secondOutput α β hα hβ hw C p b g hg h v,
      output ε a α β hε ha hα hβ hw p h v C b) ∈ (pureMomentum ε hε h).graph := by
  have hp (k : ℕ) := power_graph ε a α β hε ha hα hβ hw p (direction α β v) k h hh C b
  have hs := (pureMomentum ε hε h).graph.smul_mem ((-Complex.I*(h:ℂ))^2)
    ((pureMomentum ε hε h).graph.add_mem
      ((pureMomentum ε hε h).graph.add_mem (hp 2)
        ((pureMomentum ε hε h).graph.smul_mem (2*linearSource b v) (hp 1)))
      ((pureMomentum ε hε h).graph.smul_mem (linearSource b v^2+(linearForm (direction α β v) v:ℂ)) (hp 0)))
  simpa only [KFCausalSourcedSecondMomentum.secondOutput,KFCausalSourcedSecondMomentum.secondState,
    output,Prod.smul_mk] using hs

theorem output_continuous (B : ℝ) (C : ℝ → ℂ) (b : ℝ → Fin 5 → ℂ)
    (hCc : Continuous C) (hbc : Continuous b) (hbB : ∀ θ, sourceSize (b θ) ≤ B) (h : ℝ) (v : Transverse) :
    Continuous (fun θ => output ε a α β hε ha hα hβ hw p h v (C θ) (b θ)) := by
  have hc : Continuous (fun θ => linearSource (b θ) v) := by unfold linearSource; fun_prop
  have hp (k : ℕ) := powerOutput_continuous ε a α β hε ha hα hβ hw p B C b hCc hbc hbB (direction α β v) k h
  exact continuous_const.smul (((hp 2).add ((continuous_const.mul hc).smul (hp 1))).add
    (((hc.pow 2).add continuous_const).smul (hp 0)))

#print axioms multiplier_controlled
#print axioms multiplier_differentiable
#print axioms multiplier_rate
#print axioms power_graph
#print axioms powerOutput_continuous
#print axioms graph
#print axioms output_continuous
end
end UnifiedTheory.Audit.KFCausalSourcedKineticSecondPureClock
