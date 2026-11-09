/- The actual normalized zero-charge packets have exactly linear
pure-clock-momentum expectation. Along negative frequencies this
expectation is unbounded in magnitude while full projected energy stays
bounded. No time evolution or dynamical response sign is inferred. -/
import UnifiedTheory.Audit.KFCausalNegativeFrequencyExpectation
import UnifiedTheory.Audit.KFCausalNegativeFrequencyProjected

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedMomentumExpectation
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockCommonDomain (clockInverse)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (trialState neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalNegativeFrequencyProjected
  (structured input_norm input_fixed input_sourced momentum_sourced energy_le)
open UnifiedTheory.Audit.KFCausalNegativeFrequencyExpectation
  (pureOutput_expectation inverse_pairing_positive)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (input momentumOutput momentum_graph)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (projectedEnergy)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (action)

theorem real_smul_pairing (r : ℝ) (f g : Hilbert) :
    (inner ℂ (r • f) (r • g)).re = r^2*(inner ℂ f g).re := by
  have he : inner ℂ (r • f) (r • g) = (r:ℂ)^2*inner ℂ f g := by
    rw [inner_smul_left_eq_smul,inner_smul_right_eq_smul]
    simp only [Complex.real_smul]
    ring
  rw [he,← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "S" p:arg => structured a h p ha
local notation "f" p:arg => input ε h hε hh (S p)
local notation "Bf" p:arg => momentumOutput ε h hε hh (S p)
local notation "N" => (‖trialState ε a h hε ha hh‖⁻¹:ℝ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "raw" p:arg => KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw 1 p 0

def drift : ℝ := h*(inner ℂ (f 0) (clockInverse ε hε (f 0))).re

theorem drift_positive (hp : 0 < h) : 0 < drift ε a h hε ha hh := by
  apply mul_pos hp
  apply inverse_pairing_positive ε hε
  exact norm_ne_zero_iff.mp (by rw [input_norm]; norm_num)

theorem expectation_exact (p : ℝ) : (inner ℂ (f p) (Bf p)).re = p*drift ε a h hε ha hh := by
  have hi : (inner ℂ (f 0) (clockInverse ε hε (f 0))).re =
      N^2*(inner ℂ (raw 0) (clockInverse ε hε (raw 0))).re := by
    rw [input_sourced,(clockInverse ε hε).map_smul_of_tower,real_smul_pairing]
  rw [input_sourced,momentum_sourced,real_smul_pairing,pureOutput_expectation]
  unfold drift
  rw [hi]
  ring

theorem negative_expectation_unbounded (hp : 0 < h) (M : ℝ) :
    ∃ n : ℕ, (inner ℂ (f (-(n:ℝ))) (Bf (-(n:ℝ)))).re < -M := by
  have hd := drift_positive ε a h hε ha hh hp
  obtain ⟨n,hn⟩ := exists_nat_gt (M/drift ε a h hε ha hh)
  refine ⟨n,?_⟩
  rw [expectation_exact]
  have hb := (div_lt_iff₀ hd).mp hn
  nlinarith only [hb]

variable (hb : |h| ≤ 2*Real.pi*ε/3)

theorem bounded_energy_unbounded_expectation (hp : 0 < h) (mass2 quartic vacuum t M : ℝ) :
    ∃ n : ℕ,
      ‖f (-(n:ℝ))‖ = 1 ∧
      (∀ θ, action h hh θ (f (-(n:ℝ))) = f (-(n:ℝ))) ∧
      (f (-(n:ℝ)),Bf (-(n:ℝ))) ∈ (KFCausalClockFloorPureClockMomentum.pureMomentum ε hε h).graph ∧
      projectedEnergy ε h hε hh hb (S (-(n:ℝ))) mass2 quartic vacuum t ≤
        projectedEnergy ε h hε hh hb (S 0) mass2 quartic vacuum t ∧
      M < |(inner ℂ (f (-(n:ℝ))) (Bf (-(n:ℝ)))).re| := by
  obtain ⟨n,hn⟩ := negative_expectation_unbounded ε a h hε ha hh hp M
  refine ⟨n,input_norm ε a h hε ha hh _,input_fixed ε a h hε ha hh _,
    momentum_graph ε h hε hh _,energy_le ε a h hε ha hh hb hp _
      (neg_nonpos.mpr (Nat.cast_nonneg n)) mass2 quartic vacuum t,?_⟩
  have hl : M < -(inner ℂ (f (-(n:ℝ))) (Bf (-(n:ℝ)))).re := by linarith only [hn]
  exact hl.trans_le (neg_le_abs _)

theorem no_energy_expectation_bound (hp : 0 < h) (mass2 quartic vacuum t : ℝ) :
    ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ, p ≤ 0 →
      |(inner ℂ (f p) (Bf p)).re| ≤
        K*(1+projectedEnergy ε h hε hh hb (S p) mass2 quartic vacuum t) := by
  rintro ⟨K,hK,hbound⟩
  obtain ⟨n,_,_,_,he,hm⟩ := bounded_energy_unbounded_expectation ε a h hε ha hh hb hp
    mass2 quartic vacuum t (K*(1+projectedEnergy ε h hε hh hb (S 0) mass2 quartic vacuum t))
  have hb' := (hbound (-(n:ℝ)) (neg_nonpos.mpr (Nat.cast_nonneg n))).trans
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1:ℝ)) he) hK)
  exact (not_lt_of_ge hb') hm

#print axioms real_smul_pairing
#print axioms drift_positive
#print axioms expectation_exact
#print axioms negative_expectation_unbounded
#print axioms bounded_energy_unbounded_expectation
#print axioms no_energy_expectation_bound
end
end UnifiedTheory.Audit.KFCausalProjectedMomentumExpectation
