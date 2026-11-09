/- The full initial classical-coefficient pairing converges. The two
matter outputs vanish in norm and the ordered output has the proved
clock-dependent drift pairing; every actual energy weight is retained. -/
import UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialDriftSeed
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output commonOutput)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight energyWeight_norm_square)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms
open UnifiedTheory.Audit.KFCausalClockFloorTrialUniformEnergy
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyLimit
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (trialState_shifted_graph)
open UnifiedTheory.Audit.KFCausalClockFloorStrongInitialOutput
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator
open UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityOutput

theorem pairing_complex_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (c : ℂ) (f : E) :
    (inner ℂ (c • f) (A (c • f))).re = ‖c‖^2*(inner ℂ f (A f)).re := by
  rw [map_smul,inner_smul_left,inner_smul_right,← mul_assoc,Complex.conj_mul',← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem classicalOutput_pairing (ε : ℝ) (hε : 0 < ε) (g : Output (Fin 8) Hilbert) :
    (inner ℂ g (classicalOutput ε hε g)).re =
      (inner ℂ (g 5) (driftOperator ε hε (g 5))).re+
      (inner ℂ (g 6) (driftOperator ε hε (g 6))).re+
      (inner ℂ (g 7) (driftOperator ε hε (g 7))).re := by
  rw [PiLp.inner_apply,Complex.re_sum]
  norm_num [Fin.sum_univ_succ,classicalOutput_apply,classicalFactor]
  exact (add_assoc (inner ℂ (g 5) (driftOperator ε hε (g 5))).re
    (inner ℂ (g 6) (driftOperator ε hε (g 6))).re
    (inner ℂ (g 7) (driftOperator ε hε (g 7))).re).symm

theorem weighted_classical_pairing (ε : ℝ) (hε : 0 < ε) (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (g : Fin 8 → Hilbert) :
    (inner ℂ (WithLp.toLp 2 (fun i => energyWeight mass2 quartic vacuum t i • g i))
      (classicalOutput ε hε (WithLp.toLp 2 (fun i => energyWeight mass2 quartic vacuum t i • g i)))).re =
    Real.exp (2*t)*(mass2/2*(inner ℂ (g 5) (driftOperator ε hε (g 5))).re+
      quartic/4*(inner ℂ (g 6) (driftOperator ε hε (g 6))).re+
      vacuum*(inner ℂ (g 7) (driftOperator ε hε (g 7))).re) := by
  rw [classicalOutput_pairing]
  simp only [pairing_complex_smul,energyWeight_norm_square mass2 quartic vacuum t hm hq hv]
  change (Real.exp (2*t)*mass2/2)*(inner ℂ (g 5) (driftOperator ε hε (g 5))).re+
      (Real.exp (2*t)*quartic/4)*(inner ℂ (g 6) (driftOperator ε hε (g 6))).re+
      (Real.exp (2*t)*vacuum)*(inner ℂ (g 7) (driftOperator ε hε (g 7))).re = _
  ring

theorem drift_pairing_bound (ε : ℝ) (hε : 0 < ε) (g : Hilbert) :
    |(inner ℂ g (driftOperator ε hε g)).re| ≤ (1/ε)*‖g‖^2 := by
  apply (Complex.abs_re_le_norm _).trans
  apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
  have h := mul_le_mul_of_nonneg_left (driftOperator_norm ε hε g) (norm_nonneg g)
  nlinarith only [h]

def normalizedFactor (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) : Hilbert :=
  (‖trialState ε a hbar hε ha hh‖⁻¹:ℝ) •
    factorValue ε hε hbar v l (trialCommon ε a hbar hε ha hh hb v l) i

def normalizedJoint (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (mass2 quartic vacuum t : ℝ) : Output (Fin 8) Hilbert :=
  (‖trialState ε a hbar hε ha hh‖⁻¹:ℝ) •
    jointOutput ε hε hbar v l mass2 quartic vacuum t (trialCommon ε a hbar hε ha hh hb v l)

theorem normalizedJoint_eq (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (mass2 quartic vacuum t : ℝ) :
    normalizedJoint ε a hbar hε ha hh hb v l mass2 quartic vacuum t =
      WithLp.toLp 2 (fun i => energyWeight mass2 quartic vacuum t i •
        normalizedFactor ε a hbar hε ha hh hb v l i) := by
  apply PiLp.ext
  intro i
  exact smul_comm (‖trialState ε a hbar hε ha hh‖⁻¹:ℝ) (energyWeight mass2 quartic vacuum t i)
    (factorValue ε hε hbar v l (trialCommon ε a hbar hε ha hh hb v l) i)

theorem normalizedFactor_norm_square (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    ‖normalizedFactor ε a hbar hε ha hh hb v l i‖^2 = factorRatio ε a hbar hε ha hh hb v l i := by
  rw [normalizedFactor,norm_smul,mul_pow,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_pow]
  exact (div_eq_inv_mul _ _).symm

theorem normalizedFactor_seven (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : hbar ≠ 0) (hb : |hbar| ≤ 2*Real.pi*ε/3)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    normalizedFactor ε a hbar hε ha hh hb v l 7 = normalizedOutput ε a hbar hε ha hh hb := by
  have he := (orderedExponential ε hε hbar).mem_graph_snd_inj'
    (trial_factor_graph ε a hbar hε ha hh hb v l 7)
    (trialState_shifted_graph ε a hbar hε ha hh hb) rfl
  dsimp only [Prod.snd] at he
  exact congrArg (fun x : Hilbert => (‖trialState ε a hbar hε ha hh‖⁻¹:ℝ) • x) he

theorem zero_factor_pairing_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (i : Fin 8) (hi : factorLimit ε a i = 0) :
    Tendsto (fun n => (inner ℂ (normalizedFactor ε a (h n) hε ha (hh n) (hb n) v l i)
      (driftOperator ε hε (normalizedFactor ε a (h n) hε ha (hh n) (hb n) v l i))).re) atTop (𝓝 0) := by
  have ht := factorRatio_tendsto ε a hε ha h hh hb hz v l i
  rw [hi] at ht
  apply squeeze_zero_norm
    (fun n => by simpa only [Real.norm_eq_abs,normalizedFactor_norm_square] using
      drift_pairing_bound ε hε (normalizedFactor ε a (h n) hε ha (hh n) (hb n) v l i))
  simpa only [mul_zero] using ht.const_mul (1/ε)

def initialClassicalDrift (ε a vacuum t : ℝ) : ℝ :=
  Real.exp (2*t)*vacuum*(driftMass ε a/clockMass ε a)

theorem normalizedJoint_drift_limit (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ)
    (mass2 quartic vacuum t : ℝ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    Tendsto (fun n => (inner ℂ (normalizedJoint ε a (h n) hε ha (hh n) (hb n) v l mass2 quartic vacuum t)
      (classicalOutput ε hε (normalizedJoint ε a (h n) hε ha (hh n) (hb n) v l mass2 quartic vacuum t))).re)
      atTop (𝓝 (initialClassicalDrift ε a vacuum t)) := by
  simp_rw [normalizedJoint_eq,weighted_classical_pairing ε hε mass2 quartic vacuum t hm hq hv]
  have h5 := (zero_factor_pairing_limit ε a hε ha h hh hb hz v l 5 rfl).const_mul (mass2/2)
  have h6 := (zero_factor_pairing_limit ε a hε ha h hh hb hz v l 6 rfl).const_mul (quartic/4)
  have h7 := normalizedOutput_drift_limit ε a hε ha h hh hb hz
  have hsum := ((h5.add h6).add (h7.const_mul vacuum)).const_mul (Real.exp (2*t))
  simpa only [normalizedFactor_seven,mul_zero,zero_add,initialClassicalDrift,mul_assoc] using hsum

#print axioms pairing_complex_smul
#print axioms classicalOutput_pairing
#print axioms weighted_classical_pairing
#print axioms drift_pairing_bound
#print axioms normalizedJoint_eq
#print axioms normalizedFactor_norm_square
#print axioms normalizedFactor_seven
#print axioms zero_factor_pairing_limit
#print axioms normalizedJoint_drift_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialDriftSeed
