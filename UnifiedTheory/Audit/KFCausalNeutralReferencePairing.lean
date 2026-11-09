/- Exact neutral-test pairing in the reference form and its physical
energy estimate. The canonical rate is bounded uniformly in bounded
nonzero hbar, with the actual time-dependent energy as weight. -/
import UnifiedTheory.Audit.KFCausalNeutralReferenceForm
import UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalNeutralReferencePairing
noncomputable section
open scoped ComplexConjugate
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (action)
open UnifiedTheory.Audit.KFCausalNeutralTranslationFactors (action_inverse)
open UnifiedTheory.Audit.KFCausalNeutralReferenceForm
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy timeEnergy_actual)
open UnifiedTheory.Audit.KFCausalNeutralTranslationJointGraph (energyWeight_ne_zero)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCommutator (outputLp_commutator)
open UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator (speedBound errorBound_scaled)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem action_dual (r : ℝ) (f g : Hilbert) :
    inner ℂ (action r f) g = inner ℂ f (action (-r) g) := by
  have hi : action r (action (-r) g) = g := by
    simpa only [neg_neg] using action_inverse (-r) g
  simpa only [hi] using (action r).inner_map_map f (action (-r) g)

def coefficient (h : ℝ) : ℂ := Complex.I*((1/h:ℝ):ℂ)

theorem coefficient_conj (h : ℝ) : conj (coefficient h) = -coefficient h := by
  simp [coefficient]

theorem coefficient_norm (h : ℝ) : ‖coefficient h‖ = 1/|h| := by
  simp [coefficient,Complex.norm_real,Real.norm_eq_abs]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ) (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
local notation "𝒱" => FormSpace ε hε h hne hh m g k
local notation "E" => energyOutput ε hε h hne hh m g k
local notation "T" => formTransfer ε hε h hne hh m g k
local notation "F" => formAction ε hε h hne hh m g k hm hg hk
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "R" => outputActionLp m g k

theorem reference_pairing (t r : ℝ) (u z : 𝒱 0) :
    inner ℂ u (Q t (F 0 r z)) =
      inner ℂ (E t (T 0 t u)) (R t r (E t (T 0 t z))) := by
  have hp := referenceForm_represents_closed_form ε hε h hne hh m g k t u (F 0 r z)
  have he := (congrArg (E t) (formAction_transfer ε hε h hne hh m g k hm hg hk 0 t r z)).trans
    (formAction_output ε hε h hne hh m g k hm hg hk t r (T 0 t z))
  exact hp.trans (congrArg (fun y => inner ℂ (E t (T 0 t u)) y) he)

def rate (t r : ℝ) (u : 𝒱 0) : ℂ :=
  coefficient h*(inner ℂ u (Q t (F 0 r u))-conj (inner ℂ u (Q t (F 0 (-r) u))))

theorem rate_output (t r : ℝ) (u : 𝒱 0) :
    rate ε hε h hne hh m g k hm hg hk t r u =
      coefficient h*(inner ℂ (E t (T 0 t u)) (R t r (E t (T 0 t u)))-
        inner ℂ (R t (-r) (E t (T 0 t u))) (E t (T 0 t u))) := by
  simp only [rate,reference_pairing,inner_conj_symm]

theorem canonical_rate_bound (t v H : ℝ) (hH : |h| ≤ H) (u : 𝒱 0) :
    ‖rate ε hε h hne hh m g k hm hg hk t (h*v) u‖ ≤
      speedBound (energyWeight m g k t) H v*timeEnergy ε hε h hne hh m g k t u := by
  let y := E t (T 0 t u)
  let w := energyWeight m g k t
  have hb := outputLp_commutator angleMeasure w (energyWeight_ne_zero m g k t hm hg hk)
    ((h*v:ℝ):ℂ) (h*v) y y
  have hc : ‖inner ℂ y (R t (h*v) y)-inner ℂ (R t (-(h*v)) y) y‖ ≤
      |h| *speedBound w H v*‖y‖*‖y‖ := by
    apply le_trans (by simpa only [outputActionLp,Complex.ofReal_neg] using hb)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (errorBound_scaled w h v H hH) (norm_nonneg y)) (norm_nonneg y)
  have divide (a b c x : ℝ) (hx : 0 < x) (ha : a ≤ x*b*c*c) : (1/x)*a ≤ b*c^2 := by
    have hd : a/x ≤ b*c*c := by
      apply (div_le_iff₀ hx).mpr
      nlinarith only [ha]
    calc
      (1/x)*a = a/x := by ring
      _ ≤ b*c*c := hd
      _ = b*c^2 := by ring
  calc
    _ = (1/|h|)*‖inner ℂ y (R t (h*v) y)-inner ℂ (R t (-(h*v)) y) y‖ := by
      simp only [rate_output,norm_mul,coefficient_norm]
      rfl
    _ ≤ speedBound w H v*‖y‖^2 := divide _ _ _ _ (abs_pos.mpr hne) hc
    _ = _ := congrArg (fun z => speedBound w H v*z) (timeEnergy_actual ε hε h hne hh m g k t u)

#print axioms action_dual
#print axioms coefficient_conj
#print axioms coefficient_norm
#print axioms reference_pairing
#print axioms rate_output
#print axioms canonical_rate_bound

end
end UnifiedTheory.Audit.KFCausalNeutralReferencePairing
