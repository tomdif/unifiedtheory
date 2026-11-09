/- Unconditional Two-Time Resolvent Action Difference Identities and Norm Bounds
for all real couplings on the time-independent common operator domain
Dom_common = (Dom T ∩ Dom Kr ∩ Dom P) ∩ Dom Tres(0). At every shift a > 0 and
times t, s, the resolvents R_{H(t)}(a) and R_{S(t)}(a) applied to the shifted
time-s operators H(s) + a and S(s) + a reproduce the identity up to explicit
O(a⁻¹ |exp(2t) - exp(2s)|) growing/potential error terms. -/
import UnifiedTheory.Audit.KFCausalClockFloorUnconditionalTwoTimeEvolution
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianClockCore
import UnifiedTheory.Audit.KFCausalClockFloorResidualClockCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorTwoTimeResolventDifference
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalPositiveResolventBounds (resolvent_apply_norm_bound)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain
   common_domain_subset_hamiltonian
   common_domain_subset_residual
   common_domain_subset_growing
   unconditional_two_time_residual_difference
   unconditional_two_time_hamiltonian_growing_difference
   unconditional_two_time_hamiltonian_three_operator_difference)

private theorem shifted_sub_eq (ht_val hs_val f z : Hilbert) (a : ℝ) (c : ℂ)
    (hdiff : ht_val-hs_val=c • z) :
    (ht_val+a • f)-(hs_val+a • f)=c • z := by
  calc
    (ht_val+a • f)-(hs_val+a • f) = ht_val-hs_val := by abel
    _ = c • z := hdiff

private theorem resolvent_sub_of_shifted_diff (R : Hilbert →L[ℂ] Hilbert)
    (f ht_val hs_val z : Hilbert) (a : ℝ) (c : ℂ)
    (hl : R (ht_val+a • f)=f)
    (hshift : (ht_val+a • f)-(hs_val+a • f)=c • z) :
    f-R (hs_val+a • f)=c • R z := by
  calc
    f-R (hs_val+a • f) = R (ht_val+a • f)-R (hs_val+a • f) := by rw [hl]
    _ = R ((ht_val+a • f)-(hs_val+a • f)) := (R.map_sub _ _).symm
    _ = R (c • z) := congrArg R hshift
    _ = c • R z := R.map_smul c z

private theorem norm_sub_le_of_resolvent_sub (R : Hilbert →L[ℂ] Hilbert)
    (f hs_val z : Hilbert) (a c : ℝ)
    (hsub : f-R (hs_val+a • f)=(c:ℂ) • R z)
    (hbound : ‖R z‖ ≤ a⁻¹*‖z‖) :
    ‖f-R (hs_val+a • f)‖ ≤ a⁻¹* |c| *‖z‖ := by
  rw [hsub,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have h1 : |c| *‖R z‖ ≤ |c| *(a⁻¹*‖z‖) :=
    mul_le_mul_of_nonneg_left hbound (abs_nonneg c)
  linarith

private theorem component_bound_of_sum (a c : ℝ) (ha : 0 < a) (k_val p_val : Hilbert)
    (h : ‖k_val+p_val‖ ≤ ‖k_val‖+‖p_val‖) :
    a⁻¹* |c| *‖k_val+p_val‖ ≤ a⁻¹* |c| *(‖k_val‖+‖p_val‖) :=
  mul_le_mul_of_nonneg_left h (mul_nonneg (inv_nonneg.mpr ha.le) (abs_nonneg c))

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k

abbrev unconditionalDomain : Submodule ℂ Hilbert :=
  commonOperatorDomain ε hε h hh hb m g k

theorem hamiltonian_shifted_two_time_difference (t s a : ℝ) (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    (H t ⟨f,common_domain_subset_hamiltonian ε hε h hh hb m g k t hf⟩+a • f)-
      (H s ⟨f,common_domain_subset_hamiltonian ε hε h hh hb m g k s hf⟩+a • f)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
        (G) ⟨f,common_domain_subset_growing ε hε h hh hb m g k hf⟩ :=
  shifted_sub_eq _ _ f _ a _
    (unconditional_two_time_hamiltonian_growing_difference ε hε h hh hb m g k t s f hf)

theorem hamiltonian_shifted_two_time_three_operator_difference (t s a : ℝ) (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    (H t ⟨f,common_domain_subset_hamiltonian ε hε h hh hb m g k t hf⟩+a • f)-
      (H s ⟨f,common_domain_subset_hamiltonian ε hε h hh hb m g k s hf⟩+a • f)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
        ((K) ⟨f,hf.1.1.2⟩+(P) ⟨f,hf.1.2⟩) :=
  shifted_sub_eq _ _ f _ a _
    (unconditional_two_time_hamiltonian_three_operator_difference ε hε h hh hb m g k t s f hf)

theorem residual_shifted_two_time_difference (t s a : ℝ) (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    (S t ⟨f,common_domain_subset_residual ε hε h hh hb m g k t hf⟩+a • f)-
      (S s ⟨f,common_domain_subset_residual ε hε h hh hb m g k s hf⟩+a • f)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) • (P) ⟨f,hf.1.2⟩ :=
  shifted_sub_eq _ _ f _ a _
    (unconditional_two_time_residual_difference ε hε h hh hb m g k t s f hf)

theorem hamiltonian_resolvent_two_time_action_sub (t s a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    f-RH t a (H s ⟨f,common_domain_subset_hamiltonian ε hε h hh hb m g k s hf⟩+a • f)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
        RH t a ((G) ⟨f,common_domain_subset_growing ε hε h hh hb m g k hf⟩) :=
  resolvent_sub_of_shifted_diff (RH t a) f _ _ _ a _
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha
      ⟨f,common_domain_subset_hamiltonian ε hε h hh hb m g k t hf⟩)
    (hamiltonian_shifted_two_time_difference ε hε h hh hb m g k t s a f hf)

theorem hamiltonian_resolvent_two_time_three_operator_sub (t s a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    f-RH t a (H s ⟨f,common_domain_subset_hamiltonian ε hε h hh hb m g k s hf⟩+a • f)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
        RH t a ((K) ⟨f,hf.1.1.2⟩+(P) ⟨f,hf.1.2⟩) :=
  resolvent_sub_of_shifted_diff (RH t a) f _ _ _ a _
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha
      ⟨f,common_domain_subset_hamiltonian ε hε h hh hb m g k t hf⟩)
    (hamiltonian_shifted_two_time_three_operator_difference ε hε h hh hb m g k t s a f hf)

theorem hamiltonian_resolvent_two_time_norm_bound (t s a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖f-RH t a (H s ⟨f,common_domain_subset_hamiltonian ε hε h hh hb m g k s hf⟩+a • f)‖ ≤
      a⁻¹* |Real.exp (2*t)-Real.exp (2*s)| *
        ‖(G) ⟨f,common_domain_subset_growing ε hε h hh hb m g k hf⟩‖ :=
  norm_sub_le_of_resolvent_sub (RH t a) f _ _ a (Real.exp (2*t)-Real.exp (2*s))
    (hamiltonian_resolvent_two_time_action_sub ε hε h hh hb m g k t s a ha f hf)
    (resolvent_apply_norm_bound (H t) (RH t a) a ha
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) _)

theorem hamiltonian_resolvent_two_time_component_norm_bound (t s a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖f-RH t a (H s ⟨f,common_domain_subset_hamiltonian ε hε h hh hb m g k s hf⟩+a • f)‖ ≤
      a⁻¹* |Real.exp (2*t)-Real.exp (2*s)| *
        (‖(K) ⟨f,hf.1.1.2⟩‖+‖(P) ⟨f,hf.1.2⟩‖) := by
  have h1 := norm_sub_le_of_resolvent_sub (RH t a) f _ _ a (Real.exp (2*t)-Real.exp (2*s))
    (hamiltonian_resolvent_two_time_three_operator_sub ε hε h hh hb m g k t s a ha f hf)
    (resolvent_apply_norm_bound (H t) (RH t a) a ha
      (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) _)
  exact h1.trans (component_bound_of_sum a (Real.exp (2*t)-Real.exp (2*s)) ha _ _
    (norm_add_le _ _))

theorem residual_resolvent_two_time_action_sub (t s a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    f-RS t a (S s ⟨f,common_domain_subset_residual ε hε h hh hb m g k s hf⟩+a • f)=
      ((Real.exp (2*t)-Real.exp (2*s):ℝ):ℂ) •
        RS t a ((P) ⟨f,hf.1.2⟩) :=
  resolvent_sub_of_shifted_diff (RS t a) f _ _ _ a _
    (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t a ha
      ⟨f,common_domain_subset_residual ε hε h hh hb m g k t hf⟩)
    (residual_shifted_two_time_difference ε hε h hh hb m g k t s a f hf)

theorem residual_resolvent_two_time_norm_bound (t s a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ commonOperatorDomain ε hε h hh hb m g k) :
    ‖f-RS t a (S s ⟨f,common_domain_subset_residual ε hε h hh hb m g k s hf⟩+a • f)‖ ≤
      a⁻¹* |Real.exp (2*t)-Real.exp (2*s)| *‖(P) ⟨f,hf.1.2⟩‖ :=
  norm_sub_le_of_resolvent_sub (RS t a) f _ _ a (Real.exp (2*t)-Real.exp (2*s))
    (residual_resolvent_two_time_action_sub ε hε h hh hb m g k t s a ha f hf)
    (resolvent_apply_norm_bound (S t) (RS t a) a ha
      (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
      (KFCausalClosedGraphForm.hamiltonian_positive (SD t)) _)

#print axioms hamiltonian_shifted_two_time_difference
#print axioms hamiltonian_shifted_two_time_three_operator_difference
#print axioms residual_shifted_two_time_difference
#print axioms hamiltonian_resolvent_two_time_action_sub
#print axioms hamiltonian_resolvent_two_time_three_operator_sub
#print axioms hamiltonian_resolvent_two_time_norm_bound
#print axioms hamiltonian_resolvent_two_time_component_norm_bound
#print axioms residual_resolvent_two_time_action_sub
#print axioms residual_resolvent_two_time_norm_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorTwoTimeResolventDifference
