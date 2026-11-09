/- Identification of form-state limits with the existing physical
propagator through the mass equation and its interval uniqueness. -/
import UnifiedTheory.Audit.KFCausalClockFloorStateMassEquation
import UnifiedTheory.Audit.KFCausalContinuousMassUniqueness
import UnifiedTheory.Audit.KFCausalClockFloorSmoothedFullDerivative
import UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakSolution
import UnifiedTheory.Audit.KFCausalClockFloorFixedDomainApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorStateLimitIdentification
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakFormContinuity
open UnifiedTheory.Audit.KFCausalClockFloorFormDomainTransport
open UnifiedTheory.Audit.KFCausalClockFloorFixedGeneratorResolvent
open UnifiedTheory.Audit.KFCausalClockFloorFullGeneratorApproximation
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "M" => massOperator ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "S" => transport ε hε h hne hh m g k
local notation "A" => fullApproximation ε hε h hne hh m g k
local notation "q" => connectionThreshold ε hε h hne hh m g k
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

theorem mass_solution_eq_formFlow (u : ℝ → V) (l r : ℝ)
    (hu : ContinuousOn u (Icc l r))
    (hd : ∀ t ∈ Ioo l r, HasDerivAt (fun z => M (u z)) (c • Q t (u t)) t)
    (t : ℝ) (ht : t ∈ Icc l r) : u t = F l t (u l) :=
  KFCausalContinuousMassUniqueness.unique J M (fun z => c • Q z)
    (embedding_injective ε hε h hne hh m g k 0)
    (mass_left_pairing ε hε h hne hh m g k)
    (KFCausalClockFloorAveragedWeakSolution.formGenerator_diagonal_zero ε hε h hne hh m g k)
    u (fun z => F l z (u l)) l r hu
    (formFlow_continuous ε hε h hne hh m g k l (u l)).continuousOn hd
    (fun z _ => KFCausalClockFloorSmoothedFullDerivative.mass_derivative ε hε h hne hh m g k l z (u l))
    (formFlow_initial ε hε h hne hh m g k l (u l)).symm t ht

theorem uniform_limit_eq_formFlow (a s l r : ℝ) (ha : 0 < a)
    (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) (hbp : ∀ n, 0 < b n)
    (hadm : ∀ n t, t ∈ Icc l r → q a s t < b n)
    (w : ℕ → ℝ → V) (u : ℝ → V) (hu : ContinuousOn u (Icc l r))
    (hw : TendstoUniformlyOn w u atTop (Icc l r))
    (hd : ∀ n t, t ∈ Icc l r →
      HasDerivWithinAt (w n) (A a (b n) s t (w n t)) (Icc l r) t)
    (t : ℝ) (ht : t ∈ Icc l r) :
    S a s t (u t) = F l t (S a s l (u l)) := by
  have hS : Continuous (S a s) := continuous_iff_continuousAt.mpr
    (fun z => (transport_derivative ε hε h hne hh m g k a s z ha).continuousAt)
  exact mass_solution_eq_formFlow ε hε h hne hh m g k (fun z => S a s z (u z)) l r
    (hS.continuousOn.clm_apply hu)
    (KFCausalClockFloorStateMassEquation.uniform_limit_mass_equation ε hε h hne hh m g k
      a s l r ha b hb hbp hadm w u hu hw hd) t ht

theorem uniform_limit_eq_physical (a s l r : ℝ) (ha : 0 < a)
    (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) (hbp : ∀ n, 0 < b n)
    (hadm : ∀ n t, t ∈ Icc l r → q a s t < b n)
    (w : ℕ → ℝ → V) (u : ℝ → V) (hu : ContinuousOn u (Icc l r))
    (hw : TendstoUniformlyOn w u atTop (Icc l r))
    (hd : ∀ n t, t ∈ Icc l r →
      HasDerivWithinAt (w n) (A a (b n) s t (w n t)) (Icc l r) t)
    (t : ℝ) (ht : t ∈ Icc l r) :
    J (S a s t (u t)) = U l t (J (S a s l (u l))) :=
  (congrArg J (uniform_limit_eq_formFlow ε hε h hne hh m g k a s l r ha
    b hb hbp hadm w u hu hw hd t ht)).trans
    (evolution_embedding ε hε h hne hh m g k l t (S a s l (u l))).symm

theorem uniform_limit_coordinate_formula (a s l r : ℝ) (ha : 0 < a)
    (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) (hbp : ∀ n, 0 < b n)
    (hadm : ∀ n t, t ∈ Icc l r → q a s t < b n)
    (w : ℕ → ℝ → V) (u : ℝ → V) (hu : ContinuousOn u (Icc l r))
    (hw : TendstoUniformlyOn w u atTop (Icc l r))
    (hd : ∀ n t, t ∈ Icc l r →
      HasDerivWithinAt (w n) (A a (b n) s t (w n t)) (Icc l r) t)
    (t : ℝ) (ht : t ∈ Icc l r) :
    u t = S a t s (F l t (S a s l (u l))) :=
  (KFCausalClockFloorFixedDomainApproximation.transport_inverse ε hε h hne hh m g k a t s ha (u t)).symm.trans
    (congrArg (S a t s) (uniform_limit_eq_formFlow ε hε h hne hh m g k a s l r ha
      b hb hbp hadm w u hu hw hd t ht))

#print axioms mass_solution_eq_formFlow
#print axioms uniform_limit_eq_formFlow
#print axioms uniform_limit_eq_physical
#print axioms uniform_limit_coordinate_formula
end
end UnifiedTheory.Audit.KFCausalClockFloorStateLimitIdentification
