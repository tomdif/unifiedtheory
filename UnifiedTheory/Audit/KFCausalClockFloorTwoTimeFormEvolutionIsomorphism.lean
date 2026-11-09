/- Continuous linear isomorphisms between the time-dependent completed energy-form
spaces induced by the nonautonomous quantum evolution, together with exact
two-time form-domain invariance, five-channel energy identities, and two-sided
exponential form-norm and component bounds on the operator form domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorEvolvedFormEnergyRegularity
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormEvolutionIsomorphism

noncomputable section

open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorAveragedFormTransport
  (FormSpace embedding energyOutput form_norm_identity
   formTransfer transfer_embedding transfer_inverse transfer_comp transfer_self)
open KFCausalClockFloorAveragedTimeControl
  (timeEnergy timeEnergy_actual timeEnergy_nonneg transported_form_norm)
open KFCausalClockFloorAveragedFormFlow
  (formFlow formFlow_initial formFlow_compose formFlow_reverse formFlow_physical_norm)
open KFCausalClockFloorAveragedFormLinearity
  (formFlow_add formFlow_smul formLinearMap)
open KFCausalClockFloorAveragedEvolution
  (evolution evolution_embedding evolution_norm)
open KFCausalClockFloorEvolvedFormEnergyRegularity
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
  (static_root_subset_clockHalf_domain static_root_clockHalf_norm_sq_le
   averaged_form_domain_le_clockHalf_domain positive_vacuum_averaged_form_domain_iff)

private theorem prop_of_eq {X : Type*} (P : X → Prop) {x y : X} (hxy : x = y) (hx : P x) :
    P y :=
  (congrArg P hxy).mp hx

private theorem operator_norm_sq_congr
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : Hilbert →ₗ.[ℂ] Y) {x y : Hilbert} (hxy : x = y)
    (hx : x ∈ T.domain) (hy : y ∈ T.domain) :
    ‖T ⟨x, hx⟩‖ ^ 2 = ‖T ⟨y, hy⟩‖ ^ 2 := by
  have hsub : (⟨x, hx⟩ : T.domain) = ⟨y, hy⟩ := Subtype.ext hxy
  exact congrArg (fun z : T.domain => ‖T z‖ ^ 2) hsub

private theorem form_output_eq_operator
    (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (w : KFCausalClosedGraphForm.FormSpace D) (f : Hilbert)
    (hJ : KFCausalClosedGraphForm.embedding D w = f) (hf : f ∈ D.operator.domain) :
    KFCausalClosedGraphForm.energyOutput D w = D.operator ⟨f, hf⟩ :=
  D.operator.mem_graph_snd_inj' w.property (D.operator.mem_graph ⟨f, hf⟩) hJ

private theorem split_le_exp_mul_total {s t j a n v u : ℝ}
    (h1 : n ≤ j + Real.exp (2 * |t - s|) * a)
    (h2 : u = j + a) (hj : 0 ≤ j) (hv : v = n) :
    v ≤ Real.exp (2 * |t - s|) * u := by
  have hexp : 1 ≤ Real.exp (2 * |t - s|) :=
    Real.one_le_exp (mul_nonneg (by norm_num) (abs_nonneg (t - s)))
  have hj_le : j ≤ Real.exp (2 * |t - s|) * j :=
    le_mul_of_one_le_left hj hexp
  nlinarith

private theorem norm_le_exp_abs_of_sq_le {s t x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsq : x ^ 2 ≤ Real.exp (2 * |t - s|) * y ^ 2) :
    x ≤ Real.exp |t - s| * y := by
  have hrew : Real.exp (2 * |t - s|) * y ^ 2 = (Real.exp |t - s| * y) ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat]
  rw [hrew] at hsq
  have hnonneg : 0 ≤ Real.exp |t - s| * y :=
    mul_nonneg (Real.exp_pos _).le hy
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hx, Real.sqrt_sq hnonneg] at hsqrt

private theorem unscale_reverse_exp_abs {s t a b : ℝ}
    (h : a ≤ Real.exp (2 * |s - t|) * b) :
    Real.exp (-2 * |t - s|) * a ≤ b := by
  rw [abs_sub_comm s t] at h
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-2 * |t - s|)).le
  have hexp :
      Real.exp (-2 * |t - s|) * (Real.exp (2 * |t - s|) * b) = b := by
    rw [← mul_assoc, ← Real.exp_add,
      show -2 * |t - s| + 2 * |t - s| = 0 by ring, Real.exp_zero, one_mul]
  rwa [hexp] at hm

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "AD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k
local notation "VT" => FormSpace ε hε h hh hw m g k
local notation "RV" => FormSpace ε hε h hh hw m g k 0
local notation "AJ" => embedding ε hε h hh hw m g k
local notation "RJ" => embedding ε hε h hh hw m g k 0
local notation "AT" => energyOutput ε hε h hh hw m g k
local notation "FT" => formTransfer ε hε h hh hw m g k
local notation "F" => formFlow ε hε h hh hw m g k
local notation "FL" => formLinearMap ε hε h hh hw m g k
local notation "U" => evolution ε hε h hh hw m g k
local notation "E" => timeEnergy ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k

/-! ### 1. Continuous Linear Two-Time Form-Space Evolution Isomorphisms -/

/-- For any `u : VT s`, transferring `u` to the reference form space `RV = VT 0` preserves
the physical Hilbert embedding `RJ (FT s 0 u) = AJ s u` and identifies the reference
time-energy `E s (FT s 0 u)` with `‖AT s u‖ ^ 2`. -/
theorem transfer_to_zero_energy_eq (s : ℝ) (u : VT s) :
    RJ (FT s 0 u) = AJ s u ∧
    E s (FT s 0 u) = ‖AT s u‖ ^ 2 :=
  ⟨transfer_embedding ε hε h hh hw m g k s 0 u,
    (timeEnergy_actual ε hε h hh hw m g k s (FT s 0 u)).symm.trans
      (congrArg (fun v : VT s => ‖AT s v‖ ^ 2)
        (transfer_inverse ε hε h hh hw m g k s 0 u))⟩

/-- The linear map `VT s →ₗ[ℂ] VT t` induced by transporting `u : VT s` to `RV`, evolving
from `s` to `t` via `formLinearMap s t`, and transporting to `VT t`. -/
def twoTimeFormLinearMap (s t : ℝ) : VT s →ₗ[ℂ] VT t :=
  (FT 0 t).toLinearMap.comp ((FL s t).comp (FT s 0).toLinearMap)

theorem twoTimeFormLinearMap_apply (s t : ℝ) (u : VT s) :
    twoTimeFormLinearMap ε hε h hh hb m g k s t u =
      evolvedForm ε hε h hh hb m g k s t t (FT s 0 u) := rfl

/-- Exact squared form-norm identity for `twoTimeFormLinearMap s t u` in `VT t`. -/
theorem twoTimeFormLinearMap_norm_sq_eq (s t : ℝ) (u : VT s) :
    ‖twoTimeFormLinearMap ε hε h hh hb m g k s t u‖ ^ 2 =
      ‖AJ s u‖ ^ 2 +
        instantFormEnergy ε hε h hh hb m g k s t t (FT s 0 u) :=
  (evolvedForm_norm_sq_eq ε hε h hh hb m g k s t t (FT s 0 u)).trans
    (congrArg (fun x : Hilbert => ‖x‖ ^ 2 +
        instantFormEnergy ε hε h hh hb m g k s t t (FT s 0 u))
      (transfer_embedding ε hε h hh hw m g k s 0 u))

/-- Squared form-norm bound for `twoTimeFormLinearMap s t u` in terms of `‖AJ s u‖ ^ 2`
and `‖AT s u‖ ^ 2`. -/
theorem twoTimeFormLinearMap_norm_sq_le_split (s t : ℝ) (u : VT s) :
    ‖twoTimeFormLinearMap ε hε h hh hb m g k s t u‖ ^ 2 ≤
      ‖AJ s u‖ ^ 2 + Real.exp (2 * |t - s|) * ‖AT s u‖ ^ 2 :=
  (twoTimeFormLinearMap_norm_sq_eq ε hε h hh hb m g k s t u).trans_le
    (add_le_add le_rfl
      ((evolved_dynamical_energy_le ε hε h hh hb m g k s t (FT s 0 u)).trans_eq
        (congrArg (Real.exp (2 * |t - s|) * ·)
          (transfer_to_zero_energy_eq ε hε h hh hb m g k s u).2)))

/-- Sharp exponential squared form-norm bound `‖twoTimeFormLinearMap s t u‖ ^ 2 ≤ e^{2|t-s|} ‖u‖ ^ 2`. -/
theorem twoTimeFormLinearMap_norm_sq_le (s t : ℝ) (u : VT s) :
    ‖twoTimeFormLinearMap ε hε h hh hb m g k s t u‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * ‖u‖ ^ 2 :=
  split_le_exp_mul_total
    (twoTimeFormLinearMap_norm_sq_le_split ε hε h hh hb m g k s t u)
    (form_norm_identity ε hε h hh hw m g k s u)
    (sq_nonneg ‖AJ s u‖) rfl

/-- Sharp exponential norm bound `‖twoTimeFormLinearMap s t u‖ ≤ e^{|t-s|} ‖u‖`. -/
theorem twoTimeFormLinearMap_norm_le (s t : ℝ) (u : VT s) :
    ‖twoTimeFormLinearMap ε hε h hh hb m g k s t u‖ ≤
      Real.exp |t - s| * ‖u‖ :=
  norm_le_exp_abs_of_sq_le (norm_nonneg _) (norm_nonneg u)
    (twoTimeFormLinearMap_norm_sq_le ε hε h hh hb m g k s t u)

/-- The continuous linear two-time form evolution operator `VT s →L[ℂ] VT t`. -/
def twoTimeFormEvolution (s t : ℝ) : VT s →L[ℂ] VT t :=
  (twoTimeFormLinearMap ε hε h hh hb m g k s t).mkContinuous
    (Real.exp |t - s|)
    (twoTimeFormLinearMap_norm_le ε hε h hh hb m g k s t)

theorem twoTimeFormEvolution_apply (s t : ℝ) (u : VT s) :
    twoTimeFormEvolution ε hε h hh hb m g k s t u =
      FT 0 t (F s t (FT s 0 u)) := rfl

theorem twoTimeFormEvolution_eq_evolvedForm (s t : ℝ) (u : VT s) :
    twoTimeFormEvolution ε hε h hh hb m g k s t u =
      evolvedForm ε hε h hh hb m g k s t t (FT s 0 u) := rfl

/-- `twoTimeFormEvolution s t` intertwines the form embeddings `AJ s` and `AJ t` with
the unitary Hilbert-space evolution `U s t`. -/
theorem twoTimeFormEvolution_embedding (s t : ℝ) (u : VT s) :
    AJ t (twoTimeFormEvolution ε hε h hh hb m g k s t u) =
      U s t (AJ s u) :=
  (evolvedForm_embedding ε hε h hh hb m g k s t t (FT s 0 u)).trans
    (congrArg (U s t) (transfer_embedding ε hε h hh hw m g k s 0 u))

theorem twoTimeFormEvolution_self (s : ℝ) (u : VT s) :
    twoTimeFormEvolution ε hε h hh hb m g k s s u = u :=
  (congrArg (FT 0 s) (formFlow_initial ε hε h hh hw m g k s (FT s 0 u))).trans
    (transfer_inverse ε hε h hh hw m g k s 0 u)

theorem twoTimeFormEvolution_comp (s r t : ℝ) (u : VT s) :
    twoTimeFormEvolution ε hε h hh hb m g k r t
        (twoTimeFormEvolution ε hε h hh hb m g k s r u) =
      twoTimeFormEvolution ε hε h hh hb m g k s t u :=
  congrArg (FT 0 t)
    ((congrArg (F r t)
      (transfer_inverse ε hε h hh hw m g k 0 r (F s r (FT s 0 u)))).trans
      (formFlow_compose ε hε h hh hw m g k s r t (FT s 0 u)))

theorem twoTimeFormEvolution_reverse (s t : ℝ) (u : VT s) :
    twoTimeFormEvolution ε hε h hh hb m g k t s
        (twoTimeFormEvolution ε hε h hh hb m g k s t u) = u :=
  (twoTimeFormEvolution_comp ε hε h hh hb m g k s t s u).trans
    (twoTimeFormEvolution_self ε hε h hh hb m g k s u)

/-- Continuous linear isomorphism `VT s ≃L[ℂ] VT t` between the completed energy-form
spaces at times `s` and `t` induced by the nonautonomous quantum evolution. -/
def twoTimeFormEvolutionEquiv (s t : ℝ) : VT s ≃L[ℂ] VT t :=
  ContinuousLinearEquiv.equivOfInverse
    (twoTimeFormEvolution ε hε h hh hb m g k s t)
    (twoTimeFormEvolution ε hε h hh hb m g k t s)
    (twoTimeFormEvolution_reverse ε hε h hh hb m g k s t)
    (twoTimeFormEvolution_reverse ε hε h hh hb m g k t s)

theorem twoTimeFormEvolutionEquiv_apply (s t : ℝ) (u : VT s) :
    twoTimeFormEvolutionEquiv ε hε h hh hb m g k s t u =
      twoTimeFormEvolution ε hε h hh hb m g k s t u := rfl

theorem twoTimeFormEvolutionEquiv_symm_apply (s t : ℝ) (v : VT t) :
    (twoTimeFormEvolutionEquiv ε hε h hh hb m g k s t).symm v =
      twoTimeFormEvolution ε hε h hh hb m g k t s v := rfl

theorem twoTimeFormEvolutionEquiv_embedding (s t : ℝ) (u : VT s) :
    AJ t (twoTimeFormEvolutionEquiv ε hε h hh hb m g k s t u) =
      U s t (AJ s u) :=
  twoTimeFormEvolution_embedding ε hε h hh hb m g k s t u

/-- Two-sided exponential form-norm bounds for `twoTimeFormEvolution s t u`. -/
theorem twoTimeFormEvolution_two_sided_norm_sq_bounds (s t : ℝ) (u : VT s) :
    Real.exp (-2 * |t - s|) * ‖u‖ ^ 2 ≤
      ‖twoTimeFormEvolution ε hε h hh hb m g k s t u‖ ^ 2 ∧
    ‖twoTimeFormEvolution ε hε h hh hb m g k s t u‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * ‖u‖ ^ 2 := by
  refine ⟨?_, twoTimeFormLinearMap_norm_sq_le ε hε h hh hb m g k s t u⟩
  have hrev :
      ‖u‖ ^ 2 ≤
        Real.exp (2 * |s - t|) *
          ‖twoTimeFormEvolution ε hε h hh hb m g k s t u‖ ^ 2 :=
    (congrArg (fun v : VT s => ‖v‖ ^ 2)
      (twoTimeFormEvolution_reverse ε hε h hh hb m g k s t u).symm).trans_le
      (twoTimeFormLinearMap_norm_sq_le ε hε h hh hb m g k t s
        (twoTimeFormEvolution ε hε h hh hb m g k s t u))
  exact unscale_reverse_exp_abs hrev

/-! ### 2. Exact Two-Time Form-Domain Invariance and Operator Form-Energy Regularity -/

/-- Canonical lift of a vector `f ∈ (Eavg s).domain` to the reference form space `RV = VT 0`. -/
def referenceGraphLift (s : ℝ) (f : Hilbert) (hf : f ∈ (Eavg s).domain) : RV :=
  FT s 0 (KFCausalClosedGraphForm.graphVector (AD s) ⟨f, hf⟩)

theorem referenceGraphLift_embedding (s : ℝ) (f : Hilbert) (hf : f ∈ (Eavg s).domain) :
    RJ (referenceGraphLift ε hε h hh hb m g k s f hf) = f :=
  transfer_embedding ε hε h hh hw m g k s 0
    (KFCausalClosedGraphForm.graphVector (AD s) ⟨f, hf⟩)

theorem referenceGraphLift_timeEnergy (s : ℝ) (f : Hilbert) (hf : f ∈ (Eavg s).domain) :
    E s (referenceGraphLift ε hε h hh hb m g k s f hf) =
      ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
  (transfer_to_zero_energy_eq ε hε h hh hb m g k s
    (KFCausalClosedGraphForm.graphVector (AD s) ⟨f, hf⟩)).2

theorem evolved_eq_referenceGraphLift (s t : ℝ) (f : Hilbert) (hf : f ∈ (Eavg s).domain) :
    U s t f = U s t (RJ (referenceGraphLift ε hε h hh hb m g k s f hf)) :=
  congrArg (U s t) (referenceGraphLift_embedding ε hε h hh hb m g k s f hf).symm

/-- If `f ∈ (Eavg s).domain`, then the evolved state `U s t f` lies in `(Eavg r).domain`
for every target time `t` and observation time `r`. -/
theorem mem_averaged_domain_of_evolved
    (s t r : ℝ) {f : Hilbert} (hf : f ∈ (Eavg s).domain) :
    U s t f ∈ (Eavg r).domain :=
  prop_of_eq (fun x : Hilbert => x ∈ (Eavg r).domain)
    (evolved_eq_referenceGraphLift ε hε h hh hb m g k s t f hf).symm
    (evolved_mem_averaged_domain ε hε h hh hb m g k s t r
      (referenceGraphLift ε hε h hh hb m g k s f hf))

/-- Exact two-time form-domain invariance: for all real couplings `m, g, k` and all
times `s, t, r : ℝ`, `U s t f ∈ (Eavg r).domain` if and only if `f ∈ (Eavg s).domain`. -/
theorem evolved_mem_averaged_domain_iff
    (s t r : ℝ) (f : Hilbert) :
    U s t f ∈ (Eavg r).domain ↔ f ∈ (Eavg s).domain := by
  constructor
  · intro hU
    have hUt : U s t f ∈ (Eavg t).domain :=
      (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_time_eq
        ε hε h hh hb m g k r t (U s t f)).mp hU
    have hback : U t s (U s t f) ∈ (Eavg s).domain :=
      mem_averaged_domain_of_evolved ε hε h hh hb m g k t s s hUt
    have hrev : U t s (U s t f) = f :=
      congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f)
        (KFCausalClockFloorAveragedEvolution.evolution_reverse ε hε h hh hw m g k s t)
    exact prop_of_eq (fun x : Hilbert => x ∈ (Eavg s).domain) hrev hback
  · exact mem_averaged_domain_of_evolved ε hε h hh hb m g k s t r

/-- If `f ∈ (Eavg s).domain`, then `U s t f` lies in all five component form domains
`Tstat`, `Kroot`, `Tpot`, `Tgrow`, `Tres r`, as well as in `(clockHalf ε).domain`. -/
theorem mem_all_form_domains_of_evolved
    (s t r : ℝ) {f : Hilbert} (hf : f ∈ (Eavg s).domain) :
    U s t f ∈ (Eavg r).domain ∧
    U s t f ∈ (Tstat).domain ∧
    U s t f ∈ (Kroot).domain ∧
    U s t f ∈ (Tpot).domain ∧
    U s t f ∈ (Tgrow).domain ∧
    U s t f ∈ (Tres r).domain ∧
    U s t f ∈ (clockHalf ε).domain := by
  let w := referenceGraphLift ε hε h hh hb m g k s f hf
  have heq := (evolved_eq_referenceGraphLift ε hε h hh hb m g k s t f hf).symm
  have hE : U s t f ∈ (Eavg r).domain :=
    mem_averaged_domain_of_evolved ε hε h hh hb m g k s t r hf
  have hstat : U s t f ∈ (Tstat).domain :=
    prop_of_eq (fun x : Hilbert => x ∈ (Tstat).domain) heq
      (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t w)
  have hrad : U s t f ∈ (Kroot).domain :=
    prop_of_eq (fun x : Hilbert => x ∈ (Kroot).domain) heq
      (evolved_mem_radialRoot_domain ε hε h hh hb m g k s t w)
  have hpot : U s t f ∈ (Tpot).domain :=
    prop_of_eq (fun x : Hilbert => x ∈ (Tpot).domain) heq
      (evolved_mem_potentialForm_domain ε hε h hh hb m g k s t w)
  have hgrow : U s t f ∈ (Tgrow).domain :=
    prop_of_eq (fun x : Hilbert => x ∈ (Tgrow).domain) heq
      (evolved_mem_growingForm_domain ε hε h hh hb m g k s t w)
  have hres : U s t f ∈ (Tres r).domain :=
    prop_of_eq (fun x : Hilbert => x ∈ (Tres r).domain) heq
      (evolved_mem_residualForm_domain ε hε h hh hb m g k s t r w)
  exact ⟨hE, hstat, hrad, hpot, hgrow, hres,
    static_root_subset_clockHalf_domain ε hε h (U s t f) hstat⟩

/-- For `f ∈ (Eavg s).domain`, the instantaneous form energy of `referenceGraphLift s f hf`
at observation time `r` equals `‖Eavg r ⟨U s t f, ...⟩‖ ^ 2`. -/
theorem instantFormEnergy_referenceGraphLift_eq
    (s t r : ℝ) {f : Hilbert} (hf : f ∈ (Eavg s).domain) :
    instantFormEnergy ε hε h hh hb m g k s t r
        (referenceGraphLift ε hε h hh hb m g k s f hf) =
      ‖Eavg r ⟨U s t f, mem_averaged_domain_of_evolved ε hε h hh hb m g k s t r hf⟩‖ ^ 2 := by
  let w := referenceGraphLift ε hε h hh hb m g k s f hf
  have hJ : AJ r (evolvedForm ε hε h hh hb m g k s t r w) = U s t f :=
    (evolvedForm_embedding ε hε h hh hb m g k s t r w).trans
      (evolved_eq_referenceGraphLift ε hε h hh hb m g k s t f hf).symm
  have hout :=
    form_output_eq_operator (AD r) (evolvedForm ε hε h hh hb m g k s t r w)
      (U s t f) hJ (mem_averaged_domain_of_evolved ε hε h hh hb m g k s t r hf)
  exact (instantFormEnergy_eq_output_norm_sq ε hε h hh hb m g k s t r w).trans
    (congrArg (fun y : EnergyOutputSpace => ‖y‖ ^ 2) hout)

/-- Exact multi-channel energy decompositions of `‖Eavg r ⟨U s t f, ...⟩‖ ^ 2` for any
initial vector `f ∈ (Eavg s).domain`. -/
theorem evolved_operator_form_energy_decompositions
    (s t r : ℝ) {f : Hilbert} (hf : f ∈ (Eavg s).domain) :
    let hdom := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t r hf
    ‖Eavg r ⟨U s t f, hdom.1⟩‖ ^ 2 =
      ‖Tstat ⟨U s t f, hdom.2.1⟩‖ ^ 2 +
        Real.exp (2 * r) * ‖Tgrow ⟨U s t f, hdom.2.2.2.2.1⟩‖ ^ 2 ∧
    ‖Eavg r ⟨U s t f, hdom.1⟩‖ ^ 2 =
      ‖Tstat ⟨U s t f, hdom.2.1⟩‖ ^ 2 +
        Real.exp (2 * r) * ‖Kroot ⟨U s t f, hdom.2.2.1⟩‖ ^ 2 +
        Real.exp (2 * r) * ‖Tpot ⟨U s t f, hdom.2.2.2.1⟩‖ ^ 2 ∧
    ‖Eavg r ⟨U s t f, hdom.1⟩‖ ^ 2 =
      Real.exp (2 * r) * ‖Kroot ⟨U s t f, hdom.2.2.1⟩‖ ^ 2 +
        ‖Tres r ⟨U s t f, hdom.2.2.2.2.2.1⟩‖ ^ 2 ∧
    ‖Tgrow ⟨U s t f, hdom.2.2.2.2.1⟩‖ ^ 2 =
      ‖Kroot ⟨U s t f, hdom.2.2.1⟩‖ ^ 2 + ‖Tpot ⟨U s t f, hdom.2.2.2.1⟩‖ ^ 2 ∧
    ‖Tres r ⟨U s t f, hdom.2.2.2.2.2.1⟩‖ ^ 2 =
      ‖Tstat ⟨U s t f, hdom.2.1⟩‖ ^ 2 +
        Real.exp (2 * r) * ‖Tpot ⟨U s t f, hdom.2.2.2.1⟩‖ ^ 2 := by
  intro hdom
  let w := referenceGraphLift ε hε h hh hb m g k s f hf
  have heq := (evolved_eq_referenceGraphLift ε hε h hh hb m g k s t f hf).symm
  have hE := (instantFormEnergy_referenceGraphLift_eq ε hε h hh hb m g k s t r hf).symm
  have hstat := operator_norm_sq_congr Tstat heq
    (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t w) hdom.2.1
  have hrad := operator_norm_sq_congr Kroot heq
    (evolved_mem_radialRoot_domain ε hε h hh hb m g k s t w) hdom.2.2.1
  have hpot := operator_norm_sq_congr Tpot heq
    (evolved_mem_potentialForm_domain ε hε h hh hb m g k s t w) hdom.2.2.2.1
  have hgrow := operator_norm_sq_congr Tgrow heq
    (evolved_mem_growingForm_domain ε hε h hh hb m g k s t w) hdom.2.2.2.2.1
  have hres := operator_norm_sq_congr (Tres r) heq
    (evolved_mem_residualForm_domain ε hε h hh hb m g k s t r w) hdom.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hE.trans
      ((evolved_instantFormEnergy_eq_static_add_growing ε hε h hh hb m g k s t r w).trans
        (congrArg₂ (· + ·) hstat (congrArg (Real.exp (2 * r) * ·) hgrow)))
  · exact hE.trans
      ((evolved_instantFormEnergy_eq_three_channel ε hε h hh hb m g k s t r w).trans
        (congrArg₂ (· + ·)
          (congrArg₂ (· + ·) hstat (congrArg (Real.exp (2 * r) * ·) hrad))
          (congrArg (Real.exp (2 * r) * ·) hpot)))
  · exact hE.trans
      ((evolved_instantFormEnergy_eq_radial_add_residual ε hε h hh hb m g k s t r w).trans
        (congrArg₂ (· + ·) (congrArg (Real.exp (2 * r) * ·) hrad) hres))
  · exact hgrow.symm.trans
      ((evolved_growing_norm_sq_split ε hε h hh hb m g k s t w).trans
        (congrArg₂ (· + ·) hrad hpot))
  · exact hres.symm.trans
      ((evolved_residual_norm_sq_split ε hε h hh hb m g k s t r w).trans
        (congrArg₂ (· + ·) hstat (congrArg (Real.exp (2 * r) * ·) hpot)))

/-- Two-sided exponential bounds on the evolved operator form energy
`‖Eavg t ⟨U s t f, ...⟩‖ ^ 2` and observation-time bounds at arbitrary `r : ℝ`. -/
theorem evolved_operator_form_energy_bounds
    (s t r : ℝ) {f : Hilbert} (hf : f ∈ (Eavg s).domain) :
    Real.exp (-2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 ≤
      ‖Eavg t ⟨U s t f, mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hf⟩‖ ^ 2 ∧
    ‖Eavg t ⟨U s t f, mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hf⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 ∧
    ‖Eavg r ⟨U s t f, mem_averaged_domain_of_evolved ε hε h hh hb m g k s t r hf⟩‖ ^ 2 ≤
      max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 ∧
    ‖Eavg r ⟨U s t f, mem_averaged_domain_of_evolved ε hε h hh hb m g k s t r hf⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - r| + |t - s|)) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 := by
  let w := referenceGraphLift ε hε h hh hb m g k s f hf
  have hEs := referenceGraphLift_timeEnergy ε hε h hh hb m g k s f hf
  have hEt := instantFormEnergy_referenceGraphLift_eq ε hε h hh hb m g k s t t hf
  have hEr := instantFormEnergy_referenceGraphLift_eq ε hε h hh hb m g k s t r hf
  have hup_t :
      ‖Eavg t ⟨U s t f, mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hf⟩‖ ^ 2 ≤
        Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    hEt.symm.trans_le
      ((evolved_dynamical_energy_le ε hε h hh hb m g k s t w).trans_eq
        (congrArg (Real.exp (2 * |t - s|) * ·) hEs))
  have hup_r :
      ‖Eavg r ⟨U s t f, mem_averaged_domain_of_evolved ε hε h hh hb m g k s t r hf⟩‖ ^ 2 ≤
        max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    hEr.symm.trans_le
      ((evolved_instantFormEnergy_le_max_initial ε hε h hh hb m g k s t r w).trans_eq
        (congrArg (max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ·) hEs))
  have hdist_r :
      ‖Eavg r ⟨U s t f, mem_averaged_domain_of_evolved ε hε h hh hb m g k s t r hf⟩‖ ^ 2 ≤
        Real.exp (2 * (|t - r| + |t - s|)) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    hEr.symm.trans_le
      ((evolved_instantFormEnergy_le_exp_distance ε hε h hh hb m g k s t r w).trans_eq
        (congrArg (Real.exp (2 * (|t - r| + |t - s|)) * ·) hEs))
  refine ⟨?_, hup_t, hup_r, hdist_r⟩
  let hUt : U s t f ∈ (Eavg t).domain :=
    mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hf
  let wt := referenceGraphLift ε hε h hh hb m g k t (U s t f) hUt
  have hEt_wt := referenceGraphLift_timeEnergy ε hε h hh hb m g k t (U s t f) hUt
  have hEs_wt := instantFormEnergy_referenceGraphLift_eq ε hε h hh hb m g k t s s hUt
  have hrev_eq : U t s (U s t f) = f :=
    congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f)
      (KFCausalClockFloorAveragedEvolution.evolution_reverse ε hε h hh hw m g k s t)
  have hnorm_rev :
      ‖Eavg s ⟨U t s (U s t f),
          mem_averaged_domain_of_evolved ε hε h hh hb m g k t s s hUt⟩‖ ^ 2 =
        ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    operator_norm_sq_congr (Eavg s) hrev_eq
      (mem_averaged_domain_of_evolved ε hε h hh hb m g k t s s hUt) hf
  have hrev_bound :
      ‖Eavg s ⟨f, hf⟩‖ ^ 2 ≤
        Real.exp (2 * |s - t|) * ‖Eavg t ⟨U s t f, hUt⟩‖ ^ 2 :=
    (hEs_wt.trans hnorm_rev).symm.trans_le
      ((evolved_dynamical_energy_le ε hε h hh hb m g k t s wt).trans_eq
        (congrArg (Real.exp (2 * |s - t|) * ·) hEt_wt))
  exact unscale_reverse_exp_abs hrev_bound

/-- Component-wise form-energy bounds along `U s t f` for any `f ∈ (Eavg s).domain`,
controlling `Tstat`, `clockHalf ε`, `Tgrow`, `Kroot`, `Tpot`, and `Tres r` in terms of
the initial form energy `‖Eavg s ⟨f, hf⟩‖ ^ 2`. -/
theorem evolved_component_form_energy_bounds
    (s t r : ℝ) {f : Hilbert} (hf : f ∈ (Eavg s).domain) :
    let hdom := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t r hf
    ‖Tstat ⟨U s t f, hdom.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 ∧
    ‖clockHalf ε ⟨U s t f, hdom.2.2.2.2.2.2⟩‖ ^ 2 ≤
      2 * (Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2) ∧
    Real.exp (2 * t) * ‖Tgrow ⟨U s t f, hdom.2.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 ∧
    ‖Tgrow ⟨U s t f, hdom.2.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 ∧
    Real.exp (2 * t) * ‖Kroot ⟨U s t f, hdom.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 ∧
    ‖Kroot ⟨U s t f, hdom.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 ∧
    Real.exp (2 * t) * ‖Tpot ⟨U s t f, hdom.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 ∧
    ‖Tpot ⟨U s t f, hdom.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 ∧
    ‖Tres r ⟨U s t f, hdom.2.2.2.2.2.1⟩‖ ^ 2 ≤
      max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 := by
  intro hdom
  let w := referenceGraphLift ε hε h hh hb m g k s f hf
  have heq := (evolved_eq_referenceGraphLift ε hε h hh hb m g k s t f hf).symm
  have hEs := referenceGraphLift_timeEnergy ε hε h hh hb m g k s f hf
  have hstat_eq := operator_norm_sq_congr Tstat heq
    (evolved_mem_staticRoot_domain ε hε h hh hb m g k s t w) hdom.2.1
  have hrad_eq := operator_norm_sq_congr Kroot heq
    (evolved_mem_radialRoot_domain ε hε h hh hb m g k s t w) hdom.2.2.1
  have hpot_eq := operator_norm_sq_congr Tpot heq
    (evolved_mem_potentialForm_domain ε hε h hh hb m g k s t w) hdom.2.2.2.1
  have hgrow_eq := operator_norm_sq_congr Tgrow heq
    (evolved_mem_growingForm_domain ε hε h hh hb m g k s t w) hdom.2.2.2.2.1
  have hres_eq := operator_norm_sq_congr (Tres r) heq
    (evolved_mem_residualForm_domain ε hε h hh hb m g k s t r w) hdom.2.2.2.2.2.1
  have hstat :
      ‖Tstat ⟨U s t f, hdom.2.1⟩‖ ^ 2 ≤ Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    hstat_eq.symm.trans_le
      ((evolved_staticRoot_norm_sq_le ε hε h hh hb m g k s t w).trans_eq
        (congrArg (Real.exp (2 * |t - s|) * ·) hEs))
  have hclock :
      ‖clockHalf ε ⟨U s t f, hdom.2.2.2.2.2.2⟩‖ ^ 2 ≤
        2 * (Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2) :=
    (static_root_clockHalf_norm_sq_le ε hε h (U s t f) hdom.2.1).trans
      (mul_le_mul_of_nonneg_left hstat (by norm_num))
  have hgrow_w :
      Real.exp (2 * t) * ‖Tgrow ⟨U s t f, hdom.2.2.2.2.1⟩‖ ^ 2 ≤
        Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    (congrArg (Real.exp (2 * t) * ·) hgrow_eq.symm).trans_le
      ((evolved_weighted_growingForm_norm_sq_le ε hε h hh hb m g k s t w).trans_eq
        (congrArg (Real.exp (2 * |t - s|) * ·) hEs))
  have hgrow :
      ‖Tgrow ⟨U s t f, hdom.2.2.2.2.1⟩‖ ^ 2 ≤
        Real.exp (2 * (|t - s| - t)) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    hgrow_eq.symm.trans_le
      ((evolved_growingForm_norm_sq_le ε hε h hh hb m g k s t w).trans_eq
        (congrArg (Real.exp (2 * (|t - s| - t)) * ·) hEs))
  have hrad_w :
      Real.exp (2 * t) * ‖Kroot ⟨U s t f, hdom.2.2.1⟩‖ ^ 2 ≤
        Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    (congrArg (Real.exp (2 * t) * ·) hrad_eq.symm).trans_le
      ((evolved_weighted_radialRoot_norm_sq_le ε hε h hh hb m g k s t w).trans_eq
        (congrArg (Real.exp (2 * |t - s|) * ·) hEs))
  have hrad :
      ‖Kroot ⟨U s t f, hdom.2.2.1⟩‖ ^ 2 ≤
        Real.exp (2 * (|t - s| - t)) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    hrad_eq.symm.trans_le
      ((evolved_radialRoot_norm_sq_le ε hε h hh hb m g k s t w).trans_eq
        (congrArg (Real.exp (2 * (|t - s| - t)) * ·) hEs))
  have hpot_w :
      Real.exp (2 * t) * ‖Tpot ⟨U s t f, hdom.2.2.2.1⟩‖ ^ 2 ≤
        Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    (congrArg (Real.exp (2 * t) * ·) hpot_eq.symm).trans_le
      ((evolved_weighted_potentialForm_norm_sq_le ε hε h hh hb m g k s t w).trans_eq
        (congrArg (Real.exp (2 * |t - s|) * ·) hEs))
  have hpot :
      ‖Tpot ⟨U s t f, hdom.2.2.2.1⟩‖ ^ 2 ≤
        Real.exp (2 * (|t - s| - t)) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    hpot_eq.symm.trans_le
      ((evolved_potentialForm_norm_sq_le ε hε h hh hb m g k s t w).trans_eq
        (congrArg (Real.exp (2 * (|t - s| - t)) * ·) hEs))
  have hres :
      ‖Tres r ⟨U s t f, hdom.2.2.2.2.2.1⟩‖ ^ 2 ≤
        max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ‖Eavg s ⟨f, hf⟩‖ ^ 2 :=
    hres_eq.symm.trans_le
      ((evolved_residualForm_norm_sq_le_max_initial ε hε h hh hb m g k s t r w).trans_eq
        (congrArg (max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ·) hEs))
  exact ⟨hstat, hclock, hgrow_w, hgrow, hrad_w, hrad, hpot_w, hpot, hres⟩

/-- Under positive vacuum `0 < k`, `U s t f` lies in `(Tstat).domain ⊓ (Kroot).domain ⊓ (Tpot).domain`
if and only if `f` lies in `(Tstat).domain ⊓ (Kroot).domain ⊓ (Tpot).domain`. -/
theorem positive_vacuum_evolved_mem_three_form_domain_iff
    (hk : 0 < k) (s t : ℝ) (f : Hilbert) :
    U s t f ∈ (Tstat).domain ⊓ (Kroot).domain ⊓ (Tpot).domain ↔
      f ∈ (Tstat).domain ⊓ (Kroot).domain ⊓ (Tpot).domain := by
  have h1 :
      U s t f ∈ (Tstat).domain ⊓ (Kroot).domain ⊓ (Tpot).domain ↔
        U s t f ∈ (Eavg t).domain :=
    (positive_vacuum_averaged_form_domain_iff ε hε h hh hb m g k hk t (U s t f)).symm
  have h2 :
      f ∈ (Tstat).domain ⊓ (Kroot).domain ⊓ (Tpot).domain ↔
        f ∈ (Eavg s).domain :=
    (positive_vacuum_averaged_form_domain_iff ε hε h hh hb m g k hk s f).symm
  exact h1.trans
    ((evolved_mem_averaged_domain_iff ε hε h hh hb m g k s t t f).trans h2.symm)

#print axioms transfer_to_zero_energy_eq
#print axioms twoTimeFormLinearMap_apply
#print axioms twoTimeFormLinearMap_norm_sq_eq
#print axioms twoTimeFormLinearMap_norm_sq_le_split
#print axioms twoTimeFormLinearMap_norm_sq_le
#print axioms twoTimeFormLinearMap_norm_le
#print axioms twoTimeFormEvolution_apply
#print axioms twoTimeFormEvolution_eq_evolvedForm
#print axioms twoTimeFormEvolution_embedding
#print axioms twoTimeFormEvolution_self
#print axioms twoTimeFormEvolution_comp
#print axioms twoTimeFormEvolution_reverse
#print axioms twoTimeFormEvolutionEquiv_apply
#print axioms twoTimeFormEvolutionEquiv_symm_apply
#print axioms twoTimeFormEvolutionEquiv_embedding
#print axioms twoTimeFormEvolution_two_sided_norm_sq_bounds
#print axioms referenceGraphLift_embedding
#print axioms referenceGraphLift_timeEnergy
#print axioms evolved_eq_referenceGraphLift
#print axioms mem_averaged_domain_of_evolved
#print axioms evolved_mem_averaged_domain_iff
#print axioms mem_all_form_domains_of_evolved
#print axioms instantFormEnergy_referenceGraphLift_eq
#print axioms evolved_operator_form_energy_decompositions
#print axioms evolved_operator_form_energy_bounds
#print axioms evolved_component_form_energy_bounds
#print axioms positive_vacuum_evolved_mem_three_form_domain_iff

end

end UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormEvolutionIsomorphism
