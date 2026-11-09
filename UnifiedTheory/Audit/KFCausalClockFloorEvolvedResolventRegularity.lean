/- Multi-domain form regularity, five-channel energy bounds, and two-time
Lipschitz and continuity estimates for compositions of the nonautonomous
quantum evolution U(s, t) with the time-dependent Hamiltonian and residual
resolvents RH(r, a) and RS(r, a). -/
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormEvolutionIsomorphism
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorEvolvedResolventRegularity

noncomputable section

open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorAveragedEvolution
  (evolution evolution_norm evolution_inner evolution_reverse)
open KFCausalClockFloorTwoTimeFormEvolutionIsomorphism
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
open KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity
open KFCausalClockFloorHamiltonianResolventFormBounds
open KFCausalClockFloorHamiltonianComponentResolventBounds

private theorem left_of_add_le {x y z : ℝ} (h : x + y ≤ z) (hy : 0 ≤ y) : x ≤ z := by
  linarith

private theorem form_output_eq_operator
    (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (w : KFCausalClosedGraphForm.FormSpace D) (f : Hilbert)
    (hJ : KFCausalClosedGraphForm.embedding D w = f) (hf : f ∈ D.operator.domain) :
    KFCausalClosedGraphForm.energyOutput D w = D.operator ⟨f, hf⟩ :=
  D.operator.mem_graph_snd_inj' w.property (D.operator.mem_graph ⟨f, hf⟩) hJ

private theorem tendsto_zero_of_sq_le_abs_exp_sq_mul {X : Type*}
    [NormedAddCommGroup X] {V : ℝ → X} (t C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ s, ‖V s‖ ^ 2 ≤ |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 * C) :
    Tendsto V (𝓝 t) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim :
      Tendsto (fun s : ℝ => |Real.exp (2 * t) - Real.exp (2 * s)| * Real.sqrt C)
        (𝓝 t) (𝓝 0) := by
    simpa only [zero_mul] using (two_time_exp_diff_tendsto_zero t).mul_const (Real.sqrt C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun s => norm_nonneg (V s)) (fun s => ?_)
  have h1 := Real.sqrt_le_sqrt (hb s)
  have hrew :
      |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 * C =
        (|Real.exp (2 * t) - Real.exp (2 * s)| * Real.sqrt C) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
  have hnonneg : 0 ≤ |Real.exp (2 * t) - Real.exp (2 * s)| * Real.sqrt C :=
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg C)
  rw [hrew, Real.sqrt_sq (norm_nonneg (V s)), Real.sqrt_sq hnonneg] at h1
  exact h1

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "AD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k
local notation "U" => evolution ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (hamiltonian_bound ε h hw) hh m g k
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k

/-! ### 1. Averaged Form-Energy Bound for the Time-Dependent Hamiltonian Resolvent -/

/-- For any `x ∈ (H t).domain`, the quadratic form `(inner ℂ (H t x) x).re` equals
the squared averaged form-operator norm `‖Eavg t ⟨x, ...⟩‖ ^ 2`. -/
theorem hamiltonian_form_energy_eq_averaged_norm_sq (t : ℝ) (x : (H t).domain) :
    (inner ℂ (H t x) (x : Hilbert)).re =
      ‖Eavg t ⟨(x : Hilbert),
        KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_averaged_domain
          ε hε h hh hb m g k t x⟩‖ ^ 2 := by
  have he := KFCausalClosedGraphForm.hamiltonian_energy (AD t) x
  have hout :=
    form_output_eq_operator (AD t) (KFCausalClosedGraphForm.formLift (AD t) x) (x : Hilbert)
      (KFCausalClosedGraphForm.embedding_formLift (AD t) x)
      (KFCausalClockFloorUnconditionalOperatorFormEnergy.hamiltonian_mem_averaged_domain
        ε hε h hh hb m g k t x)
  exact he.trans (congrArg (fun y : EnergyOutputSpace => ‖y‖ ^ 2) hout)

/-- Unconditional averaged form-energy bound for the Hamiltonian resolvent `RH t a f`:
`‖Eavg t ⟨RH t a f, ...⟩‖ ^ 2 + a * ‖RH t a f‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2`, and in particular
`‖Eavg t ⟨RH t a f, ...⟩‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2`. -/
theorem hamiltonian_resolvent_averaged_energy_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    let hE : RH t a f ∈ (Eavg t).domain :=
      (two_time_resolvent_all_domains ε hε h hh hb m g k t t a ha f).2.2.2.1
    ‖Eavg t ⟨RH t a f, hE⟩‖ ^ 2 + a * ‖RH t a f‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 ∧
    ‖Eavg t ⟨RH t a f, hE⟩‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 := by
  intro hE
  have hp := hamiltonian_resolvent_pairing_le ε hε h hh hb m g k t a ha f
  have he :=
    hamiltonian_form_energy_eq_averaged_norm_sq ε hε h hh hb m g k t
      (hamiltonianResolventPoint ε hε h hh hb m g k t a ha f)
  have h1 : ‖Eavg t ⟨RH t a f, hE⟩‖ ^ 2 + a * ‖RH t a f‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 :=
    (congrArg (· + a * ‖RH t a f‖ ^ 2) he).symm.trans_le hp
  exact ⟨h1, left_of_add_le h1 (mul_nonneg ha.le (sq_nonneg _))⟩

/-! ### 2. Resolvent Regularity of Evolved States `RH r a (U s t f)` and `RS r a (U s t f)` -/

/-- Applying the Hamiltonian resolvent `RH r a` (`0 < a`) to any evolved state `U s t f`
places `RH r a (U s t f)` in all ten operator and form domains, with Hilbert, Hamiltonian,
averaged form, static-root, radial-root, potential-form, and half-clock bounds uniform
in the evolution times `(s, t)`. -/
theorem resolvent_of_evolved_state_regularity
    (s t r q a : ℝ) (ha : 0 < a) (f : Hilbert) :
    let w := U s t f
    let hdom := two_time_resolvent_all_domains ε hε h hh hb m g k r q a ha w
    let hEr := (two_time_resolvent_all_domains ε hε h hh hb m g k r r a ha w).2.2.2.1
    (RH r a w ∈ (H r).domain ∧
     RH r a w ∈ (K).domain ∧
     RH r a w ∈ (S r).domain ∧
     RH r a w ∈ (Eavg q).domain ∧
     RH r a w ∈ (Tres q).domain ∧
     RH r a w ∈ (Tstat).domain ∧
     RH r a w ∈ (Kroot).domain ∧
     RH r a w ∈ (Tpot).domain ∧
     RH r a w ∈ (Tgrow).domain ∧
     RH r a w ∈ (clockHalf ε).domain) ∧
    ‖RH r a w‖ ≤ a⁻¹ * ‖f‖ ∧
    ‖H r ⟨RH r a w, hdom.1⟩‖ ≤ ‖f‖ ∧
    ‖Eavg r ⟨RH r a w, hEr⟩‖ ^ 2 + a * ‖RH r a w‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 ∧
    ‖Tstat ⟨RH r a w,
      hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k r a ha w⟩‖ ^ 2 +
      Real.exp (2 * r) *
        ‖Kroot ⟨RH r a w,
          hamiltonian_resolvent_mem_radialRoot_domain ε hε h hh hb m g k r a ha w⟩‖ ^ 2 +
      Real.exp (2 * r) *
        ‖Tpot ⟨RH r a w,
          hamiltonian_resolvent_mem_potentialForm_domain ε hε h hh hb m g k r a ha w⟩‖ ^ 2 +
      a * ‖RH r a w‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 ∧
    ‖clockHalf ε ⟨RH r a w,
      resolvent_in_clockHalf_domain ε hε h hh hb m g k r a ha w⟩‖ ^ 2 ≤
      2 * a⁻¹ * ‖f‖ ^ 2 ∧
    ‖clockHalf ε ⟨RS r a w,
      residual_resolvent_in_clockHalf_domain ε hε h hh hb m g k r a ha w⟩‖ ^ 2 ≤
      2 * a⁻¹ * ‖f‖ ^ 2 := by
  intro w hdom hEr
  have hnorm : ‖w‖ = ‖f‖ := evolution_norm ε hε h hh hw m g k s t f
  have hR_norm : ‖RH r a w‖ ≤ a⁻¹ * ‖f‖ :=
    (resolvent_norm_le ε hε h hh hb m g k r a ha w).trans_eq
      (congrArg (a⁻¹ * ·) hnorm)
  have hH_norm : ‖H r ⟨RH r a w, hdom.1⟩‖ ≤ ‖f‖ :=
    (resolvent_hamiltonian_norm_le ε hε h hh hb m g k r a ha w).trans_eq hnorm
  have hE_bound : ‖Eavg r ⟨RH r a w, hEr⟩‖ ^ 2 + a * ‖RH r a w‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 :=
    (hamiltonian_resolvent_averaged_energy_le ε hε h hh hb m g k r a ha w).1.trans_eq
      (congrArg (fun u : ℝ => a⁻¹ * u ^ 2) hnorm)
  have h3_bound :
      ‖Tstat ⟨RH r a w,
        hamiltonian_resolvent_mem_staticRoot_domain ε hε h hh hb m g k r a ha w⟩‖ ^ 2 +
        Real.exp (2 * r) *
          ‖Kroot ⟨RH r a w,
            hamiltonian_resolvent_mem_radialRoot_domain ε hε h hh hb m g k r a ha w⟩‖ ^ 2 +
        Real.exp (2 * r) *
          ‖Tpot ⟨RH r a w,
            hamiltonian_resolvent_mem_potentialForm_domain ε hε h hh hb m g k r a ha w⟩‖ ^ 2 +
        a * ‖RH r a w‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 :=
    (hamiltonian_resolvent_three_channel_energy_le ε hε h hh hb m g k r a ha w).trans_eq
      (congrArg (fun u : ℝ => a⁻¹ * u ^ 2) hnorm)
  have hcH :
      ‖clockHalf ε ⟨RH r a w,
        resolvent_in_clockHalf_domain ε hε h hh hb m g k r a ha w⟩‖ ^ 2 ≤
        2 * a⁻¹ * ‖f‖ ^ 2 :=
    (resolvent_clockHalf_norm_sq_bound ε hε h hh hb m g k r a ha w).trans_eq
      (congrArg (fun u : ℝ => 2 * a⁻¹ * u ^ 2) hnorm)
  have hcS :
      ‖clockHalf ε ⟨RS r a w,
        residual_resolvent_in_clockHalf_domain ε hε h hh hb m g k r a ha w⟩‖ ^ 2 ≤
        2 * a⁻¹ * ‖f‖ ^ 2 :=
    (residual_resolvent_clockHalf_norm_sq_bound ε hε h hh hb m g k r a ha w).trans_eq
      (congrArg (fun u : ℝ => 2 * a⁻¹ * u ^ 2) hnorm)
  exact ⟨hdom, hR_norm, hH_norm, hE_bound, h3_bound, hcH, hcS⟩

/-! ### 3. Evolved Resolvent States `U s t (RH s a f)` — Multi-Domain Regularity and Bounds -/

/-- Evolving a resolvent vector `RH s a f` (`0 < a`) by `U s t` produces a vector in
`(Eavg q).domain`, `(Tstat).domain`, `(Kroot).domain`, `(Tpot).domain`, `(Tgrow).domain`,
`(Tres q).domain`, and `(clockHalf ε).domain` for every target time `t` and observation
time `q`, with exact five-channel energy decompositions and explicit bounds in terms of
`a⁻¹ * ‖f‖ ^ 2`. -/
theorem evolved_resolvent_multi_domain_energy_bounds
    (s t q a : ℝ) (ha : 0 < a) (f : Hilbert) :
    let hEs : RH s a f ∈ (Eavg s).domain :=
      (two_time_resolvent_all_domains ε hε h hh hb m g k s s a ha f).2.2.2.1
    let hdom := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t q hEs
    let hEt := mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hEs
    (U s t (RH s a f) ∈ (Eavg q).domain ∧
     U s t (RH s a f) ∈ (Tstat).domain ∧
     U s t (RH s a f) ∈ (Kroot).domain ∧
     U s t (RH s a f) ∈ (Tpot).domain ∧
     U s t (RH s a f) ∈ (Tgrow).domain ∧
     U s t (RH s a f) ∈ (Tres q).domain ∧
     U s t (RH s a f) ∈ (clockHalf ε).domain) ∧
    ‖U s t (RH s a f)‖ ≤ a⁻¹ * ‖f‖ ∧
    ‖Eavg t ⟨U s t (RH s a f), hEt⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * (a⁻¹ * ‖f‖ ^ 2) ∧
    ‖Eavg q ⟨U s t (RH s a f), hdom.1⟩‖ ^ 2 ≤
      max 1 (Real.exp (2 * (q - t))) * Real.exp (2 * |t - s|) * (a⁻¹ * ‖f‖ ^ 2) ∧
    ‖Tstat ⟨U s t (RH s a f), hdom.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * (a⁻¹ * ‖f‖ ^ 2) ∧
    ‖clockHalf ε ⟨U s t (RH s a f), hdom.2.2.2.2.2.2⟩‖ ^ 2 ≤
      2 * (Real.exp (2 * |t - s|) * (a⁻¹ * ‖f‖ ^ 2)) ∧
    Real.exp (2 * t) * ‖Tgrow ⟨U s t (RH s a f), hdom.2.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * (a⁻¹ * ‖f‖ ^ 2) ∧
    ‖Tgrow ⟨U s t (RH s a f), hdom.2.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * (a⁻¹ * ‖f‖ ^ 2) ∧
    Real.exp (2 * t) * ‖Kroot ⟨U s t (RH s a f), hdom.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * (a⁻¹ * ‖f‖ ^ 2) ∧
    ‖Kroot ⟨U s t (RH s a f), hdom.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * (a⁻¹ * ‖f‖ ^ 2) ∧
    Real.exp (2 * t) * ‖Tpot ⟨U s t (RH s a f), hdom.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * (a⁻¹ * ‖f‖ ^ 2) ∧
    ‖Tpot ⟨U s t (RH s a f), hdom.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * (a⁻¹ * ‖f‖ ^ 2) ∧
    ‖Tres q ⟨U s t (RH s a f), hdom.2.2.2.2.2.1⟩‖ ^ 2 ≤
      max 1 (Real.exp (2 * (q - t))) * Real.exp (2 * |t - s|) * (a⁻¹ * ‖f‖ ^ 2) := by
  intro hEs hdom hEt
  have hE0 : ‖Eavg s ⟨RH s a f, hEs⟩‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 :=
    (hamiltonian_resolvent_averaged_energy_le ε hε h hh hb m g k s a ha f).2
  have hU_norm : ‖U s t (RH s a f)‖ ≤ a⁻¹ * ‖f‖ :=
    (evolution_norm ε hε h hh hw m g k s t (RH s a f)).trans_le
      (resolvent_norm_le ε hε h hh hb m g k s a ha f)
  have hEb := evolved_operator_form_energy_bounds ε hε h hh hb m g k s t q hEs
  have hcomp := evolved_component_form_energy_bounds ε hε h hh hb m g k s t q hEs
  have hexp_pos : 0 ≤ Real.exp (2 * |t - s|) := (Real.exp_pos _).le
  have hmax_pos : 0 ≤ max 1 (Real.exp (2 * (q - t))) * Real.exp (2 * |t - s|) :=
    mul_nonneg (le_trans zero_le_one (le_max_left 1 _)) hexp_pos
  have hexp_sub_pos : 0 ≤ Real.exp (2 * (|t - s| - t)) := (Real.exp_pos _).le
  refine ⟨hdom, hU_norm,
    hEb.2.1.trans (mul_le_mul_of_nonneg_left hE0 hexp_pos),
    hEb.2.2.1.trans (mul_le_mul_of_nonneg_left hE0 hmax_pos),
    hcomp.1.trans (mul_le_mul_of_nonneg_left hE0 hexp_pos),
    hcomp.2.1.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hE0 hexp_pos) (by norm_num)),
    hcomp.2.2.1.trans (mul_le_mul_of_nonneg_left hE0 hexp_pos),
    hcomp.2.2.2.1.trans (mul_le_mul_of_nonneg_left hE0 hexp_sub_pos),
    hcomp.2.2.2.2.1.trans (mul_le_mul_of_nonneg_left hE0 hexp_pos),
    hcomp.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_left hE0 hexp_sub_pos),
    hcomp.2.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_left hE0 hexp_pos),
    hcomp.2.2.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_left hE0 hexp_sub_pos),
    hcomp.2.2.2.2.2.2.2.2.trans (mul_le_mul_of_nonneg_left hE0 hmax_pos)⟩

/-! ### 4. Evolved Two-Time Resolvent Differences and Continuity (`s → t`) -/

/-- Unconditional weak Lipschitz bound for the evolved two-time resolvent difference
`U t₁ t₂ (RH s a f₂) - U t₁ t₂ (RH t a f₂)` for all `f₁, f₂ : Hilbert`. -/
theorem evolved_two_time_resolvent_weak_diff_bound
    (t₁ t₂ s t a : ℝ) (ha : 0 < a) (f₁ f₂ : Hilbert) :
    ‖inner ℂ f₁ (U t₁ t₂ (RH s a f₂) - U t₁ t₂ (RH t a f₂))‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f₁‖ * ‖f₂‖) := by
  have hsub : U t₁ t₂ (RH s a f₂) - U t₁ t₂ (RH t a f₂) =
      U t₁ t₂ (RH s a f₂ - RH t a f₂) :=
    (map_sub (U t₁ t₂) (RH s a f₂) (RH t a f₂)).symm
  have hrev : U t₁ t₂ (U t₂ t₁ f₁) = f₁ :=
    congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f₁)
      (evolution_reverse ε hε h hh hw m g k t₂ t₁)
  have hinn :
      inner ℂ f₁ (U t₁ t₂ (RH s a f₂) - U t₁ t₂ (RH t a f₂)) =
        inner ℂ (U t₂ t₁ f₁) (RH s a f₂ - RH t a f₂) :=
    (congrArg₂ (inner ℂ) hrev.symm hsub).trans
      (evolution_inner ε hε h hh hw m g k t₁ t₂ (U t₂ t₁ f₁) (RH s a f₂ - RH t a f₂))
  have hb_weak :=
    two_time_resolvent_weak_diff_bound ε hε h hh hb m g k s t a ha (U t₂ t₁ f₁) f₂
  exact (congrArg norm hinn).trans_le
    (hb_weak.trans_eq
      (congrArg
        (fun u : ℝ =>
          |Real.exp (2 * t) - Real.exp (2 * s)| *
            (2 * Real.exp (-(t + s)) * a⁻¹ * u * ‖f₂‖))
        (evolution_norm ε hε h hh hw m g k t₂ t₁ f₁)))

/-- Unconditional weak continuity `⟪f₁, U t₁ t₂ (RH s a f₂)⟫ → ⟪f₁, U t₁ t₂ (RH t a f₂)⟫`
as `s → t` for all `f₁, f₂ : Hilbert`. -/
theorem evolved_two_time_resolvent_weak_continuous
    (t₁ t₂ t a : ℝ) (ha : 0 < a) (f₁ f₂ : Hilbert) :
    Tendsto (fun s : ℝ => inner ℂ f₁ (U t₁ t₂ (RH s a f₂)))
      (𝓝 t) (𝓝 (inner ℂ f₁ (U t₁ t₂ (RH t a f₂)))) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  let B : ℝ → ℝ := fun s =>
    |Real.exp (2 * t) - Real.exp (2 * s)| *
      (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f₁‖ * ‖f₂‖)
  have hB_cont : Continuous B := by fun_prop
  have hB0 : B t = 0 := by simp [B]
  have hB_lim : Tendsto B (𝓝 t) (𝓝 0) := hB0 ▸ hB_cont.tendsto t
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_lim
    (fun _ => norm_nonneg _) (fun s => ?_)
  rw [← inner_sub_right f₁ (U t₁ t₂ (RH s a f₂)) (U t₁ t₂ (RH t a f₂))]
  exact evolved_two_time_resolvent_weak_diff_bound ε hε h hh hb m g k t₁ t₂ s t a ha f₁ f₂

/-- Under positive vacuum `0 < k`, for any `x ∈ (T).domain ⊓ (K).domain ⊓ (P).domain`,
the evolved shifted-resolvent difference
`U t t₂ x - U t t₂ (RH t a (H s x + a • x))` equals
`(e^{2t} - e^{2s}) • U t t₂ (RH t a (G x))` and satisfies explicit Lipschitz bounds
across Hilbert norm, `Eavg q`, `Tstat`, `clockHalf ε`, `Tgrow`, `Kroot`, `Tpot`, and `Tres q`. -/
theorem positive_vacuum_evolved_shifted_resolvent_difference_bounds
    (hk : 0 < k) (s t t₂ q a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hxs := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk s hxT hxK hxP).choose
    let hxG := (unconditional_two_operator_growing_eval
      ε hε h hh hb m g k hxK hxP).choose
    let d : Hilbert := U t t₂ x - U t t₂ (RH t a (H s ⟨x, hxs⟩ + a • x))
    d = ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) •
          U t t₂ (RH t a (G ⟨x, hxG⟩)) ∧
    ‖d‖ ≤ |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖G ⟨x, hxG⟩‖) ∧
    (∃ (hdE : d ∈ (Eavg q).domain) (hdS : d ∈ (Tstat).domain)
       (hdC : d ∈ (clockHalf ε).domain) (hdG : d ∈ (Tgrow).domain)
       (hdK : d ∈ (Kroot).domain) (hdP : d ∈ (Tpot).domain)
       (hdR : d ∈ (Tres q).domain),
      ‖Eavg q ⟨d, hdE⟩‖ ^ 2 ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 *
          (max 1 (Real.exp (2 * (q - t₂))) * Real.exp (2 * |t₂ - t|) *
            (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2)) ∧
      ‖Tstat ⟨d, hdS⟩‖ ^ 2 ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 *
          (Real.exp (2 * |t₂ - t|) * (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2)) ∧
      ‖clockHalf ε ⟨d, hdC⟩‖ ^ 2 ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 *
          (2 * (Real.exp (2 * |t₂ - t|) * (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2))) ∧
      ‖Tgrow ⟨d, hdG⟩‖ ^ 2 ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 *
          (Real.exp (2 * (|t₂ - t| - t₂)) * (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2)) ∧
      ‖Kroot ⟨d, hdK⟩‖ ^ 2 ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 *
          (Real.exp (2 * (|t₂ - t| - t₂)) * (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2)) ∧
      ‖Tpot ⟨d, hdP⟩‖ ^ 2 ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 *
          (Real.exp (2 * (|t₂ - t| - t₂)) * (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2)) ∧
      ‖Tres q ⟨d, hdR⟩‖ ^ 2 ≤
        |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 *
          (max 1 (Real.exp (2 * (q - t₂))) * Real.exp (2 * |t₂ - t|) *
            (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2))) := by
  intro hxs hxG d
  let hRG_E : RH t a (G ⟨x, hxG⟩) ∈ (Eavg t).domain :=
    (two_time_resolvent_all_domains ε hε h hh hb m g k t t a ha (G ⟨x, hxG⟩)).2.2.2.1
  let hURG := mem_all_form_domains_of_evolved ε hε h hh hb m g k t t₂ q hRG_E
  have hid := (positive_vacuum_two_time_shifted_resolvent_identity
    ε hε h hh hb m g k hk s t a ha hxT hxK hxP).choose_spec.choose_spec.1
  let c : ℂ := ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ)
  let u : Hilbert := U t t₂ (RH t a (G ⟨x, hxG⟩))
  have hd_eq : d = c • u :=
    (map_sub (U t t₂) x (RH t a (H s ⟨x, hxs⟩ + a • x))).symm.trans
      ((congrArg (U t t₂) hid).trans (map_smul (U t t₂) c (RH t a (G ⟨x, hxG⟩))))
  have hd_norm :
      ‖d‖ ≤ |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖G ⟨x, hxG⟩‖) :=
    ((congrArg norm (map_sub (U t t₂) x (RH t a (H s ⟨x, hxs⟩ + a • x))).symm).trans
      (evolution_norm ε hε h hh hw m g k t t₂ (x - RH t a (H s ⟨x, hxs⟩ + a • x)))).trans_le
      (positive_vacuum_two_time_shifted_resolvent_hilbert_bound
        ε hε h hh hb m g k hk s t a ha hxT hxK hxP).1
  have hb_u :=
    evolved_resolvent_multi_domain_energy_bounds ε hε h hh hb m g k t t₂ q a ha (G ⟨x, hxG⟩)
  have hc_norm : ‖c‖ ^ 2 = |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 := by
    change ‖((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ)‖ ^ 2 = _
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hsmul_sq :
      ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
        (A : Hilbert →ₗ.[ℂ] Y) (hu : u ∈ A.domain),
        ∃ hdA : d ∈ A.domain,
          ‖A ⟨d, hdA⟩‖ ^ 2 =
            |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 * ‖A ⟨u, hu⟩‖ ^ 2 := by
    intro Y _ _ A hu
    have hdA : d ∈ A.domain := by
      rw [hd_eq]
      exact A.domain.smul_mem c hu
    refine ⟨hdA, ?_⟩
    have hval : A ⟨d, hdA⟩ = c • A ⟨u, hu⟩ := by
      apply A.mem_graph_snd_inj' (A.mem_graph ⟨d, hdA⟩)
        (A.graph.smul_mem c (A.mem_graph ⟨u, hu⟩))
      exact hd_eq
    rw [hval, norm_smul, mul_pow, hc_norm]
  let hE_ex := hsmul_sq (Eavg q) hURG.1
  let hS_ex := hsmul_sq Tstat hURG.2.1
  let hC_ex := hsmul_sq (clockHalf ε) hURG.2.2.2.2.2.2
  let hG_ex := hsmul_sq Tgrow hURG.2.2.2.2.1
  let hK_ex := hsmul_sq Kroot hURG.2.2.1
  let hP_ex := hsmul_sq Tpot hURG.2.2.2.1
  let hR_ex := hsmul_sq (Tres q) hURG.2.2.2.2.2.1
  have hpos : 0 ≤ |Real.exp (2 * t) - Real.exp (2 * s)| ^ 2 := sq_nonneg _
  refine ⟨hd_eq, hd_norm,
    hE_ex.choose, hS_ex.choose, hC_ex.choose, hG_ex.choose,
    hK_ex.choose, hP_ex.choose, hR_ex.choose,
    hE_ex.choose_spec.trans_le (mul_le_mul_of_nonneg_left hb_u.2.2.2.1 hpos),
    hS_ex.choose_spec.trans_le (mul_le_mul_of_nonneg_left hb_u.2.2.2.2.1 hpos),
    hC_ex.choose_spec.trans_le (mul_le_mul_of_nonneg_left hb_u.2.2.2.2.2.1 hpos),
    hG_ex.choose_spec.trans_le (mul_le_mul_of_nonneg_left hb_u.2.2.2.2.2.2.2.1 hpos),
    hK_ex.choose_spec.trans_le (mul_le_mul_of_nonneg_left hb_u.2.2.2.2.2.2.2.2.2.1 hpos),
    hP_ex.choose_spec.trans_le (mul_le_mul_of_nonneg_left hb_u.2.2.2.2.2.2.2.2.2.2.2.1 hpos),
    hR_ex.choose_spec.trans_le (mul_le_mul_of_nonneg_left hb_u.2.2.2.2.2.2.2.2.2.2.2.2 hpos)⟩

/-- Under positive vacuum `0 < k`, for any `x ∈ (T).domain ⊓ (K).domain ⊓ (P).domain`,
as `s → t` the evolved shifted-resolvent difference
`d(s) := U t t₂ x - U t t₂ (RH t a (H s x + a • x))` converges to `0` simultaneously in
`Eavg q`, `Tstat`, `clockHalf ε`, `Tgrow`, `Kroot`, `Tpot`, and `Tres q`. -/
theorem positive_vacuum_evolved_shifted_resolvent_form_tendsto_zero
    (hk : 0 < k) (t t₂ q a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hdiff := fun s : ℝ =>
      (positive_vacuum_evolved_shifted_resolvent_difference_bounds
        ε hε h hh hb m g k hk s t t₂ q a ha hxT hxK hxP).2.2
    Tendsto
      (fun s : ℝ =>
        Eavg q
          ⟨U t t₂ x -
              U t t₂
                (RH t a
                  (H s
                    ⟨x,
                      (positive_vacuum_three_operator_hamiltonian_eval
                        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x)),
            (hdiff s).choose⟩)
      (𝓝 t) (𝓝 0) ∧
    Tendsto
      (fun s : ℝ =>
        Tstat
          ⟨U t t₂ x -
              U t t₂
                (RH t a
                  (H s
                    ⟨x,
                      (positive_vacuum_three_operator_hamiltonian_eval
                        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x)),
            (hdiff s).choose_spec.choose⟩)
      (𝓝 t) (𝓝 0) ∧
    Tendsto
      (fun s : ℝ =>
        clockHalf ε
          ⟨U t t₂ x -
              U t t₂
                (RH t a
                  (H s
                    ⟨x,
                      (positive_vacuum_three_operator_hamiltonian_eval
                        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x)),
            (hdiff s).choose_spec.choose_spec.choose⟩)
      (𝓝 t) (𝓝 0) ∧
    Tendsto
      (fun s : ℝ =>
        Tgrow
          ⟨U t t₂ x -
              U t t₂
                (RH t a
                  (H s
                    ⟨x,
                      (positive_vacuum_three_operator_hamiltonian_eval
                        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x)),
            (hdiff s).choose_spec.choose_spec.choose_spec.choose⟩)
      (𝓝 t) (𝓝 0) ∧
    Tendsto
      (fun s : ℝ =>
        Kroot
          ⟨U t t₂ x -
              U t t₂
                (RH t a
                  (H s
                    ⟨x,
                      (positive_vacuum_three_operator_hamiltonian_eval
                        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x)),
            (hdiff s).choose_spec.choose_spec.choose_spec.choose_spec.choose⟩)
      (𝓝 t) (𝓝 0) ∧
    Tendsto
      (fun s : ℝ =>
        Tpot
          ⟨U t t₂ x -
              U t t₂
                (RH t a
                  (H s
                    ⟨x,
                      (positive_vacuum_three_operator_hamiltonian_eval
                        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x)),
            (hdiff s).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩)
      (𝓝 t) (𝓝 0) ∧
    Tendsto
      (fun s : ℝ =>
        Tres q
          ⟨U t t₂ x -
              U t t₂
                (RH t a
                  (H s
                    ⟨x,
                      (positive_vacuum_three_operator_hamiltonian_eval
                        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x)),
            (hdiff s).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩)
      (𝓝 t) (𝓝 0) := by
  intro hdiff
  let hxG := (unconditional_two_operator_growing_eval
    ε hε h hh hb m g k hxK hxP).choose
  have hG_sq : 0 ≤ a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2 :=
    mul_nonneg (inv_nonneg.mpr ha.le) (sq_nonneg _)
  have hexp_pos : 0 ≤ Real.exp (2 * |t₂ - t|) := (Real.exp_pos _).le
  have hmax_pos : 0 ≤ max 1 (Real.exp (2 * (q - t₂))) * Real.exp (2 * |t₂ - t|) :=
    mul_nonneg (le_trans zero_le_one (le_max_left 1 _)) hexp_pos
  have hexp_sub_pos : 0 ≤ Real.exp (2 * (|t₂ - t| - t₂)) := (Real.exp_pos _).le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact tendsto_zero_of_sq_le_abs_exp_sq_mul t
      (max 1 (Real.exp (2 * (q - t₂))) * Real.exp (2 * |t₂ - t|) *
        (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2))
      (mul_nonneg hmax_pos hG_sq)
      (fun s => (hdiff s).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1)
  · exact tendsto_zero_of_sq_le_abs_exp_sq_mul t
      (Real.exp (2 * |t₂ - t|) * (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2))
      (mul_nonneg hexp_pos hG_sq)
      (fun s => (hdiff s).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1)
  · exact tendsto_zero_of_sq_le_abs_exp_sq_mul t
      (2 * (Real.exp (2 * |t₂ - t|) * (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2)))
      (mul_nonneg (by norm_num) (mul_nonneg hexp_pos hG_sq))
      (fun s => (hdiff s).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1)
  · exact tendsto_zero_of_sq_le_abs_exp_sq_mul t
      (Real.exp (2 * (|t₂ - t| - t₂)) * (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2))
      (mul_nonneg hexp_sub_pos hG_sq)
      (fun s => (hdiff s).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1)
  · exact tendsto_zero_of_sq_le_abs_exp_sq_mul t
      (Real.exp (2 * (|t₂ - t| - t₂)) * (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2))
      (mul_nonneg hexp_sub_pos hG_sq)
      (fun s => (hdiff s).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.1)
  · exact tendsto_zero_of_sq_le_abs_exp_sq_mul t
      (Real.exp (2 * (|t₂ - t| - t₂)) * (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2))
      (mul_nonneg hexp_sub_pos hG_sq)
      (fun s => (hdiff s).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.1)
  · exact tendsto_zero_of_sq_le_abs_exp_sq_mul t
      (max 1 (Real.exp (2 * (q - t₂))) * Real.exp (2 * |t₂ - t|) *
        (a⁻¹ * ‖G ⟨x, hxG⟩‖ ^ 2))
      (mul_nonneg hmax_pos hG_sq)
      (fun s => (hdiff s).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.2)

/-- Under positive vacuum `0 < k`, for any `x ∈ (T).domain ⊓ (K).domain ⊓ (P).domain`,
`U t₁ t₂ (RH t a (H s x + a • x)) → U t₁ t₂ x` in Hilbert norm as `s → t`. -/
theorem positive_vacuum_evolved_shifted_resolvent_tendsto
    (hk : 0 < k) (t₁ t₂ t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    Tendsto (fun s : ℝ =>
      U t₁ t₂ (RH t a (H s ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x)))
      (𝓝 t) (𝓝 (U t₁ t₂ x)) :=
  ((U t₁ t₂).continuous.tendsto x).comp
    (positive_vacuum_two_time_shifted_resolvent_tendsto
      ε hε h hh hb m g k hk t a ha hxT hxK hxP)

#print axioms hamiltonian_form_energy_eq_averaged_norm_sq
#print axioms hamiltonian_resolvent_averaged_energy_le
#print axioms resolvent_of_evolved_state_regularity
#print axioms evolved_resolvent_multi_domain_energy_bounds
#print axioms evolved_two_time_resolvent_weak_diff_bound
#print axioms evolved_two_time_resolvent_weak_continuous
#print axioms positive_vacuum_evolved_shifted_resolvent_difference_bounds
#print axioms positive_vacuum_evolved_shifted_resolvent_form_tendsto_zero
#print axioms positive_vacuum_evolved_shifted_resolvent_tendsto

end

end UnifiedTheory.Audit.KFCausalClockFloorEvolvedResolventRegularity
