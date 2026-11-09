/- Positive-Vacuum Two-Time Resolvent Continuity and Form-Operator Norm Bounds:
1. Unconditional positive-resolvent half-clock bounds for RH(t, a) and RS(t, a)
   on every Hilbert vector f (without domain restrictions on f):
   ‖clockHalf(RH(t,a) f)‖ ≤ √2 √(a⁻¹) ‖f‖ and ‖clockHalf(RS(t,a) f)‖ ≤ √2 √(a⁻¹) ‖f‖.
2. Unconditional two-time form energy difference identities, Lipschitz bounds,
   and s → t continuity for completed residual and full averaged form energies.
3. Positive-vacuum (k > 0) two-time Lipschitz bounds and s → t continuity for
   S(s) x → S(t) x and H(s) x → H(t) x on Dom T ∩ Dom K ∩ Dom P (and Dom H(t) ∩ Dom G).
4. Positive-vacuum (k > 0) two-time shifted-resolvent difference bounds and s → t
   convergence x - RH(t, a)(H(s) x + a x) → 0 across Hilbert, Tstat, Kroot, Tpot,
   clockHalf, K, and H(t) norms, and analogously for RS(t, a)(S(s) x + a x) → x.
5. Unconditional weak/form two-time resolvent continuity
   ⟪f₁, (RH(s, a) - RH(t, a)) f₂⟫ → 0 and ⟪f₁, (RS(s, a) - RS(t, a)) f₂⟫ → 0
   as s → t for all f₁, f₂ : Hilbert, together with strong two-time resolvent
   difference bounds when RH(s, a) f ∈ Dom G. -/
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianComponentResolventBounds
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormNormBounds

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity
noncomputable section
open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorUnconditionalTwoTimeEvolution (commonOperatorDomain)
open KFCausalClockFloorResidualFormSplit (potentialLift potentialLift_embedding residual_norm_split)
open KFCausalClockFloorTwoTimeFormTransfer
  (residualFormTransfer residualFormTransfer_embedding
   two_time_residual_norm_sq_difference growingProject
   two_time_averaged_growing_norm_sq_difference)
open KFCausalClockFloorPositiveVacuumTwoTimeOperatorDomain

theorem two_time_exp_diff_tendsto_zero (t : ℝ) :
    Tendsto (fun s : ℝ => |Real.exp (2 * t) - Real.exp (2 * s)|) (𝓝 t) (𝓝 0) := by
  have hc : Continuous (fun s : ℝ => |Real.exp (2 * t) - Real.exp (2 * s)|) := by fun_prop
  simpa only [sub_self, abs_zero] using hc.tendsto t

private theorem tendsto_zero_of_abs_exp_mul {F : ℝ → ℝ} (t C : ℝ)
    (h0 : ∀ s, 0 ≤ F s)
    (hb : ∀ s, F s ≤ |Real.exp (2 * t) - Real.exp (2 * s)| * C) :
    Tendsto F (𝓝 t) (𝓝 0) := by
  have hlim : Tendsto (fun s : ℝ => |Real.exp (2 * t) - Real.exp (2 * s)| * C) (𝓝 t) (𝓝 0) := by
    simpa only [zero_mul] using (two_time_exp_diff_tendsto_zero t).mul_const C
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim h0 hb

private theorem tendsto_zero_norm_of_abs_exp_mul {X : Type*}
    [NormedAddCommGroup X] {V : ℝ → X} (t C : ℝ)
    (hb : ∀ s, ‖V s‖ ≤ |Real.exp (2 * t) - Real.exp (2 * s)| * C) :
    Tendsto V (𝓝 t) (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr
    (tendsto_zero_of_abs_exp_mul t C (fun s => norm_nonneg (V s)) hb)

private theorem form_output_eq_operator
    (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (w : KFCausalClosedGraphForm.FormSpace D) (f : Hilbert)
    (hJ : KFCausalClosedGraphForm.embedding D w = f) (hf : f ∈ D.operator.domain) :
    KFCausalClosedGraphForm.energyOutput D w = D.operator ⟨f, hf⟩ :=
  D.operator.mem_graph_snd_inj' w.property (D.operator.mem_graph ⟨f, hf⟩) hJ

private theorem norm_sq_diff_of_eq
    {u1 u2 v1 v2 w1 w2 : EnergyOutputSpace} {c : ℝ}
    (h : ‖u1‖ ^ 2 - ‖v1‖ ^ 2 = c * ‖w1‖ ^ 2)
    (hu : u1 = u2) (hv : v1 = v2) (hw : w1 = w2) :
    ‖u2‖ ^ 2 - ‖v2‖ ^ 2 = c * ‖w2‖ ^ 2 := by
  rw [← hu, ← hv, ← hw]
  exact h

private theorem abs_sub_eq_abs_mul_sq {a b c d : ℝ} (h : a - b = c * d ^ 2) :
    |a - b| = |c| * d ^ 2 := by
  rw [h, abs_mul, abs_of_nonneg (sq_nonneg d)]

private theorem weak_diff_bound_of_parts
    (z1 z2 : ℂ) (kt ks : Hilbert) (pt ps : EnergyOutputSpace)
    (Kt Ks : Hilbert) (Pt Ps : EnergyOutputSpace)
    (t s a n1 n2 : ℝ) (ha : 0 < a) (hn1 : 0 ≤ n1)
    (hz : z1 = z2)
    (hlhs : z2 = ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) *
      (inner ℂ kt ks + inner ℂ pt ps))
    (hkt : kt = Kt) (hks : ks = Ks) (hpt : pt = Pt) (hps : ps = Ps)
    (hbKt : Real.exp t * ‖Kt‖ ≤ Real.sqrt (a⁻¹) * n1)
    (hbKs : Real.exp s * ‖Ks‖ ≤ Real.sqrt (a⁻¹) * n2)
    (hbPt : Real.exp t * ‖Pt‖ ≤ Real.sqrt (a⁻¹) * n1)
    (hbPs : Real.exp s * ‖Ps‖ ≤ Real.sqrt (a⁻¹) * n2) :
    ‖z1‖ ≤ |Real.exp (2 * t) - Real.exp (2 * s)| *
      (2 * Real.exp (-(t + s)) * a⁻¹ * n1 * n2) := by
  rw [hz, hlhs, hkt, hks, hpt, hps, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hcsK : ‖inner ℂ Kt Ks‖ ≤ ‖Kt‖ * ‖Ks‖ := norm_inner_le_norm Kt Ks
  have hcsP : ‖inner ℂ Pt Ps‖ ≤ ‖Pt‖ * ‖Ps‖ := norm_inner_le_norm Pt Ps
  have hadd : ‖inner ℂ Kt Ks + inner ℂ Pt Ps‖ ≤ ‖Kt‖ * ‖Ks‖ + ‖Pt‖ * ‖Ps‖ :=
    (norm_add_le _ _).trans (add_le_add hcsK hcsP)
  have hprodK : Real.exp (t + s) * (‖Kt‖ * ‖Ks‖) ≤ a⁻¹ * n1 * n2 := by
    have hmul := mul_le_mul hbKt hbKs
      (mul_nonneg (Real.exp_pos s).le (norm_nonneg Ks))
      (mul_nonneg (Real.sqrt_nonneg _) hn1)
    calc
      Real.exp (t + s) * (‖Kt‖ * ‖Ks‖) =
          (Real.exp t * ‖Kt‖) * (Real.exp s * ‖Ks‖) := by
            rw [Real.exp_add]; ring
      _ ≤ (Real.sqrt (a⁻¹) * n1) * (Real.sqrt (a⁻¹) * n2) := hmul
      _ = (Real.sqrt (a⁻¹)) ^ 2 * n1 * n2 := by ring
      _ = a⁻¹ * n1 * n2 := by
            rw [Real.sq_sqrt (inv_nonneg.mpr ha.le)]
  have hprodP : Real.exp (t + s) * (‖Pt‖ * ‖Ps‖) ≤ a⁻¹ * n1 * n2 := by
    have hmul := mul_le_mul hbPt hbPs
      (mul_nonneg (Real.exp_pos s).le (norm_nonneg Ps))
      (mul_nonneg (Real.sqrt_nonneg _) hn1)
    calc
      Real.exp (t + s) * (‖Pt‖ * ‖Ps‖) =
          (Real.exp t * ‖Pt‖) * (Real.exp s * ‖Ps‖) := by
            rw [Real.exp_add]; ring
      _ ≤ (Real.sqrt (a⁻¹) * n1) * (Real.sqrt (a⁻¹) * n2) := hmul
      _ = (Real.sqrt (a⁻¹)) ^ 2 * n1 * n2 := by ring
      _ = a⁻¹ * n1 * n2 := by
            rw [Real.sq_sqrt (inv_nonneg.mpr ha.le)]
  have hsum : Real.exp (t + s) * (‖Kt‖ * ‖Ks‖ + ‖Pt‖ * ‖Ps‖) ≤
      2 * (a⁻¹ * n1 * n2) := by linarith
  have hscale := mul_le_mul_of_nonneg_left hsum (Real.exp_pos (-(t + s))).le
  have hcancel : Real.exp (-(t + s)) *
      (Real.exp (t + s) * (‖Kt‖ * ‖Ks‖ + ‖Pt‖ * ‖Ps‖)) =
      ‖Kt‖ * ‖Ks‖ + ‖Pt‖ * ‖Ps‖ := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rw [hcancel] at hscale
  exact hadd.trans (hscale.trans_eq (by ring))

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
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
local notation "AD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k
local notation "AT" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k
local notation "FT" => KFCausalClockFloorAveragedFormTransport.formTransfer ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "SB" => fun t => KFCausalClosedGraphForm.energyOutput (SD t)
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD

/-! ### 1. Unconditional Positive-Resolvent Half-Clock and Form-Root Bounds -/

theorem resolvent_in_clockHalf_domain (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RH t a f ∈ (clockHalf ε).domain :=
  static_root_subset_clockHalf_domain ε hε h (RH t a f)
    (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
      ε hε h hh hb m g k t a ha f)

theorem resolvent_clockHalf_norm_sq_bound (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖clockHalf ε ⟨RH t a f, resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      2 * a⁻¹ * ‖f‖ ^ 2 := by
  have h1 := static_root_clockHalf_norm_sq_le ε hε h (RH t a f)
    (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
      ε hε h hh hb m g k t a ha f)
  have h2 := KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_static_radial_energy_le
    ε hε h hh hb m g k t a ha f
  have hrad : 0 ≤ Real.exp (2 * t) *
      ‖Kroot ⟨RH t a f, KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
        ε hε h hh hb m g k t a ha f⟩‖ ^ 2 :=
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have ha0 : 0 ≤ a * ‖RH t a f‖ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  linarith

theorem resolvent_clockHalf_norm_bound (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖clockHalf ε ⟨RH t a f, resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
      Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖f‖ := by
  have h1 := static_root_clockHalf_norm_le ε hε h (RH t a f)
    (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
      ε hε h hh hb m g k t a ha f)
  have h2 := KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_staticRoot_norm_le
    ε hε h hh hb m g k t a ha f
  calc
    ‖clockHalf ε ⟨RH t a f, resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
        Real.sqrt 2 * ‖Tstat ⟨RH t a f, _⟩‖ := h1
    _ ≤ Real.sqrt 2 * (Real.sqrt (a⁻¹) * ‖f‖) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2)
    _ = Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖f‖ := by ring

theorem residual_resolvent_in_clockHalf_domain (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RS t a f ∈ (clockHalf ε).domain :=
  static_root_subset_clockHalf_domain ε hε h (RS t a f)
    (KFCausalClockFloorHamiltonianResolventFormBounds.residual_resolvent_mem_staticRoot_domain
      ε hε h hh hb m g k t a ha f)

theorem residual_resolvent_clockHalf_norm_sq_bound (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖clockHalf ε ⟨RS t a f, residual_resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ^ 2 ≤
      2 * a⁻¹ * ‖f‖ ^ 2 := by
  have h1 := static_root_clockHalf_norm_sq_le ε hε h (RS t a f)
    (KFCausalClockFloorHamiltonianResolventFormBounds.residual_resolvent_mem_staticRoot_domain
      ε hε h hh hb m g k t a ha f)
  have h2 := KFCausalClockFloorHamiltonianResolventFormBounds.residual_resolvent_static_energy_le
    ε hε h hh hb m g k t a ha f
  have ha0 : 0 ≤ a * ‖RS t a f‖ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  linarith

theorem residual_resolvent_clockHalf_norm_bound (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖clockHalf ε ⟨RS t a f, residual_resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
      Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖f‖ := by
  have h1 := static_root_clockHalf_norm_le ε hε h (RS t a f)
    (KFCausalClockFloorHamiltonianResolventFormBounds.residual_resolvent_mem_staticRoot_domain
      ε hε h hh hb m g k t a ha f)
  have h2 := KFCausalClockFloorHamiltonianResolventFormBounds.residual_resolvent_staticRoot_norm_le
    ε hε h hh hb m g k t a ha f
  calc
    ‖clockHalf ε ⟨RS t a f, residual_resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f⟩‖ ≤
        Real.sqrt 2 * ‖Tstat ⟨RS t a f, _⟩‖ := h1
    _ ≤ Real.sqrt 2 * (Real.sqrt (a⁻¹) * ‖f‖) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2)
    _ = Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖f‖ := by ring

/-! ### 2. Two-Time Form Energy Differences, Lipschitz Bounds, and Continuity (s → t) -/

theorem two_time_residual_form_energy_diff_eq (s t : ℝ) (f : Hilbert)
    (hfs : f ∈ (Tres s).domain) (hft : f ∈ (Tres t).domain) :
    ‖Tres t ⟨f, hft⟩‖ ^ 2 - ‖Tres s ⟨f, hfs⟩‖ ^ 2 =
      (Real.exp (2 * t) - Real.exp (2 * s)) *
        ‖Tpot ⟨f, (KFCausalClockFloorUnconditionalFormDomainSynthesis.residual_domain_subset_static_inter_potential
          ε hε h hh hb m g k t f hft).2⟩‖ ^ 2 :=
  let ws := KFCausalClosedGraphForm.graphVector (SD s) ⟨f, hfs⟩
  norm_sq_diff_of_eq
    (two_time_residual_norm_sq_difference ε hε h hh hb m g k t s ws)
    (form_output_eq_operator (SD t)
      (residualFormTransfer ε hε h hh hb m g k s t ws) f
      ((residualFormTransfer_embedding ε hε h hh hb m g k s t ws).trans
        (KFCausalClosedGraphForm.graphVector_embedding (SD s) ⟨f, hfs⟩)) hft)
    (KFCausalClosedGraphForm.graphVector_output (SD s) ⟨f, hfs⟩)
    (form_output_eq_operator PD
      (potentialLift ε hε h hh hw m g k s ws) f
      ((potentialLift_embedding ε hε h hh hw m g k s ws).trans
        (KFCausalClosedGraphForm.graphVector_embedding (SD s) ⟨f, hfs⟩))
      (KFCausalClockFloorUnconditionalFormDomainSynthesis.residual_domain_subset_static_inter_potential
        ε hε h hh hb m g k t f hft).2)

theorem two_time_residual_form_energy_tendsto_zero (t : ℝ) (f : Hilbert)
    (hft : f ∈ (Tres t).domain) :
    Tendsto (fun s : ℝ =>
      |‖Tres t ⟨f, hft⟩‖ ^ 2 -
        ‖Tres s ⟨f, (residual_form_domain_time_iff ε hε h hh hb m g k t s f).mp hft⟩‖ ^ 2|)
      (𝓝 t) (𝓝 0) := by
  have hp := (KFCausalClockFloorUnconditionalFormDomainSynthesis.residual_domain_subset_static_inter_potential
    ε hε h hh hb m g k t f hft).2
  refine tendsto_zero_of_abs_exp_mul t (‖Tpot ⟨f, hp⟩‖ ^ 2) (fun _ => abs_nonneg _) (fun s => ?_)
  exact (abs_sub_eq_abs_mul_sq
    (two_time_residual_form_energy_diff_eq ε hε h hh hb m g k s t f
      ((residual_form_domain_time_iff ε hε h hh hb m g k t s f).mp hft) hft)).le

theorem two_time_averaged_form_energy_diff_eq (s t : ℝ) (f : Hilbert)
    (hfs : f ∈ (Eavg s).domain) (hft : f ∈ (Eavg t).domain) :
    ‖Eavg t ⟨f, hft⟩‖ ^ 2 - ‖Eavg s ⟨f, hfs⟩‖ ^ 2 =
      (Real.exp (2 * t) - Real.exp (2 * s)) *
        ‖Tgrow ⟨f, ((KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
          ε hε h hh hb m g k t f).mp hft).1⟩‖ ^ 2 :=
  let us := KFCausalClosedGraphForm.graphVector (AD s) ⟨f, hfs⟩
  norm_sq_diff_of_eq
    (two_time_averaged_growing_norm_sq_difference ε hε h hh hb m g k t s us)
    (form_output_eq_operator (AD t) (FT s t us) f
      ((KFCausalClockFloorAveragedFormTransport.transfer_embedding ε hε h hh hw m g k s t us).trans
        (KFCausalClosedGraphForm.graphVector_embedding (AD s) ⟨f, hfs⟩)) hft)
    (KFCausalClosedGraphForm.graphVector_output (AD s) ⟨f, hfs⟩)
    (form_output_eq_operator GD (growingProject ε hε h hh hb m g k s us) f
      ((KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding
        ε hε h hh hw m g k (FT s 0 us)).trans
        ((KFCausalClockFloorAveragedFormTransport.transfer_embedding
          ε hε h hh hw m g k s 0 us).trans
          (KFCausalClosedGraphForm.graphVector_embedding (AD s) ⟨f, hfs⟩)))
      ((KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
        ε hε h hh hb m g k t f).mp hft).1)

theorem two_time_averaged_form_energy_tendsto_zero (t : ℝ) (f : Hilbert)
    (hft : f ∈ (Eavg t).domain) :
    Tendsto (fun s : ℝ =>
      |‖Eavg t ⟨f, hft⟩‖ ^ 2 -
        ‖Eavg s ⟨f, (KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_time_eq
          ε hε h hh hb m g k t s f).mp hft⟩‖ ^ 2|)
      (𝓝 t) (𝓝 0) := by
  have hg := ((KFCausalClockFloorResidualFormReconstruction.averaged_domain_eq_growing_inter_residual
    ε hε h hh hb m g k t f).mp hft).1
  refine tendsto_zero_of_abs_exp_mul t (‖Tgrow ⟨f, hg⟩‖ ^ 2)
    (fun _ => abs_nonneg _) (fun s => ?_)
  exact (abs_sub_eq_abs_mul_sq
    (two_time_averaged_form_energy_diff_eq ε hε h hh hb m g k s t f
      ((KFCausalClockFloorUnconditionalFormDomainSynthesis.averaged_domain_time_eq
        ε hε h hh hb m g k t s f).mp hft) hft)).le

theorem positive_vacuum_two_time_averaged_form_energy_tendsto_zero (hk : 0 < k) (t : ℝ)
    {f : Hilbert} (hstat : f ∈ (Tstat).domain) (hK : f ∈ (Kroot).domain)
    (hpot : f ∈ (Tpot).domain) :
    Tendsto (fun s : ℝ =>
      |‖Eavg t ⟨f, (positive_vacuum_averaged_form_domain_iff
        ε hε h hh hb m g k hk t f).mpr ⟨⟨hstat, hK⟩, hpot⟩⟩‖ ^ 2 -
        ‖Eavg s ⟨f, (positive_vacuum_averaged_form_domain_iff
          ε hε h hh hb m g k hk s f).mpr ⟨⟨hstat, hK⟩, hpot⟩⟩‖ ^ 2|)
      (𝓝 t) (𝓝 0) :=
  two_time_averaged_form_energy_tendsto_zero ε hε h hh hb m g k t f
    ((positive_vacuum_averaged_form_domain_iff
      ε hε h hh hb m g k hk t f).mpr ⟨⟨hstat, hK⟩, hpot⟩)

/-! ### 3. Positive-Vacuum Two-Time Operator Action Bounds and Continuity -/

theorem positive_vacuum_two_time_residual_diff_norm_eq (hk : 0 < k) (s t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hxs := (positive_vacuum_three_operator_residual_eval
      ε hε h hh hb m g k hk s hxT hxK hxP).choose
    let hxt := (positive_vacuum_three_operator_residual_eval
      ε hε h hh hb m g k hk t hxT hxK hxP).choose
    ‖S t ⟨x, hxt⟩ - S s ⟨x, hxs⟩‖ = |Real.exp (2 * t) - Real.exp (2 * s)| * ‖P ⟨x, hxP⟩‖ := by
  have hev := positive_vacuum_two_time_residual_eval ε hε h hh hb m g k hk s t hxT hxK hxP
  have hdiff := hev.choose_spec.choose_spec.2.2
  dsimp only
  rw [hdiff, norm_smul, Complex.norm_real, Real.norm_eq_abs]

theorem positive_vacuum_two_time_hamiltonian_diff_norm_eq (hk : 0 < k) (s t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hxs := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk s hxT hxK hxP).choose
    let hxt := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk t hxT hxK hxP).choose
    let hxG := (unconditional_two_operator_growing_eval
      ε hε h hh hb m g k hxK hxP).choose
    ‖H t ⟨x, hxt⟩ - H s ⟨x, hxs⟩‖ = |Real.exp (2 * t) - Real.exp (2 * s)| * ‖G ⟨x, hxG⟩‖ ∧
    ‖H t ⟨x, hxt⟩ - H s ⟨x, hxs⟩‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (‖K ⟨x, hxK⟩‖ + ‖P ⟨x, hxP⟩‖) := by
  have hev := positive_vacuum_two_time_hamiltonian_eval ε hε h hh hb m g k hk s t hxT hxK hxP
  have hdiff1 := hev.choose_spec.choose_spec.choose_spec.2.2.1
  have hdiff2 := hev.choose_spec.choose_spec.choose_spec.2.2.2
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [hdiff1, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  · rw [hdiff2, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)

theorem positive_vacuum_two_time_residual_tendsto_zero (hk : 0 < k) (t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    Tendsto (fun s : ℝ =>
      S s ⟨x, (positive_vacuum_three_operator_residual_eval
        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ -
      S t ⟨x, (positive_vacuum_three_operator_residual_eval
        ε hε h hh hb m g k hk t hxT hxK hxP).choose⟩)
      (𝓝 t) (𝓝 0) := by
  refine tendsto_zero_norm_of_abs_exp_mul t ‖P ⟨x, hxP⟩‖ (fun s => ?_)
  rw [norm_sub_rev]
  exact (positive_vacuum_two_time_residual_diff_norm_eq
    ε hε h hh hb m g k hk s t hxT hxK hxP).le

theorem positive_vacuum_two_time_residual_continuous (hk : 0 < k) (t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    Tendsto (fun s : ℝ =>
      S s ⟨x, (positive_vacuum_three_operator_residual_eval
        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩)
      (𝓝 t)
      (𝓝 (S t ⟨x, (positive_vacuum_three_operator_residual_eval
        ε hε h hh hb m g k hk t hxT hxK hxP).choose⟩)) :=
  tendsto_sub_nhds_zero_iff.mp
    (positive_vacuum_two_time_residual_tendsto_zero ε hε h hh hb m g k hk t hxT hxK hxP)

theorem positive_vacuum_two_time_hamiltonian_tendsto_zero (hk : 0 < k) (t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    Tendsto (fun s : ℝ =>
      H s ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ -
      H t ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk t hxT hxK hxP).choose⟩)
      (𝓝 t) (𝓝 0) := by
  let hxG := (unconditional_two_operator_growing_eval ε hε h hh hb m g k hxK hxP).choose
  refine tendsto_zero_norm_of_abs_exp_mul t ‖G ⟨x, hxG⟩‖ (fun s => ?_)
  rw [norm_sub_rev]
  exact (positive_vacuum_two_time_hamiltonian_diff_norm_eq
    ε hε h hh hb m g k hk s t hxT hxK hxP).1.le

theorem positive_vacuum_two_time_hamiltonian_continuous (hk : 0 < k) (t : ℝ)
    {x : Hilbert} (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    Tendsto (fun s : ℝ =>
      H s ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩)
      (𝓝 t)
      (𝓝 (H t ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk t hxT hxK hxP).choose⟩)) :=
  tendsto_sub_nhds_zero_iff.mp
    (positive_vacuum_two_time_hamiltonian_tendsto_zero ε hε h hh hb m g k hk t hxT hxK hxP)

/-! ### 4. Positive-Vacuum Shifted-Resolvent Action Difference Bounds and Continuity -/

theorem positive_vacuum_two_time_shifted_resolvent_hilbert_bound (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hxs := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk s hxT hxK hxP).choose
    let hxG := (unconditional_two_operator_growing_eval
      ε hε h hh hb m g k hxK hxP).choose
    ‖x - RH t a (H s ⟨x, hxs⟩ + a • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖G ⟨x, hxG⟩‖) ∧
    ‖x - RH t a (H s ⟨x, hxs⟩ + a • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * (‖K ⟨x, hxK⟩‖ + ‖P ⟨x, hxP⟩‖)) := by
  have hx : x ∈ commonOperatorDomain ε hε h hh hb m g k := by
    rw [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk]
    exact ⟨⟨hxT, hxK⟩, hxP⟩
  have hb1 := KFCausalClockFloorTwoTimeResolventDifference.hamiltonian_resolvent_two_time_norm_bound
    ε hε h hh hb m g k t s a ha x hx
  have hb2 := KFCausalClockFloorTwoTimeResolventDifference.hamiltonian_resolvent_two_time_component_norm_bound
    ε hε h hh hb m g k t s a ha x hx
  dsimp only
  refine ⟨?_, ?_⟩
  · exact hb1.trans_eq (by ring)
  · exact hb2.trans_eq (by ring)

theorem positive_vacuum_two_time_shifted_resolvent_static_root_bound (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hxs := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk s hxT hxK hxP).choose
    let hxG := (unconditional_two_operator_growing_eval
      ε hε h hh hb m g k hxK hxP).choose
    let hd : x - RH t a (H s ⟨x, hxs⟩ + a • x) ∈ (Tstat).domain :=
      (Tstat).domain.sub_mem
        (KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨x, hxT⟩)
        (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
          ε hε h hh hb m g k t a ha (H s ⟨x, hxs⟩ + a • x))
    ‖Tstat ⟨x - RH t a (H s ⟨x, hxs⟩ + a • x), hd⟩‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (Real.sqrt (a⁻¹) * ‖G ⟨x, hxG⟩‖) := by
  let hxs := (positive_vacuum_three_operator_hamiltonian_eval
    ε hε h hh hb m g k hk s hxT hxK hxP).choose
  let hxG := (unconditional_two_operator_growing_eval
    ε hε h hh hb m g k hxK hxP).choose
  let hd : x - RH t a (H s ⟨x, hxs⟩ + a • x) ∈ (Tstat).domain :=
    (Tstat).domain.sub_mem
      (KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨x, hxT⟩)
      (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
        ε hε h hh hb m g k t a ha (H s ⟨x, hxs⟩ + a • x))
  have hid := (positive_vacuum_two_time_shifted_resolvent_identity
    ε hε h hh hb m g k hk s t a ha hxT hxK hxP).choose_spec.choose_spec.1
  let hRG : RH t a (G ⟨x, hxG⟩) ∈ (Tstat).domain :=
    KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
      ε hε h hh hb m g k t a ha (G ⟨x, hxG⟩)
  have heq : Tstat ⟨x - RH t a (H s ⟨x, hxs⟩ + a • x), hd⟩ =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • Tstat ⟨RH t a (G ⟨x, hxG⟩), hRG⟩ := by
    apply (Tstat).mem_graph_snd_inj'
      ((Tstat).mem_graph ⟨x - RH t a (H s ⟨x, hxs⟩ + a • x), hd⟩)
      ((Tstat).graph.smul_mem ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ)
        ((Tstat).mem_graph ⟨RH t a (G ⟨x, hxG⟩), hRG⟩))
    exact hid
  have hroot := KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_staticRoot_norm_le
    ε hε h hh hb m g k t a ha (G ⟨x, hxG⟩)
  dsimp only
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hroot (abs_nonneg _)

theorem positive_vacuum_two_time_shifted_resolvent_clockHalf_bound (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hxs := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk s hxT hxK hxP).choose
    let hxG := (unconditional_two_operator_growing_eval
      ε hε h hh hb m g k hxK hxP).choose
    let hd : x - RH t a (H s ⟨x, hxs⟩ + a • x) ∈ (clockHalf ε).domain :=
      static_root_subset_clockHalf_domain ε hε h (x - RH t a (H s ⟨x, hxs⟩ + a • x))
        ((Tstat).domain.sub_mem
          (KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨x, hxT⟩)
          (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
            ε hε h hh hb m g k t a ha (H s ⟨x, hxs⟩ + a • x)))
    ‖clockHalf ε ⟨x - RH t a (H s ⟨x, hxs⟩ + a • x), hd⟩‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖G ⟨x, hxG⟩‖) := by
  let hxs := (positive_vacuum_three_operator_hamiltonian_eval
    ε hε h hh hb m g k hk s hxT hxK hxP).choose
  let hxG := (unconditional_two_operator_growing_eval
    ε hε h hh hb m g k hxK hxP).choose
  let hdS : x - RH t a (H s ⟨x, hxs⟩ + a • x) ∈ (Tstat).domain :=
    (Tstat).domain.sub_mem
      (KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨x, hxT⟩)
      (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
        ε hε h hh hb m g k t a ha (H s ⟨x, hxs⟩ + a • x))
  have hc := static_root_clockHalf_norm_le ε hε h (x - RH t a (H s ⟨x, hxs⟩ + a • x)) hdS
  have hs := positive_vacuum_two_time_shifted_resolvent_static_root_bound
    ε hε h hh hb m g k hk s t a ha hxT hxK hxP
  dsimp only at hs ⊢
  calc
    ‖clockHalf ε ⟨x - RH t a (H s ⟨x, hxs⟩ + a • x),
        static_root_subset_clockHalf_domain ε hε h _ hdS⟩‖ ≤
        Real.sqrt 2 * ‖Tstat ⟨x - RH t a (H s ⟨x, hxs⟩ + a • x), hdS⟩‖ := hc
    _ ≤ Real.sqrt 2 * (|Real.exp (2 * t) - Real.exp (2 * s)| *
          (Real.sqrt (a⁻¹) * ‖G ⟨x, hxG⟩‖)) :=
        mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg 2)
    _ = |Real.exp (2 * t) - Real.exp (2 * s)| *
          (Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖G ⟨x, hxG⟩‖) := by ring

theorem positive_vacuum_two_time_shifted_resolvent_hamiltonian_bound (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hxs := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk s hxT hxK hxP).choose
    let hxt := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk t hxT hxK hxP).choose
    let hxG := (unconditional_two_operator_growing_eval
      ε hε h hh hb m g k hxK hxP).choose
    let hR : RH t a (H s ⟨x, hxs⟩ + a • x) ∈ (H t).domain :=
      (KFCausalClockFloorHamiltonianClockCore.resolves
        ε hε h hh hw m g k t a ha (H s ⟨x, hxs⟩ + a • x)).1
    ‖H t ⟨x, hxt⟩ - H t ⟨RH t a (H s ⟨x, hxs⟩ + a • x), hR⟩‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * ‖G ⟨x, hxG⟩‖ ∧
    ‖H t ⟨x, hxt⟩ - H t ⟨RH t a (H s ⟨x, hxs⟩ + a • x), hR⟩‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (‖K ⟨x, hxK⟩‖ + ‖P ⟨x, hxP⟩‖) := by
  let hxs := (positive_vacuum_three_operator_hamiltonian_eval
    ε hε h hh hb m g k hk s hxT hxK hxP).choose
  let hxt := (positive_vacuum_three_operator_hamiltonian_eval
    ε hε h hh hb m g k hk t hxT hxK hxP).choose
  let hxG := (unconditional_two_operator_growing_eval
    ε hε h hh hb m g k hxK hxP).choose
  let hR : RH t a (H s ⟨x, hxs⟩ + a • x) ∈ (H t).domain :=
    (KFCausalClockFloorHamiltonianClockCore.resolves
      ε hε h hh hw m g k t a ha (H s ⟨x, hxs⟩ + a • x)).1
  let hRG : RH t a (G ⟨x, hxG⟩) ∈ (H t).domain :=
    KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_hamiltonian_domain
      ε hε h hh hb m g k t a ha (G ⟨x, hxG⟩)
  have hid := (positive_vacuum_two_time_shifted_resolvent_identity
    ε hε h hh hb m g k hk s t a ha hxT hxK hxP).choose_spec.choose_spec.1
  have heq : H t ⟨x, hxt⟩ - H t ⟨RH t a (H s ⟨x, hxs⟩ + a • x), hR⟩ =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • H t ⟨RH t a (G ⟨x, hxG⟩), hRG⟩ := by
    apply (H t).mem_graph_snd_inj'
      ((H t).graph.sub_mem ((H t).mem_graph ⟨x, hxt⟩)
        ((H t).mem_graph ⟨RH t a (H s ⟨x, hxs⟩ + a • x), hR⟩))
      ((H t).graph.smul_mem ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ)
        ((H t).mem_graph ⟨RH t a (G ⟨x, hxG⟩), hRG⟩))
    exact hid
  have hbH := KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_hamiltonian_norm_le
    ε hε h hh hb m g k t a ha (G ⟨x, hxG⟩)
  have hGeq : G ⟨x, hxG⟩ = K ⟨x, hxK⟩ + P ⟨x, hxP⟩ :=
    (unconditional_two_operator_growing_eval ε hε h hh hb m g k hxK hxP).choose_spec
  have hb1 : ‖H t ⟨x, hxt⟩ - H t ⟨RH t a (H s ⟨x, hxs⟩ + a • x), hR⟩‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * ‖G ⟨x, hxG⟩‖ := by
    rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hbH (abs_nonneg _)
  dsimp only
  refine ⟨hb1, hb1.trans ?_⟩
  rw [hGeq]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)

theorem positive_vacuum_two_time_shifted_resolvent_radial_diff_norm_eq (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hxs := (positive_vacuum_three_operator_hamiltonian_eval
      ε hε h hh hb m g k hk s hxT hxK hxP).choose
    let hxG := (unconditional_two_operator_growing_eval
      ε hε h hh hb m g k hxK hxP).choose
    let hRK : RH t a (H s ⟨x, hxs⟩ + a • x) ∈ (K).domain :=
      (two_time_resolvent_all_domains ε hε h hh hb m g k t t a ha (H s ⟨x, hxs⟩ + a • x)).2.1
    let hRKG : RH t a (G ⟨x, hxG⟩) ∈ (K).domain :=
      KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
        ε hε h hh hb m g k t a ha (G ⟨x, hxG⟩)
    ‖K ⟨x, hxK⟩ - K ⟨RH t a (H s ⟨x, hxs⟩ + a • x), hRK⟩‖ =
      |Real.exp (2 * t) - Real.exp (2 * s)| * ‖K ⟨RH t a (G ⟨x, hxG⟩), hRKG⟩‖ := by
  let hxs := (positive_vacuum_three_operator_hamiltonian_eval
    ε hε h hh hb m g k hk s hxT hxK hxP).choose
  let hxG := (unconditional_two_operator_growing_eval
    ε hε h hh hb m g k hxK hxP).choose
  let hRK : RH t a (H s ⟨x, hxs⟩ + a • x) ∈ (K).domain :=
    (two_time_resolvent_all_domains ε hε h hh hb m g k t t a ha (H s ⟨x, hxs⟩ + a • x)).2.1
  let hRKG : RH t a (G ⟨x, hxG⟩) ∈ (K).domain :=
    KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
      ε hε h hh hb m g k t a ha (G ⟨x, hxG⟩)
  have hid := (positive_vacuum_two_time_shifted_resolvent_identity
    ε hε h hh hb m g k hk s t a ha hxT hxK hxP).choose_spec.choose_spec.1
  have heq : K ⟨x, hxK⟩ - K ⟨RH t a (H s ⟨x, hxs⟩ + a • x), hRK⟩ =
      ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ) • K ⟨RH t a (G ⟨x, hxG⟩), hRKG⟩ := by
    apply (K).mem_graph_snd_inj'
      ((K).graph.sub_mem ((K).mem_graph ⟨x, hxK⟩)
        ((K).mem_graph ⟨RH t a (H s ⟨x, hxs⟩ + a • x), hRK⟩))
      ((K).graph.smul_mem ((Real.exp (2 * t) - Real.exp (2 * s) : ℝ) : ℂ)
        ((K).mem_graph ⟨RH t a (G ⟨x, hxG⟩), hRKG⟩))
    exact hid
  dsimp only
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs]

theorem positive_vacuum_two_time_shifted_resolvent_tendsto (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    Tendsto (fun s : ℝ =>
      RH t a (H s ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x))
      (𝓝 t) (𝓝 x) := by
  let hxG := (unconditional_two_operator_growing_eval
    ε hε h hh hb m g k hxK hxP).choose
  apply tendsto_sub_nhds_zero_iff.mp
  refine tendsto_zero_norm_of_abs_exp_mul t (a⁻¹ * ‖G ⟨x, hxG⟩‖) (fun s => ?_)
  rw [norm_sub_rev]
  exact (positive_vacuum_two_time_shifted_resolvent_hilbert_bound
    ε hε h hh hb m g k hk s t a ha hxT hxK hxP).1

theorem positive_vacuum_two_time_shifted_resolvent_static_root_tendsto_zero (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    Tendsto (fun s : ℝ =>
      Tstat ⟨x - RH t a (H s ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x),
        (Tstat).domain.sub_mem
          (KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨x, hxT⟩)
          (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
            ε hε h hh hb m g k t a ha _)⟩)
      (𝓝 t) (𝓝 0) := by
  let hxG := (unconditional_two_operator_growing_eval
    ε hε h hh hb m g k hxK hxP).choose
  refine tendsto_zero_norm_of_abs_exp_mul t (Real.sqrt (a⁻¹) * ‖G ⟨x, hxG⟩‖) (fun s => ?_)
  exact positive_vacuum_two_time_shifted_resolvent_static_root_bound
    ε hε h hh hb m g k hk s t a ha hxT hxK hxP

theorem positive_vacuum_two_time_shifted_resolvent_clockHalf_tendsto_zero (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    Tendsto (fun s : ℝ =>
      clockHalf ε ⟨x - RH t a (H s ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x),
        static_root_subset_clockHalf_domain ε hε h _
          ((Tstat).domain.sub_mem
            (KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨x, hxT⟩)
            (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
              ε hε h hh hb m g k t a ha _))⟩)
      (𝓝 t) (𝓝 0) := by
  let hxG := (unconditional_two_operator_growing_eval
    ε hε h hh hb m g k hxK hxP).choose
  refine tendsto_zero_norm_of_abs_exp_mul t
    (Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖G ⟨x, hxG⟩‖) (fun s => ?_)
  exact positive_vacuum_two_time_shifted_resolvent_clockHalf_bound
    ε hε h hh hb m g k hk s t a ha hxT hxK hxP

theorem positive_vacuum_two_time_shifted_resolvent_hamiltonian_tendsto (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    Tendsto (fun s : ℝ =>
      H t ⟨RH t a (H s ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x),
        (KFCausalClockFloorHamiltonianClockCore.resolves
          ε hε h hh hw m g k t a ha _).1⟩)
      (𝓝 t)
      (𝓝 (H t ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk t hxT hxK hxP).choose⟩)) := by
  let hxG := (unconditional_two_operator_growing_eval
    ε hε h hh hb m g k hxK hxP).choose
  apply tendsto_sub_nhds_zero_iff.mp
  refine tendsto_zero_norm_of_abs_exp_mul t ‖G ⟨x, hxG⟩‖ (fun s => ?_)
  rw [norm_sub_rev]
  exact (positive_vacuum_two_time_shifted_resolvent_hamiltonian_bound
    ε hε h hh hb m g k hk s t a ha hxT hxK hxP).1

theorem positive_vacuum_two_time_shifted_resolvent_radial_tendsto (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    Tendsto (fun s : ℝ =>
      K ⟨RH t a (H s ⟨x, (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x),
        (two_time_resolvent_all_domains ε hε h hh hb m g k t t a ha _).2.1⟩)
      (𝓝 t) (𝓝 (K ⟨x, hxK⟩)) := by
  let hxG := (unconditional_two_operator_growing_eval
    ε hε h hh hb m g k hxK hxP).choose
  let hRKG : RH t a (G ⟨x, hxG⟩) ∈ (K).domain :=
    KFCausalClockFloorHamiltonianComponentResolventBounds.resolvent_mem_radial_domain
      ε hε h hh hb m g k t a ha (G ⟨x, hxG⟩)
  apply tendsto_sub_nhds_zero_iff.mp
  refine tendsto_zero_norm_of_abs_exp_mul t ‖K ⟨RH t a (G ⟨x, hxG⟩), hRKG⟩‖ (fun s => ?_)
  rw [norm_sub_rev]
  exact (positive_vacuum_two_time_shifted_resolvent_radial_diff_norm_eq
    ε hε h hh hb m g k hk s t a ha hxT hxK hxP).le

theorem positive_vacuum_two_time_residual_shifted_resolvent_bound (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    let hxs := (positive_vacuum_three_operator_residual_eval
      ε hε h hh hb m g k hk s hxT hxK hxP).choose
    ‖x - RS t a (S s ⟨x, hxs⟩ + a • x)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖P ⟨x, hxP⟩‖) := by
  have hx : x ∈ commonOperatorDomain ε hε h hh hb m g k := by
    rw [positive_vacuum_common_domain_eq_three_operator ε hε h hh hb m g k hk]
    exact ⟨⟨hxT, hxK⟩, hxP⟩
  have hb1 := KFCausalClockFloorTwoTimeResolventDifference.residual_resolvent_two_time_norm_bound
    ε hε h hh hb m g k t s a ha x hx
  dsimp only
  exact hb1.trans_eq (by ring)

theorem positive_vacuum_two_time_residual_shifted_resolvent_tendsto (hk : 0 < k)
    (t a : ℝ) (ha : 0 < a) {x : Hilbert}
    (hxT : x ∈ (T).domain) (hxK : x ∈ (K).domain) (hxP : x ∈ (P).domain) :
    Tendsto (fun s : ℝ =>
      RS t a (S s ⟨x, (positive_vacuum_three_operator_residual_eval
        ε hε h hh hb m g k hk s hxT hxK hxP).choose⟩ + a • x))
      (𝓝 t) (𝓝 x) := by
  apply tendsto_sub_nhds_zero_iff.mp
  refine tendsto_zero_norm_of_abs_exp_mul t (a⁻¹ * ‖P ⟨x, hxP⟩‖) (fun s => ?_)
  rw [norm_sub_rev]
  exact positive_vacuum_two_time_residual_shifted_resolvent_bound
    ε hε h hh hb m g k hk s t a ha hxT hxK hxP

/-! ### 5. Unconditional Weak/Form Two-Time Resolvent Continuity and Strong Continuity on Dom G -/

theorem two_time_resolvent_symmetric_inner (t a : ℝ) (ha : 0 < a) (f1 f2 : Hilbert) :
    inner ℂ (RH t a f1) f2 = inner ℂ f1 (RH t a f2) := by
  have hsa := KFCausalPositiveResolventBounds.resolvent_selfAdjoint (H t) (RH t a) a
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_selfAdjoint ε hε h hh hw m g k t)
  exact hsa.isSymmetric f1 f2

theorem two_time_residual_resolvent_symmetric_inner (t a : ℝ) (ha : 0 < a) (f1 f2 : Hilbert) :
    inner ℂ (RS t a f1) f2 = inner ℂ f1 (RS t a f2) := by
  have hsa := KFCausalPositiveResolventBounds.resolvent_selfAdjoint (S t) (RS t a) a
    (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian_selfAdjoint ε hε h hh hw m g k t)
  exact hsa.isSymmetric f1 f2

theorem two_time_resolvent_weak_diff_bound (s t a : ℝ) (ha : 0 < a) (f1 f2 : Hilbert) :
    ‖inner ℂ f1 (RH s a f2 - RH t a f2)‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f1‖ * ‖f2‖) := by
  let hrt := KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha
  let hrs := KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha
  let xt := KFCausalPositiveResolventBounds.point (H t) (RH t a) a hrt f1
  let ys := KFCausalPositiveResolventBounds.point (H s) (RH s a) a hrs f2
  let ut := KFCausalClosedGraphForm.formLift (AD t) xt
  let us := KFCausalClosedGraphForm.formLift (AD s) ys
  let R := KFCausalClockFloorGrowingRadialMultiplierForm.rootOutput ε hε h hh hw m g k
  have hz : inner ℂ f1 (RH s a f2 - RH t a f2) =
      inner ℂ f1 (RH s a f2) - inner ℂ (RH t a f1) f2 :=
    (inner_sub_right f1 (RH s a f2) (RH t a f2)).trans
      (congrArg (fun w => inner ℂ f1 (RH s a f2) - w)
        (two_time_resolvent_symmetric_inner ε hε h hh hb m g k t a ha f1 f2).symm)
  have h1 := KFCausalClockFloorTwoTimeFormResolventComparison.hamiltonian_resolvent_two_time_pairing_difference
    ε hε h hh hb m g k t s a ha f1 f2 ut us
    (KFCausalClosedGraphForm.embedding_formLift (AD t) xt)
    (KFCausalClosedGraphForm.embedding_formLift (AD s) ys)
  have hRt : R (growingProject ε hε h hh hb m g k t ut) =
      Kroot ⟨RH t a f1, KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
        ε hε h hh hb m g k t a ha f1⟩ :=
    (Kroot).mem_graph_snd_inj'
      (KFCausalClockFloorGrowingRadialMultiplierForm.rootOutput_graph
        ε hε h hh hw m g k (growingProject ε hε h hh hb m g k t ut))
      ((Kroot).mem_graph _)
      ((KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding
        ε hε h hh hw m g k (FT t 0 ut)).trans
        ((KFCausalClockFloorAveragedFormTransport.transfer_embedding
          ε hε h hh hw m g k t 0 ut).trans
          (KFCausalClosedGraphForm.embedding_formLift (AD t) xt)))
  have hRs : R (growingProject ε hε h hh hb m g k s us) =
      Kroot ⟨RH s a f2, KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_radialRoot_domain
        ε hε h hh hb m g k s a ha f2⟩ :=
    (Kroot).mem_graph_snd_inj'
      (KFCausalClockFloorGrowingRadialMultiplierForm.rootOutput_graph
        ε hε h hh hw m g k (growingProject ε hε h hh hb m g k s us))
      ((Kroot).mem_graph _)
      ((KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding
        ε hε h hh hw m g k (FT s 0 us)).trans
        ((KFCausalClockFloorAveragedFormTransport.transfer_embedding
          ε hε h hh hw m g k s 0 us).trans
          (KFCausalClosedGraphForm.embedding_formLift (AD s) ys)))
  have hPt : PB (potentialLift ε hε h hh hw m g k t
      (KFCausalClockFloorTwoTimeFormTransfer.residualProject ε hε h hh hb m g k t ut)) =
      Tpot ⟨RH t a f1, KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_potentialForm_domain
        ε hε h hh hb m g k t a ha f1⟩ :=
    form_output_eq_operator PD _ (RH t a f1)
      ((potentialLift_embedding ε hε h hh hw m g k t _).trans
        ((KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding
          ε hε h hh hw m g k t (FT t 0 ut)).trans
          ((KFCausalClockFloorAveragedFormTransport.transfer_embedding
            ε hε h hh hw m g k t 0 ut).trans
            (KFCausalClosedGraphForm.embedding_formLift (AD t) xt))))
      (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_potentialForm_domain
        ε hε h hh hb m g k t a ha f1)
  have hPs : PB (potentialLift ε hε h hh hw m g k s
      (KFCausalClockFloorTwoTimeFormTransfer.residualProject ε hε h hh hb m g k s us)) =
      Tpot ⟨RH s a f2, KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_potentialForm_domain
        ε hε h hh hb m g k s a ha f2⟩ :=
    form_output_eq_operator PD _ (RH s a f2)
      ((potentialLift_embedding ε hε h hh hw m g k s _).trans
        ((KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding
          ε hε h hh hw m g k s (FT s 0 us)).trans
          ((KFCausalClockFloorAveragedFormTransport.transfer_embedding
            ε hε h hh hw m g k s 0 us).trans
            (KFCausalClosedGraphForm.embedding_formLift (AD s) ys))))
      (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_potentialForm_domain
        ε hε h hh hb m g k s a ha f2)
  exact weak_diff_bound_of_parts _ _ _ _ _ _ _ _ _ _ t s a ‖f1‖ ‖f2‖ ha (norm_nonneg f1)
    hz h1 hRt hRs hPt hPs
    (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_radialRoot_norm_le
      ε hε h hh hb m g k t a ha f1)
    (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_radialRoot_norm_le
      ε hε h hh hb m g k s a ha f2)
    (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_potentialForm_norm_le
      ε hε h hh hb m g k t a ha f1)
    (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_potentialForm_norm_le
      ε hε h hh hb m g k s a ha f2)

theorem two_time_resolvent_weak_diff_tendsto_zero (t a : ℝ) (ha : 0 < a) (f1 f2 : Hilbert) :
    Tendsto (fun s : ℝ => inner ℂ f1 (RH s a f2 - RH t a f2)) (𝓝 t) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  let B : ℝ → ℝ := fun s =>
    |Real.exp (2 * t) - Real.exp (2 * s)| *
      (2 * Real.exp (-(t + s)) * a⁻¹ * ‖f1‖ * ‖f2‖)
  have hB_cont : Continuous B := by fun_prop
  have hB0 : B t = 0 := by simp [B]
  have hB_lim : Tendsto B (𝓝 t) (𝓝 0) := hB0 ▸ hB_cont.tendsto t
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB_lim
    (fun s => norm_nonneg _)
    (fun s => two_time_resolvent_weak_diff_bound ε hε h hh hb m g k s t a ha f1 f2)

theorem two_time_resolvent_weak_continuous (t a : ℝ) (ha : 0 < a) (f1 f2 : Hilbert) :
    Tendsto (fun s : ℝ => inner ℂ f1 (RH s a f2)) (𝓝 t) (𝓝 (inner ℂ f1 (RH t a f2))) := by
  apply tendsto_sub_nhds_zero_iff.mp
  have h := two_time_resolvent_weak_diff_tendsto_zero ε hε h hh hb m g k t a ha f1 f2
  exact h.congr' (Eventually.of_forall (fun s => inner_sub_right f1 (RH s a f2) (RH t a f2)))

theorem positive_vacuum_two_time_second_resolvent_bounds_on_growing_domain (hk : 0 < k)
    (s t a : ℝ) (ha : 0 < a) (f : Hilbert) (hG : RH s a f ∈ (G).domain) :
    let hHt := (positive_vacuum_two_time_second_resolvent_on_growing_domain
      ε hε h hh hb m g k hk s t a ha f hG).1
    let hdC : RH s a f - RH t a f ∈ (clockHalf ε).domain :=
      (clockHalf ε).domain.sub_mem
        (resolvent_in_clockHalf_domain ε hε h hh hb m g k s a ha f)
        (resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f)
    ‖RH s a f - RH t a f‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * (a⁻¹ * ‖G ⟨RH s a f, hG⟩‖) ∧
    ‖clockHalf ε ⟨RH s a f - RH t a f, hdC⟩‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| *
        (Real.sqrt 2 * Real.sqrt (a⁻¹) * ‖G ⟨RH s a f, hG⟩‖) ∧
    ‖H t ⟨RH s a f, hHt⟩ -
        H t ⟨RH t a f, (KFCausalClockFloorHamiltonianClockCore.resolves
          ε hε h hh hw m g k t a ha f).1⟩‖ ≤
      |Real.exp (2 * t) - Real.exp (2 * s)| * ‖G ⟨RH s a f, hG⟩‖ := by
  have hHs : RH s a f ∈ (H s).domain :=
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha f).1
  have htr := positive_vacuum_hamiltonian_growing_two_time_transfer
    ε hε h hh hb m g k hk s t hHs hG
  have hres : H s ⟨RH s a f, hHs⟩ + a • RH s a f = f := by
    rw [(KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha f).2]
    abel
  have hb_hilb := (positive_vacuum_two_time_shifted_resolvent_hilbert_bound
    ε hε h hh hb m g k hk s t a ha htr.1 htr.2.1 htr.2.2.1).1
  have hb_clock := positive_vacuum_two_time_shifted_resolvent_clockHalf_bound
    ε hε h hh hb m g k hk s t a ha htr.1 htr.2.1 htr.2.2.1
  have hb_ham := (positive_vacuum_two_time_shifted_resolvent_hamiltonian_bound
    ε hε h hh hb m g k hk s t a ha htr.1 htr.2.1 htr.2.2.1).1
  dsimp only at hb_hilb hb_clock hb_ham ⊢
  have hval : H s ⟨RH s a f,
      (positive_vacuum_three_operator_hamiltonian_eval
        ε hε h hh hb m g k hk s htr.1 htr.2.1 htr.2.2.1).choose⟩ + a • RH s a f = f := hres
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hval] using hb_hilb
  · have heq : clockHalf ε ⟨RH s a f - RH t a f,
        (clockHalf ε).domain.sub_mem
          (resolvent_in_clockHalf_domain ε hε h hh hb m g k s a ha f)
          (resolvent_in_clockHalf_domain ε hε h hh hb m g k t a ha f)⟩ =
        clockHalf ε ⟨RH s a f - RH t a (H s ⟨RH s a f,
          (positive_vacuum_three_operator_hamiltonian_eval
            ε hε h hh hb m g k hk s htr.1 htr.2.1 htr.2.2.1).choose⟩ + a • RH s a f),
          static_root_subset_clockHalf_domain ε hε h _
            ((Tstat).domain.sub_mem
              (KFCausalClockFloorStaticOperator.root_domain ε hε h ⟨_, htr.1⟩)
              (KFCausalClockFloorHamiltonianResolventFormBounds.hamiltonian_resolvent_mem_staticRoot_domain
                ε hε h hh hb m g k t a ha _))⟩ := by
      apply (clockHalf ε).mem_graph_snd_inj'
        ((clockHalf ε).mem_graph _) ((clockHalf ε).mem_graph _)
      change RH s a f - RH t a f = RH s a f - RH t a (H s ⟨RH s a f, _⟩ + a • RH s a f)
      rw [hval]
    rw [heq]
    exact hb_clock
  · have heq : H t ⟨RH t a f,
        (KFCausalClockFloorHamiltonianClockCore.resolves
          ε hε h hh hw m g k t a ha f).1⟩ =
        H t ⟨RH t a (H s ⟨RH s a f,
          (positive_vacuum_three_operator_hamiltonian_eval
            ε hε h hh hb m g k hk s htr.1 htr.2.1 htr.2.2.1).choose⟩ + a • RH s a f),
          (KFCausalClockFloorHamiltonianClockCore.resolves
            ε hε h hh hw m g k t a ha _).1⟩ := by
      apply (H t).mem_graph_snd_inj' ((H t).mem_graph _) ((H t).mem_graph _)
      change RH t a f = RH t a (H s ⟨RH s a f, _⟩ + a • RH s a f)
      rw [hval]
    rw [heq]
    exact hb_ham

#print axioms two_time_exp_diff_tendsto_zero
#print axioms resolvent_in_clockHalf_domain
#print axioms resolvent_clockHalf_norm_sq_bound
#print axioms resolvent_clockHalf_norm_bound
#print axioms residual_resolvent_in_clockHalf_domain
#print axioms residual_resolvent_clockHalf_norm_sq_bound
#print axioms residual_resolvent_clockHalf_norm_bound
#print axioms two_time_residual_form_energy_diff_eq
#print axioms two_time_residual_form_energy_tendsto_zero
#print axioms two_time_averaged_form_energy_diff_eq
#print axioms two_time_averaged_form_energy_tendsto_zero
#print axioms positive_vacuum_two_time_averaged_form_energy_tendsto_zero
#print axioms positive_vacuum_two_time_residual_diff_norm_eq
#print axioms positive_vacuum_two_time_hamiltonian_diff_norm_eq
#print axioms positive_vacuum_two_time_residual_tendsto_zero
#print axioms positive_vacuum_two_time_residual_continuous
#print axioms positive_vacuum_two_time_hamiltonian_tendsto_zero
#print axioms positive_vacuum_two_time_hamiltonian_continuous
#print axioms positive_vacuum_two_time_shifted_resolvent_hilbert_bound
#print axioms positive_vacuum_two_time_shifted_resolvent_static_root_bound
#print axioms positive_vacuum_two_time_shifted_resolvent_clockHalf_bound
#print axioms positive_vacuum_two_time_shifted_resolvent_hamiltonian_bound
#print axioms positive_vacuum_two_time_shifted_resolvent_radial_diff_norm_eq
#print axioms positive_vacuum_two_time_shifted_resolvent_tendsto
#print axioms positive_vacuum_two_time_shifted_resolvent_static_root_tendsto_zero
#print axioms positive_vacuum_two_time_shifted_resolvent_clockHalf_tendsto_zero
#print axioms positive_vacuum_two_time_shifted_resolvent_hamiltonian_tendsto
#print axioms positive_vacuum_two_time_shifted_resolvent_radial_tendsto
#print axioms positive_vacuum_two_time_residual_shifted_resolvent_bound
#print axioms positive_vacuum_two_time_residual_shifted_resolvent_tendsto
#print axioms two_time_resolvent_symmetric_inner
#print axioms two_time_residual_resolvent_symmetric_inner
#print axioms two_time_resolvent_weak_diff_bound
#print axioms two_time_resolvent_weak_diff_tendsto_zero
#print axioms two_time_resolvent_weak_continuous
#print axioms positive_vacuum_two_time_second_resolvent_bounds_on_growing_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumTwoTimeResolventContinuity
