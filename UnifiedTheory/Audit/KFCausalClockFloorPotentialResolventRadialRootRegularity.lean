/- Unconditional radial square-root (`Dom(K_root)`) and growing-form (`Dom(T_grow)`)
regularity of the positive potential resolvent `R_P(a) = (P + a)⁻¹` (`a > 0`) on
the full strip `|h| ≤ π * ε / 3` for all real couplings `m, g, k`:
1. Proves `0 ≤ Re ⟨M_N^(1/2) (P x), M_N^(1/2) x⟩` and the shifted coercive bound
   `a * ‖M_N^(1/2) x‖² ≤ Re ⟨M_N^(1/2) (P x + a x), M_N^(1/2) x⟩` for all `x ∈ Dom(P)`.
2. Proves the unconditional contraction `‖M_N^(1/2) (R_P(a) f)‖ ≤ a⁻¹ * ‖M_N^(1/2) f‖`
   for all `f : Hilbert` on the full strip `|h| ≤ π * ε / 3`.
3. Deduces that for every `f ∈ Dom(K_root)` and `a > 0`, `R_P(a) f` lies in
   `Dom(K_root)`, `Dom(T_pot)`, and `Dom(T_grow) = Dom(K_root) ∩ Dom(T_pot)` with
   `‖K_root (R_P(a) f)‖ ≤ a⁻¹ * ‖K_root f‖`,
   `‖T_pot (R_P(a) f)‖² ≤ a⁻¹ * ‖f‖²`, and
   `‖T_grow (R_P(a) f)‖² ≤ (a⁻¹)² * ‖K_root f‖² + a⁻¹ * ‖f‖²`. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialRadialYosidaAccretivity
import UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventRadialRegularity
import UnifiedTheory.Audit.KFCausalClockFloorResidualResolventRadialRootRegularity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventRadialRootRegularity
noncomputable section
open scoped InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator rootOutput rootOutput_graph)
open KFCausalClockFloorPotentialHamiltonian (growingLift growingLift_embedding)
open KFCausalClockFloorRadialResolventGrowing (growing_output_norm_sq)
open KFCausalClockFloorGrowingFormReconstruction (growing_domain_iff)
open KFCausalClockFloorPotentialRadialYosidaAccretivity (potential_yosida_accretive)
open KFCausalClockFloorPotentialResolventRadialRegularity (resolvent_yosida_inner_le)
open KFCausalClockFloorResidualResolventRadialRootRegularity
  (yosidaRootAction yosidaRootAction_selfAdjoint_pairing
    yosidaRootAction_sq_eq_yosida yosidaRootAction_sq_inner
    yosidaRootAction_norm_sq_eq_inner yosidaRootAction_norm_le_rootOperator
    root_domain_of_uniform_bound root_norm_of_uniform_bound)
open KFCausalClockFloorPotentialClockResolvent (resolvent resolves)
open KFCausalPositiveResolventBounds (point point_value resolvent_apply_norm_bound)

private theorem form_output_eq_operator
    (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (w : KFCausalClosedGraphForm.FormSpace D) (f : Hilbert)
    (hJ : KFCausalClosedGraphForm.embedding D w = f) (hf : f ∈ D.operator.domain) :
    KFCausalClosedGraphForm.energyOutput D w = D.operator ⟨f, hf⟩ :=
  D.operator.mem_graph_snd_inj' w.property (D.operator.mem_graph ⟨f, hf⟩) hJ

private theorem resolvent_pairing_eq {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ)
    (hr : KFCausalPositiveResolventBounds.Resolves T R a) (f : H) :
    (inner ℂ (T (point T R a hr f)) (R f)).re + a * ‖R f‖ ^ 2 =
      (inner ℂ f (R f)).re := by
  have hv := point_value T R a hr f
  rw [hv, inner_sub_left, inner_smul_left_eq_smul,
    KFCausalShiftedForm.complex_inner_square (R f)]
  simp only [Complex.sub_re, Complex.real_smul, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

private theorem resolvent_pairing_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves T R a)
    (hp : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (x : H)).re) (f : H) :
    (inner ℂ (T (point T R a hr f)) (R f)).re + a * ‖R f‖ ^ 2 ≤
      a⁻¹ * ‖f‖ ^ 2 := by
  rw [resolvent_pairing_eq T R a hr f]
  have hi : (inner ℂ f (R f)).re ≤ ‖f‖ * ‖R f‖ := re_inner_le_norm (𝕜 := ℂ) f (R f)
  have hnorm := resolvent_apply_norm_bound T R a ha hr hp f
  have hmul : ‖f‖ * ‖R f‖ ≤ ‖f‖ * (a⁻¹ * ‖f‖) :=
    mul_le_mul_of_nonneg_left hnorm (norm_nonneg f)
  linarith [show ‖f‖ * (a⁻¹ * ‖f‖) = a⁻¹ * ‖f‖ ^ 2 by ring]

private theorem bound_of_sq_accretive
    (T : Hilbert →ₗ.[ℂ] Hilbert) (R_a : Hilbert →L[ℂ] Hilbert) (a : ℝ) (ha : 0 < a)
    (hr : KFCausalPositiveResolventBounds.Resolves T R_a a)
    (S : Hilbert →L[ℂ] Hilbert)
    (hS_symm : ∀ u v : Hilbert, inner ℂ u (S v) = inner ℂ (S u) v)
    (hS_acc : ∀ x : T.domain, 0 ≤ (inner ℂ (T x) (S (S (x : Hilbert)))).re)
    (f : Hilbert) :
    ‖S (R_a f)‖ ≤ a⁻¹ * ‖S f‖ := by
  have hp := hS_acc (point T R_a a hr f)
  change 0 ≤ (inner ℂ (T (point T R_a a hr f)) (S (S (R_a f)))).re at hp
  rw [point_value, inner_sub_left, inner_smul_left_eq_smul,
    hS_symm f (S (R_a f)), hS_symm (R_a f) (S (R_a f)),
    KFCausalShiftedForm.complex_inner_square] at hp
  simp only [Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hp
  have hl : a * ‖S (R_a f)‖ ^ 2 ≤ (inner ℂ (S f) (S (R_a f))).re := by
    nlinarith
  by_cases hz : S (R_a f) = 0
  · rw [hz, norm_zero]
    positivity
  have hn : 0 < ‖S (R_a f)‖ := norm_pos_iff.mpr hz
  apply (le_inv_mul_iff₀ ha).mpr
  apply (mul_le_mul_iff_right₀ hn).mp
  have hi : (inner ℂ (S f) (S (R_a f))).re ≤ ‖S f‖ * ‖S (R_a f)‖ :=
    re_inner_le_norm (𝕜 := ℂ) (S f) (S (R_a f))
  nlinarith

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
  (hb : |h| ≤ Real.pi * ε / 3) (hh : h ≠ 0) (m g k : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN
local notation "Mroot" => yosidaRootAction ε hε h N hN
local notation "Kroot" => rootOperator ε hε h
local notation "Rroot" => rootOutput ε hε h hh hw m g k
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "PJ" => KFCausalClosedGraphForm.embedding PD
local notation "PB" => KFCausalClosedGraphForm.energyOutput PD
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "RP" => resolvent ε hε h hh hw m g k

/-! ### 1. Potential Form Energy and Growing Form Split -/

theorem potential_mem_potentialForm_domain (x : (P).domain) :
    (x : Hilbert) ∈ (Tpot).domain := by
  let u := KFCausalClosedGraphForm.formLift PD x
  have hJ : PJ u = (x : Hilbert) := KFCausalClosedGraphForm.embedding_formLift PD x
  exact hJ ▸ LinearPMap.mem_domain_of_mem_graph u.property

theorem potential_form_energy_eq_potentialOutput (x : (P).domain) :
    (inner ℂ (P x) (x : Hilbert)).re =
      ‖Tpot ⟨(x : Hilbert), potential_mem_potentialForm_domain ε hε h hb hh m g k x⟩‖ ^ 2 := by
  let u := KFCausalClosedGraphForm.formLift PD x
  have hout := form_output_eq_operator PD u (x : Hilbert)
    (KFCausalClosedGraphForm.embedding_formLift PD x)
    (potential_mem_potentialForm_domain ε hε h hb hh m g k x)
  exact (KFCausalClosedGraphForm.hamiltonian_energy PD x).trans
    (congrArg (fun y : EnergyOutputSpace => ‖y‖ ^ 2) hout)

theorem growingForm_norm_sq_eq_radialRoot_add_potentialForm
    (f : Hilbert) (hf : f ∈ (Tgrow).domain) :
    ‖Tgrow ⟨f, hf⟩‖ ^ 2 =
      ‖Kroot ⟨f, ((growing_domain_iff ε hε h hh hb m g k f).mp hf).1⟩‖ ^ 2 +
        ‖Tpot ⟨f, ((growing_domain_iff ε hε h hh hb m g k f).mp hf).2⟩‖ ^ 2 := by
  let hr := ((growing_domain_iff ε hε h hh hb m g k f).mp hf).1
  let hp := ((growing_domain_iff ε hε h hh hb m g k f).mp hf).2
  let u := KFCausalClosedGraphForm.graphVector GD ⟨f, hf⟩
  have hGJ : GJ u = f := KFCausalClosedGraphForm.graphVector_embedding GD ⟨f, hf⟩
  have hGB : GB u = Tgrow ⟨f, hf⟩ := KFCausalClosedGraphForm.graphVector_output GD ⟨f, hf⟩
  have hR : Rroot u = Kroot ⟨f, hr⟩ :=
    (Kroot).mem_graph_snd_inj' (rootOutput_graph ε hε h hh hw m g k u)
      ((Kroot).mem_graph ⟨f, hr⟩) hGJ
  have hPJ : PJ (growingLift ε hε h hh hw m g k u) = f :=
    (growingLift_embedding ε hε h hh hw m g k u).trans hGJ
  have hPB : PB (growingLift ε hε h hh hw m g k u) = Tpot ⟨f, hp⟩ :=
    form_output_eq_operator PD (growingLift ε hε h hh hw m g k u) f hPJ hp
  have hnorm := growing_output_norm_sq ε hε h hb hh m g k u
  rw [hGB, hR, hPB] at hnorm
  exact hnorm

/-! ### 2. Radial Yosida Square-Root Accretivity on Dom(P) -/

theorem potential_yosidaRoot_pairing_eq (x : (P).domain) :
    inner ℂ (Mroot (P x)) (Mroot (x : Hilbert)) =
      inner ℂ (P x) (M (x : Hilbert)) :=
  yosidaRootAction_sq_inner ε hε h N hN (P x) (x : Hilbert)

theorem potential_yosidaRoot_accretive (x : (P).domain) :
    0 ≤ (inner ℂ (Mroot (P x)) (Mroot (x : Hilbert))).re := by
  rw [potential_yosidaRoot_pairing_eq ε hε h N hN hb hh m g k x]
  exact potential_yosida_accretive ε hε h N hN hb hh m g k x

theorem potential_shifted_yosidaRoot_lower (a : ℝ) (x : (P).domain) :
    a * ‖Mroot (x : Hilbert)‖ ^ 2 ≤
      (inner ℂ (Mroot (P x + (a : ℂ) • (x : Hilbert))) (Mroot (x : Hilbert))).re := by
  have hacc := potential_yosidaRoot_accretive ε hε h N hN hb hh m g k x
  rw [map_add, map_smul, inner_add_left, inner_smul_left,
    KFCausalShiftedForm.complex_inner_square]
  simp only [Complex.add_re, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  linarith

theorem potential_shifted_yosidaRoot_norm_le (a : ℝ) (ha : 0 < a) (x : (P).domain) :
    ‖Mroot (x : Hilbert)‖ ≤ a⁻¹ * ‖Mroot (P x + (a : ℂ) • (x : Hilbert))‖ := by
  by_cases hz : Mroot (x : Hilbert) = 0
  · rw [hz, norm_zero]
    positivity
  have hn : 0 < ‖Mroot (x : Hilbert)‖ := norm_pos_iff.mpr hz
  apply (le_inv_mul_iff₀ ha).mpr
  apply (mul_le_mul_iff_right₀ hn).mp
  have hlow := potential_shifted_yosidaRoot_lower ε hε h N hN hb hh m g k a x
  have hcs : (inner ℂ (Mroot (P x + (a : ℂ) • (x : Hilbert))) (Mroot (x : Hilbert))).re ≤
      ‖Mroot (P x + (a : ℂ) • (x : Hilbert))‖ * ‖Mroot (x : Hilbert)‖ :=
    re_inner_le_norm (𝕜 := ℂ)
      (Mroot (P x + (a : ℂ) • (x : Hilbert))) (Mroot (x : Hilbert))
  nlinarith

/-! ### 3. Unconditional Full-Strip Radial Square-Root Regularity of RP(a) -/

def potentialResolventPoint (a : ℝ) (ha : 0 < a) (f : Hilbert) : (P).domain :=
  point P (RP a) a (resolves ε hε h hh hw m g k a ha) f

theorem potential_resolvent_yosidaRoot_inner_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    a * ‖Mroot (RP a f)‖ ^ 2 ≤
      (inner ℂ (Mroot f) (Mroot (RP a f))).re := by
  rw [yosidaRootAction_norm_sq_eq_inner ε hε h N hN (RP a f),
    yosidaRootAction_sq_inner ε hε h N hN f (RP a f)]
  exact resolvent_yosida_inner_le ε hε h N hN hb hh m g k a ha f

theorem potential_resolvent_yosidaRoot_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Mroot (RP a f)‖ ≤ a⁻¹ * ‖Mroot f‖ :=
  bound_of_sq_accretive P (RP a) a ha
    (resolves ε hε h hh hw m g k a ha) Mroot
    (fun u v => (yosidaRootAction_selfAdjoint_pairing ε hε h N hN u v).symm)
    (fun x => by
      rw [yosidaRootAction_sq_eq_yosida ε hε h N hN (x : Hilbert)]
      exact potential_yosida_accretive ε hε h N hN hb hh m g k x) f

theorem potential_resolvent_output_yosidaRoot_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Mroot (P (potentialResolventPoint ε hε h hb hh m g k a ha f))‖ ≤
      2 * ‖Mroot f‖ := by
  have hv : P (potentialResolventPoint ε hε h hb hh m g k a ha f) = f - a • RP a f :=
    point_value P (RP a) a (resolves ε hε h hh hw m g k a ha) f
  rw [hv, ← Complex.coe_smul, map_sub, map_smul]
  have h1 : ‖Mroot f - (a : ℂ) • Mroot (RP a f)‖ ≤
      ‖Mroot f‖ + ‖(a : ℂ) • Mroot (RP a f)‖ :=
    norm_sub_le _ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at h1
  have hr := potential_resolvent_yosidaRoot_norm_le ε hε h N hN hb hh m g k a ha f
  have h2 : a * ‖Mroot (RP a f)‖ ≤ ‖Mroot f‖ := by
    calc
      a * ‖Mroot (RP a f)‖ ≤ a * (a⁻¹ * ‖Mroot f‖) :=
        mul_le_mul_of_nonneg_left hr ha.le
      _ = (a * a⁻¹) * ‖Mroot f‖ := by ring
      _ = ‖Mroot f‖ := by rw [mul_inv_cancel₀ ha.ne', one_mul]
  linarith

theorem potential_resolvent_yosidaRoot_norm_le_rootOperator
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Mroot (RP a f)‖ ≤ a⁻¹ * ‖Kroot ⟨f, hf⟩‖ :=
  (potential_resolvent_yosidaRoot_norm_le ε hε h N hN hb hh m g k a ha f).trans
    (mul_le_mul_of_nonneg_left
      (yosidaRootAction_norm_le_rootOperator ε hε h N hN f hf)
      (inv_nonneg.mpr ha.le))

theorem potential_resolvent_mem_radialRoot_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    RP a f ∈ (Kroot).domain :=
  root_domain_of_uniform_bound ε hε h (RP a f) (a⁻¹ * ‖Kroot ⟨f, hf⟩‖)
    (fun n => potential_resolvent_yosidaRoot_norm_le_rootOperator
      ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k a ha f hf)

theorem potential_resolvent_radialRoot_norm_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Kroot ⟨RP a f,
      potential_resolvent_mem_radialRoot_domain ε hε h hb hh m g k a ha f hf⟩‖ ≤
      a⁻¹ * ‖Kroot ⟨f, hf⟩‖ :=
  root_norm_of_uniform_bound ε hε h (RP a f) (a⁻¹ * ‖Kroot ⟨f, hf⟩‖)
    (fun n => potential_resolvent_yosidaRoot_norm_le_rootOperator
      ε hε h ((n : ℝ) + 1) (by positivity) hb hh m g k a ha f hf)

theorem potential_resolvent_mem_radialRoot_inter_potential_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    RP a f ∈ (Kroot).domain ⊓ (P).domain :=
  ⟨potential_resolvent_mem_radialRoot_domain ε hε h hb hh m g k a ha f hf,
    (potentialResolventPoint ε hε h hb hh m g k a ha f).property⟩

theorem potential_resolvent_mem_potentialForm_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    RP a f ∈ (Tpot).domain :=
  potential_mem_potentialForm_domain ε hε h hb hh m g k
    (potentialResolventPoint ε hε h hb hh m g k a ha f)

theorem potential_resolvent_pairing_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    (inner ℂ (P (potentialResolventPoint ε hε h hb hh m g k a ha f)) (RP a f)).re +
      a * ‖RP a f‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 :=
  resolvent_pairing_le P (RP a) a ha
    (resolves ε hε h hh hw m g k a ha)
    (KFCausalClosedGraphForm.hamiltonian_positive PD) f

theorem potential_resolvent_energy_add_scaled_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tpot ⟨RP a f,
      potential_resolvent_mem_potentialForm_domain ε hε h hb hh m g k a ha f⟩‖ ^ 2 +
      a * ‖RP a f‖ ^ 2 ≤ a⁻¹ * ‖f‖ ^ 2 := by
  have heq := potential_form_energy_eq_potentialOutput ε hε h hb hh m g k
    (potentialResolventPoint ε hε h hb hh m g k a ha f)
  have hle := potential_resolvent_pairing_le ε hε h hb hh m g k a ha f
  change (inner ℂ (P (potentialResolventPoint ε hε h hb hh m g k a ha f)) (RP a f)).re =
    ‖Tpot ⟨RP a f,
      potential_resolvent_mem_potentialForm_domain ε hε h hb hh m g k a ha f⟩‖ ^ 2 at heq
  linarith

theorem potential_resolvent_potentialForm_norm_sq_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tpot ⟨RP a f,
      potential_resolvent_mem_potentialForm_domain ε hε h hb hh m g k a ha f⟩‖ ^ 2 ≤
      a⁻¹ * ‖f‖ ^ 2 := by
  have hle := potential_resolvent_energy_add_scaled_sq_le ε hε h hb hh m g k a ha f
  have ha0 : 0 ≤ a * ‖RP a f‖ ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  linarith

theorem potential_resolvent_potentialForm_norm_le (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖Tpot ⟨RP a f,
      potential_resolvent_mem_potentialForm_domain ε hε h hb hh m g k a ha f⟩‖ ≤
      Real.sqrt (a⁻¹) * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mp
  rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr ha.le)]
  exact potential_resolvent_potentialForm_norm_sq_le ε hε h hb hh m g k a ha f

theorem potential_resolvent_mem_growingForm_domain
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    RP a f ∈ (Tgrow).domain :=
  (growing_domain_iff ε hε h hh hb m g k (RP a f)).mpr
    ⟨potential_resolvent_mem_radialRoot_domain ε hε h hb hh m g k a ha f hf,
      potential_resolvent_mem_potentialForm_domain ε hε h hb hh m g k a ha f⟩

theorem potential_resolvent_growingForm_norm_sq_eq
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Tgrow ⟨RP a f,
      potential_resolvent_mem_growingForm_domain ε hε h hb hh m g k a ha f hf⟩‖ ^ 2 =
      ‖Kroot ⟨RP a f,
        potential_resolvent_mem_radialRoot_domain ε hε h hb hh m g k a ha f hf⟩‖ ^ 2 +
      ‖Tpot ⟨RP a f,
        potential_resolvent_mem_potentialForm_domain ε hε h hb hh m g k a ha f⟩‖ ^ 2 :=
  growingForm_norm_sq_eq_radialRoot_add_potentialForm ε hε h hb hh m g k (RP a f)
    (potential_resolvent_mem_growingForm_domain ε hε h hb hh m g k a ha f hf)

theorem potential_resolvent_growingForm_norm_sq_le
    (a : ℝ) (ha : 0 < a) (f : Hilbert) (hf : f ∈ (Kroot).domain) :
    ‖Tgrow ⟨RP a f,
      potential_resolvent_mem_growingForm_domain ε hε h hb hh m g k a ha f hf⟩‖ ^ 2 ≤
      (a⁻¹) ^ 2 * ‖Kroot ⟨f, hf⟩‖ ^ 2 + a⁻¹ * ‖f‖ ^ 2 := by
  rw [potential_resolvent_growingForm_norm_sq_eq ε hε h hb hh m g k a ha f hf]
  have h1 : ‖Kroot ⟨RP a f,
      potential_resolvent_mem_radialRoot_domain ε hε h hb hh m g k a ha f hf⟩‖ ^ 2 ≤
      (a⁻¹ * ‖Kroot ⟨f, hf⟩‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      (potential_resolvent_radialRoot_norm_le ε hε h hb hh m g k a ha f hf) 2
  rw [mul_pow] at h1
  have h2 := potential_resolvent_potentialForm_norm_sq_le ε hε h hb hh m g k a ha f
  exact add_le_add h1 h2

#print axioms potential_mem_potentialForm_domain
#print axioms potential_form_energy_eq_potentialOutput
#print axioms growingForm_norm_sq_eq_radialRoot_add_potentialForm
#print axioms potential_yosidaRoot_pairing_eq
#print axioms potential_yosidaRoot_accretive
#print axioms potential_shifted_yosidaRoot_lower
#print axioms potential_shifted_yosidaRoot_norm_le
#print axioms potential_resolvent_yosidaRoot_inner_le
#print axioms potential_resolvent_yosidaRoot_norm_le
#print axioms potential_resolvent_output_yosidaRoot_norm_le
#print axioms potential_resolvent_yosidaRoot_norm_le_rootOperator
#print axioms potential_resolvent_mem_radialRoot_domain
#print axioms potential_resolvent_radialRoot_norm_le
#print axioms potential_resolvent_mem_radialRoot_inter_potential_domain
#print axioms potential_resolvent_mem_potentialForm_domain
#print axioms potential_resolvent_pairing_le
#print axioms potential_resolvent_energy_add_scaled_sq_le
#print axioms potential_resolvent_potentialForm_norm_sq_le
#print axioms potential_resolvent_potentialForm_norm_le
#print axioms potential_resolvent_mem_growingForm_domain
#print axioms potential_resolvent_growingForm_norm_sq_eq
#print axioms potential_resolvent_growingForm_norm_sq_le
end
end UnifiedTheory.Audit.KFCausalClockFloorPotentialResolventRadialRootRegularity
