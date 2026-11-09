/- Form-core topological closure invariance, two-sided evolved energy-output
difference bounds, five-channel difference estimates, and simultaneous
multi-channel sequence convergence under the two-time form evolution
isomorphism `formEvolution s t : VT s ≃L[ℂ] VT t`. -/
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeFormEvolutionIsomorphism
import UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumHamiltonianGaussianCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorEvolvedFormCoreInvariance

noncomputable section

open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorAveragedFormTransport
  (FormSpace embedding energyOutput form_norm_identity
   formTransfer transfer_embedding transfer_inverse transfer_comp)
open KFCausalClockFloorAveragedEvolution (evolution evolution_norm)
open KFCausalClockFloorTwoTimeFormEvolutionIsomorphism

private theorem right_le_of_eq_add {a b c : ℝ} (h : c = a + b) (ha : 0 ≤ a) : b ≤ c := by
  linarith

private theorem unscale_reverse_exp_dist {s t r a b : ℝ}
    (h : a ≤ Real.exp (2 * (|s - r| + |s - t|)) * b) :
    Real.exp (-2 * (|s - r| + |t - s|)) * a ≤ b := by
  rw [abs_sub_comm s t] at h
  have hm := mul_le_mul_of_nonneg_left h
    (Real.exp_pos (-2 * (|s - r| + |t - s|))).le
  have hexp :
      Real.exp (-2 * (|s - r| + |t - s|)) *
        (Real.exp (2 * (|s - r| + |t - s|)) * b) = b := by
    rw [← mul_assoc, ← Real.exp_add,
      show -2 * (|s - r| + |t - s|) + 2 * (|s - r| + |t - s|) = 0 by ring,
      Real.exp_zero, one_mul]
  rwa [hexp] at hm

private theorem form_output_eq_operator
    (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (w : KFCausalClosedGraphForm.FormSpace D) (f : Hilbert)
    (hJ : KFCausalClosedGraphForm.embedding D w = f) (hf : f ∈ D.operator.domain) :
    KFCausalClosedGraphForm.energyOutput D w = D.operator ⟨f, hf⟩ :=
  D.operator.mem_graph_snd_inj' w.property (D.operator.mem_graph ⟨f, hf⟩) hJ

private theorem pmap_sub_norm_sq_eq {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (A : Hilbert →ₗ.[ℂ] Y) {x y z : Hilbert} (hxyz : z = x - y)
    (hx : x ∈ A.domain) (hy : y ∈ A.domain) (hz : z ∈ A.domain) :
    ‖A ⟨x, hx⟩ - A ⟨y, hy⟩‖ ^ 2 = ‖A ⟨z, hz⟩‖ ^ 2 := by
  have hval : A ⟨z, hz⟩ = A ⟨x, hx⟩ - A ⟨y, hy⟩ :=
    A.mem_graph_snd_inj' (A.mem_graph ⟨z, hz⟩)
      (A.graph.sub_mem (A.mem_graph ⟨x, hx⟩) (A.mem_graph ⟨y, hy⟩)) hxyz
  exact congrArg (fun v : Y => ‖v‖ ^ 2) hval.symm

private theorem tendsto_of_norm_sub_sq_le {X Y : Type*}
    [SeminormedAddCommGroup X] [NormedAddCommGroup Y]
    {u_seq : ℕ → X} {u : X} (hu : Tendsto u_seq atTop (𝓝 u))
    {B : ℕ → Y} {b : Y} (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ‖B n - b‖ ^ 2 ≤ C * ‖u_seq n - u‖ ^ 2) :
    Tendsto B atTop (𝓝 b) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hu0 : Tendsto (fun n : ℕ => ‖u_seq n - u‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hu
  have hlim : Tendsto (fun n : ℕ => Real.sqrt C * ‖u_seq n - u‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hu0.const_mul (Real.sqrt C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => norm_nonneg (B n - b)) (fun n => ?_)
  have h1 := Real.sqrt_le_sqrt (hb n)
  have hrew : C * ‖u_seq n - u‖ ^ 2 = (Real.sqrt C * ‖u_seq n - u‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
  have hnonneg : 0 ≤ Real.sqrt C * ‖u_seq n - u‖ :=
    mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _)
  rw [hrew, Real.sqrt_sq (norm_nonneg (B n - b)), Real.sqrt_sq hnonneg] at h1
  exact h1

/-! ### 1. Abstract Continuous Linear Equivalence Submodule Closure Invariance -/

section SubmoduleClosureEquiv

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
  [SeminormedAddCommGroup F] [NormedSpace ℂ F]

/-- Mapping a submodule `M` by `e : E ≃L[ℂ] F` coincides with its preimage under `e.symm`. -/
theorem submodule_map_eq_comap_symm (e : E ≃L[ℂ] F) (M : Submodule ℂ E) :
    M.map e.toLinearMap = M.comap e.symm.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e.symm (e x) ∈ M
    rwa [e.symm_apply_apply]
  · intro hy
    change e.symm y ∈ M at hy
    exact ⟨e.symm y, hy, e.apply_symm_apply y⟩

/-- Any continuous linear equivalence `e : E ≃L[ℂ] F` commutes with `Submodule.topologicalClosure`. -/
theorem submodule_map_topologicalClosure_eq (e : E ≃L[ℂ] F) (K : Submodule ℂ E) :
    (K.map e.toLinearMap).topologicalClosure =
      K.topologicalClosure.map e.toLinearMap := by
  apply le_antisymm
  · have hclosed :
        IsClosed ((K.topologicalClosure.map e.toLinearMap : Submodule ℂ F) : Set F) := by
      rw [submodule_map_eq_comap_symm e K.topologicalClosure]
      exact K.isClosed_topologicalClosure.preimage e.symm.continuous
    exact Submodule.topologicalClosure_minimal _
      (Submodule.map_mono K.le_topologicalClosure) hclosed
  · have hle : K ≤ (K.map e.toLinearMap).topologicalClosure.comap e.toLinearMap := by
      intro x hx
      exact (K.map e.toLinearMap).le_topologicalClosure ⟨x, hx, rfl⟩
    have hclosed :
        IsClosed (((K.map e.toLinearMap).topologicalClosure.comap e.toLinearMap :
          Submodule ℂ E) : Set E) :=
      (K.map e.toLinearMap).isClosed_topologicalClosure.preimage e.continuous
    have hcl := Submodule.topologicalClosure_minimal _ hle hclosed
    rintro y ⟨x, hx, rfl⟩
    exact hcl hx

/-- A submodule `K : Submodule ℂ E` is dense (`K.topologicalClosure = ⊤`) if and only if
its image `K.map e.toLinearMap` is dense (`(K.map e.toLinearMap).topologicalClosure = ⊤`). -/
theorem submodule_map_topologicalClosure_eq_top_iff (e : E ≃L[ℂ] F) (K : Submodule ℂ E) :
    (K.map e.toLinearMap).topologicalClosure = ⊤ ↔ K.topologicalClosure = ⊤ := by
  rw [submodule_map_topologicalClosure_eq e K]
  constructor
  · intro htop
    rw [eq_top_iff]
    intro x _
    have hy : e x ∈ K.topologicalClosure.map e.toLinearMap := by
      rw [htop]
      trivial
    rw [submodule_map_eq_comap_symm e K.topologicalClosure] at hy
    change e.symm (e x) ∈ K.topologicalClosure at hy
    rwa [e.symm_apply_apply] at hy
  · intro htop
    rw [htop, eq_top_iff]
    intro y _
    exact ⟨e.symm y, trivial, e.apply_symm_apply y⟩

end SubmoduleClosureEquiv

/-! ### 2. Form-Core Closure Invariance and Energy-Output Identifications -/

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "AD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hw m g k
local notation "VT" => FormSpace ε hε h hh hw m g k
local notation "AJ" => embedding ε hε h hh hw m g k
local notation "AT" => energyOutput ε hε h hh hw m g k
local notation "FT" => formTransfer ε hε h hh hw m g k
local notation "U" => evolution ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Tgrow" => KFCausalClockFloorGrowingOutputClosure.operator ε hε h hh hw m g k
local notation "Tres" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hw m g k
local notation "Eavg" => KFCausalClockFloorAveragedEnergy.energyOperator ε hε h
  (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hw) hh m g k

/-- Abbreviation for the two-time form evolution isomorphism `VT s ≃L[ℂ] VT t`. -/
abbrev formEvolution (s t : ℝ) : VT s ≃L[ℂ] VT t :=
  twoTimeFormEvolutionEquiv ε hε h hh hb m g k s t

/-- `formEvolution s t` maps the topological closure of any form submodule `K : Submodule ℂ (VT s)`
onto the topological closure of its image in `VT t`. -/
theorem formEvolution_map_topologicalClosure (s t : ℝ) (K : Submodule ℂ (VT s)) :
    (K.map (formEvolution ε hε h hh hb m g k s t).toLinearMap).topologicalClosure =
      K.topologicalClosure.map (formEvolution ε hε h hh hb m g k s t).toLinearMap :=
  submodule_map_topologicalClosure_eq (formEvolution ε hε h hh hb m g k s t) K

/-- A form submodule `K : Submodule ℂ (VT s)` is a form core at time `s`
(`K.topologicalClosure = ⊤`) if and only if its evolved image under `formEvolution s t`
is a form core at time `t`. -/
theorem formEvolution_core_iff (s t : ℝ) (K : Submodule ℂ (VT s)) :
    K.topologicalClosure = ⊤ ↔
      (K.map (formEvolution ε hε h hh hb m g k s t).toLinearMap).topologicalClosure = ⊤ :=
  (submodule_map_topologicalClosure_eq_top_iff (formEvolution ε hε h hh hb m g k s t) K).symm

/-- `K : Submodule ℂ (VT s)` is dense in `VT s` if and only if its image under
`formEvolution s t` is dense in `VT t`. -/
theorem formEvolution_dense_iff (s t : ℝ) (K : Submodule ℂ (VT s)) :
    Dense (K : Set (VT s)) ↔
      Dense ((K.map (formEvolution ε hε h hh hb m g k s t).toLinearMap : Submodule ℂ (VT t)) :
        Set (VT t)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.trans
    ((formEvolution_core_iff ε hε h hh hb m g k s t K).trans
      Submodule.dense_iff_topologicalClosure_eq_top.symm)

/-- Two-step composition of submodule images under `formEvolution s r` and `formEvolution r t`. -/
theorem formEvolution_comp_map (s r t : ℝ) (K : Submodule ℂ (VT s)) :
    (K.map (formEvolution ε hε h hh hb m g k s r).toLinearMap).map
        (formEvolution ε hε h hh hb m g k r t).toLinearMap =
      K.map (formEvolution ε hε h hh hb m g k s t).toLinearMap := by
  ext w
  constructor
  · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, (twoTimeFormEvolution_comp ε hε h hh hb m g k s r t u).symm⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨formEvolution ε hε h hh hb m g k s r u, ⟨u, hu, rfl⟩,
      twoTimeFormEvolution_comp ε hε h hh hb m g k s r t u⟩

/-- Evolving a form submodule `K : Submodule ℂ (VT s)` from `s` to `t` and back from `t` to `s`
recovers `K`. -/
theorem formEvolution_reverse_map (s t : ℝ) (K : Submodule ℂ (VT s)) :
    (K.map (formEvolution ε hε h hh hb m g k s t).toLinearMap).map
        (formEvolution ε hε h hh hb m g k t s).toLinearMap = K := by
  rw [formEvolution_comp_map ε hε h hh hb m g k s t s K]
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    have heq : formEvolution ε hε h hh hb m g k s s v = v :=
      twoTimeFormEvolution_self ε hε h hh hb m g k s v
    exact (congrArg (· ∈ K) heq.symm).mp hv
  · intro hu
    exact ⟨u, hu, twoTimeFormEvolution_self ε hε h hh hb m g k s u⟩

/-- Every form vector `w : VT s` embeds into `(Eavg s).domain`. -/
theorem form_embedding_in_averaged_domain (s : ℝ) (w : VT s) :
    AJ s w ∈ (Eavg s).domain :=
  LinearPMap.mem_domain_of_mem_graph w.property

/-- Every form vector `w : VT s` embeds into `(Eavg s).domain`, with
`Eavg s ⟨AJ s w, ...⟩ = AT s w` and `‖AT s w‖ ^ 2 ≤ ‖w‖ ^ 2`. -/
theorem form_embedding_mem_averaged_domain (s : ℝ) (w : VT s) :
    let hEw : AJ s w ∈ (Eavg s).domain :=
      form_embedding_in_averaged_domain ε hε h hh hb m g k s w
    Eavg s ⟨AJ s w, hEw⟩ = AT s w ∧
    ‖Eavg s ⟨AJ s w, hEw⟩‖ ^ 2 = ‖AT s w‖ ^ 2 ∧
    ‖AT s w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  intro hEw
  have heq : AT s w = Eavg s ⟨AJ s w, hEw⟩ :=
    form_output_eq_operator (AD s) w (AJ s w) rfl hEw
  exact ⟨heq.symm, congrArg (fun y : EnergyOutputSpace => ‖y‖ ^ 2) heq.symm,
    right_le_of_eq_add (form_norm_identity ε hε h hh hw m g k s w) (sq_nonneg ‖AJ s w‖)⟩

/-- For any `w : VT s` and observation time `r : ℝ`, `AJ s w ∈ (Eavg r).domain` and
`Eavg r ⟨AJ s w, ...⟩ = AT r (FT s r w)`. -/
theorem formTransfer_energyOutput_eq_operator (s r : ℝ) (w : VT s) :
    ∃ hwr : AJ s w ∈ (Eavg r).domain,
      Eavg r ⟨AJ s w, hwr⟩ = AT r (FT s r w) ∧
      ‖Eavg r ⟨AJ s w, hwr⟩‖ ^ 2 = ‖AT r (FT s r w)‖ ^ 2 := by
  have hJ : AJ r (FT s r w) = AJ s w :=
    transfer_embedding ε hε h hh hw m g k s r w
  have hm := form_embedding_in_averaged_domain ε hε h hh hb m g k r (FT s r w)
  let hwr : AJ s w ∈ (Eavg r).domain :=
    (congrArg (fun x : Hilbert => x ∈ (Eavg r).domain) hJ).mp hm
  have hout : AT r (FT s r w) = Eavg r ⟨AJ s w, hwr⟩ :=
    form_output_eq_operator (AD r) (FT s r w) (AJ s w) hJ hwr
  exact ⟨hwr, hout.symm, congrArg (fun y : EnergyOutputSpace => ‖y‖ ^ 2) hout.symm⟩

/-- For any `w : VT s`, evolution time `t`, and observation time `r`, the evolved embedding
`U s t (AJ s w)` lies in `(Eavg r).domain` and satisfies
`Eavg r ⟨U s t (AJ s w), ...⟩ = AT r (FT t r (formEvolution s t w))`. -/
theorem formEvolution_energyOutput_eq_operator (s t r : ℝ) (w : VT s) :
    let hEw : AJ s w ∈ (Eavg s).domain :=
      form_embedding_in_averaged_domain ε hε h hh hb m g k s w
    let hUr : U s t (AJ s w) ∈ (Eavg r).domain :=
      mem_averaged_domain_of_evolved ε hε h hh hb m g k s t r hEw
    Eavg r ⟨U s t (AJ s w), hUr⟩ =
      AT r (FT t r (formEvolution ε hε h hh hb m g k s t w)) ∧
    ‖Eavg r ⟨U s t (AJ s w), hUr⟩‖ ^ 2 =
      ‖AT r (FT t r (formEvolution ε hε h hh hb m g k s t w))‖ ^ 2 := by
  intro hEw hUr
  have hJ1 : AJ r (FT t r (formEvolution ε hε h hh hb m g k s t w)) =
      AJ t (formEvolution ε hε h hh hb m g k s t w) :=
    transfer_embedding ε hε h hh hw m g k t r (formEvolution ε hε h hh hb m g k s t w)
  have hJ2 : AJ t (formEvolution ε hε h hh hb m g k s t w) = U s t (AJ s w) :=
    twoTimeFormEvolutionEquiv_embedding ε hε h hh hb m g k s t w
  have hout :=
    form_output_eq_operator (AD r)
      (FT t r (formEvolution ε hε h hh hb m g k s t w))
      (U s t (AJ s w)) (hJ1.trans hJ2) hUr
  exact ⟨hout.symm, congrArg (fun y : EnergyOutputSpace => ‖y‖ ^ 2) hout.symm⟩

/-- At `r = t`, `Eavg t ⟨U s t (AJ s w), ...⟩ = AT t (formEvolution s t w)`. -/
theorem formEvolution_target_energyOutput_eq (s t : ℝ) (w : VT s) :
    let hEw : AJ s w ∈ (Eavg s).domain :=
      form_embedding_in_averaged_domain ε hε h hh hb m g k s w
    let hUt : U s t (AJ s w) ∈ (Eavg t).domain :=
      mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hEw
    Eavg t ⟨U s t (AJ s w), hUt⟩ =
      AT t (formEvolution ε hε h hh hb m g k s t w) ∧
    ‖Eavg t ⟨U s t (AJ s w), hUt⟩‖ ^ 2 =
      ‖AT t (formEvolution ε hε h hh hb m g k s t w)‖ ^ 2 := by
  intro hEw hUt
  have hJ : AJ t (formEvolution ε hε h hh hb m g k s t w) = U s t (AJ s w) :=
    twoTimeFormEvolutionEquiv_embedding ε hε h hh hb m g k s t w
  have hout :=
    form_output_eq_operator (AD t)
      (formEvolution ε hε h hh hb m g k s t w)
      (U s t (AJ s w)) hJ hUt
  exact ⟨hout.symm, congrArg (fun y : EnergyOutputSpace => ‖y‖ ^ 2) hout.symm⟩

/-! ### 3. Two-Sided Evolved Difference Bounds and Five-Channel Estimates -/

/-- Two-sided exponential difference bounds in `VT t` and in energy output `AT t` vs `AT s`
for arbitrary `u, v : VT s`, together with observation-time bounds on
`‖AT r (FT t r (formEvolution s t u - formEvolution s t v))‖ ^ 2`. -/
theorem formEvolution_two_sided_difference_bounds (s t r : ℝ) (u v : VT s) :
    Real.exp (-2 * |t - s|) * ‖u - v‖ ^ 2 ≤
      ‖formEvolution ε hε h hh hb m g k s t u -
        formEvolution ε hε h hh hb m g k s t v‖ ^ 2 ∧
    ‖formEvolution ε hε h hh hb m g k s t u -
        formEvolution ε hε h hh hb m g k s t v‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * ‖u - v‖ ^ 2 ∧
    Real.exp (-2 * |t - s|) * ‖AT s (u - v)‖ ^ 2 ≤
      ‖AT t (formEvolution ε hε h hh hb m g k s t u -
        formEvolution ε hε h hh hb m g k s t v)‖ ^ 2 ∧
    ‖AT t (formEvolution ε hε h hh hb m g k s t u -
        formEvolution ε hε h hh hb m g k s t v)‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * ‖AT s (u - v)‖ ^ 2 ∧
    Real.exp (-2 * (|s - r| + |t - s|)) * ‖AT r (FT s r (u - v))‖ ^ 2 ≤
      ‖AT t (formEvolution ε hε h hh hb m g k s t u -
        formEvolution ε hε h hh hb m g k s t v)‖ ^ 2 ∧
    ‖AT r (FT t r (formEvolution ε hε h hh hb m g k s t u -
        formEvolution ε hε h hh hb m g k s t v))‖ ^ 2 ≤
      Real.exp (2 * (|t - r| + |t - s|)) * ‖AT s (u - v)‖ ^ 2 ∧
    ‖AT r (FT t r (formEvolution ε hε h hh hb m g k s t u -
        formEvolution ε hε h hh hb m g k s t v))‖ ^ 2 ≤
      max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ‖AT s (u - v)‖ ^ 2 := by
  let w : VT s := u - v
  have hsub :
      formEvolution ε hε h hh hb m g k s t u -
        formEvolution ε hε h hh hb m g k s t v =
      formEvolution ε hε h hh hb m g k s t w :=
    (map_sub (formEvolution ε hε h hh hb m g k s t) u v).symm
  have hnorm_sub :
      ‖formEvolution ε hε h hh hb m g k s t u -
        formEvolution ε hε h hh hb m g k s t v‖ ^ 2 =
      ‖twoTimeFormEvolution ε hε h hh hb m g k s t w‖ ^ 2 :=
    congrArg (fun z : VT t => ‖z‖ ^ 2) hsub
  have hb_vt := twoTimeFormEvolution_two_sided_norm_sq_bounds ε hε h hh hb m g k s t w
  have hEw : AJ s w ∈ (Eavg s).domain :=
    form_embedding_in_averaged_domain ε hε h hh hb m g k s w
  have hEs_eq : ‖Eavg s ⟨AJ s w, hEw⟩‖ ^ 2 = ‖AT s w‖ ^ 2 :=
    (form_embedding_mem_averaged_domain ε hε h hh hb m g k s w).2.1
  have hEt_eq :
      ‖AT t (formEvolution ε hε h hh hb m g k s t u -
        formEvolution ε hε h hh hb m g k s t v)‖ ^ 2 =
      ‖Eavg t ⟨U s t (AJ s w),
        mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hEw⟩‖ ^ 2 :=
    (congrArg (fun z : VT t => ‖AT t z‖ ^ 2) hsub).trans
      (formEvolution_target_energyOutput_eq ε hε h hh hb m g k s t w).2.symm
  have hEr_eq :
      ‖AT r (FT t r (formEvolution ε hε h hh hb m g k s t u -
        formEvolution ε hε h hh hb m g k s t v))‖ ^ 2 =
      ‖Eavg r ⟨U s t (AJ s w),
        mem_averaged_domain_of_evolved ε hε h hh hb m g k s t r hEw⟩‖ ^ 2 :=
    (congrArg (fun z : VT t => ‖AT r (FT t r z)‖ ^ 2) hsub).trans
      (formEvolution_energyOutput_eq_operator ε hε h hh hb m g k s t r w).2.symm
  have hb_op := evolved_operator_form_energy_bounds ε hε h hh hb m g k s t r hEw
  have hlow_t :
      Real.exp (-2 * |t - s|) * ‖AT s w‖ ^ 2 ≤
        ‖AT t (formEvolution ε hε h hh hb m g k s t u -
          formEvolution ε hε h hh hb m g k s t v)‖ ^ 2 :=
    (congrArg (Real.exp (-2 * |t - s|) * ·) hEs_eq.symm).trans_le
      (hb_op.1.trans_eq hEt_eq.symm)
  have hup_t :
      ‖AT t (formEvolution ε hε h hh hb m g k s t u -
          formEvolution ε hε h hh hb m g k s t v)‖ ^ 2 ≤
        Real.exp (2 * |t - s|) * ‖AT s w‖ ^ 2 :=
    hEt_eq.trans_le
      (hb_op.2.1.trans_eq (congrArg (Real.exp (2 * |t - s|) * ·) hEs_eq))
  have hup_r_dist :
      ‖AT r (FT t r (formEvolution ε hε h hh hb m g k s t u -
          formEvolution ε hε h hh hb m g k s t v))‖ ^ 2 ≤
        Real.exp (2 * (|t - r| + |t - s|)) * ‖AT s w‖ ^ 2 :=
    hEr_eq.trans_le
      (hb_op.2.2.2.trans_eq
        (congrArg (Real.exp (2 * (|t - r| + |t - s|)) * ·) hEs_eq))
  have hup_r_max :
      ‖AT r (FT t r (formEvolution ε hε h hh hb m g k s t u -
          formEvolution ε hε h hh hb m g k s t v))‖ ^ 2 ≤
        max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ‖AT s w‖ ^ 2 :=
    hEr_eq.trans_le
      (hb_op.2.2.1.trans_eq
        (congrArg (max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ·) hEs_eq))
  have hUt : U s t (AJ s w) ∈ (Eavg t).domain :=
    mem_averaged_domain_of_evolved ε hε h hh hb m g k s t t hEw
  have hb_rev := evolved_operator_form_energy_bounds ε hε h hh hb m g k t s r hUt
  have hrev_vec : U t s (U s t (AJ s w)) = AJ s w :=
    congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (AJ s w))
      (KFCausalClockFloorAveragedEvolution.evolution_reverse ε hε h hh hw m g k s t)
  have hwr := (formTransfer_energyOutput_eq_operator ε hε h hh hb m g k s r w).choose
  have hwr_spec := (formTransfer_energyOutput_eq_operator ε hε h hh hb m g k s r w).choose_spec
  have hrev_sub :
      (⟨U t s (U s t (AJ s w)),
        mem_averaged_domain_of_evolved ε hε h hh hb m g k t s r hUt⟩ : (Eavg r).domain) =
      ⟨AJ s w, hwr⟩ :=
    Subtype.ext hrev_vec
  have hrev_r_eq :
      ‖AT r (FT s r w)‖ ^ 2 =
        ‖Eavg r ⟨U t s (U s t (AJ s w)),
          mem_averaged_domain_of_evolved ε hε h hh hb m g k t s r hUt⟩‖ ^ 2 :=
    hwr_spec.2.symm.trans
      (congrArg (fun z : (Eavg r).domain => ‖Eavg r z‖ ^ 2) hrev_sub.symm)
  have hrev_dist :
      ‖AT r (FT s r w)‖ ^ 2 ≤
        Real.exp (2 * (|s - r| + |s - t|)) *
          ‖AT t (formEvolution ε hε h hh hb m g k s t u -
            formEvolution ε hε h hh hb m g k s t v)‖ ^ 2 :=
    hrev_r_eq.trans_le
      (hb_rev.2.2.2.trans_eq
        (congrArg (Real.exp (2 * (|s - r| + |s - t|)) * ·) hEt_eq.symm))
  exact ⟨hb_vt.1.trans_eq hnorm_sub.symm,
    hnorm_sub.trans_le hb_vt.2,
    hlow_t, hup_t,
    unscale_reverse_exp_dist hrev_dist,
    hup_r_dist, hup_r_max⟩

/-- Explicit five-channel and half-clock difference bounds for `U s t (AJ s u) - U s t (AJ s v)`
for arbitrary `u, v : VT s` at every evolution time `t` and observation time `r`. -/
theorem formEvolution_five_channel_difference_bounds (s t r : ℝ) (u v : VT s) :
    let hu : AJ s u ∈ (Eavg s).domain :=
      form_embedding_in_averaged_domain ε hε h hh hb m g k s u
    let hv : AJ s v ∈ (Eavg s).domain :=
      form_embedding_in_averaged_domain ε hε h hh hb m g k s v
    let hdu := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t r hu
    let hdv := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t r hv
    ‖U s t (AJ s u) - U s t (AJ s v)‖ ^ 2 = ‖AJ s (u - v)‖ ^ 2 ∧
    ‖Eavg r ⟨U s t (AJ s u), hdu.1⟩ - Eavg r ⟨U s t (AJ s v), hdv.1⟩‖ ^ 2 ≤
      max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ‖AT s (u - v)‖ ^ 2 ∧
    ‖Tstat ⟨U s t (AJ s u), hdu.2.1⟩ - Tstat ⟨U s t (AJ s v), hdv.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * |t - s|) * ‖AT s (u - v)‖ ^ 2 ∧
    ‖clockHalf ε ⟨U s t (AJ s u), hdu.2.2.2.2.2.2⟩ -
        clockHalf ε ⟨U s t (AJ s v), hdv.2.2.2.2.2.2⟩‖ ^ 2 ≤
      2 * (Real.exp (2 * |t - s|) * ‖AT s (u - v)‖ ^ 2) ∧
    ‖Tgrow ⟨U s t (AJ s u), hdu.2.2.2.2.1⟩ - Tgrow ⟨U s t (AJ s v), hdv.2.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * ‖AT s (u - v)‖ ^ 2 ∧
    ‖Kroot ⟨U s t (AJ s u), hdu.2.2.1⟩ - Kroot ⟨U s t (AJ s v), hdv.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * ‖AT s (u - v)‖ ^ 2 ∧
    ‖Tpot ⟨U s t (AJ s u), hdu.2.2.2.1⟩ - Tpot ⟨U s t (AJ s v), hdv.2.2.2.1⟩‖ ^ 2 ≤
      Real.exp (2 * (|t - s| - t)) * ‖AT s (u - v)‖ ^ 2 ∧
    ‖Tres r ⟨U s t (AJ s u), hdu.2.2.2.2.2.1⟩ -
        Tres r ⟨U s t (AJ s v), hdv.2.2.2.2.2.1⟩‖ ^ 2 ≤
      max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ‖AT s (u - v)‖ ^ 2 := by
  intro hu hv hdu hdv
  let w : VT s := u - v
  have hEw : AJ s w ∈ (Eavg s).domain :=
    form_embedding_in_averaged_domain ε hε h hh hb m g k s w
  let hdw := mem_all_form_domains_of_evolved ε hε h hh hb m g k s t r hEw
  have hvec : U s t (AJ s w) = U s t (AJ s u) - U s t (AJ s v) :=
    (congrArg (U s t) (map_sub (AJ s) u v)).trans
      (map_sub (U s t) (AJ s u) (AJ s v))
  have hnorm_vec : ‖U s t (AJ s u) - U s t (AJ s v)‖ ^ 2 = ‖AJ s w‖ ^ 2 :=
    (congrArg (fun x : Hilbert => ‖x‖ ^ 2) hvec.symm).trans
      (congrArg (fun s : ℝ => s ^ 2) (evolution_norm ε hε h hh hw m g k s t (AJ s w)))
  have hEs_eq : ‖Eavg s ⟨AJ s w, hEw⟩‖ ^ 2 = ‖AT s w‖ ^ 2 :=
    (form_embedding_mem_averaged_domain ε hε h hh hb m g k s w).2.1
  have hb_op := evolved_operator_form_energy_bounds ε hε h hh hb m g k s t r hEw
  have hb_comp := evolved_component_form_energy_bounds ε hε h hh hb m g k s t r hEw
  refine ⟨hnorm_vec,
    (pmap_sub_norm_sq_eq (Eavg r) hvec hdu.1 hdv.1 hdw.1).trans_le
      (hb_op.2.2.1.trans_eq
        (congrArg (max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ·) hEs_eq)),
    (pmap_sub_norm_sq_eq Tstat hvec hdu.2.1 hdv.2.1 hdw.2.1).trans_le
      (hb_comp.1.trans_eq (congrArg (Real.exp (2 * |t - s|) * ·) hEs_eq)),
    (pmap_sub_norm_sq_eq (clockHalf ε) hvec hdu.2.2.2.2.2.2 hdv.2.2.2.2.2.2
      hdw.2.2.2.2.2.2).trans_le
      (hb_comp.2.1.trans_eq
        (congrArg (fun x => 2 * (Real.exp (2 * |t - s|) * x)) hEs_eq)),
    (pmap_sub_norm_sq_eq Tgrow hvec hdu.2.2.2.2.1 hdv.2.2.2.2.1 hdw.2.2.2.2.1).trans_le
      (hb_comp.2.2.2.1.trans_eq
        (congrArg (Real.exp (2 * (|t - s| - t)) * ·) hEs_eq)),
    (pmap_sub_norm_sq_eq Kroot hvec hdu.2.2.1 hdv.2.2.1 hdw.2.2.1).trans_le
      (hb_comp.2.2.2.2.2.1.trans_eq
        (congrArg (Real.exp (2 * (|t - s| - t)) * ·) hEs_eq)),
    (pmap_sub_norm_sq_eq Tpot hvec hdu.2.2.2.1 hdv.2.2.2.1 hdw.2.2.2.1).trans_le
      (hb_comp.2.2.2.2.2.2.2.1.trans_eq
        (congrArg (Real.exp (2 * (|t - s| - t)) * ·) hEs_eq)),
    (pmap_sub_norm_sq_eq (Tres r) hvec hdu.2.2.2.2.2.1 hdv.2.2.2.2.2.1
      hdw.2.2.2.2.2.1).trans_le
      (hb_comp.2.2.2.2.2.2.2.2.trans_eq
        (congrArg (max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) * ·) hEs_eq))⟩

/-! ### 4. Simultaneous Multi-Channel Sequence Convergence under Form Evolution -/

/-- For any sequence `u_seq : ℕ → VT s` converging to `u : VT s` in `VT s`, the evolved
sequence `formEvolution s t (u_seq n)` converges to `formEvolution s t u` in `VT t`, and its
Hilbert embeddings `U s t (AJ s (u_seq n))` converge to `U s t (AJ s u)` simultaneously in
`Hilbert` and in all seven form and clock channels (`Eavg r`, `Tstat`, `clockHalf ε`,
`Tgrow`, `Kroot`, `Tpot`, and `Tres r`) at every target time `t` and observation time `r`. -/
theorem formEvolution_sequence_multi_channel_tendsto
    (s t r : ℝ) {u_seq : ℕ → VT s} {u : VT s}
    (hu_lim : Tendsto u_seq atTop (𝓝 u)) :
    let hdom_n := fun n : ℕ =>
      mem_all_form_domains_of_evolved ε hε h hh hb m g k s t r
        (form_embedding_in_averaged_domain ε hε h hh hb m g k s (u_seq n))
    let hdom_u :=
      mem_all_form_domains_of_evolved ε hε h hh hb m g k s t r
        (form_embedding_in_averaged_domain ε hε h hh hb m g k s u)
    Tendsto (fun n : ℕ => formEvolution ε hε h hh hb m g k s t (u_seq n))
      atTop (𝓝 (formEvolution ε hε h hh hb m g k s t u)) ∧
    Tendsto (fun n : ℕ => U s t (AJ s (u_seq n)))
      atTop (𝓝 (U s t (AJ s u))) ∧
    Tendsto (fun n : ℕ => Eavg r ⟨U s t (AJ s (u_seq n)), (hdom_n n).1⟩)
      atTop (𝓝 (Eavg r ⟨U s t (AJ s u), hdom_u.1⟩)) ∧
    Tendsto (fun n : ℕ => Tstat ⟨U s t (AJ s (u_seq n)), (hdom_n n).2.1⟩)
      atTop (𝓝 (Tstat ⟨U s t (AJ s u), hdom_u.2.1⟩)) ∧
    Tendsto (fun n : ℕ => clockHalf ε ⟨U s t (AJ s (u_seq n)), (hdom_n n).2.2.2.2.2.2⟩)
      atTop (𝓝 (clockHalf ε ⟨U s t (AJ s u), hdom_u.2.2.2.2.2.2⟩)) ∧
    Tendsto (fun n : ℕ => Tgrow ⟨U s t (AJ s (u_seq n)), (hdom_n n).2.2.2.2.1⟩)
      atTop (𝓝 (Tgrow ⟨U s t (AJ s u), hdom_u.2.2.2.2.1⟩)) ∧
    Tendsto (fun n : ℕ => Kroot ⟨U s t (AJ s (u_seq n)), (hdom_n n).2.2.1⟩)
      atTop (𝓝 (Kroot ⟨U s t (AJ s u), hdom_u.2.2.1⟩)) ∧
    Tendsto (fun n : ℕ => Tpot ⟨U s t (AJ s (u_seq n)), (hdom_n n).2.2.2.1⟩)
      atTop (𝓝 (Tpot ⟨U s t (AJ s u), hdom_u.2.2.2.1⟩)) ∧
    Tendsto (fun n : ℕ => Tres r ⟨U s t (AJ s (u_seq n)), (hdom_n n).2.2.2.2.2.1⟩)
      atTop (𝓝 (Tres r ⟨U s t (AJ s u), hdom_u.2.2.2.2.2.1⟩)) := by
  intro hdom_n hdom_u
  have hAT_le : ∀ n : ℕ, ‖AT s (u_seq n - u)‖ ^ 2 ≤ ‖u_seq n - u‖ ^ 2 :=
    fun n => (form_embedding_mem_averaged_domain ε hε h hh hb m g k s (u_seq n - u)).2.2
  have hexp_pos : 0 ≤ Real.exp (2 * |t - s|) := (Real.exp_pos _).le
  have hmax_pos : 0 ≤ max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|) :=
    mul_nonneg (le_trans zero_le_one (le_max_left 1 _)) hexp_pos
  have h2_pos : 0 ≤ 2 * Real.exp (2 * |t - s|) := mul_nonneg (by norm_num) hexp_pos
  have hexp_sub_pos : 0 ≤ Real.exp (2 * (|t - s| - t)) := (Real.exp_pos _).le
  have hdiff := fun n : ℕ =>
    formEvolution_five_channel_difference_bounds ε hε h hh hb m g k s t r (u_seq n) u
  refine ⟨((formEvolution ε hε h hh hb m g k s t).continuous.tendsto u).comp hu_lim,
    ((U s t).continuous.tendsto (AJ s u)).comp (((AJ s).continuous.tendsto u).comp hu_lim),
    tendsto_of_norm_sub_sq_le hu_lim
      (max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|)) hmax_pos
      (fun n => (hdiff n).2.1.trans (mul_le_mul_of_nonneg_left (hAT_le n) hmax_pos)),
    tendsto_of_norm_sub_sq_le hu_lim
      (Real.exp (2 * |t - s|)) hexp_pos
      (fun n => (hdiff n).2.2.1.trans (mul_le_mul_of_nonneg_left (hAT_le n) hexp_pos)),
    tendsto_of_norm_sub_sq_le hu_lim
      (2 * Real.exp (2 * |t - s|)) h2_pos
      (fun n => ((hdiff n).2.2.2.1.trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hAT_le n) hexp_pos) (by norm_num))).trans_eq
        (mul_assoc 2 (Real.exp (2 * |t - s|)) (‖u_seq n - u‖ ^ 2)).symm),
    tendsto_of_norm_sub_sq_le hu_lim
      (Real.exp (2 * (|t - s| - t))) hexp_sub_pos
      (fun n => (hdiff n).2.2.2.2.1.trans (mul_le_mul_of_nonneg_left (hAT_le n) hexp_sub_pos)),
    tendsto_of_norm_sub_sq_le hu_lim
      (Real.exp (2 * (|t - s| - t))) hexp_sub_pos
      (fun n => (hdiff n).2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_left (hAT_le n) hexp_sub_pos)),
    tendsto_of_norm_sub_sq_le hu_lim
      (Real.exp (2 * (|t - s| - t))) hexp_sub_pos
      (fun n => (hdiff n).2.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_left (hAT_le n) hexp_sub_pos)),
    tendsto_of_norm_sub_sq_le hu_lim
      (max 1 (Real.exp (2 * (r - t))) * Real.exp (2 * |t - s|)) hmax_pos
      (fun n => (hdiff n).2.2.2.2.2.2.2.trans (mul_le_mul_of_nonneg_left (hAT_le n) hmax_pos))⟩

/-- For any sequence `u_seq : ℕ → VT s` converging to `u : VT s`, the evolved energy outputs
`AT t (formEvolution s t (u_seq n))` and `AT r (FT t r (formEvolution s t (u_seq n)))`
converge in `EnergyOutputSpace`. -/
theorem formEvolution_energyOutput_tendsto
    (s t r : ℝ) {u_seq : ℕ → VT s} {u : VT s}
    (hu_lim : Tendsto u_seq atTop (𝓝 u)) :
    Tendsto (fun n : ℕ => AT t (formEvolution ε hε h hh hb m g k s t (u_seq n)))
      atTop (𝓝 (AT t (formEvolution ε hε h hh hb m g k s t u))) ∧
    Tendsto (fun n : ℕ => AT r (FT t r (formEvolution ε hε h hh hb m g k s t (u_seq n))))
      atTop (𝓝 (AT r (FT t r (formEvolution ε hε h hh hb m g k s t u)))) := by
  have h1 :
      Tendsto (fun n : ℕ => formEvolution ε hε h hh hb m g k s t (u_seq n))
        atTop (𝓝 (formEvolution ε hε h hh hb m g k s t u)) :=
    ((formEvolution ε hε h hh hb m g k s t).continuous.tendsto u).comp hu_lim
  have h2 :
      Tendsto (fun n : ℕ => FT t r (formEvolution ε hε h hh hb m g k s t (u_seq n)))
        atTop (𝓝 (FT t r (formEvolution ε hε h hh hb m g k s t u))) :=
    ((FT t r).continuous.tendsto (formEvolution ε hε h hh hb m g k s t u)).comp h1
  exact ⟨((AT t).continuous.tendsto (formEvolution ε hε h hh hb m g k s t u)).comp h1,
    ((AT r).continuous.tendsto (FT t r (formEvolution ε hε h hh hb m g k s t u))).comp h2⟩

#print axioms submodule_map_eq_comap_symm
#print axioms submodule_map_topologicalClosure_eq
#print axioms submodule_map_topologicalClosure_eq_top_iff
#print axioms formEvolution_map_topologicalClosure
#print axioms formEvolution_core_iff
#print axioms formEvolution_dense_iff
#print axioms formEvolution_comp_map
#print axioms formEvolution_reverse_map
#print axioms form_embedding_in_averaged_domain
#print axioms form_embedding_mem_averaged_domain
#print axioms formTransfer_energyOutput_eq_operator
#print axioms formEvolution_energyOutput_eq_operator
#print axioms formEvolution_target_energyOutput_eq
#print axioms formEvolution_two_sided_difference_bounds
#print axioms formEvolution_five_channel_difference_bounds
#print axioms formEvolution_sequence_multi_channel_tendsto
#print axioms formEvolution_energyOutput_tendsto

end

end UnifiedTheory.Audit.KFCausalClockFloorEvolvedFormCoreInvariance
