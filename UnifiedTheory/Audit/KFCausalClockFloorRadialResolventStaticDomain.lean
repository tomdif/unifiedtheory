/- Operator-level invariance of the maximal static Hamiltonian domain under
both the radial resolvent regularizer J_N and the radial Yosida multiplier M_N,
together with the explicit O(N^{-1/2}) commutator bound for [T, J_N] and strong
convergence T(J_N x) → T x on the entire static operator domain. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticFormPairing

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticDomain
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorOrbitVacuumGraph (OrbitSpace physicalOrbit)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialResolventRegularizer (action sequence_tendsto)
open KFCausalClockFloorRadialResolventLeibniz (scaledOrbitExtra scaledOrbitExtra_norm)
open KFCausalClockFloorRadialResolventStaticForm (formAction formAction_embedding)
open KFCausalClockFloorRadialResolventStaticFormPairing
  (scaledSectionFirstDual scaledOrbitSecondDual
    scaledSectionFirstDual_norm scaledOrbitSecondDual_norm
    yosidaAction_selfAdjoint_pairing formAction_output_commutator_pairing)
open KFCausalClockFloorStaticHamiltonian (hamiltonian_eq_operator)

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)

private theorem resolvent_apply (f : Hilbert) :
    action ε hε h N hN f =
      f-(N⁻¹:ℂ) • KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f := rfl

theorem resolvent_selfAdjoint_pairing (f₁ f₂ : Hilbert) :
    inner ℂ (action ε hε h N hN f₁) f₂ =
      inner ℂ f₁ (action ε hε h N hN f₂) := by
  rw [resolvent_apply,resolvent_apply,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right,← Complex.ofReal_inv,Complex.conj_ofReal,
    yosidaAction_selfAdjoint_pairing]

variable (hb : |h| ≤ Real.pi*ε/3) (hh : h ≠ 0) (m g k : ℝ)

def orbitAdjoint (φ : OrbitSpace) : Hilbert :=
  (physicalOrbit h hh).toContinuousLinearMap.adjoint φ

theorem orbitAdjoint_inner (φ : OrbitSpace) (f : Hilbert) :
    inner ℂ (orbitAdjoint h hh φ) f = inner ℂ φ (physicalOrbit h hh f) :=
  (physicalOrbit h hh).toContinuousLinearMap.adjoint_inner_left f φ

theorem orbitAdjoint_norm (φ : OrbitSpace) :
    ‖orbitAdjoint h hh φ‖ ≤ ‖φ‖ := by
  have hsq : ‖orbitAdjoint h hh φ‖^2 ≤ ‖φ‖*‖orbitAdjoint h hh φ‖ := by
    calc
      ‖orbitAdjoint h hh φ‖^2 = (inner ℂ (orbitAdjoint h hh φ) (orbitAdjoint h hh φ)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = (inner ℂ φ (physicalOrbit h hh (orbitAdjoint h hh φ))).re := by
        rw [orbitAdjoint_inner]
      _ ≤ ‖inner ℂ φ (physicalOrbit h hh (orbitAdjoint h hh φ))‖ := Complex.re_le_norm _
      _ ≤ ‖φ‖*‖physicalOrbit h hh (orbitAdjoint h hh φ)‖ := norm_inner_le_norm _ _
      _ = ‖φ‖*‖orbitAdjoint h hh φ‖ := by rw [(physicalOrbit h hh).norm_map]
  nlinarith [norm_nonneg (orbitAdjoint h hh φ),norm_nonneg φ]

def scaledExtraAdjoint (z : EnergyOutputSpace) : Hilbert :=
  (scaledOrbitExtra ε hε h N hN hh m g k).adjoint z

theorem scaledExtraAdjoint_inner (z : EnergyOutputSpace) (f : Hilbert) :
    inner ℂ (scaledExtraAdjoint ε hε h N hN hh m g k z) f =
      inner ℂ z (scaledOrbitExtra ε hε h N hN hh m g k f) :=
  (scaledOrbitExtra ε hε h N hN hh m g k).adjoint_inner_left f z

private theorem le_of_sq_le_mul {a b : ℝ} (hb : 0 ≤ b) (h : a^2 ≤ b*a) :
    a ≤ b := by
  nlinarith

theorem scaledExtraAdjoint_norm (z : EnergyOutputSpace) :
    ‖scaledExtraAdjoint ε hε h N hN hh m g k z‖ ≤
      (N⁻¹*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*‖z‖ := by
  have hsq : ‖scaledExtraAdjoint ε hε h N hN hh m g k z‖^2 ≤
      ((N⁻¹*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*‖z‖)*
        ‖scaledExtraAdjoint ε hε h N hN hh m g k z‖ := by
    calc
      ‖scaledExtraAdjoint ε hε h N hN hh m g k z‖^2 =
          (inner ℂ (scaledExtraAdjoint ε hε h N hN hh m g k z)
            (scaledExtraAdjoint ε hε h N hN hh m g k z)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = (inner ℂ z (scaledOrbitExtra ε hε h N hN hh m g k
            (scaledExtraAdjoint ε hε h N hN hh m g k z))).re := by
        rw [scaledExtraAdjoint_inner]
      _ ≤ ‖inner ℂ z (scaledOrbitExtra ε hε h N hN hh m g k
            (scaledExtraAdjoint ε hε h N hN hh m g k z))‖ := Complex.re_le_norm _
      _ ≤ ‖z‖*‖scaledOrbitExtra ε hε h N hN hh m g k
            (scaledExtraAdjoint ε hε h N hN hh m g k z)‖ := norm_inner_le_norm _ _
      _ ≤ ‖z‖*((N⁻¹*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*
            ‖scaledExtraAdjoint ε hε h N hN hh m g k z‖) :=
        mul_le_mul_of_nonneg_left
          (scaledOrbitExtra_norm ε hε h N hN hh m g k
            (scaledExtraAdjoint ε hε h N hN hh m g k z))
          (norm_nonneg z)
      _ = ((N⁻¹*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹))*‖z‖)*
            ‖scaledExtraAdjoint ε hε h N hN hh m g k z‖ := by ring
  exact le_of_sq_le_mul (by positivity) hsq

attribute [irreducible] orbitAdjoint scaledExtraAdjoint

def commutatorVector (f : Hilbert) (z : EnergyOutputSpace) : Hilbert :=
  scaledExtraAdjoint ε hε h N hN hh m g k z-
    orbitAdjoint h hh
      (scaledSectionFirstDual ε hε h N hN z+
        scaledOrbitSecondDual ε hε h N hN hh f)

theorem commutatorVector_inner (f₁ : Hilbert) (z₁ : EnergyOutputSpace) (f₂ : Hilbert) :
    inner ℂ (commutatorVector ε hε h N hN hh m g k f₁ z₁) f₂ =
      inner ℂ z₁ (scaledOrbitExtra ε hε h N hN hh m g k f₂)-
        inner ℂ (scaledSectionFirstDual ε hε h N hN z₁+
          scaledOrbitSecondDual ε hε h N hN hh f₁) (physicalOrbit h hh f₂) := by
  unfold commutatorVector
  rw [inner_sub_left,scaledExtraAdjoint_inner,orbitAdjoint_inner]

theorem commutatorVector_norm (f : Hilbert) (z : EnergyOutputSpace) :
    ‖commutatorVector ε hε h N hN hh m g k f z‖ ≤
      (3*(N⁻¹*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹)))*‖z‖+
        (N⁻¹*(6*h^2/ε^2))*‖f‖ := by
  unfold commutatorVector
  have h1 := scaledExtraAdjoint_norm ε hε h N hN hh m g k z
  have h2 := (orbitAdjoint_norm h hh _).trans
    ((norm_add_le _ _).trans (add_le_add
      (scaledSectionFirstDual_norm ε hε h N hN z)
      (scaledOrbitSecondDual_norm ε hε h N hN hh f)))
  have hsub := (norm_sub_le _ _).trans (add_le_add h1 h2)
  linarith

private theorem variational_pairing_step (f₁ f₂ y : Hilbert) (z₁ : EnergyOutputSpace) :
    inner ℂ (action ε hε h N hN y) f₂+
      inner ℂ z₁ (scaledOrbitExtra ε hε h N hN hh m g k f₂)-
      inner ℂ (scaledSectionFirstDual ε hε h N hN z₁+
        scaledOrbitSecondDual ε hε h N hN hh f₁) (physicalOrbit h hh f₂) =
      inner ℂ (action ε hε h N hN y+
        commutatorVector ε hε h N hN hh m g k f₁ z₁) f₂ :=
  ((add_sub_assoc _ _ _).trans
    (congrArg (inner ℂ (action ε hε h N hN y) f₂ + ·)
      (commutatorVector_inner ε hε h N hN hh m g k f₁ z₁ f₂).symm)).trans
    (inner_add_left _ _ _).symm

local notation "hw" => wide_bound ε hε h hb
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hw m g k 0
local notation "TV" => KFCausalClockFloorStaticHamiltonian.StaticForm ε hε h hh hw m g k 0
local notation "TJ" => KFCausalClosedGraphForm.embedding TD
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "TstatOp" => KFCausalClockFloorStaticOperator.operator ε hε h

theorem formAction_variational_pairing (u : TV) (y : Hilbert)
    (hy : ∀ w : TV, inner ℂ (TB u) (TB w) = inner ℂ y (TJ w)) (v : TV) :
    inner ℂ (TB (formAction ε hε h N hN hb hh m g k u)) (TB v) =
      inner ℂ (action ε hε h N hN y+
        commutatorVector ε hε h N hN hh m g k (TJ u) (TB u)) (TJ v) := by
  have h1 : inner ℂ (TB u) (TB (formAction ε hε h N hN hb hh m g k v)) =
      inner ℂ (action ε hε h N hN y) (TJ v) :=
    (hy (formAction ε hε h N hN hb hh m g k v)).trans
      ((congrArg (inner ℂ y) (formAction_embedding ε hε h N hN hb hh m g k v)).trans
        (resolvent_selfAdjoint_pairing ε hε h N hN y (TJ v)).symm)
  exact (formAction_output_commutator_pairing ε hε h N hN hb hh m g k u v).trans
    ((congrArg (fun c : ℂ =>
        c+inner ℂ (TB u) (scaledOrbitExtra ε hε h N hN hh m g k (TJ v))-
          inner ℂ (scaledSectionFirstDual ε hε h N hN (TB u)+
            scaledOrbitSecondDual ε hε h N hN hh (TJ u)) (physicalOrbit h hh (TJ v))) h1).trans
      (variational_pairing_step ε hε h N hN hh m g k (TJ u) (TJ v) y (TB u)))

private theorem hamiltonian_graph_cast {f₁ f₂ q : Hilbert} (hf : f₁ = f₂)
    (hg : (f₁,q) ∈
      (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw m g k 0).graph) :
    (f₂,q) ∈ (TstatOp).graph := by
  rwa [hf,hamiltonian_eq_operator] at hg

theorem formAction_hamiltonian_graph (u : TV) (y : Hilbert)
    (hy : ∀ w : TV, inner ℂ (TB u) (TB w) = inner ℂ y (TJ w)) :
    (action ε hε h N hN (TJ u),
      action ε hε h N hN y+
        commutatorVector ε hε h N hN hh m g k (TJ u) (TB u)) ∈
      (TstatOp).graph := by
  have hchar := (KFCausalClosedGraphForm.hamiltonian_domain_characterization TD
    (formAction ε hε h N hN hb hh m g k u)
    (action ε hε h N hN y+
      commutatorVector ε hε h N hN hh m g k (TJ u) (TB u))).mpr
      (formAction_variational_pairing ε hε h N hN hb hh m g k u y hy)
  obtain ⟨hd,he⟩ := hchar
  have hg : (TJ (formAction ε hε h N hN hb hh m g k u),
      action ε hε h N hN y+
        commutatorVector ε hε h N hN hh m g k (TJ u) (TB u)) ∈
      (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw m g k 0).graph :=
    (LinearPMap.mem_graph_iff _).mpr ⟨⟨_,hd⟩,rfl,he⟩
  exact hamiltonian_graph_cast ε hε h hb hh m g k
    (formAction_embedding ε hε h N hN hb hh m g k u) hg

private theorem mem_hamiltonian_domain_of_mem (f : Hilbert) (hf : f ∈ (TstatOp).domain) :
    f ∈ (KFCausalClosedGraphForm.hamiltonian TD).domain := by
  change f ∈ (KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hw m g k 0).domain
  rwa [hamiltonian_eq_operator]

def domainFormLift (x : (TstatOp).domain) : TV :=
  KFCausalClosedGraphForm.formLift TD
    ⟨(x:Hilbert),mem_hamiltonian_domain_of_mem ε hε h hb hh m g k (x:Hilbert) x.property⟩

theorem domainFormLift_embedding (x : (TstatOp).domain) :
    TJ (domainFormLift ε hε h hb hh m g k x) = (x:Hilbert) :=
  KFCausalClosedGraphForm.embedding_formLift TD _

theorem domainFormLift_represents (x : (TstatOp).domain) (w : TV) :
    inner ℂ (TB (domainFormLift ε hε h hb hh m g k x)) (TB w) =
      inner ℂ (TstatOp x) (TJ w) := by
  let xh : (KFCausalClosedGraphForm.hamiltonian TD).domain :=
    ⟨(x:Hilbert),mem_hamiltonian_domain_of_mem ε hε h hb hh m g k (x:Hilbert) x.property⟩
  have hp := KFCausalClosedGraphForm.hamiltonian_represents_form TD xh w
  have hg : ((x:Hilbert),KFCausalClosedGraphForm.hamiltonian TD xh) ∈ (TstatOp).graph :=
    hamiltonian_graph_cast ε hε h hb hh m g k rfl
      ((KFCausalClosedGraphForm.hamiltonian TD).mem_graph xh)
  have heq : KFCausalClosedGraphForm.hamiltonian TD xh = TstatOp x :=
    (TstatOp).mem_graph_snd_inj' hg ((TstatOp).mem_graph x) rfl
  exact hp.trans (congrArg (fun z => inner ℂ z (TJ w)) heq)

private theorem output_norm_of_inner_eq (z : EnergyOutputSpace) (y f : Hilbert)
    (hp : inner ℂ z z = inner ℂ y f) :
    ‖z‖ ≤ Real.sqrt (‖y‖*‖f‖) := by
  have hsq : ‖z‖^2 ≤ ‖y‖*‖f‖ := by
    calc
      ‖z‖^2 = (inner ℂ z z).re := (inner_self_eq_norm_sq (𝕜 := ℂ) z).symm
      _ = (inner ℂ y f).re := by rw [hp]
      _ ≤ ‖inner ℂ y f‖ := Complex.re_le_norm _
      _ ≤ ‖y‖*‖f‖ := norm_inner_le_norm _ _
  exact Real.le_sqrt_of_sq_le hsq

theorem domainFormLift_output_norm (x : (TstatOp).domain) :
    ‖TB (domainFormLift ε hε h hb hh m g k x)‖ ≤
      Real.sqrt (‖TstatOp x‖*‖(x:Hilbert)‖) := by
  have hp := (domainFormLift_represents ε hε h hb hh m g k x
    (domainFormLift ε hε h hb hh m g k x)).trans
    (congrArg (inner ℂ (TstatOp x)) (domainFormLift_embedding ε hε h hb hh m g k x))
  exact output_norm_of_inner_eq
    (TB (domainFormLift ε hε h hb hh m g k x)) (TstatOp x) (x:Hilbert) hp

private theorem resolvent_graph_of_eq {f₁ f₂ y : Hilbert} {z : EnergyOutputSpace}
    (hf : f₁ = f₂)
    (hg : (action ε hε h N hN f₁,
      action ε hε h N hN y+
        commutatorVector ε hε h N hN hh m g k f₁ z) ∈ (TstatOp).graph) :
    (action ε hε h N hN f₂,
      action ε hε h N hN y+
        commutatorVector ε hε h N hN hh m g k f₂ z) ∈ (TstatOp).graph :=
  hf ▸ hg

theorem staticOperator_resolvent_graph (x : (TstatOp).domain) :
    (action ε hε h N hN (x:Hilbert),
      action ε hε h N hN (TstatOp x)+
        commutatorVector ε hε h N hN hh m g k (x:Hilbert)
          (TB (domainFormLift ε hε h hb hh m g k x))) ∈ (TstatOp).graph :=
  resolvent_graph_of_eq ε hε h N hN hh m g k
    (domainFormLift_embedding ε hε h hb hh m g k x)
    (formAction_hamiltonian_graph ε hε h N hN hb hh m g k
      (domainFormLift ε hε h hb hh m g k x) (TstatOp x)
      (domainFormLift_represents ε hε h hb hh m g k x))

include hb hh m g k in
theorem staticOperator_resolvent_domain (f : Hilbert) (hf : f ∈ (TstatOp).domain) :
    action ε hε h N hN f ∈ (TstatOp).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (staticOperator_resolvent_graph ε hε h N hN hb hh m g k ⟨f,hf⟩)

include hb hh m g k in
theorem staticOperator_yosida_domain (f : Hilbert) (hf : f ∈ (TstatOp).domain) :
    KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f ∈ (TstatOp).domain := by
  have hj := staticOperator_resolvent_domain ε hε h N hN hb hh m g k f hf
  have hsub := (TstatOp).domain.sub_mem hf hj
  have hsmul := (TstatOp).domain.smul_mem (N:ℂ) hsub
  have heq : (N:ℂ) • (f-action ε hε h N hN f) =
      KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f := by
    rw [resolvent_apply,sub_sub_cancel,smul_smul]
    have hNne : (N:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
    rw [mul_inv_cancel₀ hNne,one_smul]
  rwa [heq] at hsmul

theorem staticOperator_resolvent_apply (x : (TstatOp).domain) :
    TstatOp ⟨action ε hε h N hN (x:Hilbert),
      staticOperator_resolvent_domain ε hε h N hN hb hh m g k (x:Hilbert) x.property⟩ =
      action ε hε h N hN (TstatOp x)+
        commutatorVector ε hε h N hN hh m g k (x:Hilbert)
          (TB (domainFormLift ε hε h hb hh m g k x)) :=
  (TstatOp).mem_graph_snd_inj'
    ((TstatOp).mem_graph _)
    (staticOperator_resolvent_graph ε hε h N hN hb hh m g k x) rfl

theorem staticOperator_resolvent_commutator_eq (x : (TstatOp).domain) :
    TstatOp ⟨action ε hε h N hN (x:Hilbert),
      staticOperator_resolvent_domain ε hε h N hN hb hh m g k (x:Hilbert) x.property⟩-
      action ε hε h N hN (TstatOp x) =
      commutatorVector ε hε h N hN hh m g k (x:Hilbert)
        (TB (domainFormLift ε hε h hb hh m g k x)) :=
  (congrArg (fun w => w-action ε hε h N hN (TstatOp x))
    (staticOperator_resolvent_apply ε hε h N hN hb hh m g k x)).trans
    (add_sub_cancel_left _ _)

theorem staticOperator_resolvent_commutator_bound (x : (TstatOp).domain) :
    ‖TstatOp ⟨action ε hε h N hN (x:Hilbert),
        staticOperator_resolvent_domain ε hε h N hN hb hh m g k (x:Hilbert) x.property⟩-
      action ε hε h N hN (TstatOp x)‖ ≤
      (3*(N⁻¹*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹)))*
        Real.sqrt (‖TstatOp x‖*‖(x:Hilbert)‖)+
      (N⁻¹*(6*h^2/ε^2))*‖(x:Hilbert)‖ := by
  have heq := congrArg norm
    (staticOperator_resolvent_commutator_eq ε hε h N hN hb hh m g k x)
  have hc := commutatorVector_norm ε hε h N hN hh m g k (x:Hilbert)
    (TB (domainFormLift ε hε h hb hh m g k x))
  have hb0 := domainFormLift_output_norm ε hε h hb hh m g k x
  have h1 := mul_le_mul_of_nonneg_left hb0
    (show 0 ≤ 3*(N⁻¹*(|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹)) by positivity)
  linarith

include hε in
private theorem rate_first_tendsto :
    Tendsto (fun n : ℕ =>
      3*((((n:ℝ)+1)⁻¹)*(|h| *Real.sqrt (((n:ℝ)+1)/ε)*(Real.sqrt ε)⁻¹)))
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (((n:ℝ)+1)⁻¹:ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hsq_tendsto : Tendsto (fun n : ℕ => (h^2/ε^2)*(((n:ℝ)+1)⁻¹:ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hinv.const_mul (h^2/ε^2)
  have hsqrt_tendsto : Tendsto (fun n : ℕ =>
      Real.sqrt ((h^2/ε^2)*(((n:ℝ)+1)⁻¹:ℝ))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hsq_tendsto
  have hrate : Tendsto (fun n : ℕ =>
      (((n:ℝ)+1)⁻¹)*(|h| *Real.sqrt (((n:ℝ)+1)/ε)*(Real.sqrt ε)⁻¹)) atTop (𝓝 0) := by
    apply hsqrt_tendsto.congr
    intro n
    have hNn : 0 < (n:ℝ)+1 := by positivity
    have hnonneg : 0 ≤ ((n:ℝ)+1)⁻¹*(|h| *Real.sqrt (((n:ℝ)+1)/ε)*(Real.sqrt ε)⁻¹) := by positivity
    rw [← Real.sqrt_sq hnonneg]
    congr 1
    simp only [mul_pow,inv_pow,sq_abs,
      Real.sq_sqrt (div_nonneg hNn.le hε.le),Real.sq_sqrt hε.le]
    field_simp [hNn.ne',hε.ne']
  simpa only [mul_zero] using hrate.const_mul 3

private theorem rate_second_tendsto :
    Tendsto (fun n : ℕ => (((n:ℝ)+1)⁻¹)*(6*h^2/ε^2)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (((n:ℝ)+1)⁻¹:ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  simpa only [zero_mul] using hinv.mul_const (6*h^2/ε^2)

theorem commutatorVector_tendsto (f : Hilbert) (z : EnergyOutputSpace) :
    Tendsto (fun n : ℕ =>
      commutatorVector ε hε h ((n:ℝ)+1) (by positivity) hh m g k f z)
      atTop (𝓝 0) := by
  have h1 := (rate_first_tendsto ε hε h).mul_const ‖z‖
  have h2 := (rate_second_tendsto ε h).mul_const ‖f‖
  have hbound : Tendsto (fun n : ℕ =>
      (3*((((n:ℝ)+1)⁻¹)*(|h| *Real.sqrt (((n:ℝ)+1)/ε)*(Real.sqrt ε)⁻¹)))*‖z‖+
        ((((n:ℝ)+1)⁻¹)*(6*h^2/ε^2))*‖f‖) atTop (𝓝 0) := by
    simpa only [zero_mul,add_zero] using h1.add h2
  have hn : Tendsto (fun n : ℕ =>
      ‖commutatorVector ε hε h ((n:ℝ)+1) (by positivity) hh m g k f z‖)
      atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun n => commutatorVector_norm ε hε h ((n:ℝ)+1) (by positivity) hh m g k f z)
      hbound
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hn)

include hb hh m g k in
theorem staticOperator_resolvent_commutator_tendsto (x : (TstatOp).domain) :
    Tendsto (fun n : ℕ =>
      TstatOp ⟨action ε hε h ((n:ℝ)+1) (by positivity) (x:Hilbert),
        staticOperator_resolvent_domain ε hε h ((n:ℝ)+1) (by positivity)
          hb hh m g k (x:Hilbert) x.property⟩-
        action ε hε h ((n:ℝ)+1) (by positivity) (TstatOp x))
      atTop (𝓝 0) :=
  (commutatorVector_tendsto ε hε h hh m g k (x:Hilbert)
    (TB (domainFormLift ε hε h hb hh m g k x))).congr
    (fun n => (staticOperator_resolvent_commutator_eq ε hε h ((n:ℝ)+1) (by positivity)
      hb hh m g k x).symm)

include hb hh m g k in
theorem staticOperator_resolvent_tendsto (x : (TstatOp).domain) :
    Tendsto (fun n : ℕ =>
      TstatOp ⟨action ε hε h ((n:ℝ)+1) (by positivity) (x:Hilbert),
        staticOperator_resolvent_domain ε hε h ((n:ℝ)+1) (by positivity)
          hb hh m g k (x:Hilbert) x.property⟩)
      atTop (𝓝 (TstatOp x)) := by
  have h1 := sequence_tendsto ε hε h (TstatOp x)
  have h2 := commutatorVector_tendsto ε hε h hh m g k (x:Hilbert)
    (TB (domainFormLift ε hε h hb hh m g k x))
  have hsum : Tendsto (fun n : ℕ =>
      action ε hε h ((n:ℝ)+1) (by positivity) (TstatOp x)+
        commutatorVector ε hε h ((n:ℝ)+1) (by positivity) hh m g k (x:Hilbert)
          (TB (domainFormLift ε hε h hb hh m g k x)))
      atTop (𝓝 (TstatOp x)) := by
    simpa only [add_zero] using h1.add h2
  exact hsum.congr (fun n =>
    (staticOperator_resolvent_apply ε hε h ((n:ℝ)+1) (by positivity) hb hh m g k x).symm)

#print axioms resolvent_selfAdjoint_pairing
#print axioms orbitAdjoint_inner
#print axioms orbitAdjoint_norm
#print axioms scaledExtraAdjoint_inner
#print axioms scaledExtraAdjoint_norm
#print axioms commutatorVector_inner
#print axioms commutatorVector_norm
#print axioms formAction_variational_pairing
#print axioms formAction_hamiltonian_graph
#print axioms domainFormLift_embedding
#print axioms domainFormLift_represents
#print axioms domainFormLift_output_norm
#print axioms staticOperator_resolvent_graph
#print axioms staticOperator_resolvent_domain
#print axioms staticOperator_yosida_domain
#print axioms staticOperator_resolvent_apply
#print axioms staticOperator_resolvent_commutator_eq
#print axioms staticOperator_resolvent_commutator_bound
#print axioms commutatorVector_tendsto
#print axioms staticOperator_resolvent_commutator_tendsto
#print axioms staticOperator_resolvent_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventStaticDomain
