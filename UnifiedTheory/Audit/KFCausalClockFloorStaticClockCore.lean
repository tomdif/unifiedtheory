/- The completed original static energy form is stable under the
inverse-clock defect operator, making the associated static kinetic
Hamiltonian inverse-clock accretive at each physical time t. Consequently,
positive shifted resolvents of the static Hamiltonian preserve the unbounded
half-clock domain, their scaled approximants converge in the half-clock
graph norm, and the intersection of the static Hamiltonian domain with the
half-clock domain is a graph core for both operators. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorPotentialClockCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticClockCore
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)
open KFCausalClockFloorShiftedDefect (shiftedDefect shiftedDefect_coe symbol shift_bound)
open KFCausalClockFloorEnergyDefectAction (factorAction outputAction outputAction_apply)
open KFCausalClockFloorClockOperator (clockOperator defect_clock)
open KFCausalClockFloorPureClockClockResponse (half_graph)
open KFCausalClockFloorGrowingClockResolvent (inverse_pairing inverse_selfAdjoint inverse_dense)
open KFCausalClockFloorPotentialClockApproximation (cutoff cutoff_pos cutoff_tendsto)
open KFCausalHamiltonianCoreFromSources (graphMap sectorGraph source_graph_closure)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)

private theorem multiplier_real_nonnegative
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (m : X → ℂ) (f g : Lp ℂ 2 μ) (hm : ∀ x, 0 ≤ (m x).re)
    (hg : g =ᵐ[μ] fun x => m x*f x) : 0 ≤ (inner ℂ f g).re := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
  change (∫ x, (inner ℂ (f x) (g x)).re ∂μ)=
    (∫ x, inner ℂ (f x) (g x) ∂μ).re at he
  rw [L2.inner_def,← he]
  apply integral_nonneg_of_ae
  filter_upwards [hg] with x hx
  rw [hx]
  change 0 ≤ (inner ℂ (f x) (m x • f x)).re
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change 0 ≤ (m x*((‖f x‖:ℝ):ℂ)^2).re
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_nonneg (hm x) (sq_nonneg ‖f x‖)

private theorem dense_contraction_identity {X E ι : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (J : E → X) (hJ : DenseRange J) (S : ι → X →L[ℂ] X)
    (hS : ∀ i x, ‖S i x‖ ≤ ‖x‖) (l : Filter ι)
    (hc : ∀ w, Tendsto (fun i => S i (J w)) l (𝓝 (J w))) (x : X) :
    Tendsto (fun i => S i x) l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨w,hw⟩ := hJ.exists_dist_lt x (show 0 < δ/3 from by positivity)
  have hl := Metric.tendsto_nhds.mp (hc w) (δ/3) (by positivity)
  filter_upwards [hl] with i hi
  have hd : dist (S i x) (S i (J w)) ≤ dist x (J w) := by
    simpa only [dist_eq_norm,map_sub] using hS i (x-J w)
  have ht := dist_triangle (S i x) (S i (J w)) x
  have ht' := dist_triangle (S i (J w)) (J w) x
  rw [dist_comm (J w) x] at ht'
  linarith

private theorem adjoint_contraction_identity {X ι : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (S : ι → X →L[ℂ] X) (hS : ∀ i, ‖S i‖ ≤ 1) (l : Filter ι)
    (hc : ∀ x, Tendsto (fun i => S i x) l (𝓝 x)) (x : X) :
    Tendsto (fun i => (S i).adjoint x) l (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  have hd : 0 < 2*‖x‖+1 := by positivity
  have hl := Metric.tendsto_nhds.mp (hc x) (δ^2/(2*‖x‖+1)) (by positivity)
  filter_upwards [hl] with i hi
  have hn : ‖(S i).adjoint x‖ ≤ ‖x‖ := by
    apply ((S i).adjoint.le_opNorm x).trans
    simpa only [LinearIsometryEquiv.norm_map,one_mul] using
      mul_le_mul_of_nonneg_right (hS i) (norm_nonneg x)
  have hs := norm_sub_sq (𝕜 := ℂ) ((S i).adjoint x) x
  change ‖(S i).adjoint x-x‖^2 = ‖(S i).adjoint x‖^2-
    2*(inner ℂ ((S i).adjoint x) x).re+‖x‖^2 at hs
  rw [ContinuousLinearMap.adjoint_inner_left] at hs
  have hp := re_inner_le_norm (𝕜 := ℂ) x (x-S i x)
  rw [inner_sub_right,KFCausalShiftedForm.complex_inner_square] at hp
  change ‖x‖^2-(inner ℂ x (S i x)).re ≤ ‖x‖*‖x-S i x‖ at hp
  rw [norm_sub_rev x (S i x)] at hp
  rw [dist_eq_norm] at hi ⊢
  have hi' := (lt_div_iff₀ hd).mp hi
  have hnn := norm_nonneg ((S i).adjoint x)
  have hnx := norm_nonneg x
  have hne := norm_nonneg (S i x-x)
  have hnd := norm_nonneg ((S i).adjoint x-x)
  nlinarith

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "L" => inverseL ε hε
local notation "D" => defectOperator ε hε
local notation "R_out" => outputAction ε hε h hb
local notation "L_out" => ContinuousLinearMap.compLpL 2 angleMeasure R_out
local notation "TD" => KFCausalClockFloorStaticHamiltonian.formData ε hε h hh hb m g k t
local notation "TV" => KFCausalClockFloorStaticHamiltonian.StaticForm ε hε h hh hb m g k t
local notation "TJ" => KFCausalClosedGraphForm.embedding TD
local notation "TB" => KFCausalClosedGraphForm.energyOutput TD
local notation "T_op" => KFCausalClockFloorStaticHamiltonian.hamiltonian ε hε h hh hb m g k t

private theorem factor_real_nonnegative (i : Fin 8) (f : Hilbert) :
    0 ≤ (inner ℂ f (factorAction ε hε h hb i f)).re := by
  unfold factorAction
  split_ifs with hi
  · exact multiplier_real_nonnegative _ f (D f)
      (fun x => (KFCausalClockFloorCanonicalDefect.defect_positive ε x.1 hε).le)
      (defectOperator_coe ε hε f)
  · have hs := multiplier_real_nonnegative (symbol ε h)
      (KFCausalClockFloorDefectCoordinates.straightening ε hε f)
      (KFCausalClockFloorDefectCoordinates.straightening ε hε (shiftedDefect ε hε h hb f))
      (fun x => KFCausalClockFloorDefectSign.complexDefect_re_nonnegative ε hε _
        (KFCausalClockFloorFullGaussian.third_strip_subset ε hε _
          (by simpa using shift_bound ε h hb)))
      (shiftedDefect_coe ε hε h hb f)
    simpa only [LinearIsometryEquiv.inner_map_map] using hs

private theorem output_real_nonnegative (f : Output (Fin 8) Hilbert) :
    0 ≤ (inner ℂ f (R_out f)).re := by
  rw [PiLp.inner_apply,Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => factor_real_nonnegative ε hε h hb i (f i))

private theorem outputLp_real_nonnegative (f : EnergyOutputSpace) :
    0 ≤ (inner ℂ f (L_out f)).re := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) f (L_out f))
  change (∫ θ, (inner ℂ (f θ) (L_out f θ)).re ∂angleMeasure)=
    (∫ θ, inner ℂ (f θ) (L_out f θ) ∂angleMeasure).re at he
  rw [L2.inner_def,← he]
  apply integral_nonneg_of_ae
  filter_upwards [(R_out).coeFn_compLp f] with θ hθ
  change (R_out).compLp f θ=R_out (f θ) at hθ
  change 0 ≤ (inner ℂ (f θ) ((R_out).compLp f θ)).re
  rw [hθ]
  exact output_real_nonnegative ε hε h hb (f θ)

private theorem static_commute (f : EnergyOutputSpace) :
    staticOutputLp (L_out f) = L_out (staticOutputLp f) := by
  apply Lp.ext
  filter_upwards [KFCausalPhysicalEnergyTransport.staticOutput.coeFn_compLp (L_out f),
    (R_out).coeFn_compLp f,(R_out).coeFn_compLp (staticOutputLp f),
    KFCausalPhysicalEnergyTransport.staticOutput.coeFn_compLp f] with θ h1 h2 h3 h4
  change KFCausalPhysicalEnergyTransport.staticOutput.compLp ((R_out).compLp f) θ =
    (R_out).compLp (KFCausalPhysicalEnergyTransport.staticOutput.compLp f) θ
  change KFCausalPhysicalEnergyTransport.staticOutput.compLp ((R_out).compLp f) θ =
    KFCausalPhysicalEnergyTransport.staticOutput ((R_out).compLp f θ) at h1
  change (R_out).compLp (KFCausalPhysicalEnergyTransport.staticOutput.compLp f) θ =
    R_out (KFCausalPhysicalEnergyTransport.staticOutput.compLp f θ) at h3
  rw [h1,h2,h3,h4]
  apply PiLp.ext
  intro i
  simp only [KFCausalPhysicalEnergyTransport.staticOutput,
    KFCausalFiniteOutputRescaling.selected_apply,outputAction_apply]
  split_ifs <;> simp only [map_zero]

private theorem averaged_static_defect
    (u : KFCausalClockFloorAveragedEnergy.AveragedSpace ε hε h (hamiltonian_bound ε h hb) hh m g k t) :
    ∃ u' : KFCausalClockFloorAveragedEnergy.AveragedSpace ε hε h (hamiltonian_bound ε h hb) hh m g k t,
      KFCausalClockFloorAveragedEnergy.embedding ε hε h (hamiltonian_bound ε h hb) hh m g k t u' =
        D (KFCausalClockFloorAveragedEnergy.embedding ε hε h (hamiltonian_bound ε h hb) hh m g k t u) ∧
      KFCausalClockFloorStaticRootSource.staticOutput ε hε h hh hb m g k t u' =
        L_out (KFCausalClockFloorStaticRootSource.staticOutput ε hε h hh hb m g k t u) := by
  let lift := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hb m g k t
  have hl : Function.Surjective lift :=
    KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hb m g k t
  let w := lift u
  let fw := KFCausalClockFloorReferenceClockCore.formDefect ε hε h hh hb m g k t w
  let u' := Classical.choose (hl fw)
  have hu' : lift u' = fw := Classical.choose_spec (hl fw)
  refine ⟨u',?_,?_⟩
  · have he1 := (KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding
      ε hε h hh hb m g k t u').symm
    have he2 := congrArg (KFCausalClosedGraphForm.embedding
      (KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hb m g k t)) hu'
    have he3 := KFCausalClockFloorReferenceClockCore.defect_embedding ε hε h hh hb m g k t w
    have he4 := congrArg D (KFCausalClockFloorAveragedHamiltonian.graphFormVector_embedding
      ε hε h hh hb m g k t u)
    exact he1.trans (he2.trans (he3.trans he4))
  · have ho1 := (KFCausalClockFloorAveragedHamiltonian.graphFormVector_output
      ε hε h hh hb m g k t u').symm
    have ho2 := congrArg (KFCausalClosedGraphForm.energyOutput
      (KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hb m g k t)) hu'
    have ho3 := KFCausalClockFloorReferenceClockCore.defect_output ε hε h hh hb m g k t w
    have ho4 := congrArg L_out (KFCausalClockFloorAveragedHamiltonian.graphFormVector_output
      ε hε h hh hb m g k t u)
    have ho : KFCausalClockFloorAveragedEnergy.energyOutput ε hε h (hamiltonian_bound ε h hb) hh m g k t u' =
        L_out (KFCausalClockFloorAveragedEnergy.energyOutput ε hε h (hamiltonian_bound ε h hb) hh m g k t u) :=
      ho1.trans (ho2.trans (ho3.trans ho4))
    exact (congrArg staticOutputLp ho).trans
      (static_commute ε hε h hb
        (KFCausalClockFloorAveragedEnergy.energyOutput ε hε h (hamiltonian_bound ε h hb) hh m g k t u))

theorem static_output_defect (f : Hilbert) (y : EnergyOutputSpace)
    (hy : (f,y) ∈ (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g k t).graph) :
    (D f,L_out y) ∈ (KFCausalClockFloorStaticOutputClosure.operator ε hε h hh hb m g k t).graph := by
  rw [KFCausalClockFloorStaticOutputClosure.operator_graph] at hy ⊢
  let G0 := KFCausalClockFloorStaticOutputClosure.initialGraph ε hε h hh hb m g k t
  let M := (D).prodMap L_out
  have hG : G0 ≤ G0.topologicalClosure.comap M.toLinearMap := by
    rintro z ⟨u,rfl⟩
    apply G0.le_topologicalClosure
    have hd := averaged_static_defect ε hε h hh hb m g k t u
    let u' := Classical.choose hd
    have hu' := Classical.choose_spec hd
    exact ⟨u',congrArg₂ Prod.mk hu'.1 hu'.2⟩
  exact G0.topologicalClosure_minimal hG (G0.isClosed_topologicalClosure.preimage M.continuous) hy

def staticFormDefect : TV →L[ℂ] TV :=
  KFCausalClosedGraphDiagonalAction.action TD D L_out
    (static_output_defect ε hε h hh hb m g k t)

theorem staticFormDefect_embedding (u : TV) :
    TJ (staticFormDefect ε hε h hh hb m g k t u) = D (TJ u) := rfl

theorem staticFormDefect_output (u : TV) :
    TB (staticFormDefect ε hε h hh hb m g k t u) = L_out (TB u) := rfl

private theorem form_accretive
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (A : KFCausalClosedGraphForm.Data X Y) (dMap : X →L[ℂ] X) (lMap : Y →L[ℂ] Y)
    (F : KFCausalClosedGraphForm.FormSpace A →L[ℂ] KFCausalClosedGraphForm.FormSpace A)
    (hj : ∀ u, KFCausalClosedGraphForm.embedding A (F u)=dMap (KFCausalClosedGraphForm.embedding A u))
    (he : ∀ u, KFCausalClosedGraphForm.energyOutput A (F u)=lMap (KFCausalClosedGraphForm.energyOutput A u))
    (hp : ∀ y, 0 ≤ (inner ℂ y (lMap y)).re)
    (x : (KFCausalClosedGraphForm.hamiltonian A).domain) :
    0 ≤ (inner ℂ (KFCausalClosedGraphForm.hamiltonian A x) (dMap (x : X))).re := by
  have hpair := KFCausalClosedGraphForm.hamiltonian_represents_form A x
    (F (KFCausalClosedGraphForm.formLift A x))
  rw [hj,he,KFCausalClosedGraphForm.embedding_formLift] at hpair
  rw [← hpair]
  exact hp _

private theorem form_mixed_accretive
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (A : KFCausalClosedGraphForm.Data X Y) (dMap : X →L[ℂ] X) (lMap : Y →L[ℂ] Y)
    (F : KFCausalClosedGraphForm.FormSpace A →L[ℂ] KFCausalClosedGraphForm.FormSpace A)
    (hj : ∀ u, KFCausalClosedGraphForm.embedding A (F u)=dMap (KFCausalClosedGraphForm.embedding A u))
    (he : ∀ u, KFCausalClosedGraphForm.energyOutput A (F u)=lMap (KFCausalClosedGraphForm.energyOutput A u))
    (hp : ∀ y, 0 ≤ (inner ℂ y (lMap y)).re)
    (x : (KFCausalClosedGraphForm.hamiltonian A).domain)
    (v : KFCausalClosedGraphForm.FormSpace A) (c : ℝ) (hc : 0 < c)
    (hd : dMap (KFCausalClosedGraphForm.embedding A v)=(c:ℂ) • (x:X)) :
    0 ≤ (inner ℂ (KFCausalClosedGraphForm.hamiltonian A x)
      (KFCausalClosedGraphForm.embedding A v)).re := by
  let u := KFCausalClosedGraphForm.formLift A x
  have hu : F v=(c:ℂ) • u := by
    apply KFCausalClosedGraphForm.embedding_injective A
    rw [hj,map_smul,KFCausalClosedGraphForm.embedding_formLift]
    exact hd
  have hb' : lMap (KFCausalClosedGraphForm.energyOutput A v)=
      (c:ℂ) • KFCausalClosedGraphForm.energyOutput A u := by
    rw [← he,hu,map_smul]
  have hpos := hp (KFCausalClosedGraphForm.energyOutput A v)
  rw [hb',inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hpos
  have hr : 0 ≤ (inner ℂ (KFCausalClosedGraphForm.energyOutput A v)
      (KFCausalClosedGraphForm.energyOutput A u)).re := (mul_nonneg_iff_of_pos_left hc).mp hpos
  rw [show (inner ℂ (KFCausalClosedGraphForm.energyOutput A v)
      (KFCausalClosedGraphForm.energyOutput A u)).re=
      (inner ℂ (KFCausalClosedGraphForm.energyOutput A u)
      (KFCausalClosedGraphForm.energyOutput A v)).re from inner_re_symm (𝕜 := ℂ) _ _] at hr
  rw [← KFCausalClosedGraphForm.hamiltonian_represents_form A x v]
  exact hr

theorem static_inverse_clock_accretive (x : (T_op).domain) :
    0 ≤ (inner ℂ (T_op x) (D (x : Hilbert))).re :=
  form_accretive TD D L_out (staticFormDefect ε hε h hh hb m g k t)
    (staticFormDefect_embedding ε hε h hh hb m g k t)
    (staticFormDefect_output ε hε h hh hb m g k t)
    (outputLp_real_nonnegative ε hε h hb) x

theorem static_clock_form_accretive (x : (T_op).domain) (v : TV)
    (hc : ((x : Hilbert),TJ v) ∈ (clockOperator ε hε).graph) :
    0 ≤ (inner ℂ (T_op x) (TJ v)).re :=
  form_mixed_accretive TD D L_out (staticFormDefect ε hε h hh hb m g k t)
    (staticFormDefect_embedding ε hε h hh hb m g k t)
    (staticFormDefect_output ε hε h hh hb m g k t)
    (outputLp_real_nonnegative ε hε h hb) x v ε hε (defect_clock ε hε _ _ hc)

def unitResolvent : Hilbert →L[ℂ] Hilbert := KFCausalFormResolvent.resolvent TJ
local notation "R1" => unitResolvent ε hε h hh hb m g k t

private theorem r_injective : Function.Injective R1 :=
  KFCausalFormResolvent.resolvent_injective TJ
    (KFCausalClosedGraphForm.embedding_injective TD) (KFCausalClosedGraphForm.embedding_dense TD)

private theorem r_positive (x : Hilbert) : 0 ≤ (inner ℂ (R1 x) x).re :=
  (KFCausalFormResolvent.resolvent_positive TJ x).trans_eq
    (congrArg Complex.re (KFCausalFormResolvent.resolvent_symmetric TJ x x).symm)

private theorem r_contraction (x : Hilbert) : ‖R1 x‖ ≤ ‖x‖ := by
  have hj : ‖TJ‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
    simpa only [one_mul] using KFCausalClosedGraphForm.embedding_contraction TD v)
  exact ((R1).le_opNorm x).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (KFCausalFormResolvent.resolvent_norm_le_one TJ hj) (norm_nonneg x))

private theorem shift_isUnit (a : ℝ) (ha : 0 < a) :
    IsUnit (KFCausalShiftedResolventFromOne.shift R1 a) :=
  KFCausalShiftedResolventFromOne.shift_isUnit R1 a ha (r_positive ε hε h hh hb m g k t)
    (r_contraction ε hε h hh hb m g k t) (KFCausalFormResolvent.resolvent_symmetric TJ)

def resolvent (a : ℝ) : Hilbert →L[ℂ] Hilbert := KFCausalShiftedResolventFromOne.resolvent R1 a
local notation "R" => resolvent ε hε h hh hb m g k t

theorem resolves (a : ℝ) (ha : 0 < a) :
    KFCausalPositiveResolventBounds.Resolves T_op (R a) a :=
  KFCausalShiftedResolventFromOne.resolves R1 (r_injective ε hε h hh hb m g k t) a
    (shift_isUnit ε hε h hh hb m g k t a ha)

theorem left_inverse (a : ℝ) (ha : 0 < a) (x : (T_op).domain) :
    R a (T_op x + a • (x : Hilbert)) = x :=
  KFCausalShiftedResolventFromOne.left_inverse R1 (r_injective ε hε h hh hb m g k t) a
    (shift_isUnit ε hε h hh hb m g k t a ha) x

theorem weighted_resolvent_bound (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖L (R a f)‖ ≤ a⁻¹*‖L f‖ := by
  let hr := resolves ε hε h hh hb m g k t a ha
  have hp := static_inverse_clock_accretive
    ε hε h hh hb m g k t (KFCausalPositiveResolventBounds.point T_op (R a) a hr f)
  change 0 ≤ (inner ℂ (T_op (KFCausalPositiveResolventBounds.point T_op (R a) a hr f))
    (D (R a f))).re at hp
  rw [KFCausalPositiveResolventBounds.point_value,inner_sub_left,
    inner_smul_left_eq_smul,← inverse_pairing ε hε f (R a f),
    ← inverse_pairing ε hε (R a f) (R a f),
    KFCausalShiftedForm.complex_inner_square] at hp
  simp only [Complex.sub_re,Complex.real_smul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hp
  have hl : a*‖L (R a f)‖^2 ≤ (inner ℂ (L f) (L (R a f))).re := by
    nlinarith
  by_cases hz : L (R a f) = 0
  · rw [hz,norm_zero]
    positivity
  have hn : 0 < ‖L (R a f)‖ := norm_pos_iff.mpr hz
  apply (le_inv_mul_iff₀ ha).mpr
  apply (mul_le_mul_iff_right₀ hn).mp
  have hi : (inner ℂ (L f) (L (R a f))).re ≤ ‖L f‖*‖L (R a f)‖ :=
    re_inner_le_norm (𝕜 := ℂ) (L f) (L (R a f))
  nlinarith

def weightedResolvent (a : ℝ) : Hilbert →L[ℂ] Hilbert :=
  ((L).comp (R a)).toLinearMap.extendOfNorm (L).toLinearMap
local notation "W" => weightedResolvent ε hε h hh hb m g k t

theorem weighted_intertwines (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    W a (L f) = L (R a f) :=
  LinearMap.extendOfNorm_eq (inverse_dense ε hε)
    ⟨a⁻¹,weighted_resolvent_bound ε hε h hh hb m g k t a ha⟩ f

theorem weighted_norm_bound (a : ℝ) (ha : 0 < a) :
    ‖W a‖ ≤ a⁻¹ :=
  LinearMap.opNorm_extendOfNorm_le (inverse_dense ε hε) (inv_nonneg.mpr ha.le)
    (weighted_resolvent_bound ε hε h hh hb m g k t a ha)

theorem dual_intertwines (a : ℝ) (ha : 0 < a) (f : Hilbert) :
    R a (L f) = L ((W a).adjoint f) := by
  have he : (W a).comp L = (L).comp (R a) := by
    apply ContinuousLinearMap.ext
    intro x
    exact weighted_intertwines ε hε h hh hb m g k t a ha x
  have hl := (inverse_selfAdjoint ε hε).isSymmetric.clm_adjoint_eq
  have hr := (KFCausalPositiveResolventBounds.resolvent_selfAdjoint T_op (R a) a
    (resolves ε hε h hh hb m g k t a ha)
    (KFCausalClosedGraphForm.hamiltonian_selfAdjoint TD)).isSymmetric.clm_adjoint_eq
  have hd := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A.adjoint) he
  change ((W a).comp L).adjoint = ((L).comp (R a)).adjoint at hd
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,hl,hr] at hd
  exact (congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f) hd).symm

theorem resolvent_half_graph (a : ℝ) (ha : 0 < a) (f z : Hilbert)
    (hf : (f,z) ∈ (clockHalf ε).graph) :
    (R a f,(W a).adjoint z) ∈ (clockHalf ε).graph := by
  apply (half_graph ε hε _ _).mpr
  rw [(half_graph ε hε f z).mp hf]
  exact dual_intertwines ε hε h hh hb m g k t a ha z

theorem resolvent_half_domain (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) : R a f ∈ (clockHalf ε).domain :=
  LinearPMap.mem_domain_of_mem_graph (resolvent_half_graph ε hε h hh hb m g k t a ha
    f (clockHalf ε ⟨f,hf⟩) ((clockHalf ε).mem_graph ⟨f,hf⟩))

theorem resolvent_half_norm_bound (a : ℝ) (ha : 0 < a) (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    ‖clockHalf ε ⟨R a f,resolvent_half_domain ε hε h hh hb m g k t a ha f hf⟩‖ ≤
      a⁻¹*‖clockHalf ε ⟨f,hf⟩‖ := by
  have hg := resolvent_half_graph ε hε h hh hb m g k t a ha f
    (clockHalf ε ⟨f,hf⟩) ((clockHalf ε).mem_graph ⟨f,hf⟩)
  have he := (clockHalf ε).mem_graph_snd_inj' hg
    ((clockHalf ε).mem_graph ⟨R a f,resolvent_half_domain ε hε h hh hb m g k t a ha f hf⟩) rfl
  change (W a).adjoint (clockHalf ε ⟨f,hf⟩) =
    clockHalf ε ⟨R a f,resolvent_half_domain ε hε h hh hb m g k t a ha f hf⟩ at he
  rw [← he]
  apply ((W a).adjoint.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [LinearIsometryEquiv.norm_map] using weighted_norm_bound ε hε h hh hb m g k t a ha

def approximation (n : ℕ) : Hilbert →L[ℂ] Hilbert := cutoff n • R (cutoff n)
def weightedApproximation (n : ℕ) : Hilbert →L[ℂ] Hilbert := cutoff n • W (cutoff n)

theorem weighted_norm (n : ℕ) :
    ‖weightedApproximation ε hε h hh hb m g k t n‖ ≤ 1 := by
  rw [weightedApproximation,norm_smul,Real.norm_eq_abs,abs_of_pos (cutoff_pos n)]
  calc
    _ ≤ cutoff n * (cutoff n)⁻¹ := mul_le_mul_of_nonneg_left
      (weighted_norm_bound ε hε h hh hb m g k t (cutoff n) (cutoff_pos n)) (cutoff_pos n).le
    _ = 1 := mul_inv_cancel₀ (ne_of_gt (cutoff_pos n))

theorem approximation_strong (f : Hilbert) :
    Tendsto (fun n => approximation ε hε h hh hb m g k t n f) atTop (𝓝 f) := by
  exact (KFCausalYosidaApproximation.scaled_resolvent_strong_limit T_op R
    (KFCausalClosedGraphForm.hamiltonian_dense TD)
    (resolves ε hε h hh hb m g k t)
    (KFCausalClosedGraphForm.hamiltonian_positive TD)
    (left_inverse ε hε h hh hb m g k t) f).comp cutoff_tendsto

theorem weighted_strong (f : Hilbert) :
    Tendsto (fun n => weightedApproximation ε hε h hh hb m g k t n f) atTop (𝓝 f) := by
  apply dense_contraction_identity L (inverse_dense ε hε)
    (weightedApproximation ε hε h hh hb m g k t) _ atTop _ f
  · intro n x
    exact ((weightedApproximation ε hε h hh hb m g k t n).le_opNorm x).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (weighted_norm ε hε h hh hb m g k t n) (norm_nonneg x))
  · intro w
    have ht := (L).continuous.tendsto w |>.comp (approximation_strong ε hε h hh hb m g k t w)
    simpa only [Function.comp_def,weightedApproximation,approximation,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.map_smul_of_tower,weighted_intertwines ε hε h hh hb m g k t _ (cutoff_pos _)] using ht

theorem weighted_adjoint_strong (f : Hilbert) :
    Tendsto (fun n => (weightedApproximation ε hε h hh hb m g k t n).adjoint f) atTop (𝓝 f) :=
  adjoint_contraction_identity _ (weighted_norm ε hε h hh hb m g k t) atTop
    (weighted_strong ε hε h hh hb m g k t) f

theorem approximation_half_graph (n : ℕ) (f z : Hilbert)
    (hf : (f,z) ∈ (clockHalf ε).graph) :
    (approximation ε hε h hh hb m g k t n f,
      (weightedApproximation ε hε h hh hb m g k t n).adjoint z) ∈ (clockHalf ε).graph := by
  have hg := ((clockHalf ε).graph.restrictScalars ℝ).smul_mem (cutoff n)
    (resolvent_half_graph ε hε h hh hb m g k t (cutoff n) (cutoff_pos n) f z hf)
  have he : (weightedApproximation ε hε h hh hb m g k t n).adjoint =
      cutoff n • (W (cutoff n)).adjoint := by
    rw [weightedApproximation,← Complex.coe_smul,map_smulₛₗ]
    simp only [Complex.conj_ofReal,Complex.coe_smul]
  rw [he]
  exact hg

theorem approximation_static_domain (n : ℕ) (f : Hilbert) :
    approximation ε hε h hh hb m g k t n f ∈ (T_op).domain :=
  ((T_op).domain.restrictScalars ℝ).smul_mem (cutoff n)
    (resolves ε hε h hh hb m g k t (cutoff n) (cutoff_pos n) f).1

theorem half_graph_convergence (f z : Hilbert) :
    Tendsto (fun n => (approximation ε hε h hh hb m g k t n f,
      (weightedApproximation ε hε h hh hb m g k t n).adjoint z)) atTop (𝓝 (f,z)) :=
  (approximation_strong ε hε h hh hb m g k t f).prodMk_nhds
    (weighted_adjoint_strong ε hε h hh hb m g k t z)

def commonDomain : Submodule ℂ Hilbert := (T_op).domain ⊓ (clockHalf ε).domain
def staticGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (T_op).graph ⊓ (clockHalf ε).domain.comap (LinearMap.fst ℂ Hilbert Hilbert)
def halfGraph : Submodule ℂ (Hilbert × Hilbert) :=
  (clockHalf ε).graph ⊓ (T_op).domain.comap (LinearMap.fst ℂ Hilbert Hilbert)

theorem static_graph_core :
    (staticGraph ε hε h hh hb m g k t).topologicalClosure = (T_op).graph := by
  have hd : (clockHalf ε).domain.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp (clockHalf_selfAdjoint ε).dense_domain
  have he := source_graph_closure T_op (R 1) 1
    (resolves ε hε h hh hb m g k t 1 zero_lt_one)
    (left_inverse ε hε h hh hb m g k t 1 zero_lt_one)
    (KFCausalClosedGraphForm.hamiltonian_closed TD)
    ⊤ (clockHalf ε).domain isClosed_univ hd (fun _ _ => trivial) (fun _ _ => trivial)
  have hm : (clockHalf ε).domain.map (graphMap (R 1) 1).toLinearMap ≤
      staticGraph ε hε h hh hb m g k t := by
    rintro p ⟨f,hf,rfl⟩
    obtain ⟨hx,hv⟩ := resolves ε hε h hh hb m g k t 1 zero_lt_one f
    exact ⟨(T_op).mem_graph_iff.mpr ⟨⟨R 1 f,hx⟩,rfl,hv⟩,
      resolvent_half_domain ε hε h hh hb m g k t 1 zero_lt_one f hf⟩
  have hc := Submodule.topologicalClosure_mono hm
  rw [he] at hc
  have hs : sectorGraph T_op ⊤ = (T_op).graph := by simp [sectorGraph]
  rw [hs] at hc
  exact le_antisymm (Submodule.topologicalClosure_minimal _ (fun _ hp => hp.1)
    (KFCausalClosedGraphForm.hamiltonian_closed TD)) hc

theorem half_graph_core :
    (halfGraph ε hε h hh hb m g k t).topologicalClosure = (clockHalf ε).graph := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (fun _ hp => hp.1)
      (clockHalf_selfAdjoint ε).isClosed
  · rintro ⟨f,z⟩ hf
    exact mem_closure_of_tendsto (half_graph_convergence ε hε h hh hb m g k t f z)
      (Eventually.of_forall fun n =>
        ⟨approximation_half_graph ε hε h hh hb m g k t n f z hf,
          approximation_static_domain ε hε h hh hb m g k t n f⟩)

theorem common_dense : Dense (commonDomain ε hε h hh hb m g k t : Set Hilbert) := by
  have hs : ((clockHalf ε).domain : Set Hilbert) ⊆
      closure (commonDomain ε hε h hh hb m g k t : Set Hilbert) := by
    intro f hf
    exact mem_closure_of_tendsto (approximation_strong ε hε h hh hb m g k t f)
      (Eventually.of_forall fun n =>
        ⟨approximation_static_domain ε hε h hh hb m g k t n f,
          LinearPMap.mem_domain_of_mem_graph
            (approximation_half_graph ε hε h hh hb m g k t n f
              (clockHalf ε ⟨f,hf⟩) ((clockHalf ε).mem_graph ⟨f,hf⟩))⟩)
  intro f
  exact closure_minimal hs isClosed_closure ((clockHalf_selfAdjoint ε).dense_domain f)

#print axioms static_output_defect
#print axioms staticFormDefect_embedding
#print axioms staticFormDefect_output
#print axioms static_inverse_clock_accretive
#print axioms static_clock_form_accretive
#print axioms resolves
#print axioms left_inverse
#print axioms weighted_resolvent_bound
#print axioms weighted_intertwines
#print axioms weighted_norm_bound
#print axioms dual_intertwines
#print axioms resolvent_half_graph
#print axioms resolvent_half_domain
#print axioms resolvent_half_norm_bound
#print axioms weighted_norm
#print axioms approximation_strong
#print axioms weighted_strong
#print axioms weighted_adjoint_strong
#print axioms approximation_half_graph
#print axioms approximation_static_domain
#print axioms half_graph_convergence
#print axioms static_graph_core
#print axioms half_graph_core
#print axioms common_dense
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticClockCore
