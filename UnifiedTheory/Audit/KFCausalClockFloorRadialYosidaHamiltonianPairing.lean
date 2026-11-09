/- The actual full Hamiltonian tested against the bounded radial cutoff.
The static Leibniz loss is uniform in the cutoff; the growing part keeps
the proved radial lower bound. All pairings use the original completed
form and its actual circle sections. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaStaticLowerBound
import UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialDomination
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonianBridge

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaHamiltonianPairing
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorRadialYosidaSymbol (action)
open KFCausalClockFloorRadialYosidaStaticLowerBound (symmetric_pairing_lower)
open KFCausalClockFloorRadialYosidaKinetics (symmetricCorrection)
open KFCausalClockFloorRadialYosidaEnergy (transformedOutput factorOutput factorCorrection)
open KFCausalClockFloorRadialYosidaReference (wide_bound averagedAction averagedAction_embedding
  averagedAction_growing growingActionLp)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalPhysicalEnergyTransport (staticOutput growingOutput)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace staticOutputLp growingOutputLp)

private theorem inverse_square (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    ‖inverseL ε hε f‖^2 ≤ (1/ε)*‖f‖^2 := by
  have hn := KFCausalClockFloorBoundedInverse.inverseAction_norm_bound ε hε f
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  simpa only [mul_pow,inv_pow,Real.sq_sqrt hε.le,one_div] using hs

private theorem integrated_lower {X H K : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (μ : Measure X) (f : Lp H 2 μ) (u v : Lp K 2 μ) (c : ℝ)
    (hp : ∀ᵐ x ∂μ, -c*‖f x‖^2 ≤ (inner ℂ (u x) (v x)).re) :
    -c*‖f‖^2 ≤ (inner ℂ u v).re := by
  have hf : Integrable (fun x => ‖f x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have he := integral_mono_ae (hf.const_mul (-c)) (L2.integrable_inner (𝕜 := ℂ) u v).re hp
  rw [integral_const_mul,← KFCausalAveragedEnergyGraph.l2_norm_square,
    integral_re (L2.integrable_inner (𝕜 := ℂ) u v)] at he
  exact he

private theorem lp_action_lower {X E H K : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (μ : Measure X) (j : E →L[ℂ] H) (a : E →L[ℂ] K)
    (b : E →L[ℂ] E) (p : K →L[ℂ] K) (c : ℝ)
    (hl : ∀ e, -c*‖j e‖^2 ≤ (inner ℂ (p (a e)) (p (a (b e)))).re)
    (s : Lp E 2 μ) :
    -c*‖j.compLp s‖^2 ≤
      (inner ℂ (p.compLp (a.compLp s)) (p.compLp (a.compLp (b.compLp s)))).re := by
  apply integrated_lower
  filter_upwards [j.coeFn_compLp s,a.coeFn_compLp s,b.coeFn_compLp s,
    a.coeFn_compLp (b.compLp s),p.coeFn_compLp (a.compLp s),
    p.coeFn_compLp (a.compLp (b.compLp s))] with θ hj ha hb hab hp hpb
  rw [hj,hp,hpb,ha,hab,hb]
  exact hl (s θ)

private theorem split_pairing {V K : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (a b : V →L[ℂ] K) (t : ℝ) (q : V →L[ℂ] V)
    (hq : q=KFCausalBoundedFormCurve.formOperator a b t) (u v : V) :
    inner ℂ u (q v)=inner ℂ (a u) (a v)+(Real.exp (2*t):ℂ)*inner ℂ (b u) (b v) :=
  (congrArg (fun f : V →L[ℂ] V => inner ℂ u (f v)) hq).trans
    (KFCausalBoundedFormCurve.formOperator_pairing a b t u v)

private theorem variational_cutoff_lower {V H K : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (j : V →L[ℂ] H) (a b : V →L[ℂ] K) (q : V →L[ℂ] V)
    (d : H →L[ℂ] H) (t c : ℝ)
    (hq : q=KFCausalBoundedFormCurve.formOperator a b t)
    (u v : V) (x y : H) (hu : j u=x) (hv : j v=d (j u))
    (hp : inner ℂ u (q v)=inner ℂ y (j v))
    (ha : -c*‖j u‖^2 ≤ (inner ℂ (a u) (a v)).re)
    (hb : ‖d (j u)‖^2 ≤ (inner ℂ (b u) (b v)).re) :
    Real.exp (2*t)*‖d x‖^2 ≤ (inner ℂ y (d x)).re+c*‖x‖^2 := by
  have hf := split_pairing a b t q hq u v
  have he := congrArg Complex.re (hf.symm.trans hp)
  rw [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,hv,hu] at he
  rw [hu] at ha hb
  have hmul := mul_le_mul_of_nonneg_left hb (Real.exp_pos (2*t)).le
  linarith

private theorem static_inner (z w : Output (Fin 8) Hilbert) :
    inner ℂ (staticOutput z) (staticOutput w)=
      inner ℂ (z 0) (w 0)+inner ℂ (z 1) (w 1)+inner ℂ (z 2) (w 2) := by
  simp only [staticOutput,KFCausalFiniteOutputRescaling.selected_apply,PiLp.inner_apply,
    Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Fin.succ_zero_eq_one]
  norm_num only [Nat.reduceLT,if_true,if_false,inner_zero_left,Finset.sum_empty,
    add_zero]
  exact (add_assoc _ _ _).symm

theorem output_static_lower (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ) (f : Hilbert) (z : Output (Fin 8) Hilbert) :
    -(h^2/ε^2)*‖f‖^2 ≤
      (inner ℂ (staticOutput z) (staticOutput
        (transformedOutput ε hε h N hN hb (energyWeight m g k t) f z))).re := by
  let c : ℂ := (Real.sqrt (1/2):ℂ)
  have hc : ‖c‖^2=(1/2:ℝ) := by
    rw [show c=(Real.sqrt (1/2):ℂ) from rfl,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/2)]
  have hnorm : ‖inverseL ε hε (c • f)‖^2=(1/2)*‖inverseL ε hε f‖^2 := by
    rw [map_smul,norm_smul,mul_pow,hc]
  have h1 := symmetric_pairing_lower ε hε h N hN 0 (c • f) (z 1)
  have h2 := symmetric_pairing_lower ε hε h N hN 1 (c • f) (z 2)
  rw [hnorm,map_smul] at h1 h2
  have h0 := KFCausalClockFloorRadialYosidaOutputAccretivity.action_accretive ε hε h N hN (z 0)
  have hi := mul_le_mul_of_nonneg_left (inverse_square ε hε f)
    (show 0 ≤ h^2/ε by positivity)
  have hrow (i : Fin 8) :
      transformedOutput ε hε h N hN hb (energyWeight m g k t) f z i=
        factorOutput ε hε h N hN hb i (z i)+
          energyWeight m g k t i • factorCorrection ε hε h N hN i f := rfl
  rw [static_inner,hrow,hrow,hrow]
  change -(h^2/ε^2)*‖f‖^2 ≤
    (inner ℂ (z 0) (action ε hε h N hN (z 0)+(energyWeight m g k t 0) • (0:Hilbert))+
    inner ℂ (z 1) (action ε hε h N hN (z 1)+c • symmetricCorrection ε hε h N hN 0 f)+
    inner ℂ (z 2) (action ε hε h N hN (z 2)+c • symmetricCorrection ε hε h N hN 1 f)).re
  simp only [smul_zero,add_zero,Complex.add_re]
  have he : (h^2/ε)*(1/ε)=h^2/ε^2 := by ring
  rw [← mul_assoc,he] at hi
  linarith

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ)
local notation "hs" => KFCausalClockFloorRadialYosidaEnergy.energy_bound ε hε h hb
local notation "hw" => wide_bound ε hε h hb
local notation "BD" => KFCausalClockFloorFormHamiltonian.formData ε hε h hs m g k 0
local notation "BJ" => KFCausalClosedGraphForm.embedding BD
local notation "BA" => KFCausalClosedGraphForm.energyOutput BD
local notation "AV" => KFCausalClockFloorAveragedEnergy.AveragedSpace ε hε h hs hh m g k 0
local notation "AJ" => KFCausalClockFloorAveragedEnergy.embedding ε hε h hs hh m g k 0
local notation "AA" => KFCausalClockFloorAveragedEnergy.energyOutput ε hε h hs hh m g k 0
local notation "AS" => KFCausalClockFloorAveragedEnergy.sectionMap ε hε h hs hh m g k 0

theorem averaged_static_lower (N : ℝ) (hN : 0 < N) (u : AV) :
    -(h^2/ε^2)*‖AJ u‖^2 ≤
      (inner ℂ (staticOutputLp (AA u)) (staticOutputLp
        (AA (averagedAction ε hε h N hN hb hh m g k u)))).re := by
  let BF := KFCausalClockFloorRadialYosidaForm.formAction ε hε h N hN hb hh m g k 0
  let s := AS u
  have hl (v : KFCausalClosedGraphForm.FormSpace BD) :
      -(h^2/ε^2)*‖BJ v‖^2 ≤
        (inner ℂ (staticOutput (BA v)) (staticOutput (BA (BF v)))).re := by
    rw [KFCausalClockFloorRadialYosidaForm.formAction_output]
    exact output_static_lower ε hε h N hN hb m g k 0 (BJ v) (BA v)
  have hp := lp_action_lower angleMeasure (BJ) (BA) BF staticOutput (h^2/ε^2) hl s
  have he : (BJ).compLp s=KFCausalUnitIntervalOrbit.orbit
      (KFCausalPhysicalCircleAction.group h hh) (2*Real.pi) (AJ u) :=
    KFCausalAveragedFormSpace.compatibility _ _ _ u
  have ha : (BA).compLp s=AA u := rfl
  have hb' : (BA).compLp (BF.compLp s)=
      AA (averagedAction ε hε h N hN hb hh m g k u) := rfl
  have hn : ‖(BJ).compLp s‖=‖AJ u‖ :=
    (congrArg norm he).trans (LinearIsometry.norm_map _ _)
  have hpa := congrArg (fun y : EnergyOutputSpace => staticOutput.compLp y) ha
  have hpb := congrArg (fun y : EnergyOutputSpace => staticOutput.compLp y) hb'
  calc
    -(h^2/ε^2)*‖AJ u‖^2=-(h^2/ε^2)*‖(BJ).compLp s‖^2 :=
      congrArg (fun r : ℝ => -(h^2/ε^2)*r^2) hn.symm
    _ ≤ _ := hp
    _ = _ := congrArg₂ (fun y z : EnergyOutputSpace => (inner ℂ y z).re) hpa hpb

local notation "RV" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "RJ" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0
local notation "RA" => KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hw m g k
local notation "RB" => KFCausalClockFloorAveragedRegularity.growingMap ε hε h hh hw m g k
local notation "GD" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k
local notation "GL" => KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k

theorem reference_lower (N : ℝ) (hN : 0 < N) (u : RV) :
    ∃ v : RV, RJ v=action ε hε h N hN (RJ u) ∧
      -(h^2/ε^2)*‖RJ u‖^2 ≤ (inner ℂ (RA u) (RA v)).re ∧
      ‖action ε hε h N hN (RJ u)‖^2 ≤ (inner ℂ (RB u) (RB v)).re := by
  let lift := KFCausalClockFloorAveragedHamiltonian.graphFormVector ε hε h hh hw m g k 0
  have hl : Function.Surjective lift :=
    KFCausalClockFloorAveragedHamiltonian.graphFormVector_surjective ε hε h hh hw m g k 0
  let a := Classical.choose (hl u)
  have ha := Classical.choose_spec (hl u)
  let v := lift (averagedAction ε hε h N hN hb hh m g k a)
  have hJ : AJ a=RJ u := congrArg RJ ha
  have hA : staticOutputLp (AA a)=RA u := congrArg RA ha
  have hV : RJ v=action ε hε h N hN (RJ u) :=
    (averagedAction_embedding ε hε h N hN hb hh m g k a).trans
      (congrArg (action ε hε h N hN) hJ)
  refine ⟨v,hV,?_,?_⟩
  · have hl := averaged_static_lower ε hε h hh hb m g k N hN a
    have hv : staticOutputLp (AA (averagedAction ε hε h N hN hb hh m g k a))=RA v := rfl
    simpa only [hJ,hA,hv] using hl
  · have he : GL v=KFCausalClockFloorRadialYosidaGrowing.formAction ε hε h N hN hb hh m g k (GL u) := by
      apply KFCausalClosedGraphForm.embedding_injective GD
      exact hV
    have hl := KFCausalClockFloorGrowingRadialDomination.form_lower ε hε h hh hb m g k N hN (GL u)
    have hOut := congrArg (KFCausalClosedGraphForm.energyOutput GD) he.symm
    change KFCausalClosedGraphForm.energyOutput GD
      (KFCausalClockFloorRadialYosidaGrowing.formAction ε hε h N hN hb hh m g k (GL u))=RB v at hOut
    change ‖action ε hε h N hN (RJ u)‖^2 ≤
      (inner ℂ (RB u) (KFCausalClosedGraphForm.energyOutput GD
        (KFCausalClockFloorRadialYosidaGrowing.formAction ε hε h N hN hb hh m g k (GL u)))).re at hl
    exact hl.trans_eq (congrArg (fun y => (inner ℂ (RB u) y).re) hOut)

theorem hamiltonian_cutoff_pairing (N : ℝ) (hN : 0 < N) (t : ℝ)
    (x : (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t).domain) :
    Real.exp (2*t)*‖action ε hε h N hN (x:Hilbert)‖^2 ≤
      (inner ℂ (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t x)
        (action ε hε h N hN (x:Hilbert))).re+(h^2/ε^2)*‖(x:Hilbert)‖^2 := by
  let u := KFCausalClockFloorAveragedHamiltonianBridge.referenceLift ε hε h hh hw m g k t x
  have hj : RJ u=(x:Hilbert) :=
    KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift ε hε h hh hw m g k t x
  obtain ⟨v,hv,hStaticLower,hGrowingLower⟩ := reference_lower ε hε h hh hb m g k N hN u
  have hp := KFCausalClockFloorAveragedHamiltonianBridge.hamiltonian_reference_pairing
    ε hε h hh hw m g k t x v
  exact variational_cutoff_lower RJ RA RB
    (KFCausalClockFloorAveragedRegularity.referenceFormOperator ε hε h hh hw m g k t)
    (action ε hε h N hN) t (h^2/ε^2) rfl u v (x:Hilbert)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t x)
    hj hv hp hStaticLower hGrowingLower

#print axioms output_static_lower
#print axioms averaged_static_lower
#print axioms reference_lower
#print axioms hamiltonian_cutoff_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaHamiltonianPairing
