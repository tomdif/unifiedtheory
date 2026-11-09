/- The original full Hamiltonian splits as its time-weighted maximal
radial operator plus the Hamiltonian obtained by closing the original
static and ordered-potential rows. The radial domain is derived on all
of Dom H; the residual is identified by dense variational testing.
This does not identify the residual with the natural sum T+exp(2t)P. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticPotentialHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialDomination
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingRadialPairing

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialSum
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalPhysicalEnergyTransport (timeOutput timeOutput_apply)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorStaticPotentialOutputClosure (selectedOutput selectedOutputLp retained sourceMap)
open KFCausalClockFloorStaticPotentialHamiltonian (referenceLift referenceLift_dense)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOperator rootOutput rootOutput_graph rootOutput_inner)

private theorem split_pairing {V K : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (a b : V →L[ℂ] K) (t : ℝ) (q : V →L[ℂ] V)
    (hq : q=KFCausalBoundedFormCurve.formOperator a b t) (u v : V) :
    inner ℂ u (q v)=inner ℂ (a u) (a v)+(Real.exp (2*t):ℂ)*inner ℂ (b u) (b v) :=
  (congrArg (fun f : V →L[ℂ] V => inner ℂ u (f v)) hq).trans
    (KFCausalBoundedFormCurve.formOperator_pairing a b t u v)

private theorem residual_identity (a b c d e f q : ℂ)
    (hs : a=q*b+c) (ha : a=d) (hb : b=e) (hf : f=d-q*e) : c=f := by
  rw [ha,hb] at hs
  rw [hf]
  linear_combination -hs

private theorem omitted_split (z w : Output (Fin 8) Hilbert) :
    inner ℂ z w=(inner ℂ (z 3) (w 3)+inner ℂ (z 4) (w 4))+
      inner ℂ (selectedOutput z) (selectedOutput w) := by
  simp only [PiLp.inner_apply,Fin.sum_univ_succ,selectedOutput,
    KFCausalFiniteOutputRescaling.selected_apply,retained,Fin.val_zero,Fin.val_succ]
  norm_num only [Nat.reduceLT,or_true,true_or,or_false,false_or,
    if_true,if_false,inner_zero_left,Finset.sum_empty,add_zero]
  change inner ℂ (z 0) (w 0)+(inner ℂ (z 1) (w 1)+(inner ℂ (z 2) (w 2)+
    (inner ℂ (z 3) (w 3)+(inner ℂ (z 4) (w 4)+(inner ℂ (z 5) (w 5)+
    (inner ℂ (z 6) (w 6)+inner ℂ (z 7) (w 7)))))))=
    (inner ℂ (z 3) (w 3)+inner ℂ (z 4) (w 4))+
    (inner ℂ (z 0) (w 0)+(inner ℂ (z 1) (w 1)+(inner ℂ (z 2) (w 2)+
    (0+(0+(inner ℂ (z 5) (w 5)+(inner ℂ (z 6) (w 6)+inner ℂ (z 7) (w 7))))))))
  abel

private theorem point_split (t : ℝ) (z w : Output (Fin 8) Hilbert) :
    inner ℂ (timeOutput 0 t z) (timeOutput 0 t w)=
      (Real.exp (2*t):ℂ)*(inner ℂ (z 3) (w 3)+inner ℂ (z 4) (w 4))+
      inner ℂ (selectedOutput (timeOutput 0 t z)) (selectedOutput (timeOutput 0 t w)) := by
  have he : (Real.exp t:ℂ)*(Real.exp t:ℂ)=(Real.exp (2*t):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add,show t+t=2*t by ring]
  have hs := omitted_split (timeOutput 0 t z) (timeOutput 0 t w)
  have h3 : inner ℂ (timeOutput 0 t z 3) (timeOutput 0 t w 3)=
      (Real.exp (2*t):ℂ)*inner ℂ (z 3) (w 3) := by
    change inner ℂ ((Real.exp (t-0):ℂ) • z 3) ((Real.exp (t-0):ℂ) • w 3)=_
    rw [sub_zero,inner_smul_left,inner_smul_right,Complex.conj_ofReal,← mul_assoc,he]
  have h4 : inner ℂ (timeOutput 0 t z 4) (timeOutput 0 t w 4)=
      (Real.exp (2*t):ℂ)*inner ℂ (z 4) (w 4) := by
    change inner ℂ ((Real.exp (t-0):ℂ) • z 4) ((Real.exp (t-0):ℂ) • w 4)=_
    rw [sub_zero,inner_smul_left,inner_smul_right,Complex.conj_ofReal,← mul_assoc,he]
  exact hs.trans (congrArg (fun q : ℂ => q+inner ℂ
    (selectedOutput (timeOutput 0 t z)) (selectedOutput (timeOutput 0 t w)))
    ((congrArg₂ (·+·) h3 h4).trans (mul_add _ _ _).symm))

private theorem inner_sub_real_smul (f r z : Hilbert) (c : ℝ) :
    inner ℂ (f-(c:ℂ) • r) z=inner ℂ f z-(c:ℂ)*inner ℂ r z := by
  rw [inner_sub_left,inner_smul_left,Complex.conj_ofReal]

private theorem lp_split {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (μ : Measure X) (T P : E →L[ℂ] E) (C D : E →L[ℂ] F) (q : ℂ)
    (hsplit : ∀ z w, inner ℂ (T z) (T w)=q*(inner ℂ (C z) (C w)+inner ℂ (D z) (D w))+
      inner ℂ (P (T z)) (P (T w))) (z w : Lp E 2 μ) :
    inner ℂ (T.compLp z) (T.compLp w)=q*(inner ℂ (C.compLp z) (C.compLp w)+
      inner ℂ (D.compLp z) (D.compLp w))+
      inner ℂ (P.compLp (T.compLp z)) (P.compLp (T.compLp w)) := by
  have he : (fun θ => inner ℂ (T.compLp z θ) (T.compLp w θ)) =ᵐ[μ]
      fun θ => q*(inner ℂ (C.compLp z θ) (C.compLp w θ)+inner ℂ (D.compLp z θ) (D.compLp w θ))+
        inner ℂ (P.compLp (T.compLp z) θ) (P.compLp (T.compLp w) θ) := by
    filter_upwards [T.coeFn_compLp z,T.coeFn_compLp w,
      P.coeFn_compLp (T.compLp z),P.coeFn_compLp (T.compLp w),
      C.coeFn_compLp z,C.coeFn_compLp w,D.coeFn_compLp z,D.coeFn_compLp w]
      with θ hz hw hpz hpw hcz hcw hdz hdw
    rw [hpz,hpw,hz,hw,hcz,hcw,hdz,hdw]
    exact hsplit (z θ) (w θ)
  have hC := L2.integrable_inner (𝕜 := ℂ) (C.compLp z) (C.compLp w)
  have hD := L2.integrable_inner (𝕜 := ℂ) (D.compLp z) (D.compLp w)
  have hP := L2.integrable_inner (𝕜 := ℂ) (P.compLp (T.compLp z)) (P.compLp (T.compLp w))
  have hCD : Integrable (fun θ => q*(inner ℂ (C.compLp z θ) (C.compLp w θ)+
      inner ℂ (D.compLp z θ) (D.compLp w θ))) μ := (hC.add hD).const_mul q
  rw [L2.inner_def,integral_congr_ae he,integral_add hCD hP,integral_const_mul,integral_add hC hD]
  rfl

private theorem output_split (t : ℝ) (z w : EnergyOutputSpace) :
    inner ℂ (timeOutputLp 0 t z) (timeOutputLp 0 t w)=
      (Real.exp (2*t):ℂ)*(inner ℂ (coordinateLp 3 z) (coordinateLp 3 w)+
        inner ℂ (coordinateLp 4 z) (coordinateLp 4 w))+
      inner ℂ (selectedOutputLp (timeOutputLp 0 t z)) (selectedOutputLp (timeOutputLp 0 t w)) :=
  lp_split angleMeasure (timeOutput 0 t) selectedOutput (coordinate 3) (coordinate 4)
    (Real.exp (2*t):ℂ) (point_split t) z w

private theorem form_graph (D : KFCausalClosedGraphForm.Data Hilbert EnergyOutputSpace)
    (u : KFCausalClosedGraphForm.FormSpace D) (y : Hilbert)
    (hp : ∀ v, inner ℂ (KFCausalClosedGraphForm.energyOutput D u)
      (KFCausalClosedGraphForm.energyOutput D v)=inner ℂ y (KFCausalClosedGraphForm.embedding D v)) :
    (KFCausalClosedGraphForm.embedding D u,y) ∈ (KFCausalClosedGraphForm.hamiltonian D).graph := by
  obtain ⟨hu,he⟩ := (KFCausalClosedGraphForm.hamiltonian_domain_characterization D u y).mpr hp
  have hg := (KFCausalClosedGraphForm.hamiltonian D).mem_graph
    ⟨KFCausalClosedGraphForm.embedding D u,hu⟩
  rwa [he] at hg

private theorem formal_self {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] (A : X →ₗ.[ℂ] X) (hA : IsSelfAdjoint A) : A.IsFormalAdjoint A := by
  have hf := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hA] at hf

private theorem graph_pairing (A : Hilbert →ₗ.[ℂ] Hilbert) (hA : IsSelfAdjoint A)
    (f z v w : Hilbert) (hf : (f,z) ∈ A.graph) (hv : (v,w) ∈ A.graph) :
    inner ℂ f w=inner ℂ z v := by
  have hfd := LinearPMap.mem_domain_of_mem_graph hf
  have hvd := LinearPMap.mem_domain_of_mem_graph hv
  have ef : A ⟨f,hfd⟩=z := A.mem_graph_snd_inj' (A.mem_graph ⟨f,hfd⟩) hf rfl
  have ev : A ⟨v,hvd⟩=w := A.mem_graph_snd_inj' (A.mem_graph ⟨v,hvd⟩) hv rfl
  simpa only [ef,ev] using (formal_self A hA ⟨f,hfd⟩ ⟨v,hvd⟩).symm

private theorem sum_graph (K P : Hilbert →ₗ.[ℂ] Hilbert) (f r p : Hilbert)
    (hr : (f,r) ∈ K.graph) (hp : (f,p) ∈ P.graph) : (f,r+p) ∈ (K+P).graph := by
  have hk := LinearPMap.mem_domain_of_mem_graph hr
  have hp' := LinearPMap.mem_domain_of_mem_graph hp
  have heK : K ⟨f,hk⟩=r := K.mem_graph_snd_inj' (K.mem_graph ⟨f,hk⟩) hr rfl
  have heP : P ⟨f,hp'⟩=p := P.mem_graph_snd_inj' (P.mem_graph ⟨f,hp'⟩) hp rfl
  exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨f,⟨hk,hp'⟩⟩,rfl,by
    change K ⟨f,hk⟩+P ⟨f,hp'⟩=r+p
    rw [heK,heP]⟩

private theorem maximal_sum (A K P : Hilbert →ₗ.[ℂ] Hilbert)
    (hA : IsSelfAdjoint A) (hK : K.IsFormalAdjoint K) (hP : P.IsFormalAdjoint P)
    (hle : A ≤ K+P) : A=K+P := by
  have hsum : (K+P).IsFormalAdjoint (K+P) := by
    intro x y
    change inner ℂ (K ⟨x,x.property.1⟩+P ⟨x,x.property.2⟩) (y:Hilbert)=
      inner ℂ (x:Hilbert) (K ⟨y,y.property.1⟩+P ⟨y,y.property.2⟩)
    rw [inner_add_left,inner_add_right]
    exact congrArg₂ (·+·) (hK ⟨(x:Hilbert),x.property.1⟩ ⟨(y:Hilbert),y.property.1⟩)
      (hP ⟨(x:Hilbert),x.property.2⟩ ⟨(y:Hilbert),y.property.2⟩)
  have hf : A.IsFormalAdjoint (K+P) := by
    intro x y
    have he : A x=(K+P) ⟨x,hle.1 x.property⟩ := hle.2 rfl
    rw [he]
    exact hsum ⟨x,hle.1 x.property⟩ y
  have hrev := hf.le_adjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hrev
  exact le_antisymm hle hrev

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "V" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hw m g k 0
local notation "J" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hw m g k 0
local notation "A" => KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hw m g k 0
local notation "GL" => KFCausalClockFloorGrowingHamiltonian.referenceLift ε hε h hh hw m g k
local notation "R" => rootOutput ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k t
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hw m g k t
local notation "SJ" => KFCausalClosedGraphForm.embedding SD
local notation "SB" => KFCausalClosedGraphForm.energyOutput SD
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k t
local notation "B" => sourceMap ε hε h hh hw m g k t

def radialOutput (x : (H).domain) : Hilbert := (K)
  ⟨(x:Hilbert),KFCausalClockFloorHamiltonianRadialDomination.radial_domain ε hε h hh hb m g k t x⟩
def residualOutput (x : (H).domain) : Hilbert := H x-(Real.exp (2*t):ℂ) • radialOutput ε hε h hh hb m g k t x

private theorem root_pairing (x : (H).domain) (v : V) :
    inner ℂ (R (GL (KFCausalClockFloorAveragedHamiltonianBridge.referenceLift ε hε h hh hw m g k t x)))
      (R (GL v))=inner ℂ (radialOutput ε hε h hh hb m g k t x) (J v) := by
  let u := KFCausalClockFloorAveragedHamiltonianBridge.referenceLift ε hε h hh hw m g k t x
  have hu := rootOutput_graph ε hε h hh hw m g k (GL u)
  have hj : KFCausalClosedGraphForm.embedding
      (KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hw m g k) (GL u)=(x:Hilbert) :=
    (KFCausalClockFloorGrowingHamiltonian.referenceLift_embedding ε hε h hh hw m g k u).trans
      (KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift ε hε h hh hw m g k t x)
  have hu' : ((x:Hilbert),R (GL u)) ∈ (rootOperator ε hε h).graph :=
    (congrArg (fun f : Hilbert => (f,R (GL u)) ∈ (rootOperator ε hε h).graph) hj).mp hu
  have hr := KFCausalClockFloorGaussianGrowingRadialPairing.root_square_graph ε hε h _ _ _ hu'
    ((K).mem_graph ⟨(x:Hilbert),KFCausalClockFloorHamiltonianRadialDomination.radial_domain ε hε h hh hb m g k t x⟩)
  exact graph_pairing (rootOperator ε hε h)
    (KFCausalClockFloorGrowingRadialMultiplierForm.root_selfAdjoint ε hε h) _ _ _ _ hr
    (rootOutput_graph ε hε h hh hw m g k (GL v))

private theorem reference_split (u v : V) :
    inner ℂ u (KFCausalClockFloorAveragedRegularity.referenceFormOperator ε hε h hh hw m g k t v)=
      (Real.exp (2*t):ℂ)*inner ℂ (R (GL u)) (R (GL v))+inner ℂ (B u) (B v) := by
  have hs := output_split t (A u) (A v)
  have hr := rootOutput_inner ε hε h hh hw m g k (GL u) (GL v)
  have hr' : inner ℂ (R (GL u)) (R (GL v))=
      inner ℂ (coordinateLp 3 (A u)) (coordinateLp 3 (A v))+
        inner ℂ (coordinateLp 4 (A u)) (coordinateLp 4 (A v)) := by
    simpa only [KFCausalClockFloorGrowingHamiltonian.referenceLift_output,
      KFCausalClockFloorAveragedRegularity.growingMap,ContinuousLinearMap.comp_apply,
      KFCausalClockFloorOrbitFactorGraphs.coordinate_growing,show ¬ (3:ℕ)<3 by decide,
      show ¬ (4:ℕ)<3 by decide,if_false] using hr
  have ht := KFCausalAveragedOutputRescaling.timeOutputLp_inner 0 t (A u) (A v)
  have hq := split_pairing
    (KFCausalClockFloorAveragedRegularity.staticMap ε hε h hh hw m g k)
    (KFCausalClockFloorAveragedRegularity.growingMap ε hε h hh hw m g k) t
    (KFCausalClockFloorAveragedRegularity.referenceFormOperator ε hε h hh hw m g k t) rfl u v
  have he : inner ℂ u (KFCausalClockFloorAveragedRegularity.referenceFormOperator ε hε h hh hw m g k t v)=
      inner ℂ (timeOutputLp 0 t (A u)) (timeOutputLp 0 t (A v)) := by
    exact hq.trans (by simpa only [sub_zero] using ht.symm)
  exact he.trans (hs.trans (congrArg (fun z : ℂ => (Real.exp (2*t):ℂ)*z+inner ℂ (B u) (B v)) hr'.symm))

theorem residual_graph (x : (H).domain) :
    ((x:Hilbert),residualOutput ε hε h hh hb m g k t x) ∈ (S).graph := by
  let u := KFCausalClockFloorAveragedHamiltonianBridge.referenceLift ε hε h hh hw m g k t x
  let v := referenceLift ε hε h hh hw m g k t u
  have hp : ∀ w : SV, inner ℂ (SB v) (SB w)=
      inner ℂ (residualOutput ε hε h hh hb m g k t x) (SJ w) := by
    intro w
    refine congrFun ((referenceLift_dense ε hε h hh hw m g k t).equalizer
      (continuous_const.inner (𝕜 := ℂ) (SB).continuous)
      (continuous_const.inner (𝕜 := ℂ) (SJ).continuous) ?_) w
    funext z
    have hs := reference_split ε hε h hh hb m g k t u z
    have hh' := KFCausalClockFloorAveragedHamiltonianBridge.hamiltonian_reference_pairing
      ε hε h hh hw m g k t x z
    have hk := root_pairing ε hε h hh hb m g k t x z
    have hi : inner ℂ (residualOutput ε hε h hh hb m g k t x) (J z)=
        inner ℂ (H x) (J z)-(Real.exp (2*t):ℂ)*inner ℂ (radialOutput ε hε h hh hb m g k t x) (J z) :=
      inner_sub_real_smul (H x) (radialOutput ε hε h hh hb m g k t x) (J z) (Real.exp (2*t))
    exact residual_identity _ _ _ _ _ _ _ hs hh' hk hi
  have hg := form_graph SD v (residualOutput ε hε h hh hb m g k t x) hp
  have he : SJ v=(x:Hilbert) :=
    (KFCausalClockFloorStaticPotentialHamiltonian.referenceLift_embedding ε hε h hh hw m g k t u).trans
      (KFCausalClockFloorAveragedHamiltonianBridge.embedding_referenceLift ε hε h hh hw m g k t x)
  exact (congrArg (fun f : Hilbert =>
    (f,residualOutput ε hε h hh hb m g k t x) ∈ (S).graph) he).mp hg

theorem residual_domain (x : (H).domain) : (x:Hilbert) ∈ (S).domain :=
  LinearPMap.mem_domain_of_mem_graph (residual_graph ε hε h hh hb m g k t x)

theorem operator_sum : (H)=(Real.exp (2*t):ℂ) • (K)+(S) := by
  have hk : ((Real.exp (2*t):ℂ) • (K)).IsFormalAdjoint ((Real.exp (2*t):ℂ) • (K)) := by
    intro x y
    change inner ℂ ((Real.exp (2*t):ℂ) • (K) x) (y:Hilbert)=
      inner ℂ (x:Hilbert) ((Real.exp (2*t):ℂ) • (K) y)
    rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal]
    exact congrArg (fun z : ℂ => (Real.exp (2*t):ℂ)*z)
      (formal_self (K) (KFCausalClockFloorRadialYosidaDomain.operator_selfAdjoint ε hε h) x y)
  apply maximal_sum _ _ _
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_selfAdjoint ε hε h hh hw m g k t) hk
    (formal_self (S) (KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian_selfAdjoint ε hε h hh hw m g k t))
  apply LinearPMap.le_graph_iff.mp
  rintro ⟨f,z⟩ hfz
  let x : (H).domain := ⟨f,LinearPMap.mem_domain_of_mem_graph hfz⟩
  have he : H x=z := (H).mem_graph_snd_inj' ((H).mem_graph x) hfz rfl
  have hk' : ((x:Hilbert),(Real.exp (2*t):ℂ) • radialOutput ε hε h hh hb m g k t x) ∈
      ((Real.exp (2*t):ℂ) • (K)).graph :=
    (LinearPMap.mem_graph_iff _).mpr ⟨⟨(x:Hilbert),
      KFCausalClockFloorHamiltonianRadialDomination.radial_domain ε hε h hh hb m g k t x⟩,rfl,rfl⟩
  have hp := residual_graph ε hε h hh hb m g k t x
  have hs := sum_graph ((Real.exp (2*t):ℂ) • (K)) (S) (x:Hilbert)
    ((Real.exp (2*t):ℂ) • radialOutput ε hε h hh hb m g k t x)
    (residualOutput ε hε h hh hb m g k t x) hk' hp
  have ha : (Real.exp (2*t):ℂ) • radialOutput ε hε h hh hb m g k t x+
      residualOutput ε hε h hh hb m g k t x=z := by rw [← he,residualOutput]; abel
  exact (congrArg (fun y : Hilbert => ((x:Hilbert),y) ∈
    ((Real.exp (2*t):ℂ) • (K)+(S)).graph) ha).mp hs

theorem domain_iff (x : Hilbert) :
    x ∈ (H).domain ↔ x ∈ (K).domain ∧ x ∈ (S).domain := by
  rw [operator_sum ε hε h hh hb m g k t,LinearPMap.add_domain]
  rfl

theorem residual_output (x : (H).domain) :
    S ⟨(x:Hilbert),residual_domain ε hε h hh hb m g k t x⟩=
      H x-(Real.exp (2*t):ℂ) • radialOutput ε hε h hh hb m g k t x :=
  (S).mem_graph_snd_inj' ((S).mem_graph _)
    (residual_graph ε hε h hh hb m g k t x) rfl

#print axioms residual_graph
#print axioms residual_domain
#print axioms operator_sum
#print axioms domain_iff
#print axioms residual_output
end
end UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialSum
