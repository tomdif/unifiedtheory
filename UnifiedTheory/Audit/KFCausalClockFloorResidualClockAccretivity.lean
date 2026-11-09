/- Both the time-dependent residual Hamiltonian (retaining the static and
time-weighted ordered-potential rows while omitting the two radial kinetic
rows) and the full time-dependent physical Hamiltonian are accretive with
respect to the bounded inverse-clock defect operator and the unbounded clock
form pairing at every physical time. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticPotentialHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorPotentialClockAccretivity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorResidualClockAccretivity
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)
open KFCausalClockFloorShiftedDefect (shiftedDefect shiftedDefect_coe symbol shift_bound)
open KFCausalClockFloorEnergyDefectAction (factorAction outputAction outputAction_apply)
open KFCausalClockFloorClockOperator (clockOperator defect_clock)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open KFCausalClockFloorAveragedFormTransport (FormSpace)
open KFCausalClockFloorStaticPotentialOutputClosure (retained selectedOutputLp sourceMap)

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

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "D" => defectOperator ε hε
local notation "R" => outputAction ε hε h hb
local notation "L" => ContinuousLinearMap.compLpL 2 angleMeasure R
local notation "V0" => FormSpace ε hε h hh hb m g k 0
local notation "J0" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb m g k 0
local notation "B" => sourceMap ε hε h hh hb m g k t
local notation "T" => KFCausalClockFloorStaticPotentialOutputClosure.operator ε hε h hh hb m g k t
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hb m g k t
local notation "SV" => KFCausalClockFloorStaticPotentialHamiltonian.ResidualForm ε hε h hh hb m g k t
local notation "SJ" => KFCausalClosedGraphForm.embedding SD
local notation "SB" => KFCausalClosedGraphForm.energyOutput SD
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hb m g k t
local notation "HD" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hh hb m g k t
local notation "HV" => FormSpace ε hε h hh hb m g k t
local notation "HJ" => KFCausalClosedGraphForm.embedding HD
local notation "HB" => KFCausalClosedGraphForm.energyOutput HD
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb m g k t

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
    0 ≤ (inner ℂ f (R f)).re := by
  rw [PiLp.inner_apply,Complex.re_sum]
  exact Finset.sum_nonneg (fun i _ => factor_real_nonnegative ε hε h hb i (f i))

private theorem outputLp_real_nonnegative (f : EnergyOutputSpace) :
    0 ≤ (inner ℂ f (L f)).re := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) f (L f))
  change (∫ θ, (inner ℂ (f θ) (L f θ)).re ∂angleMeasure)=
    (∫ θ, inner ℂ (f θ) (L f θ) ∂angleMeasure).re at he
  rw [L2.inner_def,← he]
  apply integral_nonneg_of_ae
  filter_upwards [(R).coeFn_compLp f] with θ hθ
  change (R).compLp f θ=R (f θ) at hθ
  change 0 ≤ (inner ℂ (f θ) ((R).compLp f θ)).re
  rw [hθ]
  exact output_real_nonnegative ε hε h hb (f θ)

private theorem selected_commute (p : Fin 8 → Prop) [DecidablePred p]
    (f : EnergyOutputSpace) :
    (KFCausalFiniteOutputRescaling.selected p).compLp (L f)=
      L ((KFCausalFiniteOutputRescaling.selected p).compLp f) := by
  let Sel : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
    KFCausalFiniteOutputRescaling.selected p
  apply Lp.ext
  filter_upwards [Sel.coeFn_compLp (L f),(R).coeFn_compLp f,
    (R).coeFn_compLp (Sel.compLp f),Sel.coeFn_compLp f] with θ h1 h2 h3 h4
  change Sel.compLp ((R).compLp f) θ=(R).compLp (Sel.compLp f) θ
  change Sel.compLp ((R).compLp f) θ=Sel ((R).compLp f θ) at h1
  change (R).compLp (Sel.compLp f) θ=R (Sel.compLp f θ) at h3
  rw [h1,h2,h3,h4]
  apply PiLp.ext
  intro i
  simp only [Sel,KFCausalFiniteOutputRescaling.selected_apply,outputAction_apply]
  split_ifs <;> simp only [map_zero]

private theorem time_commute (s t : ℝ) (f : EnergyOutputSpace) :
    timeOutputLp s t (L f) = L (timeOutputLp s t f) := by
  let Tm : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
    KFCausalPhysicalEnergyTransport.timeOutput s t
  apply Lp.ext
  filter_upwards [Tm.coeFn_compLp (L f),(R).coeFn_compLp f,
    (R).coeFn_compLp (Tm.compLp f),Tm.coeFn_compLp f] with θ h1 h2 h3 h4
  change Tm.compLp ((R).compLp f) θ = (R).compLp (Tm.compLp f) θ
  change Tm.compLp ((R).compLp f) θ = Tm ((R).compLp f θ) at h1
  change (R).compLp (Tm.compLp f) θ = R (Tm.compLp f θ) at h3
  rw [h1,h2,h3,h4]
  apply PiLp.ext
  intro i
  simp only [Tm,KFCausalPhysicalEnergyTransport.timeOutput_apply,outputAction_apply]
  split_ifs <;> simp only [map_smul]

theorem reference_residual_output (u : V0) :
    B (KFCausalClockFloorReferenceClockCore.formDefect ε hε h hh hb m g k 0 u) = L (B u) := by
  change selectedOutputLp (timeOutputLp 0 t
    (KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hb m g k 0
      (KFCausalClockFloorReferenceClockCore.formDefect ε hε h hh hb m g k 0 u))) = _
  rw [KFCausalClockFloorReferenceClockCore.defect_output]
  rw [time_commute ε hε h hb 0 t]
  exact selected_commute ε hε h hb retained _

theorem residual_output_defect (f : Hilbert) (y : EnergyOutputSpace)
    (hy : (f,y) ∈ (T).graph) : (D f,L y) ∈ (T).graph := by
  rw [KFCausalClockFloorStaticPotentialOutputClosure.operator_graph] at hy ⊢
  let G0 := KFCausalClockFloorStaticPotentialOutputClosure.initialGraph ε hε h hh hb m g k t
  let M := (D).prodMap L
  have hG : G0 ≤ G0.topologicalClosure.comap M.toLinearMap := by
    rintro z ⟨u,rfl⟩
    apply G0.le_topologicalClosure
    refine ⟨KFCausalClockFloorReferenceClockCore.formDefect ε hε h hh hb m g k 0 u,?_⟩
    apply Prod.ext
    · exact KFCausalClockFloorReferenceClockCore.defect_embedding ε hε h hh hb m g k 0 u
    · exact reference_residual_output ε hε h hh hb m g k t u
  exact G0.topologicalClosure_minimal hG (G0.isClosed_topologicalClosure.preimage M.continuous) hy

def residualFormDefect : SV →L[ℂ] SV :=
  KFCausalClosedGraphDiagonalAction.action SD D L
    (residual_output_defect ε hε h hh hb m g k t)

theorem residualFormDefect_embedding (u : SV) :
    SJ (residualFormDefect ε hε h hh hb m g k t u) = D (SJ u) := rfl

theorem residualFormDefect_output (u : SV) :
    SB (residualFormDefect ε hε h hh hb m g k t u) = L (SB u) := rfl

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

theorem residual_inverse_clock_accretive (x : (S).domain) :
    0 ≤ (inner ℂ (S x) (D (x : Hilbert))).re :=
  form_accretive SD D L (residualFormDefect ε hε h hh hb m g k t)
    (residualFormDefect_embedding ε hε h hh hb m g k t)
    (residualFormDefect_output ε hε h hh hb m g k t)
    (outputLp_real_nonnegative ε hε h hb) x

theorem residual_clock_form_accretive (x : (S).domain) (v : SV)
    (hc : ((x : Hilbert),SJ v) ∈ (clockOperator ε hε).graph) :
    0 ≤ (inner ℂ (S x) (SJ v)).re :=
  form_mixed_accretive SD D L (residualFormDefect ε hε h hh hb m g k t)
    (residualFormDefect_embedding ε hε h hh hb m g k t)
    (residualFormDefect_output ε hε h hh hb m g k t)
    (outputLp_real_nonnegative ε hε h hb) x v ε hε (defect_clock ε hε _ _ hc)

theorem hamiltonian_inverse_clock_accretive (x : (H).domain) :
    0 ≤ (inner ℂ (H x) (D (x : Hilbert))).re :=
  form_accretive HD D L (KFCausalClockFloorReferenceClockCore.formDefect ε hε h hh hb m g k t)
    (KFCausalClockFloorReferenceClockCore.defect_embedding ε hε h hh hb m g k t)
    (KFCausalClockFloorReferenceClockCore.defect_output ε hε h hh hb m g k t)
    (outputLp_real_nonnegative ε hε h hb) x

theorem hamiltonian_clock_form_accretive (x : (H).domain) (v : HV)
    (hc : ((x : Hilbert),HJ v) ∈ (clockOperator ε hε).graph) :
    0 ≤ (inner ℂ (H x) (HJ v)).re :=
  form_mixed_accretive HD D L (KFCausalClockFloorReferenceClockCore.formDefect ε hε h hh hb m g k t)
    (KFCausalClockFloorReferenceClockCore.defect_embedding ε hε h hh hb m g k t)
    (KFCausalClockFloorReferenceClockCore.defect_output ε hε h hh hb m g k t)
    (outputLp_real_nonnegative ε hε h hb) x v ε hε (defect_clock ε hε _ _ hc)

#print axioms reference_residual_output
#print axioms residual_output_defect
#print axioms residualFormDefect_embedding
#print axioms residualFormDefect_output
#print axioms residual_inverse_clock_accretive
#print axioms residual_clock_form_accretive
#print axioms hamiltonian_inverse_clock_accretive
#print axioms hamiltonian_clock_form_accretive
end
end UnifiedTheory.Audit.KFCausalClockFloorResidualClockAccretivity
