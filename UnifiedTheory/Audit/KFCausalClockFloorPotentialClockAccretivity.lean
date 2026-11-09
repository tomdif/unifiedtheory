/- The actual potential form is stable under the inverse-clock defect.
The transport is extended through the literal original ordered-output
closure. Accretivity is on the whole associated potential Hamiltonian
domain; no static kinetic or residual Hamiltonian domain is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorPotentialHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorReferenceClockCore

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPotentialClockAccretivity
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)
open KFCausalClockFloorShiftedDefect (shiftedDefect shiftedDefect_coe symbol shift_bound)
open KFCausalClockFloorEnergyDefectAction (factorAction outputAction outputAction_apply)
open KFCausalClockFloorClockOperator (clockOperator defect_clock)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace growingOutputLp)

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
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "D" => defectOperator ε hε
local notation "R" => outputAction ε hε h hb
local notation "L" => ContinuousLinearMap.compLpL 2 angleMeasure R
local notation "V" => KFCausalClockFloorAveragedFormTransport.FormSpace ε hε h hh hb m g k 0
local notation "J" => KFCausalClockFloorAveragedFormTransport.embedding ε hε h hh hb m g k 0
local notation "B" => KFCausalClockFloorPotentialOutputClosure.potentialMap ε hε h hh hb m g k
local notation "T" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hb m g k
local notation "GD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hb m g k
local notation "GV" => KFCausalClockFloorPotentialHamiltonian.PotentialForm ε hε h hh hb m g k
local notation "GJ" => KFCausalClosedGraphForm.embedding GD
local notation "GB" => KFCausalClosedGraphForm.energyOutput GD
local notation "G" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hb m g k

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
  let S : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
    KFCausalFiniteOutputRescaling.selected p
  apply Lp.ext
  filter_upwards [S.coeFn_compLp (L f),(R).coeFn_compLp f,
    (R).coeFn_compLp (S.compLp f),S.coeFn_compLp f] with θ h1 h2 h3 h4
  change S.compLp ((R).compLp f) θ=(R).compLp (S.compLp f) θ
  change S.compLp ((R).compLp f) θ=S ((R).compLp f θ) at h1
  change (R).compLp (S.compLp f) θ=R (S.compLp f θ) at h3
  rw [h1,h2,h3,h4]
  apply PiLp.ext
  intro i
  simp only [S,KFCausalFiniteOutputRescaling.selected_apply,outputAction_apply]
  split_ifs <;> simp only [map_zero]

private theorem reference_output (u : V) :
    B (KFCausalClockFloorReferenceClockCore.formDefect ε hε h hh hb m g k 0 u)=L (B u) := by
  change KFCausalClockFloorChartPhasePairing.orderedOutputLp (growingOutputLp
    (KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hb m g k 0
      (KFCausalClockFloorReferenceClockCore.formDefect ε hε h hh hb m g k 0 u)))=_
  rw [KFCausalClockFloorReferenceClockCore.defect_output]
  have hg := selected_commute ε hε h hb (fun i : Fin 8 => ¬i.val<3)
    (KFCausalClockFloorAveragedFormTransport.energyOutput ε hε h hh hb m g k 0 u)
  change growingOutputLp (L _)=L (growingOutputLp _) at hg
  rw [hg]
  exact selected_commute ε hε h hb (fun i : Fin 8 => ¬i.val<5) _

theorem potential_output_defect (f : Hilbert) (y : EnergyOutputSpace)
    (hy : (f,y) ∈ (T).graph) : (D f,L y) ∈ (T).graph := by
  rw [KFCausalClockFloorPotentialOutputClosure.operator_graph] at hy ⊢
  let S := KFCausalClockFloorPotentialOutputClosure.initialGraph ε hε h hh hb m g k
  let M := (D).prodMap L
  have hS : S ≤ S.topologicalClosure.comap M.toLinearMap := by
    rintro z ⟨u,rfl⟩
    apply S.le_topologicalClosure
    refine ⟨KFCausalClockFloorReferenceClockCore.formDefect ε hε h hh hb m g k 0 u,?_⟩
    apply Prod.ext
    · exact KFCausalClockFloorReferenceClockCore.defect_embedding ε hε h hh hb m g k 0 u
    · exact reference_output ε hε h hh hb m g k u
  exact S.topologicalClosure_minimal hS (S.isClosed_topologicalClosure.preimage M.continuous) hy

def formDefect : GV →L[ℂ] GV :=
  KFCausalClosedGraphDiagonalAction.action GD D L
    (potential_output_defect ε hε h hh hb m g k)

theorem formDefect_embedding (u : GV) :
    GJ (formDefect ε hε h hh hb m g k u)=D (GJ u) := rfl

theorem formDefect_output (u : GV) :
    GB (formDefect ε hε h hh hb m g k u)=L (GB u) := rfl

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


theorem inverse_clock_accretive (x : (G).domain) :
    0 ≤ (inner ℂ (G x) (D (x : Hilbert))).re :=
  form_accretive GD D L (formDefect ε hε h hh hb m g k)
    (formDefect_embedding ε hε h hh hb m g k)
    (formDefect_output ε hε h hh hb m g k)
    (outputLp_real_nonnegative ε hε h hb) x

theorem clock_form_accretive (x : (G).domain) (v : GV)
    (hc : ((x : Hilbert),GJ v) ∈ (clockOperator ε hε).graph) :
    0 ≤ (inner ℂ (G x) (GJ v)).re :=
  form_mixed_accretive GD D L (formDefect ε hε h hh hb m g k)
    (formDefect_embedding ε hε h hh hb m g k)
    (formDefect_output ε hε h hh hb m g k)
    (outputLp_real_nonnegative ε hε h hb) x v ε hε (defect_clock ε hε _ _ hc)

#print axioms potential_output_defect
#print axioms formDefect_embedding
#print axioms formDefect_output
#print axioms inverse_clock_accretive
#print axioms clock_form_accretive
end
end UnifiedTheory.Audit.KFCausalClockFloorPotentialClockAccretivity
