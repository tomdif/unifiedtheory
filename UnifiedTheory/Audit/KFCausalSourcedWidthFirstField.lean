/- Actual linear physical fields after the first vacuum square, for the
full sourced reciprocal packets. The existing doubled ordered matter
graph supplies the moment; the squeeze and inverse clock preserve the
exact graph. This does not assert a further vacuum-square domain. -/
import UnifiedTheory.Audit.KFCausalSourcedWidthSecondInput
import UnifiedTheory.Audit.KFCausalPhysicalSpectatorGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSourcedWidthFirstField
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalPhysicalField (physicalField physicalField_graph)
open KFCausalReciprocalSqueezeFlow (squeeze squeezeEquiv squeeze_compose squeeze_initial)
open KFCausalReciprocalSqueezeTransport (transport transport_coe squeezeFlow_apply
  squeezeFlow_quasiMeasurePreserving)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalSourcedWidthSecondInput (state doubledOutput firstOutput first_graph first_mixed density)
open KFCausalPhysicalMixedCoordinates (mixedCoordinates)
open KFCausalPhysicalSpectatorGraph (symmetricPosition symmetricIndex symmetric_position_graph_iff)

def squeezedField (t : ℝ) (l : Transverse →L[ℝ] ℝ) : Transverse →L[ℝ] ℝ :=
  l.comp (squeezeEquiv t).toContinuousLinearEquiv.toContinuousLinearMap

private theorem squeezedField_apply (t : ℝ) (l : Transverse →L[ℝ] ℝ) (x : Transverse) :
    squeezedField t l x = l (squeeze t x) := rfl

theorem squeeze_field_graph (t : ℝ) (l : Transverse →L[ℝ] ℝ) (f g : Hilbert)
    (hg : (f,g) ∈ (physicalField (squeezedField t l)).graph) :
    (transport t f,transport t g) ∈ (physicalField l).graph := by
  apply (physicalField_graph l _ _).mpr
  have hr := (squeezeFlow_quasiMeasurePreserving t).ae
    ((physicalField_graph (squeezedField t l) f g).mp hg)
  filter_upwards [transport_coe t f,transport_coe t g,hr] with x hf hg hr
  rw [hg,hr,hf]
  simp only [squeezeFlow_apply,squeezedField_apply,squeeze_compose,neg_add_cancel,squeeze_initial]
  ring

theorem inverse_field_graph (ε : ℝ) (hε : 0 < ε) (l : Transverse →L[ℝ] ℝ)
    (f g : Hilbert) (hg : (f,g) ∈ (physicalField l).graph) :
    (inverseL ε hε f,inverseL ε hε g) ∈ (physicalField l).graph := by
  apply (physicalField_graph l _ _).mpr
  filter_upwards [KFCausalClockFloorClockHalf.inverseAction_coe ε hε f,
    KFCausalClockFloorClockHalf.inverseAction_coe ε hε g,
    (physicalField_graph l f g).mp hg] with x hf hg hr
  change (inverseL ε hε f) x = _ at hf
  change (inverseL ε hε g) x = _ at hg
  rw [hg,hf,hr]
  ring

variable (ε h a w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a) (hw : 1 ≤ w)
  (hb : |h| ≤ Real.pi*ε/3)
local notation "τ" => Real.log w/2
local notation "hτ" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => KFCausalChargeGaussianGeometry.groundWidth h
local notation "β" => KFCausalReciprocalGaussianDomain.baseWidth h τ
local notation "hα" => KFCausalChargeGaussianGeometry.groundWidth_positive h hh
local notation "hβ" => KFCausalReciprocalGaussianDomain.baseWidth_positive h hh τ
local notation "hwidth" => KFCausalReciprocalGaussianDomain.baseWidth_bound h hh τ hτ
local notation "d" => KFCausalNeutralExponentialProfiles.neutralSource ((Real.exp (-τ):ℂ)*b)
local notation "Q" => KFCausalReciprocalNeutralPackets.rescaledPolynomial τ P
local notation "c" => (Real.exp (-τ/2):ℂ)
local notation "hb₂" => KFCausalGaussianVacuumSquare.double_strip ε h hb
local notation "dirs" => KFCausalPhysicalEnergyFactors.modelDirections
local notation "field" => KFCausalMatterOrderedDomain.pointField

def doubledFieldOutput (l : Transverse →L[ℝ] ℝ) : Hilbert := c • transport (-τ)
  (KFCausalVariableWidthPolynomialDomain.output ε a α β hε ha hα hβ hwidth (2*h)
    C p d 4 hb₂ Q dirs (squeezedField (-τ) l) 5)

def fieldOutput (l : Transverse →L[ℝ] ℝ) : Hilbert :=
  inverseL ε hε (doubledFieldOutput ε h a w C p b P hε hh ha hw hb l)

theorem doubled_field_graph (l : Transverse →L[ℝ] ℝ) :
    (doubledOutput ε h a w C p b P hε hh ha hw hb,
      doubledFieldOutput ε h a w C p b P hε hh ha hw hb l) ∈ (physicalField l).graph := by
  let U := KFCausalVariableWidthPolynomialDomain.output ε a α β hε ha hα hβ hwidth (2*h)
    C p d 4 hb₂ Q dirs field 7
  let V := KFCausalVariableWidthPolynomialDomain.output ε a α β hε ha hα hβ hwidth (2*h)
    C p d 4 hb₂ Q dirs (squeezedField (-τ) l) 5
  have hV := KFCausalVariableWidthPolynomialDomain.output_graph ε a α β hε ha hα hβ hwidth
    (2*h) C p d 4 hb₂ Q dirs (squeezedField (-τ) l) 5
  obtain ⟨Y,hY,hL⟩ := (composition_graph _ _ _ _).mp hV
  have hU := KFCausalVariableWidthPolynomialDomain.output_graph ε a α β hε ha hα hβ hwidth
    (2*h) C p d 4 hb₂ Q dirs field 7
  have he : Y = U := (orderedExponential ε hε (2*h)).mem_graph_snd_inj' hY hU rfl
  rw [he] at hL
  exact (physicalField l).graph.smul_mem c (squeeze_field_graph (-τ) l U V hL)

theorem first_field_graph (l : Transverse →L[ℝ] ℝ) :
    (firstOutput ε h a w C p b P hε hh ha hw hb,
      fieldOutput ε h a w C p b P hε hh ha hw hb l) ∈ (physicalField l).graph :=
  inverse_field_graph ε hε l _ _ (doubled_field_graph ε h a w C p b P hε hh ha hw hb l)

theorem field_after_square_graph (l : Transverse →L[ℝ] ℝ) :
    (state ε h a w C p b P hε hh ha hw,
      fieldOutput ε h a w C p b P hε hh ha hw hb l) ∈
      (composition (physicalField l) (KFCausalClockFloorVacuumSquare.square ε hε h)).graph :=
  (composition_graph _ _ _ _).mpr ⟨_,first_graph ε h a w C p b P hε hh ha hw hb,
    first_field_graph ε h a w C p b P hε hh ha hw hb l⟩

theorem symmetric_first_mixed (i : Fin 2) :
    mixedCoordinates (fieldOutput ε h a w C p b P hε hh ha hw hb (symmetricPosition i)) =ᵐ[volume]
      fun z => (z.2 (symmetricIndex i) : ℂ)*density ε h a w C p b P z := by
  have hg := (symmetric_position_graph_iff i _ _).mp
    (first_field_graph ε h a w C p b P hε hh ha hw hb (symmetricPosition i))
  filter_upwards [hg,first_mixed ε h a w C p b P hε hh ha hw hb] with z hg hf
  rw [hg,hf]

include hε hh ha hw hb in
theorem symmetric_moment_memLp (i : Fin 2) :
    MemLp (fun z => (z.2 (symmetricIndex i) : ℂ)*density ε h a w C p b P z) 2 :=
  (Lp.memLp (mixedCoordinates
    (fieldOutput ε h a w C p b P hε hh ha hw hb (symmetricPosition i)))).ae_eq
      (symmetric_first_mixed ε h a w C p b P hε hh ha hw hb i)

#print axioms squeeze_field_graph
#print axioms inverse_field_graph
#print axioms doubled_field_graph
#print axioms first_field_graph
#print axioms field_after_square_graph
#print axioms symmetric_first_mixed
#print axioms symmetric_moment_memLp
end
end UnifiedTheory.Audit.KFCausalSourcedWidthFirstField
