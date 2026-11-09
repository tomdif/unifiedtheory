/- Bounded holomorphic clock functions transport all eight actual natural
second graphs. The two longitudinal half steps shift the multiplier twice;
the proof retains the primitive intermediate graph witnesses. -/
import UnifiedTheory.Audit.KFCausalAnalyticClockFamily
import UnifiedTheory.Audit.KFCausalBoundedClockFactorGraphs
import UnifiedTheory.Audit.KFCausalBoundedClockMatterGraphs
import UnifiedTheory.Audit.KFCausalNaturalSecondHamiltonianGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalAnalyticClockSecondTransport
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalRegularizedLongitudinalChart (chart chart_continuous)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorClockHalf (clockHalf inverseClockHalf)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalNaturalSecondHamiltonianGraph (component)

variable (F : ℂ → ℂ) (h M : ℝ)
  (hF : ∀ q, |q.im| ≤ |h| → AnalyticAt ℂ F q)
  (hM : 0 ≤ M) (hB : ∀ q, |q.im| ≤ |h| → ‖F q‖ ≤ M)

def line (ε y s : ℝ) : ℂ := F ((chart ε s:ℂ)+(y:ℂ)*Complex.I)

include hF in
private theorem line_continuous (ε y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (line F ε y) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  exact (hF _ (by simpa using hy)).continuousAt.comp
    (((Complex.continuous_ofReal.comp (chart_continuous ε)).add continuous_const).continuousAt)

def operator (ε y : ℝ) (hy : |y| ≤ |h|) : Hilbert →L[ℂ] Hilbert :=
  KFCausalBoundedClockCharge.multiplier (line F ε y)
    (line_continuous F h hF ε y hy).measurable M hM
    (fun s => hB _ (by simpa using hy))

theorem operator_coe (ε y : ℝ) (hy : |y| ≤ |h|) (f : Hilbert) :
    operator F h M hF hM hB ε y hy f =ᵐ[volume]
      fun x => line F ε y x.1*f x :=
  KFCausalBoundedClockCharge.multiplier_coe _ _ _ _ _ f

theorem operator_charge (ε y : ℝ) (hy : |y| ≤ |h|) (hh : h ≠ 0)
    (θ : ℝ) (f : Hilbert) :
    operator F h M hF hM hB ε y hy (KFCausalPhysicalCircleAction.action h hh θ f) =
      KFCausalPhysicalCircleAction.action h hh θ (operator F h M hF hM hB ε y hy f) :=
  KFCausalBoundedClockCharge.multiplier_charge _ _ _ _ _ h hh θ f

private theorem half_graph (ε : ℝ) (hε : 0 < ε) (y : ℝ)
    (hy : |y|+|h|/2 ≤ |h|) (f g : Hilbert)
    (hg : (f,g) ∈ (longitudinalExponential ε hε h (1/2)).graph) :
    (operator F h M hF hM hB ε y (by linarith [abs_nonneg h]) f,
      operator F h M hF hM hB ε (y-h/2)
        (by calc |y-h/2| ≤ |y|+|h|/2 := by simpa [abs_div] using abs_sub y (h/2)
                 _ ≤ |h| := hy) g) ∈
      (longitudinalExponential ε hε h (1/2)).graph := by
  let G : ℂ → ℂ := fun q => F (q+(y:ℂ)*Complex.I)
  have hs (q : ℂ) (hq : |q.im| ≤ |h|/2) : |(q+(y:ℂ)*Complex.I).im| ≤ |h| := by
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,mul_one,
      Complex.ofReal_im,Complex.I_re,mul_zero,add_zero]
    exact (abs_add_le _ _).trans (by linarith)
  have hG (q : ℂ) (hq : |q.im| ≤ |h|/2) : AnalyticAt ℂ G q :=
    (hF _ (hs q hq)).comp (f := fun z : ℂ => z+(y:ℂ)*Complex.I) (x := q)
      (by fun_prop)
  have hBG (q : ℂ) (hq : |q.im| ≤ |h|/2) : ‖G q‖ ≤ M := hB _ (hs q hq)
  have he (r : ℝ) (hr : |r| ≤ |h|/2) :
      KFCausalAnalyticClockFamily.operator G (|h|/2) M hG hM hBG ε hε r hr =
        operator F h M hF hM hB ε (y+r)
          (by calc |y+r| ≤ |y|+|r| := abs_add_le _ _
                   _ ≤ |h| := by linarith) := by
    apply KFCausalAnalyticClockFamily.operator_eq
    intro u
    filter_upwards [operator_coe F h M hF hM hB ε (y+r) _ u] with x hx
    rw [hx]
    unfold line G
    congr 2
    push_cast
    ring
  have hh0 : |(0:ℝ)| ≤ |h|/2 := by simp; positivity
  have hh1 : |-h/2| ≤ |h|/2 := by simp [abs_div]
  have H := KFCausalAnalyticClockFamily.graph G (|h|/2) M hG hM hBG ε hε h hh0 hh1 f g hg
  rw [he 0 hh0,he (-h/2) hh1] at H
  simpa only [add_zero,sub_eq_add_neg,neg_div] using H

private theorem clock_graph (ε y : ℝ) (hy : |y| ≤ |h|) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    (operator F h M hF hM hB ε y hy f,operator F h M hF hM hB ε y hy g) ∈
      (clockHalf ε).graph :=
  KFCausalBoundedClockFactorGraphs.half_graph _ _ _ _ _ ε f g hg

private theorem inverse_graph (ε y : ℝ) (hy : |y| ≤ |h|) (f g : Hilbert)
    (hg : (f,g) ∈ (inverseClockHalf ε).graph) :
    (operator F h M hF hM hB ε y hy f,operator F h M hF hM hB ε y hy g) ∈
      (inverseClockHalf ε).graph :=
  KFCausalBoundedClockFactorGraphs.inverse_half_graph _ _ _ _ _ ε f g hg

private theorem momentum_graph (ε y : ℝ) (hy : |y| ≤ |h|) (hh : h ≠ 0)
    (v : KFCausalTransverseDilationFlow.Transverse) (f g : Hilbert)
    (hg : (f,g) ∈ (KFCausalPhysicalTransverseMomentum.transverseMomentum h v).graph) :
    (operator F h M hF hM hB ε y hy f,operator F h M hF hM hB ε y hy g) ∈
      (KFCausalPhysicalTransverseMomentum.transverseMomentum h v).graph :=
  KFCausalBoundedClockFactorGraphs.transverse_graph _ _ _ _ _ h hh v f g hg

private theorem field_graph (ε y : ℝ) (hy : |y| ≤ |h|)
    (f g : Hilbert) (hg : (f,g) ∈ (KFCausalPhysicalField.physicalField pointField).graph) :
    (operator F h M hF hM hB ε y hy f,operator F h M hF hM hB ε y hy g) ∈
      (KFCausalPhysicalField.physicalField pointField).graph :=
  KFCausalBoundedClockMatterGraphs.field_graph _ _ _ _ _ pointField f g hg

private theorem fieldSquare_graph (ε y : ℝ) (hy : |y| ≤ |h|)
    (f g : Hilbert) (hg : (f,g) ∈ (KFCausalTransverseFieldSquare.fieldSquare pointField).graph) :
    (operator F h M hF hM hB ε y hy f,operator F h M hF hM hB ε y hy g) ∈
      (KFCausalTransverseFieldSquare.fieldSquare pointField).graph :=
  KFCausalBoundedClockMatterGraphs.square_graph _ _ _ _ _ pointField f g hg

def firstShift (j : Fin 8) : ℝ := if 5 ≤ j.val then -h/2 else 0
def secondShift (j : Fin 8) : ℝ := if 5 ≤ j.val then -h else 0

private theorem firstShift_bound (j : Fin 8) : |firstShift h j| ≤ |h| := by
  unfold firstShift
  split_ifs <;> simp [abs_div]
private theorem secondShift_bound (j : Fin 8) : |secondShift h j| ≤ |h| := by
  unfold secondShift
  split_ifs <;> simp

private theorem ordered_graph (ε : ℝ) (hε : 0 < ε) (y : ℝ)
    (hy : |y|+|h|/2 ≤ |h|) (f g : Hilbert)
    (hg : (f,g) ∈ (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph) :
    (operator F h M hF hM hB ε y (by linarith [abs_nonneg h]) f,
      operator F h M hF hM hB ε (y-h/2)
        (by calc |y-h/2| ≤ |y|+|h|/2 := by simpa [abs_div] using abs_sub y (h/2)
                 _ ≤ |h| := hy) g) ∈
      (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph := by
  obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hg
  exact (composition_graph _ _ _ _).mpr ⟨_,
    inverse_graph F h M hF hM hB ε y _ _ _ hu,
    half_graph F h M hF hM hB ε hε y hy u g hg⟩

private theorem reversed_graph (ε : ℝ) (hε : 0 < ε) (y : ℝ)
    (hy : |y|+|h|/2 ≤ |h|) (f g : Hilbert)
    (hg : (f,g) ∈ (KFCausalClockFloorTrialSpectralDomain.reversedExponential ε hε h).graph) :
    (operator F h M hF hM hB ε y (by linarith [abs_nonneg h]) f,
      operator F h M hF hM hB ε (y-h/2)
        (by calc |y-h/2| ≤ |y|+|h|/2 := by simpa [abs_div] using abs_sub y (h/2)
                 _ ≤ |h| := hy) g) ∈
      (KFCausalClockFloorTrialSpectralDomain.reversedExponential ε hε h).graph := by
  obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hg
  exact (composition_graph _ _ _ _).mpr ⟨_,
    half_graph F h M hF hM hB ε hε y hy f u hu,
    inverse_graph F h M hF hM hB ε (y-h/2) _ _ _ hg⟩

theorem forward_graph (ε : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (j : Fin 8)
    (f g : Hilbert) (hg : (f,g) ∈ (energyFactor ε hε h modelDirections pointField j).graph) :
    (operator F h M hF hM hB ε 0 (by simp) f,
      operator F h M hF hM hB ε (firstShift h j) (firstShift_bound h j) g) ∈
      (energyFactor ε hε h modelDirections pointField j).graph := by
  have hy : |(0:ℝ)|+|h|/2 ≤ |h| := by simp
  fin_cases j
  · exact clock_graph F h M hF hM hB ε 0 (by simp) f g hg
  · exact KFCausalBoundedClockFactorGraphs.kinetic_graph _ _ _ _ _ ε h hh _ f g hg
  · exact KFCausalBoundedClockFactorGraphs.kinetic_graph _ _ _ _ _ ε h hh _ f g hg
  · exact KFCausalBoundedClockFactorGraphs.kinetic_graph _ _ _ _ _ ε h hh _ f g hg
  · exact KFCausalBoundedClockFactorGraphs.kinetic_graph _ _ _ _ _ ε h hh _ f g hg
  · obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hg
    exact (composition_graph _ _ _ _).mpr ⟨_,by simpa only [zero_sub,neg_div] using ordered_graph F h M hF hM hB ε hε 0 hy f u hu,
      field_graph F h M hF hM hB ε (-h/2) (firstShift_bound h 5) u g hg⟩
  · obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hg
    exact (composition_graph _ _ _ _).mpr ⟨_,by simpa only [zero_sub,neg_div] using ordered_graph F h M hF hM hB ε hε 0 hy f u hu,
      fieldSquare_graph F h M hF hM hB ε (-h/2) (firstShift_bound h 6) u g hg⟩
  · change (operator F h M hF hM hB ε 0 _ f,
      operator F h M hF hM hB ε (-h/2) _ g) ∈
        (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).graph
    simpa only [zero_sub,neg_div] using ordered_graph F h M hF hM hB ε hε 0 hy f g hg

theorem reverse_graph (ε : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (j : Fin 8)
    (f g : Hilbert) (hg : (f,g) ∈ (reverseFactor ε hε h modelDirections pointField j).graph) :
    (operator F h M hF hM hB ε (firstShift h j) (firstShift_bound h j) f,
      operator F h M hF hM hB ε (secondShift h j) (secondShift_bound h j) g) ∈
      (reverseFactor ε hε h modelDirections pointField j).graph := by
  have hy : |-h/2|+|h|/2 ≤ |h| := by simp [abs_div]
  have he : -h/2-h/2=-h := by ring
  fin_cases j
  · exact clock_graph F h M hF hM hB ε 0 (by simp) f g hg
  · obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hg
    exact (composition_graph _ _ _ _).mpr ⟨_,momentum_graph F h M hF hM hB ε 0 (by simp) hh _ f u hu,
      inverse_graph F h M hF hM hB ε 0 (by simp) u g hg⟩
  · obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hg
    exact (composition_graph _ _ _ _).mpr ⟨_,momentum_graph F h M hF hM hB ε 0 (by simp) hh _ f u hu,
      inverse_graph F h M hF hM hB ε 0 (by simp) u g hg⟩
  · obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hg
    exact (composition_graph _ _ _ _).mpr ⟨_,momentum_graph F h M hF hM hB ε 0 (by simp) hh _ f u hu,
      inverse_graph F h M hF hM hB ε 0 (by simp) u g hg⟩
  · obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hg
    exact (composition_graph _ _ _ _).mpr ⟨_,momentum_graph F h M hF hM hB ε 0 (by simp) hh _ f u hu,
      inverse_graph F h M hF hM hB ε 0 (by simp) u g hg⟩
  · obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hg
    exact (composition_graph _ _ _ _).mpr ⟨_,
      field_graph F h M hF hM hB ε (-h/2) (firstShift_bound h 5) f u hu,
      by simpa only [he] using reversed_graph F h M hF hM hB ε hε (-h/2) hy u g hg⟩
  · obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hg
    exact (composition_graph _ _ _ _).mpr ⟨_,
      fieldSquare_graph F h M hF hM hB ε (-h/2) (firstShift_bound h 6) f u hu,
      by simpa only [he] using reversed_graph F h M hF hM hB ε hε (-h/2) hy u g hg⟩
  · simpa only [he] using reversed_graph F h M hF hM hB ε hε (-h/2) hy f g hg

theorem second_graph (ε : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (j : Fin 8)
    (f g : Hilbert) (hg : (f,g) ∈ (component ε hε h j).graph) :
    (operator F h M hF hM hB ε 0 (by simp) f,
      operator F h M hF hM hB ε (secondShift h j) (secondShift_bound h j) g) ∈
      (component ε hε h j).graph := by
  obtain ⟨u,hu,hg⟩ := (composition_graph _ _ _ _).mp hg
  exact (composition_graph _ _ _ _).mpr ⟨_,
    forward_graph F h M hF hM hB ε hε hh j f u hu,
    reverse_graph F h M hF hM hB ε hε hh j u g hg⟩

#print axioms operator_coe
#print axioms operator_charge
#print axioms forward_graph
#print axioms reverse_graph
#print axioms second_graph
end
end UnifiedTheory.Audit.KFCausalAnalyticClockSecondTransport
