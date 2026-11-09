/- The actual bounded radial Yosida multiplier preserves every original
clock and kinetic first-factor domain. The two symmetric rows have the
derived bounded Leibniz correction; the antisymmetric rows commute. -/
import UnifiedTheory.Audit.KFCausalBoundedDirectionalLeibniz
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaDerivative
import UnifiedTheory.Audit.KFCausalSymmetricMomentumGraphEquivalence
import UnifiedTheory.Audit.KFCausalAntisymmetricMomentumGraphEquivalence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaKinetics
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalSymmetricMomentumCoordinates (symmetricDirection symmetricVector)
open KFCausalSymmetricMomentumGraphEquivalence (symmetric_graph_iff)
open KFCausalAntisymmetricMomentumCoordinates (antiDirection antiSymbol)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open KFCausalClockFloorAntisymmetricGraph (inverseL_charge_coe clockMomentum_graph_iff)
open KFCausalClockFloorClockHalf (clockHalf half_inverse_graph)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalClockFloorRadialYosidaSymbol
open KFCausalClockFloorRadialYosidaDerivative

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)

include hε hN in
private theorem symbol_measurable : Measurable (fun x : Joint 2 4 => (symbol ε h N x:ℂ)) :=
  (Complex.continuous_ofReal.comp (symbol_continuous ε hε h N hN)).measurable

include hε hN in
private theorem complex_symbol_bound (x : Joint 2 4) : ‖(symbol ε h N x:ℂ)‖ ≤ N := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (symbol_nonnegative ε hε h N hN x)]
  exact symbol_le ε hε h N hN x

include hε hN in
private theorem derivative_measurable (i : Fin 2) :
    Measurable (fun x : Joint 2 4 => (derivativeSymbol ε h N i x:ℂ)) :=
  (Complex.continuous_ofReal.comp (derivativeSymbol_continuous ε hε h N hN i)).measurable

include hε hN in
private theorem complex_derivative_bound (i : Fin 2) (x : Joint 2 4) :
    ‖(derivativeSymbol ε h N i x:ℂ)‖ ≤ Real.sqrt (N/ε) := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact derivativeSymbol_bound ε hε h N hN i x

def derivativeAction (i : Fin 2) : Hilbert →L[ℂ] Hilbert :=
  (chargeCoordinates.symm : JointHilbert 2 4 →L[ℂ] Hilbert).comp
    ((KFCausalBoundedLpMultiplier.operator (fun x => (derivativeSymbol ε h N i x:ℂ))
      (derivative_measurable ε hε h N hN i) (Real.sqrt (N/ε)) (Real.sqrt_nonneg _)
      (complex_derivative_bound ε hε h N hN i)).comp
        (chargeCoordinates : Hilbert →L[ℂ] JointHilbert 2 4))

private theorem action_coordinates (f : Hilbert) :
    chargeCoordinates (action ε hε h N hN f)=
      KFCausalBoundedLpMultiplier.operator (fun x => (symbol ε h N x:ℂ))
        (symbol_measurable ε hε h N hN) N hN.le (complex_symbol_bound ε hε h N hN)
          (chargeCoordinates f) := by
  apply Lp.ext
  exact (action_coe ε hε h N hN f).trans
    (KFCausalBoundedLpMultiplier.operator_coe _ _ _ _ _ _).symm

private theorem derivativeAction_coordinates (i : Fin 2) (f : Hilbert) :
    chargeCoordinates (derivativeAction ε hε h N hN i f)=
      KFCausalBoundedLpMultiplier.operator (fun x => (derivativeSymbol ε h N i x:ℂ))
        (derivative_measurable ε hε h N hN i) (Real.sqrt (N/ε)) (Real.sqrt_nonneg _)
        (complex_derivative_bound ε hε h N hN i) (chargeCoordinates f) :=
  chargeCoordinates.apply_symm_apply _

theorem derivativeAction_coe (i : Fin 2) (f : Hilbert) :
    chargeCoordinates (derivativeAction ε hε h N hN i f) =ᵐ[volume]
      fun x => (derivativeSymbol ε h N i x:ℂ)*(chargeCoordinates f) x := by
  rw [derivativeAction_coordinates]
  exact KFCausalBoundedLpMultiplier.operator_coe _ _ _ _ _ _

theorem derivativeAction_norm (i : Fin 2) (f : Hilbert) :
    ‖derivativeAction ε hε h N hN i f‖ ≤ Real.sqrt (N/ε)*‖f‖ := by
  rw [← chargeCoordinates.norm_map (derivativeAction ε hε h N hN i f),
    derivativeAction_coordinates,← chargeCoordinates.norm_map f]
  exact KFCausalBoundedLpMultiplier.operator_norm _ _ _ _ _ _

theorem action_inverseL (f : Hilbert) :
    inverseL ε hε (action ε hε h N hN f)=action ε hε h N hN (inverseL ε hε f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [inverseL_charge_coe ε hε (action ε hε h N hN f),
    action_coe ε hε h N hN f,action_coe ε hε h N hN (inverseL ε hε f),
    inverseL_charge_coe ε hε f] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  ring

theorem clock_graph (f g : Hilbert) (hfg : (f,g) ∈ (clockHalf ε).graph) :
    (action ε hε h N hN f,action ε hε h N hN g) ∈ (clockHalf ε).graph := by
  apply (half_inverse_graph ε hε _ _).mpr
  apply (inverseL_graph ε hε _ _).mpr
  have he := (inverseL_graph ε hε g f).mp ((half_inverse_graph ε hε f g).mp hfg)
  rw [action_inverseL,← he]

theorem symmetric_graph (hh : h ≠ 0) (i : Fin 2) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h (symmetricDirection i)).graph) :
    (action ε hε h N hN f,
      action ε hε h N hN g+(-Complex.I*(h:ℂ)) • derivativeAction ε hε h N hN i f) ∈
      (transverseMomentum h (symmetricDirection i)).graph := by
  have hg := KFCausalBoundedDirectionalLeibniz.spectral_graph (symmetricVector i)
    (fun x => (symbol ε h N x:ℂ)) (fun x => (derivativeSymbol ε h N i x:ℂ))
    (symbol_measurable ε hε h N hN) (derivative_measurable ε hε h N hN i)
    N (Real.sqrt (N/ε)) hN.le (Real.sqrt_nonneg _)
    (complex_symbol_bound ε hε h N hN) (complex_derivative_bound ε hε h N hN i)
    (fun x t => (symbol_hasDerivAt ε hε h N hN i x t).ofReal_comp)
    h hh (chargeCoordinates f) (chargeCoordinates g) ((symmetric_graph_iff h hh i f g).mp hfg)
  apply (symmetric_graph_iff h hh i _ _).mpr
  simpa only [map_add,map_smul,action_coordinates,derivativeAction_coordinates] using hg

def symmetricCorrection (i : Fin 2) : Hilbert →L[ℂ] Hilbert :=
  (-Complex.I*(h:ℂ)) • (derivativeAction ε hε h N hN i).comp (inverseL ε hε)

theorem ordered_symmetric_graph (hh : h ≠ 0) (i : Fin 2) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h (symmetricDirection i)).graph) :
    (action ε hε h N hN f,action ε hε h N hN g+symmetricCorrection ε hε h N hN i f) ∈
      (clockMomentum ε h (symmetricDirection i)).graph := by
  apply (clockMomentum_graph_iff ε hε h _ _ _).mpr
  rw [action_inverseL]
  exact symmetric_graph ε hε h N hN hh i _ _ ((clockMomentum_graph_iff ε hε h _ f g).mp hfg)

theorem symmetricCorrection_norm (i : Fin 2) (f : Hilbert) :
    ‖symmetricCorrection ε hε h N hN i f‖ ≤
      (|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹)*‖f‖ := by
  change ‖(-Complex.I*(h:ℂ)) • derivativeAction ε hε h N hN i (inverseL ε hε f)‖ ≤ _
  rw [norm_smul,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left (derivativeAction_norm ε hε h N hN i (inverseL ε hε f))
    (abs_nonneg h)).trans
  have hi : ‖inverseL ε hε f‖ ≤ (Real.sqrt ε)⁻¹*‖f‖ :=
    KFCausalClockFloorBoundedInverse.inverseAction_norm_bound ε hε f
  calc
    |h| *(Real.sqrt (N/ε)*‖inverseL ε hε f‖) ≤
        |h| *(Real.sqrt (N/ε)*((Real.sqrt ε)⁻¹*‖f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

theorem antisymmetric_graph (hh : h ≠ 0) (i : Fin 2) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h (antiDirection i)).graph) :
    (action ε hε h N hN f,action ε hε h N hN g) ∈
      (transverseMomentum h (antiDirection i)).graph := by
  apply (KFCausalAntisymmetricMomentumGraphEquivalence.antisymmetric_graph_iff h hh i _ _).mpr
  filter_upwards [action_coe ε hε h N hN f,action_coe ε hε h N hN g,
    (KFCausalAntisymmetricMomentumGraphEquivalence.antisymmetric_graph_iff h hh i f g).mp hfg]
      with x hf hg hx
  rw [hf,hg,hx]
  ring

def correction (i : Fin 4) : Hilbert →L[ℂ] Hilbert :=
  if hi : i.val < 2 then symmetricCorrection ε hε h N hN ⟨i.val,hi⟩ else 0

theorem kinetic_graph (hh : h ≠ 0) (i : Fin 4) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h (modelDirections i)).graph) :
    (action ε hε h N hN f,action ε hε h N hN g+correction ε hε h N hN i f) ∈
      (clockMomentum ε h (modelDirections i)).graph := by
  fin_cases i
  · exact ordered_symmetric_graph ε hε h N hN hh 0 f g hfg
  · exact ordered_symmetric_graph ε hε h N hN hh 1 f g hfg
  · have hg := antisymmetric_graph ε hε h N hN hh 0 _ _
      ((clockMomentum_graph_iff ε hε h _ f g).mp hfg)
    apply (clockMomentum_graph_iff ε hε h _ _ _).mpr
    change (inverseL ε hε (action ε hε h N hN f),action ε hε h N hN g+0) ∈ _
    rw [add_zero,action_inverseL]
    exact hg
  · have hg := antisymmetric_graph ε hε h N hN hh 1 _ _
      ((clockMomentum_graph_iff ε hε h _ f g).mp hfg)
    apply (clockMomentum_graph_iff ε hε h _ _ _).mpr
    change (inverseL ε hε (action ε hε h N hN f),action ε hε h N hN g+0) ∈ _
    rw [add_zero,action_inverseL]
    exact hg

#print axioms derivativeAction_coe
#print axioms derivativeAction_norm
#print axioms action_inverseL
#print axioms clock_graph
#print axioms symmetric_graph
#print axioms ordered_symmetric_graph
#print axioms symmetricCorrection_norm
#print axioms antisymmetric_graph
#print axioms kinetic_graph
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaKinetics
