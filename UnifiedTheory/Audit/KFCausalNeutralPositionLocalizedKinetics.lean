/- The same localized physical neutral-position observable used by the
matter theorem preserves every natural ordered kinetic graph. Its exact
bounded correction is derived on all domain states, with explicit hbar
and Gaussian-width dependence. Charge averaging is not asserted. -/
import UnifiedTheory.Audit.KFCausalPhysicalGaussianCutoff
import UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL inverseL_graph inverseAction_norm_bound)
open UnifiedTheory.Audit.KFCausalClockFloorKineticModulation (kinetic_graph_iff)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier (action physicalPhase)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianCutoff (cutoff derivativeOperator)

def chargedLinear : Configuration →L[ℝ] ℝ where
  toFun x := x.2 2+x.2 3
  map_add' _ _ := by simp only [Prod.snd_add,Pi.add_apply]; ring
  map_smul' c x := by
    change c*x.2 2+c*x.2 3=c*(x.2 2+x.2 3)
    ring
  cont := by fun_prop

theorem zero_bound (ε : ℝ) (hε : 0 < ε) : |(0:ℝ)| ≤ Real.pi*ε/3 := by simp; positivity

def input (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) : Hilbert →L[ℂ] Hilbert :=
  action ε δ v hε hδ 0 (zero_bound ε hε)

theorem input_coe (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) :
    input ε δ v hε hδ f =ᵐ[volume] fun x => physicalPhase δ v x*f x :=
  KFCausalNeutralPositionLocalizedMultiplier.action_zero_coe ε δ v hε hδ _ f

theorem input_eq (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) :
    input ε δ v hε hδ f = KFCausalNeutralPositionCharge.action v (cutoff δ hδ chargedLinear f) := by
  apply Lp.ext
  filter_upwards [input_coe ε δ v hε hδ f,
    KFCausalNeutralPositionCharge.action_coe v (cutoff δ hδ chargedLinear f),
    KFCausalPhysicalGaussianCutoff.cutoff_coe δ hδ chargedLinear f] with x hm hp hq
  rw [hm,hp,hq,KFCausalNeutralPositionLocalizedLimit.physicalPhase_damping]
  change ((KFCausalGaussianCutoffTaylor.amplitude δ (chargedLinear x):ℂ)*
    KFCausalCanonicalWeylAlgebra.scalar (v*x.2 4))*f x = _
  ring

def momentumCorrection (δ v : ℝ) (hδ : 0 < δ) (h : ℝ) (d : Transverse) : Hilbert →L[ℂ] Hilbert :=
  (KFCausalNeutralPositionCharge.action v : Hilbert →L[ℂ] Hilbert).comp
    ((-Complex.I*(h:ℂ)) • derivativeOperator δ hδ chargedLinear d+
      ((h*(v*d 4):ℝ):ℂ) • cutoff δ hδ chargedLinear)

theorem momentum_graph_input (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (h : ℝ) (hne : h ≠ 0) (d : Transverse) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h d).graph) :
    (input ε δ v hε hδ f,input ε δ v hε hδ g+momentumCorrection δ v hδ h d f) ∈
      (transverseMomentum h d).graph := by
  have hg := KFCausalPhysicalGaussianCutoff.momentum_graph_cutoff δ hδ chargedLinear h hne d f g hfg
  have hp := KFCausalPhysicalMomentumModulation.momentum_graph_modulation h hne d
    (KFCausalNeutralPositionCharge.frequency v) _ _ hg
  change (KFCausalNeutralPositionCharge.action v (cutoff δ hδ chargedLinear f),
    KFCausalNeutralPositionCharge.action v (cutoff δ hδ chargedLinear g+
      (-Complex.I*(h:ℂ)) • derivativeOperator δ hδ chargedLinear d f+
        ((h*(v*d 4):ℝ):ℂ) • cutoff δ hδ chargedLinear f)) ∈ (transverseMomentum h d).graph at hp
  change (input ε δ v hε hδ f,input ε δ v hε hδ g+
    KFCausalNeutralPositionCharge.action v ((-Complex.I*(h:ℂ)) • derivativeOperator δ hδ chargedLinear d f+
      ((h*(v*d 4):ℝ):ℂ) • cutoff δ hδ chargedLinear f)) ∈ (transverseMomentum h d).graph
  rw [input_eq,input_eq]
  simpa only [map_add,add_assoc] using hp

theorem momentumCorrection_norm (δ v : ℝ) (hδ : 0 < δ) (h : ℝ) (d : Transverse) (f : Hilbert) :
    ‖momentumCorrection δ v hδ h d f‖ ≤
      |h| * (2*Real.sqrt δ*|d 2+d 3|+|v*d 4|)*‖f‖ := by
  change ‖KFCausalNeutralPositionCharge.action v ((-Complex.I*(h:ℂ)) • derivativeOperator δ hδ chargedLinear d f+
    ((h*(v*d 4):ℝ):ℂ) • cutoff δ hδ chargedLinear f)‖ ≤ _
  rw [(KFCausalNeutralPositionCharge.action v).norm_map]
  have hD := KFCausalPhysicalGaussianCutoff.derivativeOperator_norm δ hδ chargedLinear d f
  change ‖derivativeOperator δ hδ chargedLinear d f‖ ≤ |d 2+d 3| * (2*Real.sqrt δ)*‖f‖ at hD
  have hQ := KFCausalPhysicalGaussianCutoff.cutoff_norm δ hδ chargedLinear f
  calc
    _ ≤ ‖(-Complex.I*(h:ℂ)) • derivativeOperator δ hδ chargedLinear d f‖+
      ‖((h*(v*d 4):ℝ):ℂ) • cutoff δ hδ chargedLinear f‖ := norm_add_le _ _
    _ = |h| * ‖derivativeOperator δ hδ chargedLinear d f‖+
      |h| * |v*d 4| * ‖cutoff δ hδ chargedLinear f‖ := by
        simp only [norm_smul,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
    _ ≤ |h| * (|d 2+d 3| * (2*Real.sqrt δ)*‖f‖)+|h| * |v*d 4| * ‖f‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hD (abs_nonneg h))
        (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ = _ := by ring

theorem inverseL_input (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) :
    inverseL ε hε (input ε δ v hε hδ f) = input ε δ v hε hδ (inverseL ε hε f) := by
  have hg := KFCausalNeutralPositionLocalizedMatter.inverseHalf_graph_action ε δ v hε hδ
    0 (zero_bound ε hε) f (inverseL ε hε f) ((inverseL_graph ε hε f _).mpr rfl)
  exact ((inverseL_graph ε hε _ _).mp hg).symm

def kineticCorrection (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (h : ℝ) (d : Transverse) : Hilbert →L[ℂ] Hilbert :=
  (momentumCorrection δ v hδ h d).comp (inverseL ε hε)

theorem kinetic_graph_input (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (h : ℝ) (hne : h ≠ 0) (d : Transverse) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h d).graph) :
    (input ε δ v hε hδ f,input ε δ v hε hδ g+kineticCorrection ε δ v hε hδ h d f) ∈
      (clockMomentum ε h d).graph := by
  rw [kinetic_graph_iff ε hε,inverseL_input]
  exact momentum_graph_input ε δ v hε hδ h hne d _ _ ((kinetic_graph_iff ε hε h d f g).mp hfg)

theorem kineticCorrection_norm (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (h : ℝ) (d : Transverse) (f : Hilbert) :
    ‖kineticCorrection ε δ v hε hδ h d f‖ ≤
      (|h| * (2*Real.sqrt δ*|d 2+d 3|+|v*d 4|)*(Real.sqrt ε)⁻¹)*‖f‖ := by
  apply (momentumCorrection_norm δ v hδ h d (inverseL ε hε f)).trans
  have hi := inverseAction_norm_bound ε hε f
  change ‖inverseL ε hε f‖ ≤ _ at hi
  exact (mul_le_mul_of_nonneg_left hi (by positivity)).trans_eq (by ring)

#print axioms zero_bound
#print axioms input_coe
#print axioms input_eq
#print axioms momentum_graph_input
#print axioms momentumCorrection_norm
#print axioms inverseL_input
#print axioms kinetic_graph_input
#print axioms kineticCorrection_norm

end
end UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics
