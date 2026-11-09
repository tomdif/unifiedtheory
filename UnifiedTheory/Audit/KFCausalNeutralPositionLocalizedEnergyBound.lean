/- Quantitative control of the actual localized action on the full
unaveraged closed energy graph. The state correction is O(abs(hbar)),
with all constants displayed. Neither charge averaging nor cutoff removal
in graph norm is assumed or concluded. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedEnergyBound
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection (outputMap correctionMap)
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedKinetics
open UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (closedEnergy)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)

def directionConstant (ε δ v : ℝ) (d : Transverse) : ℝ :=
  (2*Real.sqrt δ*|d 2+d 3|+|v*d 4|)*(Real.sqrt ε)⁻¹

def rowConstant (ε δ v : ℝ) (d : Fin 4 → Transverse) : Fin 8 → ℝ :=
  ![0,directionConstant ε δ v (d 0),directionConstant ε δ v (d 1),
    directionConstant ε δ v (d 2),directionConstant ε δ v (d 3),0,0,0]

def correctionConstant (ε δ v : ℝ) (d : Fin 4 → Transverse) (c : Fin 8 → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖c i‖^2*(rowConstant ε δ v d i)^2)

theorem rowConstant_nonneg (ε δ v : ℝ) (d : Fin 4 → Transverse) (i : Fin 8) :
    0 ≤ rowConstant ε δ v d i := by
  fin_cases i <;> dsimp [rowConstant,directionConstant] <;> positivity

variable (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (h : ℝ)
  (hh : |h| ≤ 2*Real.pi*ε/3) (d : Fin 4 → Transverse)

theorem directionCorrection_norm (a : Transverse) (f : Hilbert) :
    ‖kineticCorrection ε δ v hε hδ h a f‖ ≤ |h| * directionConstant ε δ v a*‖f‖ :=
  (kineticCorrection_norm ε δ v hε hδ h a f).trans_eq (by unfold directionConstant; ring)

theorem factorCorrection_norm (i : Fin 8) (f : Hilbert) :
    ‖factorCorrection ε δ v hε hδ h d i f‖ ≤ |h| * rowConstant ε δ v d i*‖f‖ := by
  fin_cases i
  · change ‖(0:Hilbert)‖ ≤ |h| * 0*‖f‖
    simp only [norm_zero,mul_zero,zero_mul,le_refl]
  · exact directionCorrection_norm ε δ v hε hδ h (d 0) f
  · exact directionCorrection_norm ε δ v hε hδ h (d 1) f
  · exact directionCorrection_norm ε δ v hε hδ h (d 2) f
  · exact directionCorrection_norm ε δ v hε hδ h (d 3) f
  · change ‖(0:Hilbert)‖ ≤ |h| * 0*‖f‖
    simp only [norm_zero,mul_zero,zero_mul,le_refl]
  · change ‖(0:Hilbert)‖ ≤ |h| * 0*‖f‖
    simp only [norm_zero,mul_zero,zero_mul,le_refl]
  · change ‖(0:Hilbert)‖ ≤ |h| * 0*‖f‖
    simp only [norm_zero,mul_zero,zero_mul,le_refl]

theorem factorOutput_norm (i : Fin 8) (f : Hilbert) :
    ‖factorOutput ε δ v hε hδ h hh i f‖ ≤ Real.exp (v^2*h^2/(8*δ*ε^2))*‖f‖ := by
  have hR : 1 ≤ Real.exp (v^2*h^2/(8*δ*ε^2)) := Real.one_le_exp_iff.mpr (by positivity)
  have hM : ‖input ε δ v hε hδ f‖ ≤ Real.exp (v^2*h^2/(8*δ*ε^2))*‖f‖ :=
    (KFCausalNeutralPositionLocalizedMultiplier.action_zero_contractive ε δ v hε hδ (zero_bound ε hε) f).trans
      (le_mul_of_one_le_left (norm_nonneg f) hR)
  have hB := KFCausalNeutralPositionLocalizedMatter.output_norm ε δ v hε hδ h hh f
  fin_cases i
  · exact hM
  · exact hM
  · exact hM
  · exact hM
  · exact hM
  · exact hB
  · exact hB
  · exact hB

theorem output_norm (g : Output (Fin 8) Hilbert) :
    ‖outputMap (factorOutput ε δ v hε hδ h hh) g‖ ≤ Real.exp (v^2*h^2/(8*δ*ε^2))*‖g‖ :=
  KFCausalJointGraphBoundedCorrection.outputMap_norm _ _ (Real.exp_pos _).le
    (factorOutput_norm ε δ v hε hδ h hh) g

theorem correction_norm (c : Fin 8 → ℂ) (f : Hilbert) :
    ‖correctionMap (factorCorrection ε δ v hε hδ h d) c f‖ ≤
      |h| * correctionConstant ε δ v d c*‖f‖ := by
  have hsum : 0 ≤ ∑ i : Fin 8, ‖c i‖^2*(rowConstant ε δ v d i)^2 :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hs : ‖correctionMap (factorCorrection ε δ v hε hδ h d) c f‖^2 ≤
      (|h| * correctionConstant ε δ v d c*‖f‖)^2 := by
    rw [PiLp.norm_sq_eq_of_L2,mul_pow,mul_pow,correctionConstant,Real.sq_sqrt hsum,
      Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    change ‖c i • factorCorrection ε δ v hε hδ h d i f‖^2 ≤ _
    rw [norm_smul,mul_pow]
    calc
      _ ≤ ‖c i‖^2*(|h| * rowConstant ε δ v d i*‖f‖)^2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (factorCorrection_norm ε δ v hε hδ h d i f) 2)
          (sq_nonneg _)
      _ = _ := by ring
  have hn : 0 ≤ |h| * correctionConstant ε δ v d c*‖f‖ := by
    unfold correctionConstant
    positivity
  nlinarith [norm_nonneg (correctionMap (factorCorrection ε δ v hε hδ h d) c f)]

theorem transformedOutput_norm (c : Fin 8 → ℂ) (f : Hilbert) (g : Output (Fin 8) Hilbert) :
    ‖transformedOutput ε δ v hε hδ h hh d c f g‖ ≤
      Real.exp (v^2*h^2/(8*δ*ε^2))*‖g‖+|h| * correctionConstant ε δ v d c*‖f‖ :=
  (norm_add_le _ _).trans
    (add_le_add (output_norm ε δ v hε hδ h hh g) (correction_norm ε δ v hε hδ h d c f))

variable (hne : h ≠ 0) (l : Transverse →L[ℝ] ℝ) (mass2 quartic vacuum t : ℝ)

theorem closed_bound (f : (closedEnergy ε hε h d l mass2 quartic vacuum t).domain) :
    ‖closedEnergy ε hε h d l mass2 quartic vacuum t
      ⟨input ε δ v hε hδ f,closed_domain ε δ v hε hδ h hh hne d l mass2 quartic vacuum t f f.property⟩‖ ≤
        Real.exp (v^2*h^2/(8*δ*ε^2))*‖closedEnergy ε hε h d l mass2 quartic vacuum t f‖+
          |h| * correctionConstant ε δ v d (energyWeight mass2 quartic vacuum t)*‖(f:Hilbert)‖ := by
  rw [closed_action ε δ v hε hδ h hh hne d l mass2 quartic vacuum t]
  exact transformedOutput_norm ε δ v hε hδ h hh d _ f _

include hh hne in
theorem closed_graph_with_bound (f : Hilbert) (g : Output (Fin 8) Hilbert)
    (hfg : (f,g) ∈ (closedEnergy ε hε h d l mass2 quartic vacuum t).graph) :
    ∃ g' : Output (Fin 8) Hilbert,
      (input ε δ v hε hδ f,g') ∈ (closedEnergy ε hε h d l mass2 quartic vacuum t).graph ∧
        ‖g'‖ ≤ Real.exp (v^2*h^2/(8*δ*ε^2))*‖g‖+
          |h| * correctionConstant ε δ v d (energyWeight mass2 quartic vacuum t)*‖f‖ :=
  ⟨_,closed_graph ε δ v hε hδ h hh hne d l mass2 quartic vacuum t f g hfg,
    transformedOutput_norm ε δ v hε hδ h hh d _ f g⟩

#print axioms rowConstant_nonneg
#print axioms directionCorrection_norm
#print axioms factorCorrection_norm
#print axioms factorOutput_norm
#print axioms output_norm
#print axioms correction_norm
#print axioms transformedOutput_norm
#print axioms closed_bound
#print axioms closed_graph_with_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedEnergyBound
