/- Closure of the actual homogeneous energy form by its joint factors.
The graph is single-valued, densely defined and complete in the energy
graph norm. Construction of the associated Hamiltonian remains separate. -/
import UnifiedTheory.Audit.KFCausalRegularizedClockFactor
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedClosedForm
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
open UnifiedTheory.Audit.KFCausalRegularizedFormDomain
open UnifiedTheory.Audit.KFCausalRegularizedAdjointTests
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedClockFactor
open UnifiedTheory.Audit.KFCausalSeparatedGraphClosure

abbrev Output := WithLp 2 (Hilbert × Hilbert)

def coreToJoint (ε : ℝ) (hε : 0 < ε) (hbar a b : ℝ) : functionCore ε hε hbar →ₗ[ℂ] Output :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert Hilbert).symm.toLinearMap.comp
    (((a : ℂ) • coreToClock ε hε hbar).prod ((b : ℂ) • coreToMomentum ε hε hbar))

def jointInputTest (ε : ℝ) (hε : 0 < ε) (a b : ℝ) : ℝ ⊕ ℝ → Hilbert
  | .inl p => (a : ℂ) • clockInputPairVector p
  | .inr p => (b : ℂ) • inputPairVector ε hε p
def jointOutputTest (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : ℝ ⊕ ℝ → Output
  | .inl p => WithLp.toLp 2 (clockOutputPairVector ε hε p,0)
  | .inr p => WithLp.toLp 2 (0,outputPairVector hbar p)

theorem joint_tests_separate (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (y : Output)
    (hy : ∀ j, inner ℂ (jointOutputTest ε hε hbar j) y=0) : y=0 := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply clock_pair_vectors_separate ε hε
    intro p
    simpa [jointOutputTest,WithLp.prod_inner_apply] using hy (.inl p)
  · apply pair_vectors_separate hbar
    intro p
    simpa [jointOutputTest,WithLp.prod_inner_apply] using hy (.inr p)

theorem joint_pairing (ε : ℝ) (hε : 0 < ε) (hbar a b : ℝ)
    (f : functionCore ε hε hbar) (j : ℝ ⊕ ℝ) :
    inner ℂ (jointOutputTest ε hε hbar j) (coreToJoint ε hε hbar a b f)=
      inner ℂ (jointInputTest ε hε a b j) (coreToHilbert ε hε hbar f) := by
  cases j with
  | inl p =>
    simp [jointOutputTest,jointInputTest,coreToJoint,WithLp.prod_inner_apply,
      inner_smul_left_eq_smul,inner_smul_right_eq_smul,hilbert_clock_pairing]
  | inr p =>
    simp [jointOutputTest,jointInputTest,coreToJoint,WithLp.prod_inner_apply,
      inner_smul_left_eq_smul,inner_smul_right_eq_smul,hilbert_momentum_pairing]

def jointInitial (ε : ℝ) (hε : 0 < ε) (hbar a b : ℝ) : Hilbert →ₗ.[ℂ] Output :=
  initialOperator (coreToHilbert ε hε hbar) (coreToJoint ε hε hbar a b)
def jointClosed (ε : ℝ) (hε : 0 < ε) (hbar a b : ℝ) : Hilbert →ₗ.[ℂ] Output :=
  closedOperator (coreToHilbert ε hε hbar) (coreToJoint ε hε hbar a b)

theorem joint_initial_graph (ε : ℝ) (hε : 0 < ε) (hbar a b : ℝ) :
    (jointInitial ε hε hbar a b).graph=
      graphRange (coreToHilbert ε hε hbar) (coreToJoint ε hε hbar a b) :=
  initialOperator_graph _ _ (jointInputTest ε hε a b) (jointOutputTest ε hε hbar)
    (joint_tests_separate ε hε hbar) (joint_pairing ε hε hbar a b)

theorem joint_closed_graph (ε : ℝ) (hε : 0 < ε) (hbar a b : ℝ) :
    (jointClosed ε hε hbar a b).graph=
      (graphRange (coreToHilbert ε hε hbar) (coreToJoint ε hε hbar a b)).topologicalClosure :=
  closedOperator_graph _ _ (jointInputTest ε hε a b) (jointOutputTest ε hε hbar)
    (joint_tests_separate ε hε hbar) (joint_pairing ε hε hbar a b)

theorem joint_isClosable (ε : ℝ) (hε : 0 < ε) (hbar a b : ℝ) :
    (jointInitial ε hε hbar a b).IsClosable :=
  operator_closable _ _ (jointInputTest ε hε a b) (jointOutputTest ε hε hbar)
    (joint_tests_separate ε hε hbar) (joint_pairing ε hε hbar a b)

theorem joint_isClosed (ε : ℝ) (hε : 0 < ε) (hbar a b : ℝ) :
    (jointClosed ε hε hbar a b).IsClosed :=
  operator_closed _ _ (jointInputTest ε hε a b) (jointOutputTest ε hε hbar)
    (joint_tests_separate ε hε hbar) (joint_pairing ε hε hbar a b)

theorem joint_contains_core (ε : ℝ) (hε : 0 < ε) (hbar a b : ℝ)
    (f : functionCore ε hε hbar) :
    (coreToHilbert ε hε hbar f,coreToJoint ε hε hbar a b f) ∈ (jointClosed ε hε hbar a b).graph := by
  rw [joint_closed_graph]
  apply Submodule.le_topologicalClosure
  exact ⟨f,rfl⟩

theorem joint_dense (ε : ℝ) (hε : 0 < ε) (hbar a b : ℝ) :
    Dense ((jointClosed ε hε hbar a b).domain : Set Hilbert) := by
  have hd : Dense (formDomain ε hε hbar : Set Hilbert) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (dense_form_domain ε hε hbar)
  apply hd.mono
  rintro _ ⟨f,rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (joint_contains_core ε hε hbar a b f)

theorem norm_toLp_square (f : ℝ → ℂ) (hf : MemLp f 2) :
    ‖hf.toLp f‖^2=∫ q, ‖f q‖^2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    _ = inner ℂ (hf.toLp f) (hf.toLp f) := by
      simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hf.toLp f)).symm
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with q hq
      rw [hq,inner_self_eq_norm_sq_to_K]
      norm_cast

def homogeneousEnergy (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) (f : ℝ → ℂ) : ℝ :=
  (∫ q, clockQ ε hε q*‖f q‖^2)/2+
    coupling*Real.exp (2*t)*(∫ k, Real.exp (2*Real.pi*hbar*k)*‖(𝓕 (inverseHalfApply ε hε f)) k‖^2)

theorem joint_norm_energy (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) (hc : 0 ≤ coupling)
    (f : functionCore ε hε hbar) :
    ‖coreToJoint ε hε hbar (Real.sqrt (1/2)) (Real.sqrt coupling*Real.exp t) f‖^2=
      homogeneousEnergy ε hε hbar coupling t f := by
  change ‖WithLp.toLp 2 (((Real.sqrt (1/2) : ℝ) : ℂ) • coreToClock ε hε hbar f,
    ((Real.sqrt coupling*Real.exp t : ℝ) : ℂ) • coreToMomentum ε hε hbar f)‖^2=_
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst,WithLp.toLp_snd,norm_smul,mul_pow,Complex.norm_real,
    Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/2),Real.sq_sqrt hc]
  change (1/2)*‖(clockOutput_memLp ε hε hbar f).toLp _‖^2+
    coupling*(Real.exp t)^2*‖(momentumOutput_memLp ε hε hbar f).toLp _‖^2=_
  rw [norm_toLp_square,norm_toLp_square,← Real.exp_nat_mul]
  simp only [clockOutput_square,momentumOutput_square,homogeneousEnergy]
  push_cast
  ring

/-- This closed graph, with its Hilbert product norm, is the completed
form space. The coordinate projection is single-valued by construction. -/
def energyGraph (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    Submodule ℂ (WithLp 2 (Hilbert × Output)) :=
  (jointClosed ε hε hbar (Real.sqrt (1/2)) (Real.sqrt coupling*Real.exp t)).graph.comap
    (WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert Output).toLinearMap

theorem energyGraph_isClosed (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    IsClosed (energyGraph ε hε hbar coupling t : Set (WithLp 2 (Hilbert × Output))) :=
  (joint_isClosed ε hε hbar _ _).preimage
    (WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert Output).continuous

theorem energyGraph_complete (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    CompleteSpace (energyGraph ε hε hbar coupling t) :=
  (energyGraph_isClosed ε hε hbar coupling t).completeSpace_coe

theorem core_energy_graph_norm (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) (hc : 0 ≤ coupling)
    (f : functionCore ε hε hbar) :
    let z := WithLp.toLp 2 (coreToHilbert ε hε hbar f,
      coreToJoint ε hε hbar (Real.sqrt (1/2)) (Real.sqrt coupling*Real.exp t) f)
    z ∈ energyGraph ε hε hbar coupling t ∧
      ‖z‖^2=‖coreToHilbert ε hε hbar f‖^2+homogeneousEnergy ε hε hbar coupling t f := by
  refine ⟨joint_contains_core ε hε hbar _ _ f,?_⟩
  rw [WithLp.prod_norm_sq_eq_of_L2]
  exact congrArg (fun e => ‖coreToHilbert ε hε hbar f‖^2+e) (joint_norm_energy ε hε hbar coupling t hc f)

#print axioms joint_tests_separate
#print axioms joint_pairing
#print axioms joint_isClosable
#print axioms joint_isClosed
#print axioms joint_dense
#print axioms joint_norm_energy
#print axioms energyGraph_complete
#print axioms core_energy_graph_norm

end
end UnifiedTheory.Audit.KFCausalRegularizedClosedForm
