/- Construct and close the homogeneous Fourier-space form factor
B psi(k)=exp(pi*hbar*k) Fourier(c^(-1/2) psi)(k).
The domain and separating adjoint tests are explicit. This is not yet
a self-adjoint Hamiltonian or a dynamical/continuum limit. -/
import UnifiedTheory.Audit.KFCausalRegularizedAdjointTests
import UnifiedTheory.Audit.KFCausalSeparatedGraphClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
open UnifiedTheory.Audit.KFCausalRegularizedTrialBounds
open UnifiedTheory.Audit.KFCausalRegularizedFormDomain
open UnifiedTheory.Audit.KFCausalRegularizedAdjointTests
open UnifiedTheory.Audit.KFCausalSeparatedGraphClosure

abbrev Hilbert := Lp ℂ 2 (volume : Measure ℝ)

theorem momentumOutput_square (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f : ℝ → ℂ) (k : ℝ) :
    ‖momentumOutput ε hε hbar f k‖^2=
      Real.exp (2*Real.pi*hbar*k)*‖(𝓕 (inverseHalfApply ε hε f)) k‖^2 := by
  simp only [momentumOutput,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),mul_pow,← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem momentumOutput_memLp (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : functionCore ε hε hbar) : MemLp (momentumOutput ε hε hbar f) 2 := by
  have hf := f.property
  have hc : Continuous (momentumOutput ε hε hbar f) := by
    have hF := fourier_continuous_integrable _ hf.2.2.2.1
    unfold momentumOutput
    fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  simpa only [momentumOutput_square] using hf.2.2.2.2

def coreToMomentum (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    functionCore ε hε hbar →ₗ[ℂ] Hilbert where
  toFun f := (momentumOutput_memLp ε hε hbar f).toLp (momentumOutput ε hε hbar f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(momentumOutput_memLp ε hε hbar (f+g)).coeFn_toLp,
      Lp.coeFn_add ((momentumOutput_memLp ε hε hbar f).toLp _)
        ((momentumOutput_memLp ε hε hbar g).toLp _),
      (momentumOutput_memLp ε hε hbar f).coeFn_toLp,
      (momentumOutput_memLp ε hε hbar g).coeFn_toLp] with k hfg hadd hf hg
    rw [hfg,hadd]
    dsimp only [Pi.add_apply]
    rw [hf,hg]
    change momentumOutput ε hε hbar ((f : ℝ → ℂ)+(g : ℝ → ℂ)) k=_
    simp only [momentumOutput,inverseHalf_add,
      fourier_add_integrable _ _ f.property.2.2.2.1 g.property.2.2.2.1,Pi.add_apply,mul_add]
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [(momentumOutput_memLp ε hε hbar (a • f)).coeFn_toLp,
      Lp.coeFn_smul a ((momentumOutput_memLp ε hε hbar f).toLp _),
      (momentumOutput_memLp ε hε hbar f).coeFn_toLp] with k haf hsm hf
    simp only [RingHom.id_apply]
    rw [haf,hsm]
    dsimp only [Pi.smul_apply]
    rw [hf]
    change momentumOutput ε hε hbar (fun q => a*(f : ℝ → ℂ) q) k=a*momentumOutput ε hε hbar f k
    simp only [momentumOutput,inverseHalf_const_mul,fourier_const_mul]
    ring

def inputPairVector (ε : ℝ) (hε : 0 < ε) (p : ℝ) : Hilbert :=
  star ((inputTest_memLp ε hε p).toLp (inputTest ε hε p))
def outputPairVector (hbar p : ℝ) : Hilbert :=
  star ((outputTest_memLp hbar p).toLp (outputTest hbar p))

theorem inner_star_toLp (g : ℝ → ℂ) (hg : MemLp g 2) (f : Hilbert) :
    inner ℂ (star (hg.toLp g)) f=∫ q, g q*f q := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (hg.toLp g),hg.coeFn_toLp] with q hs hgq
  rw [hs]
  dsimp only [Pi.star_apply]
  rw [hgq,RCLike.inner_apply']
  simp

theorem pair_vectors_separate (hbar : ℝ) (f : Hilbert)
    (hf : ∀ p, inner ℂ (outputPairVector hbar p) f=0) : f=0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply output_tests_separate hbar f (Lp.memLp f)
  intro p
  simpa only [outputPairVector,inner_star_toLp] using hf p

theorem hilbert_momentum_pairing (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : functionCore ε hε hbar) (p : ℝ) :
    inner ℂ (outputPairVector hbar p) (coreToMomentum ε hε hbar f)=
      inner ℂ (inputPairVector ε hε p) (coreToHilbert ε hε hbar f) := by
  rw [outputPairVector,inputPairVector,inner_star_toLp,inner_star_toLp]
  have ho : (∫ k, outputTest hbar p k*(coreToMomentum ε hε hbar f) k)=
      ∫ k, outputTest hbar p k*momentumOutput ε hε hbar f k := by
    apply integral_congr_ae
    filter_upwards [(momentumOutput_memLp ε hε hbar f).coeFn_toLp] with k hk
    exact congrArg (fun z => outputTest hbar p k*z) hk
  have hi : (∫ q, inputTest ε hε p q*(coreToHilbert ε hε hbar f) q)=
      ∫ q, inputTest ε hε p q*(f : ℝ → ℂ) q := by
    apply integral_congr_ae
    filter_upwards [(functionCore_memLp ε hε hbar f).coeFn_toLp] with q hq
    exact congrArg (fun z => inputTest ε hε p q*z) hq
  rw [ho,hi]
  exact momentum_pairing ε hε hbar p f f.property.2.2.2.1

def momentumInitial (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  initialOperator (coreToHilbert ε hε hbar) (coreToMomentum ε hε hbar)
def momentumClosed (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  closedOperator (coreToHilbert ε hε hbar) (coreToMomentum ε hε hbar)

theorem momentum_initial_graph (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    (momentumInitial ε hε hbar).graph=graphRange (coreToHilbert ε hε hbar) (coreToMomentum ε hε hbar) :=
  initialOperator_graph _ _ (inputPairVector ε hε) (outputPairVector hbar)
    (pair_vectors_separate hbar) (hilbert_momentum_pairing ε hε hbar)

theorem momentum_closed_graph (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    (momentumClosed ε hε hbar).graph=
      (graphRange (coreToHilbert ε hε hbar) (coreToMomentum ε hε hbar)).topologicalClosure :=
  closedOperator_graph _ _ (inputPairVector ε hε) (outputPairVector hbar)
    (pair_vectors_separate hbar) (hilbert_momentum_pairing ε hε hbar)

theorem momentum_isClosable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    (momentumInitial ε hε hbar).IsClosable :=
  operator_closable _ _ (inputPairVector ε hε) (outputPairVector hbar)
    (pair_vectors_separate hbar) (hilbert_momentum_pairing ε hε hbar)

theorem momentum_isClosed (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    (momentumClosed ε hε hbar).IsClosed :=
  operator_closed _ _ (inputPairVector ε hε) (outputPairVector hbar)
    (pair_vectors_separate hbar) (hilbert_momentum_pairing ε hε hbar)

theorem momentum_initial_domain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    (momentumInitial ε hε hbar).domain=formDomain ε hε hbar := by
  change (graphRange (coreToHilbert ε hε hbar) (coreToMomentum ε hε hbar)).toLinearPMap.domain=_
  rw [Submodule.toLinearPMap_domain]
  ext x
  constructor
  · rintro ⟨z,⟨f,rfl⟩,rfl⟩
    exact ⟨f,rfl⟩
  · rintro ⟨f,rfl⟩
    exact ⟨(coreToHilbert ε hε hbar f,coreToMomentum ε hε hbar f),⟨f,rfl⟩,rfl⟩

theorem momentum_closed_extends (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    momentumInitial ε hε hbar ≤ momentumClosed ε hε hbar := by
  apply LinearPMap.le_of_le_graph
  rw [momentum_initial_graph,momentum_closed_graph]
  exact (graphRange (coreToHilbert ε hε hbar) (coreToMomentum ε hε hbar)).le_topologicalClosure

theorem momentum_closed_dense (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    Dense ((momentumClosed ε hε hbar).domain : Set Hilbert) := by
  have hd : Dense ((momentumInitial ε hε hbar).domain : Set Hilbert) := by
    rw [momentum_initial_domain,Submodule.dense_iff_topologicalClosure_eq_top]
    exact dense_form_domain ε hε hbar
  exact hd.mono (momentum_closed_extends ε hε hbar).1

/-- The resulting closed, densely defined operator really extends the
specified Fourier-space form factor on every vector of the explicit core. -/
theorem exists_closed_momentum (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    ∃ B : Hilbert →ₗ.[ℂ] Hilbert, B.IsClosed ∧ Dense (B.domain : Set Hilbert) ∧
      ∀ f : functionCore ε hε hbar,
        (coreToHilbert ε hε hbar f,coreToMomentum ε hε hbar f) ∈ B.graph := by
  refine ⟨momentumClosed ε hε hbar,momentum_isClosed ε hε hbar,
    momentum_closed_dense ε hε hbar,?_⟩
  intro f
  rw [momentum_closed_graph]
  apply Submodule.le_topologicalClosure
  exact ⟨f,rfl⟩

#print axioms momentumOutput_memLp
#print axioms hilbert_momentum_pairing
#print axioms momentum_initial_graph
#print axioms momentum_isClosable
#print axioms momentum_isClosed
#print axioms momentum_initial_domain
#print axioms momentum_closed_dense
#print axioms exists_closed_momentum

end
end UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
