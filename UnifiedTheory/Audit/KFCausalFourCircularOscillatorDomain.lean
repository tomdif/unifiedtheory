/- The sum of the two actual planar polynomial oscillators, embedded into
four-dimensional L2, and its entire graph closure in the circular basis. -/
import UnifiedTheory.Audit.KFCausalCircularOscillatorDomain
import UnifiedTheory.Audit.KFCausalCircularZeroLevelCounting
import UnifiedTheory.Audit.KFCausalPlaneOscillatorFunctions
import UnifiedTheory.Audit.KFCausalIsometricOperatorCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Tensor and polynomial-range coercions require additional elaboration steps.
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFourCircularOscillatorDomain
noncomputable section
open MeasureTheory TensorProduct
open KFCausalEuclideanProductCoordinates (BlockHilbert)
open KFCausalHermiteProductBasis (Index joinCoordinates)
open KFCausalCircularOscillatorBasis
open KFCausalCircularOscillatorTriangular (energy)
open KFCausalL2TensorEmbedding (productState)

variable (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b)
local notation "D" => Domain c hc b hb
local notation "T" => operator c hc b hb
local notation "B" => KFCausalFourCircularChargeBasis.basis c hc b hb

def embedding : (D ⊗[ℂ] D) →ₗᵢ[ℂ] BlockHilbert 4 :=
  (joinCoordinates 2 2).toLinearIsometry.comp
    ((KFCausalL2TensorEmbedding.tensorEmbedding volume volume).comp
      (TensorProduct.mapIsometry (D).subtypeₗᵢ (D).subtypeₗᵢ))

theorem embedding_tmul (u v : D) : embedding c hc b hb (u ⊗ₜ[ℂ] v) =
    joinCoordinates 2 2 (productState volume volume u.val v.val) := rfl

def tensorOperator : (D ⊗[ℂ] D) →ₗ[ℂ] (D ⊗[ℂ] D) :=
  TensorProduct.map (T) LinearMap.id + TensorProduct.map LinearMap.id (T)

theorem tensorOperator_tmul (u v : D) :
    tensorOperator c hc b hb (u ⊗ₜ[ℂ] v) = (T u) ⊗ₜ[ℂ] v + u ⊗ₜ[ℂ] (T v) := rfl

theorem tensor_symmetric (u v : D ⊗[ℂ] D) :
    inner ℂ (tensorOperator c hc b hb u) v = inner ℂ u (tensorOperator c hc b hb v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u u' hu hu' => simp only [map_add, inner_add_left, hu, hu']
  | tmul u u' =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v v' hv hv' => simp only [map_add, inner_add_right, hv, hv']
    | tmul v v' =>
      simp only [tensorOperator_tmul, inner_add_left, inner_add_right,
        TensorProduct.inner_tmul, operator_symmetric]

def core : BlockHilbert 4 →ₗ.[ℂ] BlockHilbert 4 :=
  KFCausalIsometricOperatorCore.core (embedding c hc b hb) (tensorOperator c hc b hb)

theorem core_graph (u : D ⊗[ℂ] D) :
    (embedding c hc b hb u, embedding c hc b hb (tensorOperator c hc b hb u)) ∈
      (core c hc b hb).graph :=
  KFCausalIsometricOperatorCore.core_graph (embedding c hc b hb) (tensorOperator c hc b hb) u

theorem core_symmetric : (core c hc b hb).IsFormalAdjoint (core c hc b hb) :=
  KFCausalIsometricOperatorCore.symmetric (embedding c hc b hb) (tensorOperator c hc b hb)
    (tensor_symmetric c hc b hb)

def mode (i : ℕ × ℕ) : D := polynomialEquiv c hc b hb
  (normalizedPolynomial c hc b hb (Nat.pair i.1 i.2))

theorem mode_coe (i : ℕ × ℕ) : (mode c hc b hb i).val =
    KFCausalFourCircularChargeBasis.planeBasis c hc b hb i := by
  rw [KFCausalFourCircularChargeBasis.planeBasis_apply]
  exact normalized_state c hc b hb _

theorem mode_operator (i : ℕ × ℕ) : T (mode c hc b hb i) =
    (energy c b (Nat.pair i.1 i.2):ℂ) • mode c hc b hb i := by
  change T (polynomialEquiv c hc b hb _) = _
  rw [operator_apply, polynomial_eigenvalue, map_smul]
  rfl

def energy4 (i : Index) : ℝ :=
  energy c b (Nat.pair i.1.1 i.1.2)+energy c b (Nat.pair i.2.1 i.2.2)

theorem energy4_formula (i : Index) : energy4 c b i =
    4*b*c^2*((KFCausalCircularZeroLevelCounting.occupation i:ℝ)+2) := by
  simp [energy4, energy, KFCausalCircularPolynomialBasis.exponent, Nat.unpair_pair,
    KFCausalCircularZeroLevelCounting.occupation,
    KFCausalCircularZeroLevelCounting.positiveCount,
    KFCausalCircularZeroLevelCounting.negativeCount]
  ring

theorem basis_graph (i : Index) : (B i, (energy4 c b i:ℂ) • B i) ∈ (core c hc b hb).graph := by
  have hi : embedding c hc b hb (mode c hc b hb i.1 ⊗ₜ[ℂ] mode c hc b hb i.2) = B i := by
    rw [embedding_tmul, mode_coe, mode_coe]
    simp only [KFCausalFourCircularChargeBasis.basis, KFCausalHermiteProductBasis.mapBasis_apply,
      KFCausalProductHilbertExpansion.productBasis_apply]
  have hg := core_graph c hc b hb (mode c hc b hb i.1 ⊗ₜ[ℂ] mode c hc b hb i.2)
  rw [tensorOperator_tmul, mode_operator, mode_operator,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← add_smul, map_smul, hi] at hg
  simpa only [energy4, Complex.ofReal_add] using hg

def closedOperator : BlockHilbert 4 →ₗ.[ℂ] BlockHilbert 4 := (core c hc b hb).closure

theorem graph_iff (f g : BlockHilbert 4) :
    (f, g) ∈ (closedOperator c hc b hb).graph ↔
      ∀ i, inner ℂ (B i) g = (energy4 c b i:ℂ)*inner ℂ (B i) f :=
  KFCausalCompleteEigenbasisClosure.graph_iff (core c hc b hb) (B) (energy4 c b)
    (core_symmetric c hc b hb) (basis_graph c hc b hb) f g

theorem domain_iff_summable (f : BlockHilbert 4) :
    f ∈ (closedOperator c hc b hb).domain ↔
      Summable (fun i => (energy4 c b i)^2*‖inner ℂ (B i) f‖^2) :=
  KFCausalCompleteEigenbasisClosure.domain_iff_summable (core c hc b hb) (B) (energy4 c b)
    (core_symmetric c hc b hb) (basis_graph c hc b hb) f

theorem zero_level_energy (p : ℕ) (i : KFCausalCircularZeroLevelCounting.Level p) :
    energy4 c b i.val = 8*b*c^2*(p+1) := by
  rw [energy4_formula, KFCausalCircularZeroLevelCounting.level_occupation]
  push_cast
  ring

/-- The exact numerical scaling needed in the free energy form. This arithmetic
identity alone does not identify the full six-dimensional Hamiltonian graph. -/
theorem matched_energy_scale (h : ℝ) (hh : h ≠ 0) (t : ℝ) (i : Index) :
    energy4 (2*Real.pi*h) (Real.exp t/(2*h)) i / (8*Real.pi^2) =
      h*Real.exp t*((KFCausalCircularZeroLevelCounting.occupation i:ℝ)+2) := by
  rw [energy4_formula]
  field_simp [hh, Real.pi_ne_zero]
  <;> ring

#print axioms tensor_symmetric
#print axioms core_graph
#print axioms basis_graph
#print axioms graph_iff
#print axioms domain_iff_summable
#print axioms zero_level_energy
#print axioms matched_energy_scale
end
end UnifiedTheory.Audit.KFCausalFourCircularOscillatorDomain
