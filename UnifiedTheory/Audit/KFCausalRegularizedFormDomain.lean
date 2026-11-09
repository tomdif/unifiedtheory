/- A densely defined linear form domain for the homogeneous regularized
candidate. The Fourier integrals are used only on L1 dressed vectors.
This file proves density, not closedness or existence of a Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
import UnifiedTheory.Audit.KFCausalRegularizedTrialBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedFormDomain
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedTrialBounds

theorem norm_add_square_bound (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have h := (sq_le_sq₀ (norm_nonneg (a+b)) (add_nonneg (norm_nonneg a) (norm_nonneg b))).mpr
    (norm_add_le a b)
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

theorem integrable_weighted_square_add (w : ℝ → ℝ) (hw : Measurable w)
    (hpos : ∀ q, 0 ≤ w q) (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable (fun q => w q*‖f q‖^2))
    (hgi : Integrable (fun q => w q*‖g q‖^2)) :
    Integrable (fun q => w q*‖f q+g q‖^2) := by
  apply ((hfi.add hgi).const_mul 2).mono' ((hw.mul ((hf.add hg).norm.pow_const 2)).aestronglyMeasurable)
  filter_upwards [] with q
  simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hpos q) (sq_nonneg _))]
  dsimp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left (norm_add_square_bound (f q) (g q)) (hpos q)]

theorem fourier_add_integrable (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    𝓕 (f+g)=𝓕 f+𝓕 g := by
  exact VectorFourier.fourierIntegral_add (L := (innerₗ ℝ))
    Real.continuous_fourierChar (by fun_prop) hf hg

theorem fourier_continuous_integrable (f : ℝ → ℂ) (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ)
    Real.continuous_fourierChar (by fun_prop) hf

theorem inverseHalf_add (ε : ℝ) (hε : 0 < ε) (f g : ℝ → ℂ) :
    inverseHalfApply ε hε (f+g)=inverseHalfApply ε hε f+inverseHalfApply ε hε g := by
  funext q
  simp [inverseHalfApply,add_div]

theorem formCore_add (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f g : ℝ → ℂ)
    (hf : FormCore ε hε hbar f) (hg : FormCore ε hε hbar g) : FormCore ε hε hbar (f+g) := by
  rcases hf with ⟨hfm,hfn,hfc,hfi,hfp⟩
  rcases hg with ⟨hgm,hgn,hgc,hgi,hgp⟩
  refine ⟨hfm.add hgm,?_,?_,?_,?_⟩
  · simpa only [one_mul] using integrable_weighted_square_add (fun _ => 1)
      measurable_const (fun _ => by norm_num) f g hfm hgm
      (by simpa using hfn) (by simpa using hgn)
  · exact integrable_weighted_square_add (clockQ ε hε) (clockQ_continuous ε hε).measurable
      (fun q => (clockQ_positive ε hε q).le) f g hfm hgm hfc hgc
  · rw [inverseHalf_add]
    exact hfi.add hgi
  · rw [inverseHalf_add,fourier_add_integrable _ _ hfi hgi]
    exact integrable_weighted_square_add (fun k => Real.exp (2*Real.pi*hbar*k)) (by fun_prop)
      (fun _ => (Real.exp_pos _).le) _ _
      (fourier_continuous_integrable _ hfi).measurable
      (fourier_continuous_integrable _ hgi).measurable hfp hgp

def functionCore (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | FormCore ε hε hbar f}
  zero_mem' := by
    simpa using formCore_const_mul ε hε hbar _ (trial_mem_formCore ε hε hbar) 0
  add_mem' := formCore_add ε hε hbar _ _
  smul_mem' a f hf := formCore_const_mul ε hε hbar f hf a

theorem functionCore_memLp (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : functionCore ε hε hbar) : MemLp (f : ℝ → ℂ) 2 :=
  (memLp_two_iff_integrable_sq_norm f.property.1.aestronglyMeasurable).mpr f.property.2.1

def coreToHilbert (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    functionCore ε hε hbar →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f := (functionCore_memLp ε hε hbar f).toLp f
  map_add' f g := MemLp.toLp_add (functionCore_memLp ε hε hbar f) (functionCore_memLp ε hε hbar g)
  map_smul' a f := MemLp.toLp_const_smul a (functionCore_memLp ε hε hbar f)

def formDomain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  (coreToHilbert ε hε hbar).range

/-- The explicitly constructed finite-energy domain is dense for every
positive regulator and every real hbar. No density hypothesis is supplied. -/
theorem dense_form_domain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    (formDomain ε hε hbar).topologicalClosure=⊤ := by
  have hs : Submodule.span ℂ (Set.range (modulatedTrialLp ε hε)) ≤ formDomain ε hε hbar := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    exact ⟨⟨modulate p (trial ε hε),modulatedTrial_mem_formCore ε hε hbar p⟩,rfl⟩
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_modulated_span ε hε] at hc
  exact top_le_iff.mp hc

#print axioms integrable_weighted_square_add
#print axioms formCore_add
#print axioms functionCore_memLp
#print axioms dense_form_domain

end
end UnifiedTheory.Audit.KFCausalRegularizedFormDomain
