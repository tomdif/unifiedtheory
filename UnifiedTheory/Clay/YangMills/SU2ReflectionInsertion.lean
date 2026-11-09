/- A marked normalized SU(2) crossing can be restored at the cost of its
exact Haar mass, even with arbitrary other positive crossing interactions
and a continuous complex half-source. This proves a polynomial removal cost
for the explicitly constructed reflection form. Identifying a spatial cut
of the modified Wilson ground state with this form is still required. -/
import UnifiedTheory.Clay.YangMills.PositiveKernelInsertion
import UnifiedTheory.Clay.YangMills.SU2CrossingHaarFloor
import UnifiedTheory.Clay.YangMills.WilsonReflectionForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2ReflectionInsertion
noncomputable section
open MeasureTheory PositiveKernelForm PositiveKernelInsertion WilsonSlabOperator
open SU2CrossingHaarFloor WilsonReflectionForm

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

theorem insertion_lower (B : PositiveKernel X) (hB : Continuous B.value)
    (h : X → Q) (hh : Continuous h) (β : ℝ) (hβ : 0 ≤ β)
    (f : X → ℂ) (hf : Continuous f) :
    SU2GaussianMass.mass β * (form μ B f).re ≤
      (form μ (product B (pullback (positiveKernel β hβ) h)) f).re := by
  apply PositiveKernelInsertion.insertion_lower μ B
    (pullback (positiveKernel β hβ) h) (pullback (remainder β hβ) h) hB
      ((positiveKernel_continuous β hβ).comp
        ((hh.comp continuous_fst).prodMk (hh.comp continuous_snd)))
      ((remainder_continuous β hβ).comp
        ((hh.comp continuous_fst).prodMk (hh.comp continuous_snd)))
      _ _ f hf
  intro x y
  exact (remainder_value β hβ (h x) (h y)).trans (Complex.ofReal_sub _ _)

theorem polynomial_removal (B : PositiveKernel X) (hB : Continuous B.value)
    (h : X → Q) (hh : Continuous h) (β : ℝ) (hβ : 3 / 4 ≤ β)
    (f : X → ℂ) (hf : Continuous f) :
    (form μ B f).re ≤ SU2GaussianMass.cap β *
      (form μ (product B (pullback (positiveKernel β (by linarith)) h)) f).re := by
  have hm := SU2GaussianMass.mass_cap_lower β hβ
  have hn := (form_nonneg μ B hB f hf).1
  have hc := SU2GaussianMass.cap_nonneg β (by linarith)
  have hi := insertion_lower μ B hB h hh β (by linarith) f hf
  calc
    _ ≤ (SU2GaussianMass.mass β * SU2GaussianMass.cap β) * (form μ B f).re := by
      nlinarith
    _ = SU2GaussianMass.cap β * (SU2GaussianMass.mass β * (form μ B f).re) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi hc

variable {P : Type*} [Fintype P]

def crossingProduct (β : P → ℝ) (hβ : ∀ p, 0 ≤ β p) (h : P → X → Q) : PositiveKernel X :=
  finiteProduct (fun p => pullback (positiveKernel (β p) (hβ p)) (h p))

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] in
theorem crossingProduct_value (β : P → ℝ) (hβ : ∀ p, 0 ≤ β p)
    (h : P → X → Q) (x y : X) :
    (crossingProduct β hβ h).value (x, y) =
      ((∏ p, kernel (β p) (h p x) (h p y) : ℝ) : ℂ) := by
  rw [crossingProduct, finiteProduct_value, Complex.ofReal_prod]
  rfl

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem crossingProduct_continuous (β : P → ℝ) (hβ : ∀ p, 0 ≤ β p)
    (h : P → X → Q) (hh : ∀ p, Continuous (h p)) :
    Continuous (crossingProduct β hβ h).value := by
  have hreal : Continuous (fun z : X × X =>
      ∏ p, kernel (β p) (h p z.1) (h p z.2)) :=
    continuous_finset_prod Finset.univ (fun p _ =>
      (SU2CrossingHaarFloor.kernel_continuous (β p)).comp
      (f := fun z : X × X => (h p z.1, h p z.2))
      (((hh p).comp continuous_fst).prodMk ((hh p).comp continuous_snd)))
  have hc : Continuous (fun z : X × X =>
      ((∏ p, kernel (β p) (h p z.1) (h p z.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hreal
  exact hc.congr (fun z => (crossingProduct_value β hβ h z.1 z.2).symm)

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [BorelSpace X] [IsFiniteMeasure μ] in
theorem crossing_form (β : P → ℝ) (hβ : ∀ p, 0 ≤ β p)
    (h : P → X → Q) (f : X → ℂ) :
    form μ (crossingProduct β hβ h) f =
      reflectionForm μ (fun x y => ∏ p, kernel (β p) (h p x) (h p y)) f := by
  unfold form reflectionForm
  simp only [crossingProduct_value]

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [BorelSpace X] [IsFiniteMeasure μ] in
theorem marked_form (β : P → ℝ) (hβ : ∀ p, 0 ≤ β p)
    (h : P → X → Q) (q : X → Q) (b : ℝ) (hb : 0 ≤ b) (f : X → ℂ) :
    form μ (product (crossingProduct β hβ h) (pullback (positiveKernel b hb) q)) f =
      reflectionForm μ (fun x y => (∏ p, kernel (β p) (h p x) (h p y)) *
        kernel b (q x) (q y)) f := by
  unfold form reflectionForm
  simp only [product_value, crossingProduct_value, pullback, positiveKernel,
    Complex.ofReal_mul]

/-- The number and coupling strengths of the other crossings do not enter
the removal price. The half-source may be any continuous complex function. -/
theorem crossing_polynomial_removal (β : P → ℝ) (hβ : ∀ p, 0 ≤ β p)
    (h : P → X → Q) (hh : ∀ p, Continuous (h p))
    (q : X → Q) (hq : Continuous q) (b : ℝ) (hb : 3 / 4 ≤ b)
    (f : X → ℂ) (hf : Continuous f) :
    (reflectionForm μ (fun x y => ∏ p, kernel (β p) (h p x) (h p y)) f).re ≤
      SU2GaussianMass.cap b * (reflectionForm μ (fun x y =>
        (∏ p, kernel (β p) (h p x) (h p y)) * kernel b (q x) (q y)) f).re := by
  have hi := polynomial_removal μ (crossingProduct β hβ h)
    (crossingProduct_continuous β hβ h hh) q hq b hb f hf
  rwa [crossing_form, marked_form] at hi

end
end UnifiedTheory.Clay.YangMills.SU2ReflectionInsertion
