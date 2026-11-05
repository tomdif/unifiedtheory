/- Iterated exact Haar-floor insertion through an arbitrary positive kernel.
The cost is the product of the true one-factor masses. The background and
source remain unchanged while the finitely many crossing factors are restored. -/
import UnifiedTheory.Clay.YangMills.SU2ReflectionInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SU2FiniteInsertion
noncomputable section
open MeasureTheory PositiveKernelForm PositiveKernelInsertion WilsonSlabOperator
open SU2CrossingHaarFloor

variable {X : Type*}

def augment (s : ℝ) (hs : 0 ≤ s) (B : PositiveKernel X) : List (X → Q) → PositiveKernel X
  | [] => B
  | h :: ts => augment s hs (product B (pullback (positiveKernel s hs) h)) ts

theorem augment_value (s : ℝ) (hs : 0 ≤ s) (B : PositiveKernel X)
    (ts : List (X → Q)) (a b : X) :
    (augment s hs B ts).value (a,b) =
      B.value (a,b) * ((ts.map (fun h => kernel s (h a) (h b))).prod : ℝ) := by
  induction ts generalizing B with
  | nil => simp [augment]
  | cons h ts ih =>
    simp only [augment, ih, product_value, pullback, positiveKernel, List.map_cons,
      List.prod_cons, Complex.ofReal_mul]
    ring

variable [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem product_continuous (s : ℝ) (hs : 0 ≤ s) (B : PositiveKernel X)
    (hB : Continuous B.value) (h : X → Q) (hh : Continuous h) :
    Continuous (product B (pullback (positiveKernel s hs) h)).value := by
  have hc := hB.mul ((positiveKernel_continuous s hs).comp
    (f := fun z : X × X => (h z.1,h z.2))
    ((hh.comp continuous_fst).prodMk (hh.comp continuous_snd)))
  exact hc.congr (fun z => (product_value B (pullback (positiveKernel s hs) h) z.1 z.2).symm)

theorem list_floor (s : ℝ) (hs : 0 ≤ s) (B : PositiveKernel X) (hB : Continuous B.value)
    (ts : List (X → Q)) (hts : ∀ h ∈ ts, Continuous h) (f : X → ℂ) (hf : Continuous f) :
    (SU2GaussianMass.mass s)^ts.length * (form μ B f).re ≤
      (form μ (augment s hs B ts) f).re := by
  induction ts generalizing B with
  | nil => simp [augment]
  | cons h ts ih =>
    have hh := hts h List.mem_cons_self
    have hi := SU2ReflectionInsertion.insertion_lower μ B hB h hh s hs f hf
    have hr := ih (product B (pullback (positiveKernel s hs) h))
      (product_continuous s hs B hB h hh) (fun k hk => hts k (List.mem_cons_of_mem h hk))
    calc
      _ = (SU2GaussianMass.mass s)^ts.length *
          (SU2GaussianMass.mass s * (form μ B f).re) := by rw [List.length_cons, pow_succ]; ring
      _ ≤ (SU2GaussianMass.mass s)^ts.length *
          (form μ (product B (pullback (positiveKernel s hs) h)) f).re :=
        mul_le_mul_of_nonneg_left hi (pow_nonneg (SU2GaussianMass.mass_pos s).le _)
      _ ≤ _ := hr

variable {P : Type*} [Fintype P]

def finiteAugment (s : ℝ) (hs : 0 ≤ s) (B : PositiveKernel X) (h : P → X → Q) :
    PositiveKernel X := augment s hs B (Finset.univ.toList.map h)

omit [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] in
theorem finiteAugment_value (s : ℝ) (hs : 0 ≤ s) (B : PositiveKernel X)
    (h : P → X → Q) (a b : X) :
    (finiteAugment s hs B h).value (a,b) =
      B.value (a,b) * (∏ p, kernel s (h p a) (h p b) : ℝ) := by
  rw [finiteAugment, augment_value, List.map_map, Finset.prod_map_toList]
  rfl

theorem finite_floor (s : ℝ) (hs : 0 ≤ s) (B : PositiveKernel X) (hB : Continuous B.value)
    (h : P → X → Q) (hh : ∀ p, Continuous (h p)) (f : X → ℂ) (hf : Continuous f) :
    (SU2GaussianMass.mass s)^(Fintype.card P) * (form μ B f).re ≤
      (form μ (finiteAugment s hs B h) f).re := by
  have hi := list_floor μ s hs B hB (Finset.univ.toList.map h)
    (by intro k hk; obtain ⟨p,_,rfl⟩ := List.mem_map.mp hk; exact hh p) f hf
  simpa only [List.length_map, Finset.length_toList, Finset.card_univ, finiteAugment] using hi

theorem finite_removal (s : ℝ) (hs : 3 / 4 ≤ s) (B : PositiveKernel X)
    (hB : Continuous B.value) (h : P → X → Q) (hh : ∀ p, Continuous (h p))
    (f : X → ℂ) (hf : Continuous f) :
    (form μ B f).re ≤ (SU2GaussianMass.cap s)^(Fintype.card P) *
      (form μ (finiteAugment s (by linarith) B h) f).re := by
  have hi := finite_floor μ s (by linarith) B hB h hh f hf
  have hn := (form_nonneg μ B hB f hf).1
  have hc := SU2GaussianMass.cap_nonneg s (by linarith)
  have hp : 1 ≤ (SU2GaussianMass.mass s * SU2GaussianMass.cap s)^(Fintype.card P) :=
    one_le_pow₀ (SU2GaussianMass.mass_cap_lower s hs)
  calc
    _ ≤ (SU2GaussianMass.mass s * SU2GaussianMass.cap s)^(Fintype.card P) *
        (form μ B f).re := by nlinarith
    _ = (SU2GaussianMass.cap s)^(Fintype.card P) *
        ((SU2GaussianMass.mass s)^(Fintype.card P) * (form μ B f).re) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi (pow_nonneg hc _)

end
end UnifiedTheory.Clay.YangMills.SU2FiniteInsertion
