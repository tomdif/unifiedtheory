/- Actual local two-point contact distributions and their derivatives.
Every finite contact jet vanishes on strictly separated reflected tests,
including the moving lattice reflection once its offset is small enough.
No counterterm coefficient, moment bound, or physical field identification
is inferred, and this does not assert full all-order reflection positivity. -/
import UnifiedTheory.Clay.YangMills.WilsonReflectedTensor
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.DiagonalContactTerms
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4
open SchwartzConfigurationTensor WilsonReflectedTensor CellReflectionCovariance
open SchwartzConfigurationConjugation AffineCellReflection
open scoped Topology NNReal

def doubleMap : Configuration 1 →L[ℝ] Configuration 1 × Configuration 1 :=
  (ContinuousLinearMap.id ℝ (Configuration 1)).prod (ContinuousLinearMap.id ℝ (Configuration 1))

theorem doubleMap_isometry : Isometry doubleMap := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (x,x) (y,y) = dist x y
  rw [Prod.dist_eq, max_self]

def diagonal (x : Configuration 1) : Configuration 2 := concat 1 1 (x,x)

def diagonalPullback : CorrelationTest 2 →L[ℂ] CorrelationTest 1 :=
  (SchwartzMap.compCLMOfAntilipschitz ℂ doubleMap.hasTemperateGrowth
    doubleMap_isometry.antilipschitz).comp
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (concat 1 1))

@[simp] theorem diagonalPullback_apply (f : CorrelationTest 2) (x : Configuration 1) :
    diagonalPullback f x = f (diagonal x) := rfl

def contact : CorrelationTest 2 →L[ℂ] ℂ :=
  (SchwartzMap.integralCLM ℂ (volume : Measure (Configuration 1))).comp diagonalPullback

@[simp] theorem contact_apply (f : CorrelationTest 2) :
    contact f = ∫ x, f (diagonal x) := rfl

/-- The sign is the distributional derivative convention. Directions need
not be normal to the diagonal; arbitrary finite jets are allowed. -/
def contactJet (n : ℕ) (v : Fin n → Configuration 2) : CorrelationTest 2 →L[ℂ] ℂ :=
  ((-1 : ℂ)^n) • contact.comp (LineDeriv.iteratedLineDerivOpCLM ℂ (CorrelationTest 2) v)

theorem contactJet_zero_of_disjoint (n : ℕ) (v : Fin n → Configuration 2)
    (f : CorrelationTest 2) (hf : ∀ x, diagonal x ∉ tsupport f) : contactJet n v f = 0 := by
  have hd (x : Configuration 1) :
      (LineDeriv.iteratedLineDerivOpCLM ℂ (CorrelationTest 2) v f) (diagonal x) = 0 := by
    by_contra hx
    exact hf x ((SchwartzMap.tsupport_iteratedLineDerivOp_subset v f) (subset_tsupport _ hx))
  simp only [contactJet, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    contact_apply, hd, integral_zero, smul_zero]

def SupportedAfter (tau : ℝ) (f : CorrelationTest 1) : Prop :=
  ∀ x, f x ≠ 0 → tau ≤ x (0,0)

def timeGap (x : Configuration 2) : ℝ :=
  (split 1 1 x).2 (0,0) - (split 1 1 x).1 (0,0)

theorem timeGap_continuous : Continuous timeGap :=
  ((PiLp.continuous_apply 2 _ (0,0)).comp ((split 1 1).continuous.snd)).sub
    ((PiLp.continuous_apply 2 _ (0,0)).comp ((split 1 1).continuous.fst))

@[simp] theorem timeGap_diagonal (x : Configuration 1) : timeGap (diagonal x) = 0 := by
  unfold timeGap diagonal
  rw [split_concat]
  exact sub_self _

theorem reflected_support_gap (tau a : ℝ) (plane : Plane) (f g : CorrelationTest 1)
    (hf : SupportedAfter tau f) (hg : SupportedAfter tau g) :
    tsupport (reflectedTensor 1 1 a plane f g) ⊆
      {x | 2 * tau-cellOffset a plane ≤ timeGap x} := by
  apply closure_minimal _ (isClosed_le continuous_const timeGap_continuous)
  intro x hx
  have hm : star (f (reflectPoints 1 a plane (split 1 1 x).1)) * g (split 1 1 x).2 ≠ 0 := by
    simpa only [Function.mem_support, reflectedTensor, tensor_apply, conjugation_apply,
      reflectionPullback_apply] using hx
  have hf' := hf (reflectPoints 1 a plane (split 1 1 x).1) (by
    intro h
    apply hm
    simp only [h, star_zero, zero_mul])
  have hg' := hg _ (right_ne_zero_of_mul hm)
  change tau ≤ cellOffset a plane - (split 1 1 x).1 (0,0) at hf'
  change 2 * tau-cellOffset a plane ≤ timeGap x
  unfold timeGap
  linarith

theorem reflected_diagonal_disjoint (tau a : ℝ) (plane : Plane)
    (f g : CorrelationTest 1) (hf : SupportedAfter tau f) (hg : SupportedAfter tau g)
    (hgap : cellOffset a plane < 2 * tau) :
    ∀ x, diagonal x ∉ tsupport (reflectedTensor 1 1 a plane f g) := by
  intro x hx
  have h := reflected_support_gap tau a plane f g hf hg hx
  change 2 * tau-cellOffset a plane ≤ timeGap (diagonal x) at h
  rw [timeGap_diagonal] at h
  linarith

/-- Derivatives of delta, of every finite order, are invisible to the
strictly separated reflected two-point pairing. -/
theorem contactJet_reflected_zero (n : ℕ) (v : Fin n → Configuration 2)
    (tau a : ℝ) (plane : Plane) (f g : CorrelationTest 1)
    (hf : SupportedAfter tau f) (hg : SupportedAfter tau g)
    (hgap : cellOffset a plane < 2 * tau) :
    contactJet n v (reflectedTensor 1 1 a plane f g) = 0 :=
  contactJet_zero_of_disjoint n v _
    (reflected_diagonal_disjoint tau a plane f g hf hg hgap)

def finiteContact {ι : Type*} [Fintype ι] (order : ι → ℕ)
    (v : (i : ι) → Fin (order i) → Configuration 2) (c : ι → ℂ) :
    CorrelationTest 2 →L[ℂ] ℂ := ∑ i, c i • contactJet (order i) (v i)

theorem finiteContact_reflected_zero {ι : Type*} [Fintype ι] (order : ι → ℕ)
    (v : (i : ι) → Fin (order i) → Configuration 2) (c : ι → ℂ)
    (tau a : ℝ) (plane : Plane) (f g : CorrelationTest 1)
    (hf : SupportedAfter tau f) (hg : SupportedAfter tau g)
    (hgap : cellOffset a plane < 2 * tau) :
    finiteContact order v c (reflectedTensor 1 1 a plane f g) = 0 := by
  simp only [finiteContact, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    contactJet_reflected_zero _ _ tau a plane f g hf hg hgap, smul_zero, Finset.sum_const_zero]

theorem subtraction_preserves_reflected {ι : Type*} [Fintype ι] (order : ι → ℕ)
    (v : (i : ι) → Fin (order i) → Configuration 2) (c : ι → ℂ)
    (F : CorrelationTest 2 →L[ℂ] ℂ) (tau a : ℝ) (plane : Plane) (f g : CorrelationTest 1)
    (hf : SupportedAfter tau f) (hg : SupportedAfter tau g)
    (hgap : cellOffset a plane < 2 * tau) :
    (F-finiteContact order v c) (reflectedTensor 1 1 a plane f g) =
      F (reflectedTensor 1 1 a plane f g) := by
  rw [ContinuousLinearMap.sub_apply,
    finiteContact_reflected_zero order v c tau a plane f g hf hg hgap, sub_zero]

/-- At zero reflection offset, every strictly positive separation is enough. -/
theorem zero_offset_contactJet (n : ℕ) (v : Fin n → Configuration 2)
    (tau : ℝ) (htau : 0 < tau) (plane : Plane) (f g : CorrelationTest 1)
    (hf : SupportedAfter tau f) (hg : SupportedAfter tau g) :
    contactJet n v (reflectedTensor 1 1 0 plane f g) = 0 := by
  apply contactJet_reflected_zero n v tau 0 plane f g hf hg
  simp only [cellOffset, ite_self]
  linarith

/-- The cutoff may change every coefficient, direction and derivative order.
Only the fixed physical separation controls eventual invisibility. -/
theorem eventually_all_contacts_zero {κ : Type*} {l : Filter κ}
    (a : κ → ℝ) (ha : Tendsto a l (𝓝 0)) (tau : ℝ) (htau : 0 < tau)
    (plane : Plane) (f g : CorrelationTest 1)
    (hf : SupportedAfter tau f) (hg : SupportedAfter tau g) :
    ∀ᶠ k in l, ∀ (n : ℕ) (v : Fin n → Configuration 2),
      contactJet n v (reflectedTensor 1 1 (a k) plane f g) = 0 := by
  have hoff : Tendsto (fun k => cellOffset (a k) plane) l (𝓝 0) := by
    by_cases h : plane.1.1 = 0
    · simpa only [cellOffset, h, if_true] using (tendsto_const_nhds (x := (0 : ℝ)) (f := l))
    · simpa only [cellOffset, h, if_false] using ha
  filter_upwards [hoff.eventually (gt_mem_nhds (by linarith : 0 < 2 * tau))] with k hk n v
  exact contactJet_reflected_zero n v tau (a k) plane f g hf hg hk

theorem cutoff_dependent_subtraction {κ ι : Type*} {l : Filter κ} [Fintype ι]
    (a : κ → ℝ) (ha : Tendsto a l (𝓝 0)) (tau : ℝ) (htau : 0 < tau)
    (plane : Plane) (f g : CorrelationTest 1)
    (hf : SupportedAfter tau f) (hg : SupportedAfter tau g)
    (order : κ → ι → ℕ) (v : (k : κ) → (i : ι) → Fin (order k i) → Configuration 2)
    (c : κ → ι → ℂ) (F : κ → CorrelationTest 2 →L[ℂ] ℂ) :
    ∀ᶠ k in l, (F k - finiteContact (order k) (v k) (c k))
      (reflectedTensor 1 1 (a k) plane f g) = F k (reflectedTensor 1 1 (a k) plane f g) := by
  filter_upwards [eventually_all_contacts_zero a ha tau htau plane f g hf hg] with k hk
  simp only [ContinuousLinearMap.sub_apply, finiteContact, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, hk, smul_zero, Finset.sum_const_zero, sub_zero]

end
end UnifiedTheory.Clay.YangMills.DiagonalContactTerms
