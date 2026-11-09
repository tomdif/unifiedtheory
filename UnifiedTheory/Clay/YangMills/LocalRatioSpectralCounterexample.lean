/- An explicit obstruction to deriving a volume-independent transfer gap
from pointwise positivity, positive definiteness, and local ratio bounds alone.
On N binary coordinates, two product amplitudes define an actual rank-two
symmetric positive kernel. Its positive ground and orthogonal excited vectors
have eigenvalues 1 ± (24/25)^N, while every one-coordinate kernel-row and
ground-function ratio is bounded by 4/3 uniformly in N. All real eigenvalues
are classified directly; the excited/top ratio tends to one, so no strictly
positive uniform ratio gap exists. Counting-measure normalization is used;
normalizing counting measure scales both eigenvalues equally. This is not a
Wilson kernel or a counterexample to the Yang--Mills mass-gap conjecture. -/
import UnifiedTheory.Clay.YangMills.WilsonCrossingKernel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.LocalRatioSpectralCounterexample
noncomputable section
open scoped BigOperators
open Filter

abbrev Cube (N : ℕ) := Fin N → Bool

def amplitude (N : ℕ) (a b : ℝ) (x : Cube N) : ℝ :=
  ∏ i, if x i then a else b

def plus (N : ℕ) : Cube N → ℝ := amplitude N (4/5) (3/5)
def minus (N : ℕ) : Cube N → ℝ := amplitude N (3/5) (4/5)
def overlap (N : ℕ) : ℝ := (24/25 : ℝ) ^ N

def dot {N : ℕ} (f g : Cube N → ℝ) : ℝ := ∑ x, f x * g x

theorem amplitude_dot (N : ℕ) (a b c d : ℝ) :
    dot (amplitude N a b) (amplitude N c d) = (a*c+b*d) ^ N := by
  unfold dot amplitude
  simp_rw [← Finset.prod_mul_distrib]
  have hp := Fintype.prod_sum (fun (_i : Fin N) (t : Bool) =>
    (if t then a else b) * (if t then c else d))
  rw [← hp]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem plus_norm (N : ℕ) : dot (plus N) (plus N) = 1 := by
  rw [plus, amplitude_dot]
  norm_num

theorem minus_norm (N : ℕ) : dot (minus N) (minus N) = 1 := by
  rw [minus, amplitude_dot]
  norm_num

theorem cross_overlap (N : ℕ) : dot (plus N) (minus N) = overlap N := by
  rw [plus, minus, amplitude_dot]
  norm_num [overlap]

theorem dot_comm {N : ℕ} (f g : Cube N → ℝ) : dot f g = dot g f := by
  unfold dot
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

def kernel (N : ℕ) (x y : Cube N) : ℝ :=
  plus N x * plus N y + minus N x * minus N y

def transfer (N : ℕ) (f : Cube N → ℝ) (x : Cube N) : ℝ :=
  ∑ y, kernel N x y * f y

def ground (N : ℕ) (x : Cube N) : ℝ := plus N x + minus N x
def excited (N : ℕ) (x : Cube N) : ℝ := plus N x - minus N x

theorem amplitude_pos (N : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : Cube N) :
    0 < amplitude N a b x :=
  Finset.prod_pos (fun i _ => by split <;> assumption)

theorem plus_pos (N : ℕ) (x : Cube N) : 0 < plus N x :=
  amplitude_pos N _ _ (by norm_num) (by norm_num) x

theorem minus_pos (N : ℕ) (x : Cube N) : 0 < minus N x :=
  amplitude_pos N _ _ (by norm_num) (by norm_num) x

theorem kernel_pos (N : ℕ) (x y : Cube N) : 0 < kernel N x y :=
  add_pos (mul_pos (plus_pos N x) (plus_pos N y))
    (mul_pos (minus_pos N x) (minus_pos N y))

theorem kernel_symm (N : ℕ) (x y : Cube N) : kernel N x y = kernel N y x := by
  unfold kernel
  ring

theorem transfer_formula (N : ℕ) (f : Cube N → ℝ) (x : Cube N) :
    transfer N f x = plus N x * dot (plus N) f + minus N x * dot (minus N) f := by
  simp only [transfer, kernel, dot, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro y _ <;> ring

theorem dot_add {N : ℕ} (f g h : Cube N → ℝ) :
    dot f (fun x => g x + h x) = dot f g + dot f h := by
  simp only [dot, mul_add, Finset.sum_add_distrib]

theorem dot_sub {N : ℕ} (f g h : Cube N → ℝ) :
    dot f (fun x => g x - h x) = dot f g - dot f h := by
  simp only [dot, mul_sub, Finset.sum_sub_distrib]

theorem ground_eigen (N : ℕ) (x : Cube N) :
    transfer N (ground N) x = (1 + overlap N) * ground N x := by
  unfold ground
  rw [transfer_formula]
  simp only [dot_add, plus_norm, minus_norm, cross_overlap,
    dot_comm (minus N) (plus N)]
  ring

theorem excited_eigen (N : ℕ) (x : Cube N) :
    transfer N (excited N) x = (1 - overlap N) * excited N x := by
  unfold excited
  rw [transfer_formula]
  simp only [dot_sub, plus_norm, minus_norm, cross_overlap,
    dot_comm (minus N) (plus N)]
  ring

theorem kernel_quadratic (N : ℕ) (f : Cube N → ℝ) :
    dot f (transfer N f) = (dot (plus N) f) ^ 2 + (dot (minus N) f) ^ 2 := by
  calc
    _ = (∑ x, (plus N x * f x) * dot (plus N) f) +
        ∑ x, (minus N x * f x) * dot (minus N) f := by
      unfold dot
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [transfer_formula]
      unfold dot
      ring
    _ = dot (plus N) f * dot (plus N) f + dot (minus N) f * dot (minus N) f := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      rfl
    _ = _ := by ring

theorem overlap_pos (N : ℕ) : 0 < overlap N := pow_pos (by norm_num) N

theorem overlap_lt_one {N : ℕ} (hN : 0 < N) : overlap N < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_zero_of_lt hN)

theorem ground_pos (N : ℕ) (x : Cube N) : 0 < ground N x :=
  add_pos (plus_pos N x) (minus_pos N x)

theorem ground_ne_zero (N : ℕ) : ground N ≠ 0 := by
  intro hz
  have hp := ground_pos N (fun _ => false)
  rw [hz] at hp
  norm_num at hp

theorem ground_norm (N : ℕ) : dot (ground N) (ground N) = 2 * (1 + overlap N) := by
  unfold ground
  rw [dot_add, dot_comm (fun x => plus N x + minus N x) (plus N),
    dot_comm (fun x => plus N x + minus N x) (minus N)]
  rw [dot_add, dot_add, plus_norm, minus_norm, cross_overlap,
    dot_comm (minus N) (plus N), cross_overlap]
  ring

theorem excited_norm (N : ℕ) : dot (excited N) (excited N) = 2 * (1 - overlap N) := by
  unfold excited
  rw [dot_sub, dot_comm (fun x => plus N x - minus N x) (plus N),
    dot_comm (fun x => plus N x - minus N x) (minus N)]
  rw [dot_sub, dot_sub, plus_norm, minus_norm, cross_overlap,
    dot_comm (minus N) (plus N), cross_overlap]
  ring

theorem excited_ne_zero {N : ℕ} (hN : 0 < N) : excited N ≠ 0 := by
  intro hz
  have hn := excited_norm N
  rw [hz] at hn
  simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hn
  linarith [overlap_lt_one hN]

theorem ground_excited_orthogonal (N : ℕ) : dot (ground N) (excited N) = 0 := by
  unfold ground excited
  rw [dot_sub, dot_comm (fun x => plus N x + minus N x) (plus N),
    dot_comm (fun x => plus N x + minus N x) (minus N)]
  rw [dot_add, dot_add, plus_norm, minus_norm, cross_overlap,
    dot_comm (minus N) (plus N), cross_overlap]
  ring

theorem amplitude_local_comparison (N : ℕ) (a b R : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfactor : ∀ p q : Bool, (if p then a else b) ≤ R * (if q then a else b))
    (e : Fin N) (x y : Cube N) (hxy : ∀ i, i ≠ e → x i = y i) :
    amplitude N a b x ≤ R * amplitude N a b y := by
  unfold amplitude
  rw [← Finset.mul_prod_erase Finset.univ (fun i => if x i then a else b)
    (Finset.mem_univ e),
    ← Finset.mul_prod_erase Finset.univ (fun i => if y i then a else b) (Finset.mem_univ e)]
  have he : (∏ i ∈ Finset.univ.erase e, if x i then a else b) =
      ∏ i ∈ Finset.univ.erase e, if y i then a else b := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hxy i (Finset.mem_erase.mp hi).1]
  rw [he]
  have hn : 0 ≤ ∏ i ∈ Finset.univ.erase e, if y i then a else b :=
    Finset.prod_nonneg (fun i _ => by split <;> assumption)
  calc
    _ ≤ (R * (if y e then a else b)) *
        (∏ i ∈ Finset.univ.erase e, if y i then a else b) :=
      mul_le_mul_of_nonneg_right (hfactor (x e) (y e)) hn
    _ = _ := by ring

theorem plus_local_comparison (N : ℕ) (e : Fin N) (x y : Cube N)
    (hxy : ∀ i, i ≠ e → x i = y i) : plus N x ≤ (4/3 : ℝ) * plus N y := by
  apply amplitude_local_comparison N _ _ _ (by norm_num) (by norm_num) _ e x y hxy
  intro p q
  cases p <;> cases q <;> norm_num

theorem minus_local_comparison (N : ℕ) (e : Fin N) (x y : Cube N)
    (hxy : ∀ i, i ≠ e → x i = y i) : minus N x ≤ (4/3 : ℝ) * minus N y := by
  apply amplitude_local_comparison N _ _ _ (by norm_num) (by norm_num) _ e x y hxy
  intro p q
  cases p <;> cases q <;> norm_num

/-- A uniform single-coordinate row ratio coexists with a collapsing spectral gap. -/
theorem kernel_local_comparison (N : ℕ) (e : Fin N) (x y z : Cube N)
    (hxy : ∀ i, i ≠ e → x i = y i) : kernel N x z ≤ (4/3 : ℝ) * kernel N y z := by
  have hp := mul_le_mul_of_nonneg_right (plus_local_comparison N e x y hxy) (plus_pos N z).le
  have hm := mul_le_mul_of_nonneg_right (minus_local_comparison N e x y hxy) (minus_pos N z).le
  unfold kernel
  nlinarith

theorem ground_local_comparison (N : ℕ) (e : Fin N) (x y : Cube N)
    (hxy : ∀ i, i ≠ e → x i = y i) : ground N x ≤ (4/3 : ℝ) * ground N y := by
  have hp := plus_local_comparison N e x y hxy
  have hm := minus_local_comparison N e x y hxy
  unfold ground
  linarith

theorem dot_smul {N : ℕ} (f g : Cube N → ℝ) (a : ℝ) :
    dot f (fun x => a * g x) = a * dot f g := by
  simp only [dot, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem dot_transfer (N : ℕ) (f g : Cube N → ℝ) :
    dot f (transfer N g) = dot f (plus N) * dot (plus N) g +
      dot f (minus N) * dot (minus N) g := by
  calc
    _ = (∑ x, (f x * plus N x) * dot (plus N) g) +
        ∑ x, (f x * minus N x) * dot (minus N) g := by
      unfold dot
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [transfer_formula]
      unfold dot
      ring
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

/-- Every nonzero real eigenvalue is one of the two explicitly constructed values. -/
theorem eigenvalue_classification (N : ℕ) (lam : ℝ) (f : Cube N → ℝ) (hf : f ≠ 0)
    (heig : ∀ x, transfer N f x = lam * f x) :
    lam = 0 ∨ lam = 1 + overlap N ∨ lam = 1 - overlap N := by
  by_cases hl : lam = 0
  · exact Or.inl hl
  right
  let a := dot (plus N) f
  let b := dot (minus N) f
  have ha : a + overlap N * b = lam * a := by
    have he : dot (plus N) (transfer N f) = dot (plus N) (fun x => lam * f x) :=
      congrArg (dot (plus N)) (funext heig)
    rw [dot_transfer, dot_smul, plus_norm, cross_overlap, one_mul] at he
    exact he
  have hb : overlap N * a + b = lam * b := by
    have he : dot (minus N) (transfer N f) = dot (minus N) (fun x => lam * f x) :=
      congrArg (dot (minus N)) (funext heig)
    rw [dot_transfer, dot_smul, minus_norm, dot_comm (minus N) (plus N),
      cross_overlap, one_mul] at he
    exact he
  have hn : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply hf
    funext x
    have he := heig x
    rw [transfer_formula] at he
    change plus N x * a + minus N x * b = lam * f x at he
    rw [hh.1, hh.2, mul_zero, mul_zero, zero_add] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hl
  by_cases hs : a + b = 0
  · have hd : a - b ≠ 0 := by
      intro hzero
      have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      exact hn.elim (fun h => h ha0) (fun h => h hb0)
    have he : (lam - (1 - overlap N)) * (a - b) = 0 := by nlinarith [ha, hb]
    exact Or.inr (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hd))
  · have he : (lam - (1 + overlap N)) * (a + b) = 0 := by nlinarith [ha, hb]
    exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hs))

theorem eigenvalue_le_top (N : ℕ) (lam : ℝ) (f : Cube N → ℝ) (hf : f ≠ 0)
    (heig : ∀ x, transfer N f x = lam * f x) : lam ≤ 1 + overlap N := by
  rcases eigenvalue_classification N lam f hf heig with h | h | h
  · rw [h]; linarith [overlap_pos N]
  · exact h.le
  · rw [h]; linarith [overlap_pos N]

def eigenvalueRatio (N : ℕ) : ℝ := (1 - overlap N) / (1 + overlap N)

theorem eigenvalueRatio_bounds {N : ℕ} (hN : 0 < N) :
    0 < eigenvalueRatio N ∧ eigenvalueRatio N < 1 := by
  have hs := overlap_pos N
  have ht := overlap_lt_one hN
  constructor
  · exact div_pos (sub_pos.mpr ht) (by linarith)
  · apply (div_lt_one (by linarith : 0 < 1 + overlap N)).mpr
    linarith

theorem relativeGap_formula (N : ℕ) :
    1 - eigenvalueRatio N = 2 * overlap N / (1 + overlap N) := by
  unfold eigenvalueRatio
  have hn : 1 + overlap N ≠ 0 := by linarith [overlap_pos N]
  field_simp [hn]
  ring

theorem relativeGap_upper (N : ℕ) : 1 - eigenvalueRatio N ≤ 2 * (24/25 : ℝ) ^ N := by
  rw [relativeGap_formula]
  apply (div_le_iff₀ (by linarith [overlap_pos N] : 0 < 1 + overlap N)).mpr
  change 2 * overlap N ≤ (2 * overlap N) * (1 + overlap N)
  nlinarith [sq_nonneg (overlap N)]

theorem overlap_tendsto_zero : Tendsto overlap atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem eigenvalueRatio_tendsto_one : Tendsto eigenvalueRatio atTop (nhds 1) := by
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have ht := (hc.sub overlap_tendsto_zero).div
    (hc.add overlap_tendsto_zero) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  simpa only [sub_zero, add_zero, div_one] using ht

theorem kernel_real_positive (N : ℕ) (f : Cube N → ℝ) :
    0 ≤ WilsonCrossingKernel.realQuadratic (kernel N) f := by
  have he : WilsonCrossingKernel.realQuadratic (kernel N) f = dot f (transfer N f) := by
    simp only [WilsonCrossingKernel.realQuadratic, dot, transfer, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [he, kernel_quadratic]
  positivity

theorem kernel_complex_positive (N : ℕ) (f : Cube N → ℂ) :
    0 ≤ (WilsonCrossingKernel.complexQuadratic (kernel N) f).re ∧
      (WilsonCrossingKernel.complexQuadratic (kernel N) f).im = 0 := by
  constructor
  · rw [WilsonCrossingKernel.complexQuadratic_re]
    exact add_nonneg (kernel_real_positive N _) (kernel_real_positive N _)
  · exact WilsonCrossingKernel.complexQuadratic_im (kernel N) (kernel_symm N) f

/-- No strictly positive, volume-independent ratio gap follows from these
strictly positive PSD kernels with their uniform 4/3 local comparisons. -/
theorem no_uniform_ratio_gap :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 0 < N → eigenvalueRatio N ≤ 1 - δ := by
  rintro ⟨δ, hδ, hbound⟩
  have he : ∀ᶠ N : ℕ in atTop, eigenvalueRatio N ≤ 1 - δ :=
    eventually_atTop.mpr ⟨1, fun N hN => hbound N (by omega)⟩
  have hl := le_of_tendsto eigenvalueRatio_tendsto_one he
  linarith

end
end UnifiedTheory.Clay.YangMills.LocalRatioSpectralCounterexample
