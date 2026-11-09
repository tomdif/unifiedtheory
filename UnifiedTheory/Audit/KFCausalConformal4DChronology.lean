import UnifiedTheory.Audit.KFCausalConformal4DTimelikeTangents
import UnifiedTheory.Audit.KFCausalMinkowski4DTimelikeCurves

/-!
Chronology defined by existence of actual C¹ future-timelike curves, rather
than by an endpoint cone inequality. On the temporal conformal cutoff slab,
the relation agrees with the explicit Minkowski cone. Both directions are
proved: the mean-value displacement theorem and actual straight witnesses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DChronology
noncomputable section
open Set
open scoped ContDiff
open KFCausalConformal4DDiamondBenchmark (Point)
open KFCausalConformal4DDiamondAffine (future diamond endpoint)
open KFCausalConformal4DTimelikeTangents
open KFCausalMinkowski4DTimelikeCurves

def timeSlab (l u : ℝ) : Set Point := {p | l ≤ p 0 ∧ p 0 ≤ u}

def chronologicalIn (att spatial : ℝ) (S : Set Point) (p q : Point) : Prop :=
  ∃ γ : ℝ → Point, ContDiff ℝ 1 γ ∧ γ 0 = p ∧ γ 1 = q ∧
    ∀ s ∈ Icc (0 : ℝ) 1,
      γ s ∈ S ∧ futureTangent att spatial (γ s) (deriv γ s)

def chronologicalDiamondIn (att spatial : ℝ) (S : Set Point) (p q : Point) : Set Point :=
  {x | chronologicalIn att spatial S p x ∧ chronologicalIn att spatial S x q}

theorem chronological_implies_future (att spatial : ℝ) (S : Set Point) (p q : Point)
    (h : chronologicalIn att spatial S p q) : future (q - p) := by
  obtain ⟨γ, hγ, h0, h1, hv⟩ := h
  have hf := future_displacement γ hγ
    (fun s hs => future_tangent_implies att spatial _ _ (hv s hs).2)
  simpa only [h0, h1] using hf

theorem chronological_mono (att spatial : ℝ) {S T : Set Point} (hST : S ⊆ T)
    (p q : Point) (h : chronologicalIn att spatial S p q) :
    chronologicalIn att spatial T p q := by
  obtain ⟨γ, hγ, h0, h1, hv⟩ := h
  exact ⟨γ, hγ, h0, h1, fun s hs => ⟨hST (hv s hs).1, (hv s hs).2⟩⟩

theorem time_slab_chronology_iff (c : ℝ) (hc : |c| ≤ 1 / 54)
    (l u : ℝ) (hl : -2 ≤ l) (hu : u ≤ 2) (p q : Point)
    (hp : p ∈ timeSlab l u) (hq : q ∈ timeSlab l u) :
    chronologicalIn (2 * c) 0 (timeSlab l u) p q ↔ future (q - p) := by
  refine ⟨chronological_implies_future _ _ _ p q, ?_⟩
  intro hf
  obtain ⟨h0, h1⟩ := straight_endpoints p q
  refine ⟨straight p q, straight_smooth p q, h0, h1, ?_⟩
  intro s hs
  have hpq : p 0 ≤ q 0 := by have ht := hf.1; change 0 < q 0 - p 0 at ht; linarith
  obtain ⟨hs0, hs1⟩ := straight_time_bounds p q hpq s hs
  have hm : straight p q s ∈ timeSlab l u := ⟨hp.1.trans hs0, hs1.trans hq.2⟩
  refine ⟨hm, ?_⟩
  apply (temporal_future_tangent_iff c hc _ _ (abs_le.mpr
    ⟨hl.trans hm.1, hm.2.trans hu⟩)).mpr
  rw [(straight_derivative p q s).deriv]
  exact hf

theorem global_chronology_iff (c : ℝ) (hc : |c| ≤ 1 / 54) (p q : Point)
    (hp : |p 0| ≤ 2) (hq : |q 0| ≤ 2) :
    chronologicalIn (2 * c) 0 univ p q ↔ future (q - p) := by
  refine ⟨chronological_implies_future _ _ _ p q, ?_⟩
  intro hf
  exact chronological_mono _ _ (subset_univ _) p q
    ((time_slab_chronology_iff c hc (-2) 2 (by norm_num) (by norm_num)
      p q (abs_le.mp hp) (abs_le.mp hq)).mpr hf)

theorem retarded_slab_diamond (c : ℝ) (hc : |c| ≤ 1 / 54)
    (t r : ℝ) (ht : t < 0) (htb : |t| ≤ 2) :
    chronologicalDiamondIn (2 * c) 0 (timeSlab t 0) (endpoint t r) 0 =
      diamond (endpoint t r) 0 := by
  ext x
  constructor
  · intro hx
    exact ⟨chronological_implies_future _ _ _ _ _ hx.1,
      chronological_implies_future _ _ _ _ _ hx.2⟩
  · intro hx
    have hx0 : t < x 0 := by
      have h := hx.1.1
      change 0 < x 0 - t at h
      linarith
    have hx1 : x 0 < 0 := by
      have h := hx.2.1
      change 0 < 0 - x 0 at h
      linarith
    have hp : endpoint t r ∈ timeSlab t 0 := by
      change t ≤ t ∧ t ≤ 0
      exact ⟨le_rfl, ht.le⟩
    have hq : (0 : Point) ∈ timeSlab t 0 := ⟨ht.le, le_rfl⟩
    have hxm : x ∈ timeSlab t 0 := ⟨hx0.le, hx1.le⟩
    have hl := (abs_le.mp htb).1
    exact ⟨(time_slab_chronology_iff c hc t 0 hl (by norm_num) _ _ hp hxm).mpr hx.1,
      (time_slab_chronology_iff c hc t 0 hl (by norm_num) _ _ hxm hq).mpr hx.2⟩

theorem retarded_global_diamond (c : ℝ) (hc : |c| ≤ 1 / 54)
    (t r : ℝ) (ht : t < 0) (htb : |t| ≤ 2) :
    chronologicalDiamondIn (2 * c) 0 univ (endpoint t r) 0 =
      diamond (endpoint t r) 0 := by
  ext x
  constructor
  · intro hx
    exact ⟨chronological_implies_future _ _ _ _ _ hx.1,
      chronological_implies_future _ _ _ _ _ hx.2⟩
  · intro hx
    have hs : x ∈ chronologicalDiamondIn (2 * c) 0 (timeSlab t 0) (endpoint t r) 0 := by
      rwa [retarded_slab_diamond c hc t r ht htb]
    exact ⟨chronological_mono _ _ (subset_univ _) _ _ hs.1,
      chronological_mono _ _ (subset_univ _) _ _ hs.2⟩

#print axioms chronological_implies_future
#print axioms chronological_mono
#print axioms time_slab_chronology_iff
#print axioms global_chronology_iff
#print axioms retarded_slab_diamond
#print axioms retarded_global_diamond
end
end UnifiedTheory.Audit.KFCausalConformal4DChronology
