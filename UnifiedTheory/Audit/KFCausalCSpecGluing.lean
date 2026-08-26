/-
  Audit/KFCausalCSpecGluing.lean   (Volume sector — Step 5, global gluing)

  The final step of the Hauptvermutung ladder: glue the LOCAL approximate-Lorentz maps
  (supplied pointwise by trilateration + the proper-time band) into ONE global
  approximate isometry, following Madsen's Karcher-mean construction.

  DIVISION OF LABOR (as with Roy-Sinha-Surya and the Poisson variance).  The Riemannian
  barycenter / Karcher-mean existence and its metric-stability estimate are genuine
  Riemannian geometry (center of mass in a small geodesic ball), NOT formalized here.
  What that geometry supplies, and is taken here as the named hypothesis `hbary`, is the
  stability statement: if the interval values `F(a_i, b_i)` all sit within `η` of a common
  value, the barycenter's interval `F(bary a, bary b)` sits within `η + κ`, where `κ` is
  the barycenter's curvature defect (κ -> 0 as the ball shrinks).

  What is PROVED here, from that input:

    * `HasDistortion` — a map's metric-distortion defect;
    * `hasDistortion_comp` — distortion is SUBADDITIVE under composition (errors add);
    * `hasDistortion_zero_iff` — zero distortion is exactly an isometry;
    * `glue_distortion` — the barycenter of local maps each of distortion `≤ δ` is a
      GLOBAL map of distortion `≤ δ + κ`.

  Composed with Step 6: as sprinkling density -> ∞ the local distortion `δ -> 0` (band
  collapse) and the curvature defect `κ -> 0` (shrinking diamonds), so the glued map's
  distortion `δ + κ -> 0`, i.e. the two embeddings are related by a global map converging
  to an exact isometry -- the quantitative Hauptvermutung, now closed end to end (modulo
  the two cited geometric inputs: the Roy-Sinha-Surya remainder and the Karcher stability).

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecGluing

variable {X Y Z ι : Type*}

/-- A map `g : X → Y` has metric distortion at most `δ` (w.r.t. source interval `G` and
target interval `F`) if every pair's interval is preserved to within `δ`. -/
def HasDistortion (G : X → X → ℝ) (F : Y → Y → ℝ) (g : X → Y) (δ : ℝ) : Prop :=
  ∀ x x', |F (g x) (g x') - G x x'| ≤ δ

/-- A relation-restricted distortion estimate.  This is the honest target when
interval data are available only on a specified family of pairs. -/
def HasDistortionOn (R : X → X → Prop) (G : X → X → ℝ)
    (F : Y → Y → ℝ) (g : X → Y) (δ : ℝ) : Prop :=
  ∀ x x', R x x' → |F (g x) (g x') - G x x'| ≤ δ

/-- Off-diagonal control upgrades to total distortion when the diagonal is
exact and the displayed bound is nonnegative.  This is a result-level wrapper:
it does not manufacture interval-count hypotheses on the forbidden diagonal. -/
theorem hasDistortion_of_distinct
    (G : X → X → ℝ) (F : Y → Y → ℝ) (g : X → Y) (δ : ℝ)
    (hoff : HasDistortionOn (fun x x' => x ≠ x') G F g δ)
    (hdiag : ∀ x, F (g x) (g x) = G x x) (hδ : 0 ≤ δ) :
    HasDistortion G F g δ := by
  intro x x'
  by_cases h : x = x'
  · subst x'
    simp [hdiag x, hδ]
  · exact hoff x x' h

/-- **Distortion is subadditive under composition.**  A `δ`-approximate isometry followed
by an `ε`-approximate isometry is an `(ε + δ)`-approximate isometry. -/
theorem hasDistortion_comp
    (G : X → X → ℝ) (F : Y → Y → ℝ) (H : Z → Z → ℝ)
    (g : X → Y) (h : Y → Z) (δ ε : ℝ)
    (hg : HasDistortion G F g δ) (hh : HasDistortion F H h ε) :
    HasDistortion G H (fun x => h (g x)) (ε + δ) := by
  intro x x'
  calc |H (h (g x)) (h (g x')) - G x x'|
      = |(H (h (g x)) (h (g x')) - F (g x) (g x')) + (F (g x) (g x') - G x x')| := by
        congr 1; ring
    _ ≤ |H (h (g x)) (h (g x')) - F (g x) (g x')| + |F (g x) (g x') - G x x'| := abs_add_le _ _
    _ ≤ ε + δ := add_le_add (hh (g x) (g x')) (hg x x')

/-- **Zero distortion is an isometry.**  A map has distortion `0` iff it preserves every
interval exactly -- the exact-isometry limit of the approximate notion. -/
theorem hasDistortion_zero_iff (G : X → X → ℝ) (F : Y → Y → ℝ) (g : X → Y) :
    HasDistortion G F g 0 ↔ ∀ x x', F (g x) (g x') = G x x' := by
  constructor
  · intro h x x'
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (h x x') (abs_nonneg _)))
  · intro h x x'
    simp [h x x']

/-- **Global gluing (Step 5).**  Given local maps `g i` each of distortion `≤ δ` and the
Karcher-mean stability `hbary` (curvature defect `κ`), the barycenter map
`x ↦ bary (fun i => g i x)` is a GLOBAL map of distortion `≤ δ + κ`.  This is Madsen's
gluing: consistent local approximate isometries average into a global one. -/
theorem glue_distortion
    (G : X → X → ℝ) (F : Y → Y → ℝ) (bary : (ι → Y) → Y) (δ κ : ℝ)
    (hbary : ∀ (a b : ι → Y) (m η : ℝ), (∀ i, |F (a i) (b i) - m| ≤ η) →
      |F (bary a) (bary b) - m| ≤ η + κ)
    (g : ι → X → Y) (hg : ∀ i, HasDistortion G F (g i) δ) :
    HasDistortion G F (fun x => bary (fun i => g i x)) (δ + κ) := by
  intro x x'
  exact hbary (fun i => g i x) (fun i => g i x') (G x x') δ (fun i => hg i x x')

/-- **Gluing preserves the exact-isometry limit.**  If the local maps are exact isometries
(`δ = 0`) and the barycenter is exact (`κ = 0`), the glued map is an exact isometry. -/
theorem glue_isometry_of_exact
    (G : X → X → ℝ) (F : Y → Y → ℝ) (bary : (ι → Y) → Y)
    (hbary : ∀ (a b : ι → Y) (m η : ℝ), (∀ i, |F (a i) (b i) - m| ≤ η) →
      |F (bary a) (bary b) - m| ≤ η + 0)
    (g : ι → X → Y) (hg : ∀ i, HasDistortion G F (g i) 0) :
    ∀ x x', F (bary (fun i => g i x)) (bary (fun i => g i x')) = G x x' := by
  rw [← hasDistortion_zero_iff]
  have := glue_distortion G F bary 0 0 hbary g hg
  simpa using this

#print axioms hasDistortion_comp
#print axioms hasDistortion_zero_iff
#print axioms hasDistortion_of_distinct
#print axioms glue_distortion
#print axioms glue_isometry_of_exact

end UnifiedTheory.Audit.KFCausalCSpecGluing
