/- Exact interior perturbation profiles for a spatial reflection cut.
No symmetry or sign is required of the perturbation. Crossing plaquettes
must be unperturbed. A doubled profile is stated explicitly, not identified
with a set union when that identification has not been proved. -/
import UnifiedTheory.Clay.YangMills.SpatialWilsonHistoryKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialWilsonCutProfiles
noncomputable section
open WilsonTimeSlab WilsonSingleLinkStaples SpatialHalfEdgeSplit
open SpatialPlaquetteCutGeometry SpatialWilsonPlaquetteKernels SpatialWilsonReflectionKernel
open SpatialHalfEdgeLocality

variable (n : ℕ) [NeZero n]

def positivePart (δ : Plaquette n → ℝ) (p : Plaquette n) : ℝ := by
  classical
  exact if VertexPositive n p.1 then δ p else 0

def negativePart (δ : Plaquette n → ℝ) (p : Plaquette n) : ℝ := by
  classical
  exact if VertexPositive n p.1 then 0 else δ p

def reflected (δ : Plaquette n → ℝ) (p : Plaquette n) : ℝ := δ (reflectPlaquette n p)

def doubled (δ : Plaquette n → ℝ) (p : Plaquette n) : ℝ := δ p + reflected n δ p

omit [NeZero n] in
theorem parts_add (δ : Plaquette n → ℝ) (p : Plaquette n) :
    positivePart n δ p + negativePart n δ p = δ p := by
  classical
  simp only [positivePart, negativePart]
  split <;> simp

theorem action_add (γ δ : Plaquette n → ℝ) (u : SpatialLinks (2 * n) Q) :
    action n (fun p => γ p + δ p) u = action n γ u + action n δ u := by
  simp only [action, add_mul, Finset.sum_add_distrib]

theorem action_sub (γ δ : Plaquette n → ℝ) (u : SpatialLinks (2 * n) Q) :
    action n (fun p => γ p - δ p) u = action n γ u - action n δ u := by
  simp only [action, sub_mul, Finset.sum_sub_distrib]

omit [NeZero n] in
theorem defect_reflected (p : Plaquette n) (u : SpatialLinks (2 * n) Q) :
    defect n p (reflection n Q u) = defect n (reflectPlaquette n p) u := by
  unfold defect
  rw [character_reflection n Q character character_classFunction character_inverse_re]
  rfl

theorem action_reflected (δ : Plaquette n → ℝ) (u : SpatialLinks (2 * n) Q) :
    action n (reflected n δ) u = action n δ (reflection n Q u) := by
  unfold action reflected
  simp_rw [defect_reflected]
  have h := Equiv.sum_comp (plaquetteEquiv n)
    (fun p => δ p * defect n (reflectPlaquette n p) u)
  have hi (p : Plaquette n) : reflectPlaquette n (reflectPlaquette n p) = p :=
    reflectPlaquette_involutive n p
  simpa only [plaquetteEquiv, Function.Involutive.coe_toPerm, hi] using h

theorem action_doubled (δ : Plaquette n → ℝ) (a b : Half n Q) :
    action n (doubled n δ) (assemble n Q (a,b)) =
      action n δ (assemble n Q (a,b)) + action n δ (assemble n Q (b,a)) := by
  change action n (fun p => δ p + reflected n δ p) _ = _
  rw [action_add, action_reflected, ← assemble_reflection]

theorem positive_action (δ : Plaquette n → ℝ)
    (hδ : ∀ p, Crossing n p → δ p = 0) (a b : Half n Q) :
    action n (positivePart n δ) (assemble n Q (a,b)) =
      action n (positivePart n δ) (assemble n Q (a,a)) := by
  classical
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : Crossing n p
  · simp [positivePart, hδ p hp]
  · by_cases hx : VertexPositive n p.1
    · rw [interior_defect n p hp a b]
      simp only [sideHalf, if_pos hx]
    · simp [positivePart, hx]

theorem negative_action (δ : Plaquette n → ℝ)
    (hδ : ∀ p, Crossing n p → δ p = 0) (a b : Half n Q) :
    action n (negativePart n δ) (assemble n Q (a,b)) =
      action n (negativePart n δ) (assemble n Q (b,b)) := by
  classical
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : Crossing n p
  · simp [negativePart, hδ p hp]
  · by_cases hx : VertexPositive n p.1
    · simp [negativePart, hx]
    · rw [interior_defect n p hp a b]
      simp only [sideHalf, if_neg hx]

theorem action_split (δ : Plaquette n → ℝ)
    (hδ : ∀ p, Crossing n p → δ p = 0) (a b : Half n Q) :
    action n δ (assemble n Q (a,b)) =
      action n (positivePart n δ) (assemble n Q (a,a)) +
      action n (negativePart n δ) (assemble n Q (b,b)) := by
  have he : δ = fun p => positivePart n δ p + negativePart n δ p :=
    funext (fun p => (parts_add n δ p).symm)
  conv_lhs => rw [he, action_add]
  rw [positive_action n δ hδ, negative_action n δ hδ]

theorem positive_doubled_action (δ : Plaquette n → ℝ)
    (hδ : ∀ p, Crossing n p → δ p = 0) (a b : Half n Q) :
    action n (doubled n (positivePart n δ)) (assemble n Q (a,b)) =
      action n (positivePart n δ) (assemble n Q (a,a)) +
      action n (positivePart n δ) (assemble n Q (b,b)) := by
  rw [action_doubled, positive_action n δ hδ a b, positive_action n δ hδ b a]

theorem negative_doubled_action (δ : Plaquette n → ℝ)
    (hδ : ∀ p, Crossing n p → δ p = 0) (a b : Half n Q) :
    action n (doubled n (negativePart n δ)) (assemble n Q (a,b)) =
      action n (negativePart n δ) (assemble n Q (a,a)) +
      action n (negativePart n δ) (assemble n Q (b,b)) := by
  rw [action_doubled, negative_action n δ hδ a b, negative_action n δ hδ b a, add_comm]

omit [NeZero n] in
theorem doubled_invariant (δ : Plaquette n → ℝ) (p : Plaquette n) :
    doubled n δ (reflectPlaquette n p) = doubled n δ p := by
  simp only [doubled, reflected]
  rw [reflectPlaquette_involutive n p, add_comm]

theorem weight_perturb (γ δ : Plaquette n → ℝ) (u : SpatialLinks (2 * n) Q) :
    weight n (fun p => γ p - δ p) u = weight n γ u * Real.exp (action n δ u) := by
  rw [weight, action_sub, weight, ← Real.exp_add]
  congr 1
  ring

end
end UnifiedTheory.Clay.YangMills.SpatialWilsonCutProfiles
