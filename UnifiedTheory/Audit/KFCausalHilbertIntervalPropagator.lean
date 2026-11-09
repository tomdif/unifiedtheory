/- Arbitrarily long finite-interval propagators for continuous skew-adjoint
bounded operators on an arbitrary complex Hilbert space. A bounded
auxiliary equation has a Picard solution;
Gram conservation forces it onto the unit sphere, where the auxiliary
vector field equals the original linear field. -/
import UnifiedTheory.Audit.KFCausalRadialCutoff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHilbertIntervalPropagator
noncomputable section
open Set Metric
open scoped NNReal
open UnifiedTheory.Audit.KFCausalRadialCutoff

/-- Constancy uses derivatives within the interval, including its ends. -/
theorem constant_on_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) (hf : ∀ s ∈ Icc a b, HasDerivWithinAt f 0 (Icc a b) s)
    (x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : f y=f x := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0)
    hf (by intro s hs; simp) (convex_Icc a b) hx hy
  simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "M" => H →L[ℂ] H

/-- Any real scalar multiple of a skew-adjoint generator preserves the
Gram operator, even when the scalar depends on the evolving state. -/
theorem gram_derivative_zero (A : M) (hA : star A= -A) (d : ℝ) (U : ℝ → M)
    (s : Set ℝ) (t : ℝ) (hU : HasDerivWithinAt U (d • (A*U t)) s t) :
    HasDerivWithinAt (fun z => star (U z)*U z) 0 s t := by
  have hd := hU.star.mul hU
  convert hd using 1
  simp [hA,mul_assoc]

theorem linear_gram_constant (A U : ℝ → M) (hA : ∀ t, star (A t)= -A t) (T : ℝ)
    (hT : 0 ≤ T) (hU : ∀ t ∈ Icc (-T) T, HasDerivWithinAt U (A t*U t) (Icc (-T) T) t)
    (t : ℝ) (ht : t ∈ Icc (-T) T) : star (U t)*U t=star (U 0)*U 0 := by
  apply constant_on_interval _ (-T) T _ 0 t ⟨by linarith,hT⟩ ht
  intro s hs
  simpa using gram_derivative_zero (A s) (hA s) 1 U _ s (by simpa using hU s hs)

theorem cutoff_gram_constant (A U : ℝ → M) (hA : ∀ t, star (A t)= -A t) (T : ℝ)
    (hT : 0 ≤ T)
    (hU : ∀ t ∈ Icc (-T) T, HasDerivWithinAt U (A t*cutoff (U t)) (Icc (-T) T) t)
    (t : ℝ) (ht : t ∈ Icc (-T) T) : star (U t)*U t=star (U 0)*U 0 := by
  apply constant_on_interval _ (-T) T _ 0 t ⟨by linarith,hT⟩ ht
  intro s hs
  exact gram_derivative_zero (A s) (hA s) (2/(1+‖U s‖)) U _ s
    (by simpa only [cutoff,mul_smul_comm] using hU s hs)

theorem interval_unique (A U V : ℝ → M) (hA : ∀ t, star (A t)= -A t) (T : ℝ)
    (hT : 0 ≤ T)
    (hU : ∀ t ∈ Icc (-T) T, HasDerivWithinAt U (A t*U t) (Icc (-T) T) t)
    (hV : ∀ t ∈ Icc (-T) T, HasDerivWithinAt V (A t*V t) (Icc (-T) T) t)
    (hinit : U 0=V 0) (t : ℝ) (ht : t ∈ Icc (-T) T) : U t=V t := by
  have hd : ∀ s ∈ Icc (-T) T, HasDerivWithinAt (fun z => U z-V z)
      (A s*(U s-V s)) (Icc (-T) T) s := by
    intro s hs; simpa only [mul_sub] using (hU s hs).sub (hV s hs)
  have hg := linear_gram_constant A (fun z => U z-V z) hA T hT hd t ht
  simp only [hinit,sub_self,star_zero,mul_zero] at hg
  exact sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff (U t-V t)).mp hg)

variable [Nontrivial H]

theorem norm_one_of_gram_one (X : M) (hX : star X*X=1) : ‖X‖=1 := by
  have h := CStarRing.norm_star_mul_self (x := X)
  change ‖star X*X‖=‖X‖*‖X‖ at h
  rw [hX,norm_one] at h
  nlinarith [norm_nonneg X]

/-- There is a solution on every finite interval, with no small-time
restriction. The bounded auxiliary field is removed by norm conservation. -/
theorem exists_interval_propagator_nontrivial (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t)= -A t) (T : ℝ) (hT : 0 ≤ T) :
    ∃ U : ℝ → M, U 0=1 ∧
      ∀ t ∈ Icc (-T) T, HasDerivWithinAt U (A t*U t) (Icc (-T) T) t := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.continuousOn (s := Icc (-T) T))
  let K : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hbound (t : ℝ) (ht : t ∈ Icc (-T) T) : ‖A t‖ ≤ K :=
    (hB t ht).trans (le_max_left _ _)
  let radius : ℝ≥0 := (2*K)*⟨T,hT⟩
  let tzero : Icc (-T) T := ⟨0,by constructor <;> linarith⟩
  have hp : IsPicardLindelof (fun (t : ℝ) (X : M) => A t*cutoff X) tzero (1 : M)
      radius 0 (2*K) (4*K) := by
    constructor
    · intro t ht
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro X Y
      rw [dist_eq_norm,dist_eq_norm,← mul_sub]
      calc
        _ ≤ ‖A t‖*‖cutoff X-cutoff Y‖ := norm_mul_le _ _
        _ ≤ (K : ℝ)*(4*‖X-Y‖) := by
          gcongr
          · exact hbound t ht
          · simpa only [dist_eq_norm,NNReal.coe_ofNat] using cutoff_lipschitz.dist_le_mul X Y
        _ = ((4*K : ℝ≥0) : ℝ)*‖X-Y‖ := by simp; ring
    · intro X _
      exact (hA.mul continuous_const).continuousOn
    · intro t ht X _
      calc
        _ ≤ ‖A t‖*‖cutoff X‖ := norm_mul_le _ _
        _ ≤ (K : ℝ)*2 := mul_le_mul (hbound t ht) (cutoff_norm_le X) (norm_nonneg _) K.2
        _ = ((2*K : ℝ≥0) : ℝ) := by simp; ring
    · simp [radius,tzero]
  obtain ⟨U,hinit,hU⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  change U 0=1 at hinit
  refine ⟨U,hinit,?_⟩
  intro t ht
  have hg := cutoff_gram_constant A U hskew T hT hU t ht
  have hn : ‖U t‖=1 := norm_one_of_gram_one _ (by simpa [hinit] using hg)
  simpa only [cutoff_on_unit_sphere _ hn] using hU t ht

omit [Nontrivial H] in
/-- The zero Hilbert space is included without a nontriviality assumption. -/
theorem exists_interval_propagator (A : ℝ → M) (hA : Continuous A)
    (hskew : ∀ t, star (A t)= -A t) (T : ℝ) (hT : 0 ≤ T) :
    ∃ U : ℝ → M, U 0=1 ∧
      ∀ t ∈ Icc (-T) T, HasDerivWithinAt U (A t*U t) (Icc (-T) T) t := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · letI := hs
    refine ⟨fun _ => 1,rfl,?_⟩
    intro t _
    have he : A t*(1:M) = 0 := Subsingleton.elim _ _
    rw [he]
    exact hasDerivWithinAt_const t (Icc (-T) T) (1:M)
  · letI := hn
    exact exists_interval_propagator_nontrivial A hA hskew T hT

#print axioms gram_derivative_zero
#print axioms linear_gram_constant
#print axioms cutoff_gram_constant
#print axioms interval_unique
#print axioms norm_one_of_gram_one
#print axioms exists_interval_propagator

end
end UnifiedTheory.Audit.KFCausalHilbertIntervalPropagator
