/- Uniform norm convergence from transported coercive energy estimates.
This establishes a state limit, without asserting convergence of unbounded outputs. -/
import UnifiedTheory.Audit.KFCausalWeightedMassEnergy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCoerciveCauchyLimit
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem norm_sq_control (F S U : V →L[ℂ] V) (d : ℝ) (hd : 0 < d)
    (hi : ∀ x, U (S x) = x) (hc : ∀ x, d*‖x‖^2 ≤ energy F x) (x : V) :
    ‖x‖^2 ≤ (‖U‖^2/d)*energy F (S x) := by
  have hn : ‖x‖ ≤ ‖U‖*‖S x‖ := by simpa only [hi] using U.le_opNorm (S x)
  have hs := (sq_le_sq₀ (norm_nonneg x) (mul_nonneg (norm_nonneg U) (norm_nonneg (S x)))).2 hn
  have hc' := mul_le_mul_of_nonneg_left (hc (S x)) (sq_nonneg ‖U‖)
  rw [div_mul_eq_mul_div,le_div_iff₀ hd]
  have hs' := mul_le_mul_of_nonneg_right hs hd.le
  nlinarith only [hs',hc']

theorem uniform_norm_sq_control (F S U : ℝ → V →L[ℂ] V) (d : ℝ → ℝ) (l r : ℝ)
    (hU : ContinuousOn U (Icc l r)) (hd : ContinuousOn d (Icc l r))
    (hdp : ∀ t ∈ Icc l r, 0 < d t)
    (hi : ∀ t ∈ Icc l r, ∀ x, U t (S t x) = x)
    (hc : ∀ t ∈ Icc l r, ∀ x, d t*‖x‖^2 ≤ energy (F t) x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc l r, ∀ x, ‖x‖^2 ≤ K*energy (F t) (S t x) := by
  have hcont : ContinuousOn (fun t => ‖U t‖^2/d t) (Icc l r) :=
    (hU.norm.pow 2).div hd (fun t ht => ne_of_gt (hdp t ht))
  obtain ⟨N,hN⟩ := (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  refine ⟨max N 0,le_max_right _ _,fun t ht x => ?_⟩
  have he : 0 ≤ energy (F t) (S t x) :=
    (mul_nonneg (hdp t ht).le (sq_nonneg _)).trans (hc t ht (S t x))
  exact (norm_sq_control (F t) (S t) (U t) (d t) (hdp t ht) (hi t ht) (hc t ht) x).trans
    (mul_le_mul_of_nonneg_right ((hN (mem_image_of_mem _ ht)).trans (le_max_left _ _)) he)

omit [InnerProductSpace ℂ V] in
theorem uniform_cauchy_of_norm_sq {α : Type*} (w : ℕ → α → V) (I : Set α)
    (B C : ℝ) (hB : 2 ≤ B) (hC : 0 ≤ C)
    (he : ∀ n m : ℕ, ∀ t ∈ I, ‖w n t-w m t‖^2 ≤ C*(1/(B+n)+1/(B+m))) :
    UniformCauchySeqOn w atTop I := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro eps heps
  obtain ⟨N,hN⟩ := exists_nat_gt (2*C/eps^2)
  refine ⟨N,fun m hm n hn t ht => ?_⟩
  have hNp : 0 < (N:ℝ)+1 := by positivity
  have hm' : (N:ℝ)+1 ≤ B+m := by have : (N:ℝ) ≤ (m:ℝ) := Nat.cast_le.mpr hm; linarith
  have hn' : (N:ℝ)+1 ≤ B+n := by have : (N:ℝ) ≤ (n:ℝ) := Nat.cast_le.mpr hn; linarith
  have hrec := add_le_add (one_div_le_one_div_of_le hNp hm') (one_div_le_one_div_of_le hNp hn')
  have hbound := (he m n t ht).trans (mul_le_mul_of_nonneg_left hrec hC)
  have hN' : 2*C < eps^2*((N:ℝ)+1) := by
    have := (div_lt_iff₀ (sq_pos_of_pos heps)).mp hN
    nlinarith only [this,sq_pos_of_pos heps]
  have hsmall : C*(1/((N:ℝ)+1)+1/((N:ℝ)+1)) < eps^2 := by
    have := (div_lt_iff₀ hNp).mpr hN'
    convert this using 1; ring
  rw [dist_eq_norm]
  exact (sq_lt_sq₀ (norm_nonneg _) heps.le).mp (hbound.trans_lt hsmall)

theorem reciprocal_limit (B : ℝ) (hB : 2 ≤ B) :
    Tendsto (fun n : ℕ => 1/(B+n)) atTop (𝓝 (0:ℝ)) := by
  apply squeeze_zero (fun n : ℕ => one_div_nonneg.mpr (add_nonneg (le_trans (by norm_num) hB) (Nat.cast_nonneg n)))
    (fun n : ℕ => one_div_le_one_div_of_le (by positivity : 0 < (n:ℝ)+1) (by linarith))
    tendsto_one_div_add_atTop_nhds_zero_nat

omit [InnerProductSpace ℂ V] in
theorem exists_uniform_limit [CompleteSpace V] (w : ℕ → ℝ → V) (l r B C : ℝ)
    (hB : 2 ≤ B) (hC : 0 ≤ C) (hw : ∀ n, ContinuousOn (w n) (Icc l r))
    (he : ∀ n m : ℕ, ∀ t ∈ Icc l r, ‖w n t-w m t‖^2 ≤ C*(1/(B+n)+1/(B+m))) :
    ∃ u : ℝ → V, ContinuousOn u (Icc l r) ∧ TendstoUniformlyOn w u atTop (Icc l r) ∧
      ∀ n : ℕ, ∀ t ∈ Icc l r, ‖w n t-u t‖^2 ≤ C/(B+n) := by
  let u : ℝ → V := fun t => limUnder atTop (fun n => w n t)
  have hcauchy := uniform_cauchy_of_norm_sq w (Icc l r) B C hB hC he
  have hu : TendstoUniformlyOn w u atTop (Icc l r) :=
    hcauchy.tendstoUniformlyOn_of_tendsto (fun t ht => (hcauchy.cauchySeq ht).tendsto_limUnder)
  refine ⟨u,hu.continuousOn (Eventually.of_forall hw).frequently,hu,fun n t ht => ?_⟩
  have hleft := ((tendsto_const_nhds (x := w n t)).sub (hu.tendsto_at ht)).norm.pow 2
  have hright : Tendsto (fun m : ℕ => C*(1/(B+n)+1/(B+m))) atTop (𝓝 (C/(B+n))) := by
    simpa only [add_zero,mul_one_div] using
      (tendsto_const_nhds (x := C)).mul ((tendsto_const_nhds (x := 1/(B+n))).add (reciprocal_limit B hB))
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall (fun m => he n m t ht))

omit [InnerProductSpace ℂ V] in
theorem limit_initial [CompleteSpace V] (w : ℕ → ℝ → V) (u : ℝ → V) (l r : ℝ)
    (hlr : l ≤ r) (hu : TendstoUniformlyOn w u atTop (Icc l r)) (x : V)
    (hi : ∀ n, w n l = x) : u l = x := by
  apply tendsto_nhds_unique (hu.tendsto_at ⟨le_rfl,hlr⟩)
  simpa only [hi] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))

#print axioms norm_sq_control
#print axioms uniform_norm_sq_control
#print axioms uniform_cauchy_of_norm_sq
#print axioms reciprocal_limit
#print axioms exists_uniform_limit
#print axioms limit_initial
end
end UnifiedTheory.Audit.KFCausalCoerciveCauchyLimit
