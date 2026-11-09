/- Existence on any finite forward interval for continuous bounded linear
coefficients. A ball clipping gives a global Picard field; Gronwall proves
the constructed solution stays where clipping is exactly the identity. -/
import UnifiedTheory.Audit.KFCausalRadialBallClipping
import UnifiedTheory.Audit.KFCausalTransportedQuasiGrowth
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalBoundedLinearIntervalFlow
noncomputable section
open Set Metric
open scoped NNReal
open UnifiedTheory.Audit.KFCausalRadialBallClipping
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem interval_norm_bound (u du : ℝ → V) (l r K δ : ℝ)
    (hc : ContinuousOn u (Icc l r))
    (hd : ∀ t ∈ Icc l r, HasDerivWithinAt u (du t) (Icc l r) t)
    (hinit : ‖u l‖ ≤ δ) (hg : ∀ t ∈ Icc l r, ‖du t‖ ≤ K*‖u t‖) :
    ∀ t ∈ Icc l r, ‖u t‖ ≤ δ*Real.exp (K*(t-l)) := by
  have he := norm_le_gronwallBound_of_norm_deriv_right_le (K := K) (ε := 0) hc
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    hinit (fun t ht => by simpa only [add_zero] using hg t (Ico_subset_Icc_self ht))
  simpa only [gronwallBound_ε0] using he

theorem clipped_interval_solution (A : ℝ → V →L[ℂ] V) (l r : ℝ) (hlr : l ≤ r)
    (hA : ContinuousOn A (Icc l r)) (K : ℝ≥0) (hK : ∀ t ∈ Icc l r, ‖A t‖ ≤ K)
    (R : ℝ) (hR : 0 < R) (x : V) :
    ∃ u : ℝ → V, u l = x ∧ ∀ t ∈ Icc l r,
      HasDerivWithinAt u (A t (clip R (u t))) (Icc l r) t := by
  let Rn : ℝ≥0 := ⟨R,hR.le⟩
  let Tn : ℝ≥0 := ⟨r-l,sub_nonneg.mpr hlr⟩
  let radius : ℝ≥0 := K*Rn*Tn
  let initial : Icc l r := ⟨l,⟨le_rfl,hlr⟩⟩
  have hp : IsPicardLindelof (fun t y => A t (clip R y)) initial x radius 0 (K*Rn) (2*K) := by
    constructor
    · intro t ht
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro y z
      rw [dist_eq_norm,dist_eq_norm,← map_sub]
      calc
        _ ≤ ‖A t‖*‖clip R y-clip R z‖ := (A t).le_opNorm _
        _ ≤ (K:ℝ)*(2*‖y-z‖) := mul_le_mul (hK t ht)
          (by simpa only [dist_eq_norm,NNReal.coe_ofNat] using (clip_lipschitz R hR).dist_le_mul y z)
          (norm_nonneg _) K.coe_nonneg
        _ = ((2*K:ℝ≥0):ℝ)*‖y-z‖ := by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; ring
    · intro y _
      exact hA.clm_apply continuousOn_const
    · intro t ht y _
      exact ((A t).le_opNorm _).trans (mul_le_mul (hK t ht) (clip_norm_le_radius R hR y)
        (norm_nonneg _) K.coe_nonneg)
    · change (K:ℝ)*R*max (r-l) (l-l) ≤ (K:ℝ)*R*(r-l)-0
      rw [sub_self,sub_zero,max_eq_left (sub_nonneg.mpr hlr)]
  obtain ⟨u,hi,hu⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨u,hi,hu⟩

theorem exists_interval_solution (A : ℝ → V →L[ℂ] V) (l r : ℝ) (hlr : l ≤ r)
    (hA : ContinuousOn A (Icc l r)) (x : V) :
    ∃ u : ℝ → V, u l = x ∧ ContinuousOn u (Icc l r) ∧
      ∀ t ∈ Icc l r, HasDerivWithinAt u (A t (u t)) (Icc l r) t := by
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc l r)).exists_bound_of_continuousOn hA
  let K : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hK (t : ℝ) (ht : t ∈ Icc l r) : ‖A t‖ ≤ K := (hB t ht).trans (le_max_left _ _)
  let R : ℝ := (‖x‖+1)*Real.exp ((K:ℝ)*(r-l))
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨u,hi,hu⟩ := clipped_interval_solution A l r hlr hA K hK R hR x
  have hc : ContinuousOn u (Icc l r) := fun t ht => (hu t ht).continuousWithinAt
  have hg (t : ℝ) (ht : t ∈ Icc l r) : ‖A t (clip R (u t))‖ ≤ (K:ℝ)*‖u t‖ :=
    ((A t).le_opNorm _).trans (mul_le_mul (hK t ht) (clip_norm_le R hR (u t))
      (norm_nonneg _) K.coe_nonneg)
  have hn := interval_norm_bound u (fun t => A t (clip R (u t))) l r K ‖x‖ hc hu
    (by rw [hi]) hg
  have hin (t : ℝ) (ht : t ∈ Icc l r) : ‖u t‖ ≤ R := by
    calc
      _ ≤ ‖x‖*Real.exp ((K:ℝ)*(t-l)) := hn t ht
      _ ≤ ‖x‖*Real.exp ((K:ℝ)*(r-l)) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 l) K.coe_nonneg)) (norm_nonneg x)
      _ ≤ R := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.exp_pos _).le
  refine ⟨u,hi,hc,?_⟩
  intro t ht
  simpa only [clip_identity R hR (u t) (hin t ht)] using hu t ht

theorem exists_strong_interval_solution (A : ℝ → V →L[ℂ] V) (l r : ℝ) (hlr : l ≤ r)
    (hA : ContinuousOn A (Icc l r)) (x : V) :
    ∃ u : ℝ → V, u l = x ∧ ContinuousOn u (Icc l r) ∧
      ∀ t ∈ Ioo l r, HasDerivAt u (A t (u t)) t := by
  obtain ⟨u,hi,hc,hu⟩ := exists_interval_solution A l r hlr hA x
  exact ⟨u,hi,hc,fun t ht => (hu t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)

theorem exists_uniformly_stable_solutions (A : ℝ → ℝ → V →L[ℂ] V)
    (F S : ℝ → V →L[ℂ] V) (q ω ρ : ℝ → ℝ) (l r : ℝ) (hlr : l ≤ r)
    (hparams : ∃ b₀ κ : ℝ, 0 < b₀ ∧ 0 ≤ κ ∧ ∀ b, b₀ ≤ b → ∀ t ∈ Icc l r,
      q t < b ∧ 2*ω t ≤ b ∧ ρ t ≤ κ)
    (hA : ∀ b, 0 < b → (∀ t ∈ Icc l r, q t < b) → ContinuousOn (A b) (Icc l r))
    (hE : ∀ b κ t, 0 < b → l ≤ t →
      (∀ u ∈ Icc l t, q u < b ∧ 2*ω u ≤ b ∧ ρ u ≤ κ) →
      ∀ w : ℝ → V, ContinuousOn w (Icc l t) →
      (∀ u ∈ Ioo l t, HasDerivAt w (A b u (w u)) u) →
      energy (F t) (S t (w t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l (w l))) :
    ∃ b₀ κ : ℝ, 0 < b₀ ∧ 0 ≤ κ ∧ ∀ b, b₀ ≤ b → ∀ x : V,
      ∃ w : ℝ → V, w l = x ∧ ContinuousOn w (Icc l r) ∧
        (∀ t ∈ Icc l r, HasDerivWithinAt w (A b t (w t)) (Icc l r) t) ∧
        ∀ t ∈ Icc l r, energy (F t) (S t (w t)) ≤
          Real.exp (κ*(t-l))*energy (F l) (S l x) := by
  obtain ⟨b₀,κ,hb₀,hκ,hp⟩ := hparams
  refine ⟨b₀,κ,hb₀,hκ,?_⟩
  intro b hb x
  have hbpos : 0 < b := hb₀.trans_le hb
  obtain ⟨w,hi,hc,hw⟩ := exists_interval_solution (A b) l r hlr
    (hA b hbpos (fun t ht => (hp b hb t ht).1)) x
  refine ⟨w,hi,hc,hw,?_⟩
  intro t ht
  have hsub : Icc l t ⊆ Icc l r := Icc_subset_Icc le_rfl ht.2
  have hd : ∀ u ∈ Ioo l t, HasDerivAt w (A b u (w u)) u := by
    intro u hu
    have hur : u < r := hu.2.trans_le ht.2
    exact (hw u ⟨hu.1.le,hur.le⟩).hasDerivAt (Icc_mem_nhds hu.1 hur)
  have he := hE b κ t hbpos ht.1 (fun u hu => hp b hb u (hsub hu)) w (hc.mono hsub) hd
  simpa only [hi] using he

#print axioms interval_norm_bound
#print axioms clipped_interval_solution
#print axioms exists_interval_solution
#print axioms exists_strong_interval_solution
#print axioms exists_uniformly_stable_solutions
end
end UnifiedTheory.Audit.KFCausalBoundedLinearIntervalFlow
