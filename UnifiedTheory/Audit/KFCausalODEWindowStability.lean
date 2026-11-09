/- Gronwall stability on a two-sided time window. Both curves solve the
same field inside the stated region; no global Lipschitz hypothesis is needed. -/
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalODEWindowStability
noncomputable section
open Set
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem distance_forward (f : E → E) (K : ℝ≥0) (U : Set E) (hf : LipschitzOnWith K f U)
    (T : ℝ) (γ η : ℝ → E)
    (hγ : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt γ (f (γ t)) t)
    (hη : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt η (f (η t)) t)
    (hγU : ∀ t ∈ Icc (0:ℝ) T, γ t ∈ U)
    (hηU : ∀ t ∈ Icc (0:ℝ) T, η t ∈ U)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) :
    dist (γ t) (η t) ≤ dist (γ 0) (η 0)*Real.exp ((K:ℝ)*T) := by
  have h := dist_le_of_trajectories_ODE_of_mem (v := fun _ => f) (s := fun _ => U)
    (fun _ _ => hf)
    (fun u hu => (hγ u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hγ u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
    (fun u hu => hγU u (Ico_subset_Icc_self hu))
    (fun u hu => (hη u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hη u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
    (fun u hu => hηU u (Ico_subset_Icc_self hu)) (le_refl (dist (γ 0) (η 0))) t ht
  simp only [sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)) (dist_nonneg))

theorem distance_window (f : E → E) (K : ℝ≥0) (U : Set E) (hf : LipschitzOnWith K f U)
    (T : ℝ) (hT : 0 ≤ T) (γ η : ℝ → E)
    (hγ : ∀ t ∈ Icc (-T) T, HasDerivAt γ (f (γ t)) t)
    (hη : ∀ t ∈ Icc (-T) T, HasDerivAt η (f (η t)) t)
    (hγU : ∀ t ∈ Icc (-T) T, γ t ∈ U)
    (hηU : ∀ t ∈ Icc (-T) T, η t ∈ U)
    (t : ℝ) (ht : t ∈ Icc (-T) T) :
    dist (γ t) (η t) ≤ dist (γ 0) (η 0)*Real.exp ((K:ℝ)*T) := by
  have hpos (u : ℝ) (hu : u ∈ Icc (0:ℝ) T) : u ∈ Icc (-T) T := ⟨by linarith [hu.1],hu.2⟩
  have hneg (u : ℝ) (hu : u ∈ Icc (0:ℝ) T) : -u ∈ Icc (-T) T := ⟨by linarith [hu.2],by linarith [hu.1]⟩
  by_cases ht0 : 0 ≤ t
  · exact distance_forward f K U hf T γ η
      (fun u hu => hγ u (hpos u hu)) (fun u hu => hη u (hpos u hu))
      (fun u hu => hγU u (hpos u hu)) (fun u hu => hηU u (hpos u hu)) t ⟨ht0,ht.2⟩
  have hfneg : LipschitzOnWith K (fun x => -f x) U := by
    rw [← one_mul K]
    exact LipschitzWith.id.neg.comp_lipschitzOnWith hf
  have hdγ (u : ℝ) (hu : u ∈ Icc (0:ℝ) T) :
      HasDerivAt (fun v => γ (-v)) (-f (γ (-u))) u := by
    simpa only [Function.comp_def,neg_one_smul] using
      (hγ (-u) (hneg u hu)).scomp u ((hasDerivAt_id u).neg)
  have hdη (u : ℝ) (hu : u ∈ Icc (0:ℝ) T) :
      HasDerivAt (fun v => η (-v)) (-f (η (-u))) u := by
    simpa only [Function.comp_def,neg_one_smul] using
      (hη (-u) (hneg u hu)).scomp u ((hasDerivAt_id u).neg)
  have h := distance_forward (fun x => -f x) K U hfneg T (fun u => γ (-u)) (fun u => η (-u))
    hdγ hdη (fun u hu => hγU (-u) (hneg u hu)) (fun u hu => hηU (-u) (hneg u hu))
    (-t) ⟨by linarith,by linarith [ht.1]⟩
  simpa only [neg_neg,neg_zero] using h

#print axioms distance_forward
#print axioms distance_window
end
end UnifiedTheory.Audit.KFCausalODEWindowStability

