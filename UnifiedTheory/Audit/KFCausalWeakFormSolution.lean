/- A class of weak form solutions closed under complex linear combinations.
The class records local bounds and the scalar weak differential equation,
not conservation, uniqueness, or a representation by cutoff limits. -/
import UnifiedTheory.Audit.KFCausalWeakMassConservation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalWeakFormSolution
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalWeakMassConservation

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure Solution (J : E →L[ℂ] H) (A : ℝ → E →L[ℂ] E) where
  state : ℝ → E
  radius : ℝ → ℝ
  slopeBound : ℝ → ℝ
  slopeBound_nonneg : ∀ T, 0 ≤ slopeBound T
  state_bound : ∀ T z, 0 ≤ T → |z| ≤ T → ‖state z‖ ≤ radius T
  slope_bound : ∀ T z, 0 ≤ T → |z| ≤ T → ‖A z (state z)‖ ≤ slopeBound T
  slope_weak_continuous : ∀ y, Continuous (fun z => inner ℂ (A z (state z)) y)
  mass_lipschitz : ∀ T x y, 0 ≤ T → |x| ≤ T → |y| ≤ T →
    ‖gram J (state y)-gram J (state x)‖ ≤ slopeBound T*|y-x|
  equation : ∀ z y, HasDerivAt (fun t => inner ℂ (gram J (state t)) y)
    (inner ℂ (A z (state z)) y) z

variable {J : E →L[ℂ] H} {A : ℝ → E →L[ℂ] E}

def add (U V : Solution J A) : Solution J A where
  state z := U.state z+V.state z
  radius T := U.radius T+V.radius T
  slopeBound T := U.slopeBound T+V.slopeBound T
  slopeBound_nonneg T := add_nonneg (U.slopeBound_nonneg T) (V.slopeBound_nonneg T)
  state_bound T z hT hz := (norm_add_le _ _).trans
    (add_le_add (U.state_bound T z hT hz) (V.state_bound T z hT hz))
  slope_bound T z hT hz := by
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (U.slope_bound T z hT hz) (V.slope_bound T z hT hz))
  slope_weak_continuous y := by
    simpa only [map_add,inner_add_left] using (U.slope_weak_continuous y).add (V.slope_weak_continuous y)
  mass_lipschitz T x y hT hx hy := by
    have he : gram J (U.state y+V.state y)-gram J (U.state x+V.state x) =
        (gram J (U.state y)-gram J (U.state x))+(gram J (V.state y)-gram J (V.state x)) := by
      simp only [map_add]
      abel
    rw [he]
    apply (norm_add_le _ _).trans
    simpa only [add_mul] using add_le_add (U.mass_lipschitz T x y hT hx hy) (V.mass_lipschitz T x y hT hx hy)
  equation z y := by
    simpa only [map_add,inner_add_left] using (U.equation z y).add (V.equation z y)

def smul (c : ℂ) (U : Solution J A) : Solution J A where
  state z := c • U.state z
  radius T := ‖c‖*U.radius T
  slopeBound T := ‖c‖*U.slopeBound T
  slopeBound_nonneg T := mul_nonneg (norm_nonneg c) (U.slopeBound_nonneg T)
  state_bound T z hT hz := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (U.state_bound T z hT hz) (norm_nonneg c)
  slope_bound T z hT hz := by
    rw [map_smul,norm_smul]
    exact mul_le_mul_of_nonneg_left (U.slope_bound T z hT hz) (norm_nonneg c)
  slope_weak_continuous y := by
    simpa only [map_smul,inner_smul_left] using
      (continuous_const (y := starRingEnd ℂ c)).mul (U.slope_weak_continuous y)
  mass_lipschitz T x y hT hx hy := by
    rw [map_smul,map_smul,← smul_sub,norm_smul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (U.mass_lipschitz T x y hT hx hy) (norm_nonneg c)
  equation z y := by
    simpa only [map_smul,inner_smul_left] using (U.equation z y).const_mul (starRingEnd ℂ c)

def sub (U V : Solution J A) : Solution J A := add U (smul (-1) V)

theorem sub_state (U V : Solution J A) (t : ℝ) : (sub U V).state t = U.state t-V.state t := by
  simp only [sub,add,smul,neg_one_smul,sub_eq_add_neg]

theorem norm_square_conserved (hj : Function.Injective J)
    (hA : ∀ z x, (inner ℂ (A z x) x).re = 0) (U : Solution J A)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0)) (s t : ℝ) :
    ‖J (U.state t)‖^2 = ‖J (U.state s)‖^2 :=
  KFCausalWeakMassConservation.norm_square_conserved J hj U.state (fun z => A z (U.state z))
    U.radius U.slopeBound U.slopeBound_nonneg U.state_bound U.slope_bound U.slope_weak_continuous
    U.mass_lipschitz U.equation (fun z => hA z (U.state z)) δ hδ hlim s t

theorem unique (hj : Function.Injective J)
    (hA : ∀ z x, (inner ℂ (A z x) x).re = 0) (U V : Solution J A)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hlim : Tendsto δ atTop (𝓝 0))
    (s : ℝ) (hi : U.state s = V.state s) : U.state = V.state := by
  funext t
  apply hj
  have hh := norm_square_conserved hj hA (sub U V) δ hδ hlim s t
  simp only [sub_state,hi,sub_self,map_zero,norm_zero,zero_pow (by norm_num : 2 ≠ 0)] at hh
  have hz := sq_eq_zero_iff.mp hh
  exact sub_eq_zero.mp (by simpa only [map_sub] using norm_eq_zero.mp hz)

#print axioms add
#print axioms smul
#print axioms norm_square_conserved
#print axioms unique

end
end UnifiedTheory.Audit.KFCausalWeakFormSolution
