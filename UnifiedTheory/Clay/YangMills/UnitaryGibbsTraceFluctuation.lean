/- Quantitative ordinary real-trace fluctuations for actual compact Gibbs
laws on U(d). The action is only assumed entrywise Lipschitz. No reflected
boundary-response or continuum lower bound is asserted. -/
import UnifiedTheory.Clay.YangMills.UnitaryHaarCaps
import UnifiedTheory.Clay.YangMills.UnitaryTraceLocalOscillation
import UnifiedTheory.Clay.YangMills.LocalizedGibbsFluctuation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.UnitaryGibbsTraceFluctuation
noncomputable section
open MeasureTheory Matrix RegulatedGauge UnitaryHaarCaps UnitaryHaarNeighborhood
open LocalizedGibbsFluctuation CompactGibbsContinuity

variable (d : Type*) [Fintype d] [DecidableEq d] [Nonempty d]

/-- The small-cap lower bound is uniform in the center and in the location
of the global minimum. Only the action's local Lipschitz constant enters. -/
theorem variance_lower (S : Matrix.unitaryGroup d ℂ → ℝ) (hS : Continuous S)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ A B : Matrix.unitaryGroup d ℂ, ∀ r : ℝ, 0 ≤ r →
      (∀ i j, ‖A i j-B i j‖ ≤ r) → |S A-S B| ≤ L*r)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (K : ℕ) (hK : 0 < K)
    (hsmall : (Fintype.card d : ℝ)^2*entryRadius d K ≤ t^2/8) (center : ℂ) :
    massLower d K * Real.exp (-(L*((Fintype.card d : ℝ)*entryRadius d K +
      4*(Fintype.card d : ℝ)*t))) * (t^2/8)^2 ≤
      ∫ U, ‖realTrace d U-center‖^2 ∂law (compactHaar (Matrix.unitaryGroup d ℂ)) S := by
  obtain ⟨A,_,hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (Matrix.unitaryGroup d ℂ)).Nonempty) hS.continuousOn
  obtain ⟨B,hBA,hsep⟩ := UnitaryTraceLocalOscillation.exists_nearby A t ht ht1
  have hr : 0 ≤ (Fintype.card d : ℝ)*entryRadius d K := by
    unfold entryRadius
    positivity
  have hb : 0 ≤ 4*(Fintype.card d : ℝ)*t := by positivity
  have hlocal (U : Matrix.unitaryGroup d ℂ) (hU : U ∈ cap d A K) :
      S U ≤ S A + L*((Fintype.card d : ℝ)*entryRadius d K + 4*(Fintype.card d : ℝ)*t) := by
    have hh := (le_abs_self (S U-S A)).trans
      (hLip U A _ hr (cap_entry_bound d A U K hU))
    have hz := mul_nonneg hL hb
    nlinarith
  have hlocalB (U : Matrix.unitaryGroup d ℂ) (hU : U ∈ cap d B K) :
      S U ≤ S A + L*((Fintype.card d : ℝ)*entryRadius d K + 4*(Fintype.card d : ℝ)*t) := by
    have he (i j : d) : ‖U i j-A i j‖ ≤
        (Fintype.card d : ℝ)*entryRadius d K + 4*(Fintype.card d : ℝ)*t :=
      (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        (add_le_add (cap_entry_bound d B U K hU i j) (hBA i j))
    have hh := (le_abs_self (S U-S A)).trans (hLip U A _ (add_nonneg hr hb) he)
    linarith
  apply two_caps_lower (compactHaar (Matrix.unitaryGroup d ℂ)) S hS (S A)
    (L*((Fintype.card d : ℝ)*entryRadius d K + 4*(Fintype.card d : ℝ)*t))
    (fun U => hmin (Set.mem_univ U)) (cap d A K) (cap d B K)
    (cap_measurable d A K) (cap_measurable d B K) hlocal hlocalB
    (realTrace d) (realTrace_continuous d) (realTrace d A) (realTrace d B)
    (t^2/8) (by positivity)
  · change 4*(t^2/8) ≤ ‖(((trace (A : Matrix d d ℂ)).re : ℂ)-
      ((trace (B : Matrix d d ℂ)).re : ℂ))‖
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    linarith
  · intro U hU
    exact (cap_trace_bound d A U K hU).trans hsmall
  · intro U hU
    exact (cap_trace_bound d B U K hU).trans hsmall
  · exact cap_mass_lower d A K hK
  · exact cap_mass_lower d B K hK

def gridSize (k : ℕ) : ℕ := 16*(Fintype.card d)^3*k^2

def polynomialFloor (k : ℕ) : ℝ :=
  massLower d (gridSize d k) * Real.exp (-(4*(Fintype.card d : ℝ)+1)) *
    ((1/(k : ℝ))^2/8)^2

theorem polynomialFloor_pos (k : ℕ) (hk : 0 < k) : 0 < polynomialFloor d k := by
  unfold polynomialFloor
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  exact mul_pos (mul_pos (massLower_pos d _) (Real.exp_pos _)) (by positivity)

/-- An explicit polynomial floor in any integer upper bound for the action's
Lipschitz constant. In fixed dimension the grid has O(k^2) cells per coordinate. -/
theorem polynomial_lower (S : Matrix.unitaryGroup d ℂ → ℝ) (hS : Continuous S)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ A B : Matrix.unitaryGroup d ℂ, ∀ r : ℝ, 0 ≤ r →
      (∀ i j, ‖A i j-B i j‖ ≤ r) → |S A-S B| ≤ L*r)
    (k : ℕ) (hk : 0 < k) (hLk : L ≤ k) (center : ℂ) :
    polynomialFloor d k ≤
      ∫ U, ‖realTrace d U-center‖^2 ∂law (compactHaar (Matrix.unitaryGroup d ℂ)) S := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  have hd1 : (1 : ℝ) ≤ Fintype.card d := by exact_mod_cast Fintype.card_pos
  have hg : 0 < gridSize d k := by unfold gridSize; positivity
  have ht : 0 < 1/(k : ℝ) := by positivity
  have ht1 : 1/(k : ℝ) ≤ 1 := (div_le_one hk').mpr hk1
  have he : (Fintype.card d : ℝ)^2*entryRadius d (gridSize d k) =
      (1/(k : ℝ))^2/8 := by
    unfold entryRadius gridSize
    push_cast
    field_simp
    <;> ring
  have hr : 0 ≤ (Fintype.card d : ℝ)*entryRadius d (gridSize d k) := by
    unfold entryRadius
    positivity
  have hrad : (Fintype.card d : ℝ)*entryRadius d (gridSize d k) ≤ 1/(k : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hd1 hr
    have ht2 : (1/(k : ℝ))^2 ≤ 1/(k : ℝ) := by nlinarith
    nlinarith [he]
  have hC : L*((Fintype.card d : ℝ)*entryRadius d (gridSize d k) +
      4*(Fintype.card d : ℝ)*(1/(k : ℝ))) ≤ 4*(Fintype.card d : ℝ)+1 := by
    calc
      _ ≤ (k : ℝ)*((1/(k : ℝ))+4*(Fintype.card d : ℝ)*(1/(k : ℝ))) :=
        mul_le_mul hLk (add_le_add hrad le_rfl) (by positivity) (by positivity)
      _ = _ := by field_simp; ring
  have hh := variance_lower d S hS L hL hLip (1/(k : ℝ)) ht ht1 (gridSize d k) hg he.le center
  apply le_trans _ hh
  unfold polynomialFloor
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (neg_le_neg hC)) (massLower_pos d _).le

end
end UnifiedTheory.Clay.YangMills.UnitaryGibbsTraceFluctuation
