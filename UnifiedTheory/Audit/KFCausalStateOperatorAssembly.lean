/- Package the actual approximate solutions and their limits as bounded
complex-linear state operators, with strong convergence uniform in time. -/
import UnifiedTheory.Audit.KFCausalLimitLinearOperators
import UnifiedTheory.Audit.KFCausalAllDataStateConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalStateOperatorAssembly
noncomputable section
open Set Filter Topology
open UnifiedTheory.Audit.KFCausalLimitLinearOperators
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem exists_state_operators (A : ℝ → ℝ → V →L[ℂ] V) (q : ℝ → ℝ) (l r : ℝ) (hlr : l ≤ r)
    (hcont : ∀ b, 0 < b → (∀ t ∈ Icc l r, q t < b) → ContinuousOn (A b) (Icc l r))
    (hfamily : ∃ B L : ℝ, 2 ≤ B ∧ 0 ≤ L ∧ ∃ w : ℕ → V → ℝ → V, ∃ u : V → ℝ → V,
      (∀ n x, w n x l = x ∧ ContinuousOn (w n x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n x) (A (B+n) t (w n x t)) (Icc l r) t) ∧
      (∀ n : ℕ, ∀ t ∈ Icc l r, q t < B+n) ∧
      (∀ x, u x l = x ∧ ContinuousOn (u x) (Icc l r) ∧
        TendstoUniformlyOn (fun n => w n x) (u x) atTop (Icc l r)) ∧
      (∀ n x y t, t ∈ Icc l r → ‖w n x t-w n y t‖ ≤ L*‖x-y‖) ∧
      ∀ x y t, t ∈ Icc l r → ‖u x t-u y t‖ ≤ L*‖x-y‖) :
    ∃ B L : ℝ, 2 ≤ B ∧ 0 ≤ L ∧ ∃ P : ℕ → ℝ → V →L[ℂ] V, ∃ U : ℝ → V →L[ℂ] V,
      (∀ n : ℕ, ∀ t ∈ Icc l r, q t < B+n) ∧
      (∀ n, P n l = 1) ∧ U l = 1 ∧
      (∀ n t, t ∈ Icc l r → ‖P n t‖ ≤ L) ∧ (∀ t ∈ Icc l r, ‖U t‖ ≤ L) ∧
      (∀ n x, ContinuousOn (fun t => P n t x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (fun z => P n z x) (A (B+n) t (P n t x)) (Icc l r) t) ∧
      ∀ x, ContinuousOn (fun t => U t x) (Icc l r) ∧
        TendstoUniformlyOn (fun n t => P n t x) (fun t => U t x) atTop (Icc l r) := by
  obtain ⟨B,L,hB,hL,w,u,hw,hpar,hu,hstable,hustable⟩ := hfamily
  have hA (n : ℕ) : ContinuousOn (A (B+n)) (Icc l r) :=
    hcont (B+n) (lt_of_lt_of_le (by norm_num : (0:ℝ)<2)
      (hB.trans (le_add_of_nonneg_right (Nat.cast_nonneg n)))) (hpar n)
  have hadd := approximation_add (fun n => A (B+n)) w l r hA hw
  have hsmul := approximation_smul (fun n => A (B+n)) w l r hA hw
  have hP (n : ℕ) : ∃ P : ℝ → V →L[ℂ] V,
      P l = 1 ∧ (∀ t ∈ Icc l r, ‖P t‖ ≤ L) ∧ ∀ t ∈ Icc l r, ∀ x, P t x = w n x t :=
    bounded_operators (w n) l r L hlr hL (fun x => (hw n x).1) (hadd n) (hsmul n) (hstable n)
  choose P hPi hPn hPeval using hP
  have hulim (x : V) := (hu x).2.2
  obtain ⟨U,hUi,hUn,hUeval⟩ := bounded_operators u l r L hlr hL (fun x => (hu x).1)
    (limit_add w u (Icc l r) hulim hadd) (limit_smul w u (Icc l r) hulim hsmul) hustable
  refine ⟨B,L,hB,hL,P,U,hpar,hPi,hUi,hPn,hUn,?_,?_⟩
  · intro n x
    refine ⟨((hw n x).2.1).congr (fun t ht => hPeval n t ht x),?_⟩
    intro t ht
    have hd := ((hw n x).2.2 t ht).congr_of_mem (fun z hz => hPeval n z hz x) ht
    exact hd.congr_deriv (congrArg (fun v => A (B+n) t v) (hPeval n t ht x).symm)
  · intro x
    refine ⟨(hu x).2.1.congr (fun t ht => hUeval t ht x),?_⟩
    exact ((hulim x).congr (Eventually.of_forall (fun n t ht => (hPeval n t ht x).symm))).congr_right
      (fun t ht => (hUeval t ht x).symm)

#print axioms exists_state_operators
end
end UnifiedTheory.Audit.KFCausalStateOperatorAssembly
