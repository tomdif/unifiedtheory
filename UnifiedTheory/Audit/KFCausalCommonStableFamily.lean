/- Select one approximation family for every initial state. Its initial-state
stability and its domain-data velocity budgets follow from verified estimates. -/
import UnifiedTheory.Audit.KFCausalCommonVelocityWitnesses
import UnifiedTheory.Audit.KFCausalStableTrajectoryNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCommonStableFamily
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem exists_stable_family (T : V →ₗ.[ℂ] V) (A : ℝ → ℝ → V →L[ℂ] V)
    (F S : ℝ → V →L[ℂ] V) (q ω ρ : ℝ → ℝ) (l r : ℝ)
    (hcommon : ∃ B κ : ℝ, 2 ≤ B ∧ 0 ≤ κ ∧
      (∀ b, B ≤ b → ∀ t ∈ Icc l r, q t < b ∧ 2*ω t ≤ b ∧ ρ t ≤ κ) ∧
      ∀ x y, (x,y) ∈ T.graph → ∃ M : ℝ, 0 ≤ M ∧ ∀ b, B ≤ b →
        ∃ w : ℝ → V, w l = x ∧ ContinuousOn w (Icc l r) ∧ ∀ t ∈ Icc l r,
          HasDerivWithinAt w (A b t (w t)) (Icc l r) t ∧ energy (F t) (S t (A b t (w t))) ≤ M)
    (hcont : ∀ b, 0 < b → (∀ t ∈ Icc l r, q t < b) → ContinuousOn (A b) (Icc l r))
    (hex : ∀ b, 0 < b → (∀ t ∈ Icc l r, q t < b) → ∀ x,
      ∃ w : ℝ → V, w l = x ∧ ContinuousOn w (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt w (A b t (w t)) (Icc l r) t)
    (henergy : ∀ b κ t, 0 < b → l ≤ t →
      (∀ z ∈ Icc l t, q z < b ∧ 2*ω z ≤ b ∧ ρ z ≤ κ) →
      ∀ w : ℝ → V, ContinuousOn w (Icc l t) →
      (∀ z ∈ Ioo l t, HasDerivAt w (A b z (w z)) z) →
      energy (F t) (S t (w t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l (w l)))
    (hnorm : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc l r, ∀ z, ‖z‖^2 ≤ K*energy (F t) (S t z)) :
    ∃ B κ L : ℝ, 2 ≤ B ∧ 0 ≤ κ ∧ 0 ≤ L ∧ ∃ w : ℕ → V → ℝ → V,
      (∀ n x, w n x l = x ∧ ContinuousOn (w n x) (Icc l r) ∧
        ∀ t ∈ Icc l r, HasDerivWithinAt (w n x) (A (B+n) t (w n x t)) (Icc l r) t) ∧
      (∀ n : ℕ, ∀ t ∈ Icc l r, q t < B+n ∧ 2*ω t ≤ B+n ∧ ρ t ≤ κ) ∧
      (∀ n x y t, t ∈ Icc l r → ‖w n x t-w n y t‖ ≤ L*‖x-y‖) ∧
      ∀ x y, (x,y) ∈ T.graph → ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ t ∈ Icc l r,
        energy (F t) (S t (A (B+n) t (w n x t))) ≤ M := by
  obtain ⟨B,κ,hB,hκ,hparams,hbudget⟩ := hcommon
  obtain ⟨K,hK,hnorm⟩ := hnorm
  have hBn (n : ℕ) : B ≤ B+n := le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hbpos (n : ℕ) : 0 < B+(n:ℝ) := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (hB.trans (hBn n))
  have hall (n : ℕ) (x : V) : ∃ w : ℝ → V, w l = x ∧ ContinuousOn w (Icc l r) ∧
      ∀ t ∈ Icc l r, HasDerivWithinAt w (A (B+n) t (w t)) (Icc l r) t :=
    hex (B+n) (hbpos n) (fun t ht => (hparams (B+n) (hBn n) t ht).1) x
  choose w hw using hall
  let L := K*Real.exp (κ*(r-l))*(‖F l‖*‖S l‖^2)+1
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨B,κ,L,hB,hκ,hL,w,hw,fun n => hparams (B+n) (hBn n),?_,?_⟩
  · intro n x y t ht
    have he := KFCausalStableTrajectoryNorm.difference_stability (A (B+n)) F S K κ l r hK hκ hnorm
      (KFCausalStableTrajectoryNorm.interval_energy_growth (A (B+n)) F S κ l r
        (fun z hz => henergy (B+n) κ z (hbpos n) hz.1
          (fun u hu => hparams (B+n) (hBn n) u ⟨hu.1,hu.2.trans hz.2⟩)))
      (w n x) (w n y) (hw n x).2.1 (hw n y).2.1 (hw n x).2.2 (hw n y).2.2 t ht
    simpa only [(hw n x).1,(hw n y).1] using he
  · intro x y hxy
    obtain ⟨M,hM,hv⟩ := hbudget x y hxy
    refine ⟨M,hM,?_⟩
    intro n t ht
    obtain ⟨v,hvi,hvc,hvv⟩ := hv (B+n) (hBn n)
    have heq := KFCausalResolventDomainTrajectories.solution_unique (A (B+n)) l r
      (hcont (B+n) (hbpos n) (fun z hz => (hparams (B+n) (hBn n) z hz).1))
      (w n x) v (hw n x).2.1 hvc (hw n x).2.2 (fun z hz => (hvv z hz).1)
      ((hw n x).1.trans hvi.symm)
    rw [heq t ht]
    exact (hvv t ht).2

#print axioms exists_stable_family
end
end UnifiedTheory.Audit.KFCausalCommonStableFamily
