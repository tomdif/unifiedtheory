/- One approximation threshold works for all initial graph data.
The velocity budget may depend on the data, but not on the spectral parameter. -/
import UnifiedTheory.Audit.KFCausalUniformGraphTrajectories

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCommonVelocityWitnesses
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalWeightedMassEnergy (energy)
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem exists_common_witnesses (G : ℝ → V →ₗ.[ℂ] V) (A : ℝ → ℝ → V →L[ℂ] V)
    (R D F S : ℝ → V →L[ℂ] V) (q ω ρ : ℝ → ℝ) (lam l r : ℝ)
    (hpos : ∀ t x, 0 ≤ energy (F t) (S t x))
    (hparams : ∃ B κ : ℝ, 0 < B ∧ 0 ≤ κ ∧ ∀ b, B ≤ b → ∀ t ∈ Icc l r,
      q t < b ∧ 2*ω t ≤ b ∧ ρ t ≤ κ)
    (hgraphs : ∃ B κ : ℝ, 0 < B ∧ 0 ≤ κ ∧ ∀ b, B ≤ b → ∀ x y, (x,y) ∈ (G l).graph →
      ∃ w z : ℝ → V, w l = x ∧ z l = lam • x-y ∧
        ContinuousOn w (Icc l r) ∧ ContinuousOn z (Icc l r) ∧
        (∀ t ∈ Icc l r, w t = R t (z t)) ∧ ∀ t ∈ Icc l r,
          HasDerivWithinAt w (A b t (w t)) (Icc l r) t ∧
          HasDerivWithinAt z ((A b t-D t) (z t)) (Icc l r) t ∧
          (w t,lam • w t-z t) ∈ (G t).graph ∧
          energy (F t) (S t (w t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l x) ∧
          energy (F t) (S t (z t)) ≤ Real.exp (κ*(t-l))*energy (F l) (S l (lam • x-y)) ∧
          energy (F t) (S t (lam • w t-z t)) ≤ Real.exp (κ*(t-l))*
            (2*lam^2*energy (F l) (S l x)+2*energy (F l) (S l (lam • x-y))))
    (hvel : ∀ b, 0 < b → ∀ t ∈ Icc l r, q t < b → 2*ω t ≤ b →
      ∀ x y, (x,y) ∈ (G t).graph → energy (F t) (S t (A b t x)) ≤ 4*energy (F t) (S t y))
    : ∃ B κ : ℝ, 2 ≤ B ∧ 0 ≤ κ ∧
      (∀ b, B ≤ b → ∀ t ∈ Icc l r, q t < b ∧ 2*ω t ≤ b ∧ ρ t ≤ κ) ∧
      ∀ x y, (x,y) ∈ (G l).graph → ∃ M : ℝ, 0 ≤ M ∧ ∀ b, B ≤ b →
        ∃ w : ℝ → V, w l = x ∧ ContinuousOn w (Icc l r) ∧ ∀ t ∈ Icc l r,
          HasDerivWithinAt w (A b t (w t)) (Icc l r) t ∧
          energy (F t) (S t (A b t (w t))) ≤ M := by
  obtain ⟨Bp,κ,hBp,hκ,hpar⟩ := hparams
  obtain ⟨Bg,κg,hBg,hκg,hgraph⟩ := hgraphs
  let B := max 2 (max Bg Bp)
  have hB : 2 ≤ B := le_max_left _ _
  have hBpB : Bp ≤ B := (le_max_right Bg Bp).trans (le_max_right 2 (max Bg Bp))
  have hBgB : Bg ≤ B := (le_max_left Bg Bp).trans (le_max_right 2 (max Bg Bp))
  refine ⟨B,κ,hB,hκ,fun b hb => hpar b (hBpB.trans hb),?_⟩
  intro x y hxy
  let Q₀ := 2*lam^2*energy (F l) (S l x)+2*energy (F l) (S l (lam • x-y))
  let M := 4*Real.exp (κg*(r-l))*Q₀
  have hQ : 0 ≤ Q₀ := add_nonneg (mul_nonneg (by positivity) (hpos l x))
    (mul_nonneg (by norm_num) (hpos l (lam • x-y)))
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) hQ
  refine ⟨M,hM,?_⟩
  intro b hb
  obtain ⟨w,z,hi,_,hc,_,_,hw⟩ := hgraph b (hBgB.trans hb) x y hxy
  refine ⟨w,hi,hc,?_⟩
  intro t ht
  have hp := hpar b (hBpB.trans hb) t ht
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) (hB.trans hb)
  refine ⟨(hw t ht).1,?_⟩
  calc
    _ ≤ 4*energy (F t) (S t (lam • w t-z t)) := hvel b hbpos t ht hp.1 hp.2.1
      (w t) (lam • w t-z t) (hw t ht).2.2.1
    _ ≤ 4*(Real.exp (κg*(t-l))*Q₀) := mul_le_mul_of_nonneg_left (hw t ht).2.2.2.2.2 (by norm_num)
    _ ≤ 4*(Real.exp (κg*(r-l))*Q₀) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 l) hκg)) hQ) (by norm_num)
    _ = M := by dsimp only [M]; ring

#print axioms exists_common_witnesses
end
end UnifiedTheory.Audit.KFCausalCommonVelocityWitnesses
