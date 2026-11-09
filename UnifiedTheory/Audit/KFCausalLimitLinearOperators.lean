/- Linearity follows from uniqueness of the bounded approximate equations.
Uniform state limits and a common norm bound then define bounded operators. -/
import UnifiedTheory.Audit.KFCausalResolventDomainTrajectories
import UnifiedTheory.Audit.KFCausalDenseUniformStateLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalLimitLinearOperators
noncomputable section
open Set Filter Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem approximation_add (A : ℕ → ℝ → V →L[ℂ] V) (w : ℕ → V → ℝ → V) (l r : ℝ)
    (hA : ∀ n, ContinuousOn (A n) (Icc l r))
    (hw : ∀ n x, w n x l = x ∧ ContinuousOn (w n x) (Icc l r) ∧
      ∀ t ∈ Icc l r, HasDerivWithinAt (w n x) (A n t (w n x t)) (Icc l r) t) :
    ∀ n x y t, t ∈ Icc l r → w n (x+y) t = w n x t+w n y t := by
  intro n x y
  exact KFCausalResolventDomainTrajectories.solution_unique (A n) l r (hA n)
    (w n (x+y)) (fun t => w n x t+w n y t) (hw n (x+y)).2.1
    ((hw n x).2.1.add (hw n y).2.1) (hw n (x+y)).2.2
    (fun t ht => by simpa only [map_add] using ((hw n x).2.2 t ht).add ((hw n y).2.2 t ht))
    (by simp only [(hw n (x+y)).1,(hw n x).1,(hw n y).1])

theorem approximation_smul (A : ℕ → ℝ → V →L[ℂ] V) (w : ℕ → V → ℝ → V) (l r : ℝ)
    (hA : ∀ n, ContinuousOn (A n) (Icc l r))
    (hw : ∀ n x, w n x l = x ∧ ContinuousOn (w n x) (Icc l r) ∧
      ∀ t ∈ Icc l r, HasDerivWithinAt (w n x) (A n t (w n x t)) (Icc l r) t) :
    ∀ n (c : ℂ) x t, t ∈ Icc l r → w n (c • x) t = c • w n x t := by
  intro n c x
  exact KFCausalResolventDomainTrajectories.solution_unique (A n) l r (hA n)
    (w n (c • x)) (fun t => c • w n x t) (hw n (c • x)).2.1
    ((hw n x).2.1.const_smul c) (hw n (c • x)).2.2
    (fun t ht => by simpa only [map_smul] using ((hw n x).2.2 t ht).const_smul c)
    (by simp only [(hw n (c • x)).1,(hw n x).1])

omit [InnerProductSpace ℂ V] in
theorem limit_add (w : ℕ → V → ℝ → V) (u : V → ℝ → V) (I : Set ℝ)
    (hu : ∀ x, TendstoUniformlyOn (fun n => w n x) (u x) atTop I)
    (hadd : ∀ n x y t, t ∈ I → w n (x+y) t = w n x t+w n y t) :
    ∀ x y t, t ∈ I → u (x+y) t = u x t+u y t := by
  intro x y t ht
  apply tendsto_nhds_unique ((hu (x+y)).tendsto_at ht)
  have he : (fun n => w n (x+y) t) = (fun n => w n x t+w n y t) :=
    funext (fun n => hadd n x y t ht)
  rw [he]
  exact ((hu x).tendsto_at ht).add ((hu y).tendsto_at ht)

theorem limit_smul (w : ℕ → V → ℝ → V) (u : V → ℝ → V) (I : Set ℝ)
    (hu : ∀ x, TendstoUniformlyOn (fun n => w n x) (u x) atTop I)
    (hsmul : ∀ n (c : ℂ) x t, t ∈ I → w n (c • x) t = c • w n x t) :
    ∀ (c : ℂ) x t, t ∈ I → u (c • x) t = c • u x t := by
  intro c x t ht
  apply tendsto_nhds_unique ((hu (c • x)).tendsto_at ht)
  have he : (fun n => w n (c • x) t) = (fun n => c • w n x t) :=
    funext (fun n => hsmul n c x t ht)
  rw [he]
  exact ((hu x).tendsto_at ht).const_smul c

theorem bounded_operators (u : V → ℝ → V) (l r L : ℝ) (hlr : l ≤ r) (hL : 0 ≤ L)
    (hi : ∀ x, u x l = x)
    (hadd : ∀ x y t, t ∈ Icc l r → u (x+y) t = u x t+u y t)
    (hsmul : ∀ (c : ℂ) x t, t ∈ Icc l r → u (c • x) t = c • u x t)
    (hstable : ∀ x y t, t ∈ Icc l r → ‖u x t-u y t‖ ≤ L*‖x-y‖) :
    ∃ U : ℝ → V →L[ℂ] V, U l = 1 ∧ (∀ t ∈ Icc l r, ‖U t‖ ≤ L) ∧
      ∀ t ∈ Icc l r, ∀ x, U t x = u x t := by
  let f (t : Icc l r) : V →ₗ[ℂ] V := {
    toFun := fun x => u x t
    map_add' := fun x y => hadd x y t t.property
    map_smul' := fun c x => hsmul c x t t.property }
  have hb (t : Icc l r) (x : V) : ‖f t x‖ ≤ L*‖x‖ := by
    have hz : u 0 t = 0 := (f t).map_zero
    simpa only [hz,sub_zero] using hstable x 0 t t.property
  let U : ℝ → V →L[ℂ] V := fun t =>
    if ht : t ∈ Icc l r then (f ⟨t,ht⟩).mkContinuous L (hb ⟨t,ht⟩) else 0
  have heval (t : ℝ) (ht : t ∈ Icc l r) (x : V) : U t x = u x t := by
    simp only [U,dif_pos ht]
    rfl
  refine ⟨U,?_,?_,heval⟩
  · ext x
    change U l x = x
    rw [heval l ⟨le_rfl,hlr⟩ x]
    exact hi x
  · intro t ht
    simp only [U,dif_pos ht]
    exact (f ⟨t,ht⟩).mkContinuous_norm_le hL (hb ⟨t,ht⟩)

theorem exists_operator_family (A : ℕ → ℝ → V →L[ℂ] V) (w : ℕ → V → ℝ → V)
    (u : V → ℝ → V) (l r L : ℝ) (hlr : l ≤ r) (hL : 0 ≤ L)
    (hA : ∀ n, ContinuousOn (A n) (Icc l r))
    (hw : ∀ n x, w n x l = x ∧ ContinuousOn (w n x) (Icc l r) ∧
      ∀ t ∈ Icc l r, HasDerivWithinAt (w n x) (A n t (w n x t)) (Icc l r) t)
    (hi : ∀ x, u x l = x) (hc : ∀ x, ContinuousOn (u x) (Icc l r))
    (hu : ∀ x, TendstoUniformlyOn (fun n => w n x) (u x) atTop (Icc l r))
    (hstable : ∀ x y t, t ∈ Icc l r → ‖u x t-u y t‖ ≤ L*‖x-y‖) :
    ∃ U : ℝ → V →L[ℂ] V, U l = 1 ∧ (∀ t ∈ Icc l r, ‖U t‖ ≤ L) ∧
      ∀ x, ContinuousOn (fun t => U t x) (Icc l r) ∧
        TendstoUniformlyOn (fun n => w n x) (fun t => U t x) atTop (Icc l r) := by
  have hadd := limit_add w u (Icc l r) hu (approximation_add A w l r hA hw)
  have hsmul := limit_smul w u (Icc l r) hu (approximation_smul A w l r hA hw)
  obtain ⟨U,hUi,hUn,heval⟩ := bounded_operators u l r L hlr hL hi hadd hsmul hstable
  refine ⟨U,hUi,hUn,?_⟩
  intro x
  exact ⟨(hc x).congr (fun t ht => heval t ht x),
    (hu x).congr_right (fun t ht => (heval t ht x).symm)⟩

#print axioms approximation_add
#print axioms approximation_smul
#print axioms limit_add
#print axioms limit_smul
#print axioms bounded_operators
#print axioms exists_operator_family
end
end UnifiedTheory.Audit.KFCausalLimitLinearOperators
