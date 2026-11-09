/- Finite bounded-tilt loss for the actual linked quartic circle energy.
Strict positivity is proved in the imported literal-integral module;
compactness is used only to choose a finite bound. -/
import UnifiedTheory.Audit.KFCausalAngularQuarticCircle

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularQuarticCircleCompact
noncomputable section
open Set
open KFCausalAngularQuarticCircle

private def parameterSet (Z : ℝ) : Set (ℝ×ℝ×ℝ) :=
  (Icc 0 Z ×ˢ (Icc (-1) 1 ×ˢ Icc (-1) 1)) ∩ {p | p.2.1^2+p.2.2^2=1}

private theorem parameterSet_compact (Z : ℝ) : IsCompact (parameterSet Z) :=
  (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
    (isClosed_eq (by fun_prop) continuous_const)

private theorem parameterSet_mem (Z z mu l : ℝ) (hz : z∈Icc 0 Z)
    (he : mu^2+l^2=1) : (z,mu,l)∈parameterSet Z := by
  have hm : mu∈Icc (-1:ℝ) 1 := ⟨by nlinarith [sq_nonneg l],by nlinarith [sq_nonneg l]⟩
  have hl : l∈Icc (-1:ℝ) 1 := ⟨by nlinarith [sq_nonneg mu],by nlinarith [sq_nonneg mu]⟩
  exact ⟨⟨hz,hm,hl⟩,he⟩

private theorem normalized_energy_pos (z mu l : ℝ) (he : mu^2+l^2=1) :
    0<energy z mu l := by
  apply energy_positive
  by_cases hm : mu=0
  · right
    intro hl
    simp [hm,hl] at he
  · exact Or.inl hm

theorem compact_normalized_loss (Z : ℝ) (hZ : 0≤Z) :
    ∃ C : ℝ, 0≤C ∧ ∀ z mu l : ℝ, z∈Icc 0 Z → mu^2+l^2=1 →
      0≤defect z mu l+C*energy z mu l := by
  let ratio : ℝ×ℝ×ℝ → ℝ := fun p => -defect p.1 p.2.1 p.2.2/energy p.1 p.2.1 p.2.2
  have hc : ContinuousOn ratio (parameterSet Z) :=
    defect_continuous.neg.continuousOn.div energy_continuous.continuousOn (by
      intro p hp
      exact ne_of_gt (normalized_energy_pos p.1 p.2.1 p.2.2 hp.2))
  have hne : (parameterSet Z).Nonempty :=
    ⟨(0,1,0),parameterSet_mem Z 0 1 0 ⟨le_rfl,hZ⟩ (by norm_num)⟩
  obtain ⟨p,hp,hmax⟩ := (parameterSet_compact Z).exists_isMaxOn hne hc
  refine ⟨max 0 (ratio p),le_max_left _ _,?_⟩
  intro z mu l hz he
  have hb : ratio (z,mu,l)≤max 0 (ratio p) :=
    (hmax (parameterSet_mem Z z mu l hz he)).trans (le_max_right _ _)
  have hpos := normalized_energy_pos z mu l he
  have hd := (div_le_iff₀ hpos).mp hb
  linarith

theorem compact_loss (Z : ℝ) (hZ : 0≤Z) :
    ∃ C : ℝ, 0≤C ∧ ∀ z mu l : ℝ, z∈Icc 0 Z →
      0≤defect z mu l+C*energy z mu l := by
  obtain ⟨C,hC,hbound⟩ := compact_normalized_loss Z hZ
  refine ⟨C,hC,?_⟩
  intro z mu l hz
  by_cases he : mu^2+l^2=0
  · have hm : mu=0 := by nlinarith [sq_nonneg l]
    have hl : l=0 := by nlinarith [sq_nonneg mu]
    simp [hm,hl,defect,defectIntegrand,fieldIntegrand,energy,integrand]
  · let r := Real.sqrt (mu^2+l^2)
    have hr : 0<r := Real.sqrt_pos.mpr (lt_of_le_of_ne (by positivity) (Ne.symm he))
    have hr0 : r≠0 := ne_of_gt hr
    have hr2 : r^2=mu^2+l^2 := Real.sq_sqrt (by positivity)
    have hn : (mu/r)^2+(l/r)^2=1 := by field_simp; nlinarith
    have hb := hbound z (mu/r) (l/r) hz hn
    have hm : r*(mu/r)=mu := by field_simp
    have hl : r*(l/r)=l := by field_simp
    have hE := energy_scale z (mu/r) (l/r) r
    have hD := defect_scale z (mu/r) (l/r) r
    rw [hm,hl] at hE hD
    rw [hE,hD]
    nlinarith [mul_nonneg (pow_nonneg hr.le 4) hb]

theorem compact_linked_loss (Z : ℝ) (hZ : 0≤Z) :
    ∃ C : ℝ, 0≤C ∧ ∀ z mu l : ℝ, z∈Icc 0 Z →
      0≤2*tilt z mu l-l*deriv (fun x => energy z mu x) l+C*energy z mu l := by
  obtain ⟨C,hC,hbound⟩ := compact_loss Z hZ
  refine ⟨C,hC,?_⟩
  intro z mu l hz
  rw [(field_derivative z mu l).deriv,← defect_eq]
  exact hbound z mu l hz

#print axioms compact_normalized_loss
#print axioms compact_loss
#print axioms compact_linked_loss
end
end UnifiedTheory.Audit.KFCausalAngularQuarticCircleCompact
