/- The actual unbounded clock and longitudinal momentum have a dense
common composition domain. Their commutator has a unique bounded
extension, and its normalized canonical error is exactly epsilon/C. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectMomentum
import UnifiedTheory.Audit.KFCausalClockFloorClockOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumClockCommutator
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum
open UnifiedTheory.Audit.KFCausalClockFloorDefectMomentum

def commonDomain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Set Hilbert :=
  defectOperator ε hε '' ((longitudinalMomentum ε hε hbar).domain : Set Hilbert)

def commutatorExtension (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Hilbert →L[ℂ] Hilbert :=
  (-Complex.I*(hbar:ℂ)) • (ContinuousLinearMap.id ℂ Hilbert-defectOperator ε hε)

def normalizedCommutator (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Hilbert →L[ℂ] Hilbert :=
  (Complex.I/(hbar:ℂ)) • commutatorExtension ε hε hbar

theorem commonDomain_dense (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) :
    Dense (commonDomain ε hε hbar) :=
  (defectOperator_denseRange ε hε).dense_image (defectOperator ε hε).continuous
    (longitudinal_dense ε hε hbar)

/-- This is precisely the domain of the composition L C. The other
composition C L is also defined there, as proved below. -/
theorem commonDomain_iff (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f : Hilbert) :
    f ∈ commonDomain ε hε hbar ↔ ∃ cf : Hilbert,
      (f,cf) ∈ (clockOperator ε hε).graph ∧ cf ∈ (longitudinalMomentum ε hε hbar).domain := by
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact ⟨(ε:ℂ) • g,clock_defect_graph ε hε g,
      (longitudinalMomentum ε hε hbar).domain.smul_mem (ε:ℂ) hg⟩
  · rintro ⟨cf,hc,hl⟩
    refine ⟨(ε:ℂ)⁻¹ • cf,(longitudinalMomentum ε hε hbar).domain.smul_mem _ hl,?_⟩
    rw [map_smul,defect_clock ε hε f cf hc,smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hε.ne'),one_smul]

theorem commonDomain_graphs (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (f : Hilbert)
    (hf : f ∈ commonDomain ε hε hbar) :
    ∃ cf lf lcf clf : Hilbert,
      (f,cf) ∈ (clockOperator ε hε).graph ∧
      (f,lf) ∈ (longitudinalMomentum ε hε hbar).graph ∧
      (cf,lcf) ∈ (longitudinalMomentum ε hε hbar).graph ∧
      (lf,clf) ∈ (clockOperator ε hε).graph ∧
      lcf-clf = commutatorExtension ε hε hbar f := by
  rcases hf with ⟨g,hg,rfl⟩
  let D := defectOperator ε hε
  let L := longitudinalMomentum ε hε hbar
  let lg := L ⟨g,hg⟩
  let k : ℂ := Complex.I*(hbar:ℂ)/(ε:ℂ)
  have hk : (ε:ℂ)*k = Complex.I*(hbar:ℂ) := by
    have hn : (ε:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
    dsimp [k]
    field_simp
  have hl : (D g,D lg+k • D (D (g-D g))) ∈ L.graph :=
    defect_momentum_graph ε hε hbar g lg (L.mem_graph ⟨g,hg⟩)
  have hlc : ((ε:ℂ) • g,(ε:ℂ) • lg) ∈ L.graph :=
    L.graph.smul_mem (ε:ℂ) (L.mem_graph ⟨g,hg⟩)
  have hcl : (D lg+k • D (D (g-D g)),
      (ε:ℂ) • lg+(Complex.I*(hbar:ℂ)) • D (g-D g)) ∈ (clockOperator ε hε).graph := by
    have hh := clock_defect_graph ε hε (lg+k • D (g-D g))
    change (D (lg+k • D (g-D g)),(ε:ℂ) • (lg+k • D (g-D g))) ∈ _ at hh
    simpa only [map_add,map_smul,smul_add,smul_smul,hk] using hh
  refine ⟨(ε:ℂ) • g,D lg+k • D (D (g-D g)),(ε:ℂ) • lg,
    (ε:ℂ) • lg+(Complex.I*(hbar:ℂ)) • D (g-D g),
    clock_defect_graph ε hε g,hl,hlc,hcl,?_⟩
  change (ε:ℂ) • lg-((ε:ℂ) • lg+(Complex.I*(hbar:ℂ)) • D (g-D g)) =
    (-Complex.I*(hbar:ℂ)) • (D g-D (D g))
  rw [map_sub,neg_mul,neg_smul]
  abel

/-- Equality for actual products of the unbounded operators, with all
four graph conditions explicit. -/
theorem commutator_graph (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f cf lf lcf clf : Hilbert)
    (hc : (f,cf) ∈ (clockOperator ε hε).graph)
    (hl : (f,lf) ∈ (longitudinalMomentum ε hε hbar).graph)
    (hlc : (cf,lcf) ∈ (longitudinalMomentum ε hε hbar).graph)
    (hcl : (lf,clf) ∈ (clockOperator ε hε).graph) :
    lcf-clf = commutatorExtension ε hε hbar f := by
  have hf := (commonDomain_iff ε hε hbar f).mpr
    ⟨cf,hc,LinearPMap.mem_domain_of_mem_graph hlc⟩
  obtain ⟨cf',lf',lcf',clf',hc',hl',hlc',hcl',he⟩ := commonDomain_graphs ε hε hbar f hf
  have ec : cf' = cf := (clockOperator ε hε).mem_graph_snd_inj' hc' hc rfl
  have el : lf' = lf := (longitudinalMomentum ε hε hbar).mem_graph_snd_inj' hl' hl rfl
  subst cf'
  subst lf'
  have elc : lcf' = lcf := (longitudinalMomentum ε hε hbar).mem_graph_snd_inj' hlc' hlc rfl
  have ecl : clf' = clf := (clockOperator ε hε).mem_graph_snd_inj' hcl' hcl rfl
  simpa only [elc,ecl] using he

theorem commutatorExtension_unique (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (B : Hilbert →L[ℂ] Hilbert)
    (hB : ∀ f cf lf lcf clf : Hilbert,
      (f,cf) ∈ (clockOperator ε hε).graph →
      (f,lf) ∈ (longitudinalMomentum ε hε hbar).graph →
      (cf,lcf) ∈ (longitudinalMomentum ε hε hbar).graph →
      (lf,clf) ∈ (clockOperator ε hε).graph → B f = lcf-clf) :
    B = commutatorExtension ε hε hbar := by
  have he : (B : Hilbert → Hilbert) = commutatorExtension ε hε hbar :=
    Continuous.ext_on (commonDomain_dense ε hε hbar) B.continuous
      (commutatorExtension ε hε hbar).continuous (by
        intro f hf
        obtain ⟨cf,lf,lcf,clf,hc,hl,hlc,hcl,hh⟩ := commonDomain_graphs ε hε hbar f hf
        exact (hB f cf lf lcf clf hc hl hlc hcl).trans hh)
  exact DFunLike.coe_injective he

theorem normalizedCommutator_eq (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) :
    normalizedCommutator ε hε hbar = ContinuousLinearMap.id ℂ Hilbert-defectOperator ε hε := by
  unfold normalizedCommutator commutatorExtension
  rw [smul_smul]
  have he : (Complex.I/(hbar:ℂ))*(-Complex.I*(hbar:ℂ)) = 1 := by
    have hn : (hbar:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
    field_simp
    simp [Complex.I_sq]
  rw [he,one_smul]

theorem normalizedCommutator_error (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) :
    ContinuousLinearMap.id ℂ Hilbert-normalizedCommutator ε hε hbar = defectOperator ε hε := by
  rw [normalizedCommutator_eq ε hε hbar hh]
  abel

theorem no_exact_canonical_state (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
    (f : Hilbert) (hf : f ≠ 0) : normalizedCommutator ε hε hbar f ≠ f := by
  intro he
  apply defectOperator_ne_zero ε hε f hf
  have hd := congrArg (fun B : Hilbert →L[ℂ] Hilbert => B f)
    (normalizedCommutator_error ε hε hbar hh)
  change f-normalizedCommutator ε hε hbar f = defectOperator ε hε f at hd
  rw [he,sub_self] at hd
  exact hd.symm

theorem normalizedCommutator_error_apply (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
    (f : Hilbert) : f-normalizedCommutator ε hε hbar f = defectOperator ε hε f :=
  congrArg (fun B : Hilbert →L[ℂ] Hilbert => B f) (normalizedCommutator_error ε hε hbar hh)

#print axioms commonDomain_dense
#print axioms commonDomain_iff
#print axioms commonDomain_graphs
#print axioms commutator_graph
#print axioms commutatorExtension_unique
#print axioms normalizedCommutator_eq
#print axioms normalizedCommutator_error
#print axioms no_exact_canonical_state
#print axioms normalizedCommutator_error_apply

end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumClockCommutator
