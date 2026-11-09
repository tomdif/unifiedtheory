/- Continuity and boundedness of the actual displacement-orbit sources.
Bounds here are at fixed nonzero hbar; they do not assert semiclassical
uniformity. Periodicity supplies a finite source bound on the whole orbit. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalChargeModulationFlow
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds (sourceSize)

private theorem u_apply (h : ℝ) (q : Joint 2 4) (i : Fin 2) :
    uParameter h q i = -((momentumScale h)⁻¹*q (.inl i)) := rfl
private theorem v_apply (h : ℝ) (k : Joint 2 4) (i : Fin 2) :
    vParameter h k i = momentumScale h*k (.inl i) := rfl
private theorem r_apply (h : ℝ) (k : Joint 2 4) (i : Fin 4) : rParameter h k i = k (.inr i) := rfl
private theorem w_apply (h : ℝ) (q : Joint 2 4) (i : Fin 4) : wParameter h q i = q (.inr i) := rfl

theorem amplitude_continuous (h : ℝ) :
    Continuous (fun z : Joint 2 4 × Joint 2 4 => amplitude h z.1 z.2) := by
  have hq (i : Fin 2 ⊕ Fin 4) : Continuous (fun z : Joint 2 4 × Joint 2 4 => z.1 i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) i).comp continuous_fst
  have hk (i : Fin 2 ⊕ Fin 4) : Continuous (fun z : Joint 2 4 × Joint 2 4 => z.2 i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) i).comp continuous_snd
  unfold amplitude constant KFCausalFourierTranslation.phase
  simp only [Real.fourierChar_apply,PiLp.inner_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,
    add_zero,RCLike.inner_apply,conj_trivial,u_apply,v_apply,w_apply]
  fun_prop

theorem clockFrequency_continuous (h : ℝ) : Continuous (clockFrequency h) := by
  change Continuous (fun k : Joint 2 4 => 2*Real.pi*k (.inr 0))
  fun_prop

theorem source_continuous (h : ℝ) :
    Continuous (fun z : Joint 2 4 × Joint 2 4 => source h z.1 z.2) := by
  have hq (i : Fin 2 ⊕ Fin 4) : Continuous (fun z : Joint 2 4 × Joint 2 4 => z.1 i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) i).comp continuous_fst
  have hk (i : Fin 2 ⊕ Fin 4) : Continuous (fun z : Joint 2 4 × Joint 2 4 => z.2 i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) i).comp continuous_snd
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [source,coefficients] <;>
    simp only [u_apply,v_apply,r_apply,w_apply] <;> fun_prop

theorem parameter_curve_continuous (k : Joint 2 4) : Continuous (fun θ => parameter θ k) :=
  parameter_continuous.comp (f := fun θ : ℝ => (θ,k)) (continuous_id.prodMk continuous_const)

theorem amplitude_curve_continuous (h : ℝ) (q k : Joint 2 4) :
    Continuous (fun θ => amplitude h (parameter θ q) (parameter θ k)) :=
  (amplitude_continuous h).comp (f := fun θ : ℝ => (parameter θ q,parameter θ k))
    ((parameter_curve_continuous q).prodMk (parameter_curve_continuous k))

theorem source_curve_continuous (h : ℝ) (q k : Joint 2 4) :
    Continuous (fun θ => source h (parameter θ q) (parameter θ k)) :=
  (source_continuous h).comp (f := fun θ : ℝ => (parameter θ q,parameter θ k))
    ((parameter_curve_continuous q).prodMk (parameter_curve_continuous k))

theorem clockFrequency_parameter (h θ : ℝ) (k : Joint 2 4) :
    clockFrequency h (parameter θ k) = clockFrequency h k := rfl

theorem source_orbit_bound (h : ℝ) (q k : Joint 2 4) :
    ∃ B : ℝ, ∀ θ, sourceSize (source h (parameter θ q) (parameter θ k)) ≤ B := by
  have hc : Continuous (fun θ => sourceSize (source h (parameter θ q) (parameter θ k))) := by
    have hs := source_curve_continuous h q k
    unfold sourceSize
    fun_prop
  have hp : Function.Periodic (fun θ => sourceSize (source h (parameter θ q) (parameter θ k)))
      (2*Real.pi) := by
    intro θ
    dsimp only
    rw [parameter_period,parameter_period]
  obtain ⟨B,hB⟩ := (hp.compact_of_continuous (by positivity) hc).bddAbove
  exact ⟨B,fun θ => hB ⟨θ,rfl⟩⟩

#print axioms amplitude_continuous
#print axioms clockFrequency_continuous
#print axioms source_continuous
#print axioms parameter_curve_continuous
#print axioms amplitude_curve_continuous
#print axioms source_curve_continuous
#print axioms clockFrequency_parameter
#print axioms source_orbit_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds
