/- With strictly positive vacuum coupling, the retained Q output controls
the intermediate vector in both actual matter compositions. Thus the
ORIGINAL weighted joint graph is closed. No equality of separate closure
domains is assumed, and zero mass/quartic weights impose no extra domain.
The zero-vacuum case is not asserted here. -/
import UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph
import UnifiedTheory.Audit.KFCausalClockFloorJointEnergy

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumJointClosed
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalFiniteJointGraph (Output jointGraph)
open KFCausalOrderedOperatorComposition (composition composition_graph)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalClockFloorJointEnergy (initialEnergy closedEnergy)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorTrialMatter (matterFactor)
open KFCausalPhysicalField (physicalField physicalField_selfAdjoint)
open KFCausalTransverseFieldSquare (fieldSquare fieldSquare_selfAdjoint)

private theorem anchored_composition {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A Q : H →ₗ.[ℂ] H) (b c : ℂ) (hb : b ≠ 0)
    (f q z : H) (hq : (b • f,q) ∈ Q.graph) :
    (c • f,z) ∈ (composition A Q).graph ↔ ((c/b) • q,z) ∈ A.graph := by
  have hscaled : (c • f,(c/b) • q) ∈ Q.graph := by
    simpa only [Prod.smul_mk,smul_smul,div_mul_cancel₀ c hb] using
      Q.graph.smul_mem (c/b) hq
  rw [composition_graph]
  constructor
  · rintro ⟨y,hy,hz⟩
    have he : y=(c/b) • q := Q.mem_graph_snd_inj' hy hscaled rfl
    rwa [he] at hz
  · intro hz
    exact ⟨_,hscaled,hz⟩

private def firstIndex (i : Fin 5) : Fin 8 := ⟨i.val,lt_trans i.isLt (by decide)⟩

private def anchoredSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Fin 5 → H →ₗ.[ℂ] H) (Q A B : H →ₗ.[ℂ] H) (c : Fin 8 → ℂ) :
    Set (H × Output (Fin 8) H) :=
  {z | (∀ i, (c (firstIndex i) • z.1,z.2 (firstIndex i)) ∈ (S i).graph) ∧
    (c 7 • z.1,z.2 7) ∈ Q.graph ∧
    ((c 5/c 7) • z.2 7,z.2 5) ∈ A.graph ∧
    ((c 6/c 7) • z.2 7,z.2 6) ∈ B.graph}

private theorem anchoredSet_closed {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (S : Fin 5 → H →ₗ.[ℂ] H) (Q A B : H →ₗ.[ℂ] H)
    (c : Fin 8 → ℂ) (hS : ∀ i, (S i).IsClosed) (hQ : Q.IsClosed)
    (hA : A.IsClosed) (hB : B.IsClosed) : IsClosed (anchoredSet S Q A B c) := by
  have hc (i : Fin 8) : Continuous (fun z : H × Output (Fin 8) H => z.2 i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin 8 => H) i).comp continuous_snd
  have hs : IsClosed {z : H × Output (Fin 8) H |
      ∀ i, (c (firstIndex i) • z.1,z.2 (firstIndex i)) ∈ (S i).graph} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter (fun i => (hS i).preimage
      ((continuous_const.smul continuous_fst).prodMk (hc (firstIndex i))))
  have hq : IsClosed {z : H × Output (Fin 8) H | (c 7 • z.1,z.2 7) ∈ Q.graph} :=
    hQ.preimage ((continuous_const.smul continuous_fst).prodMk (hc 7))
  have ha : IsClosed {z : H × Output (Fin 8) H | ((c 5/c 7) • z.2 7,z.2 5) ∈ A.graph} :=
    hA.preimage ((continuous_const.smul (hc 7)).prodMk (hc 5))
  have hb : IsClosed {z : H × Output (Fin 8) H | ((c 6/c 7) • z.2 7,z.2 6) ∈ B.graph} :=
    hB.preimage ((continuous_const.smul (hc 7)).prodMk (hc 6))
  exact hs.inter (hq.inter (ha.inter hb))

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (v : Fin 4 → Transverse)
  (l : Transverse →L[ℝ] ℝ) (m g κ t : ℝ)
local notation "F" => energyFactor ε hε h v l
local notation "c" => energyWeight m g κ t
local notation "Q" => orderedExponential ε hε h

private theorem vacuum_weight_ne (hκ : 0 < κ) : c 7 ≠ 0 := by
  change ((Real.exp t*Real.sqrt κ : ℝ):ℂ) ≠ 0
  exact Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (Real.exp_ne_zero t) (Real.sqrt_pos.mpr hκ).ne')

private theorem joint_description (w : Fin 8 → ℂ) (hw : w 7 ≠ 0) :
    (jointGraph F w : Set (Hilbert × Output (Fin 8) Hilbert))=
      anchoredSet (fun i => F (firstIndex i)) Q (physicalField l) (fieldSquare l) w := by
  ext z
  constructor
  · intro hz
    have hq : (w 7 • z.1,z.2 7) ∈ (Q).graph := hz 7
    refine ⟨fun i => hz (firstIndex i),hq,?_,?_⟩
    · exact (anchored_composition (physicalField l) Q (w 7) (w 5)
        hw z.1 (z.2 7) (z.2 5) hq).mp (hz 5)
    · exact (anchored_composition (fieldSquare l) Q (w 7) (w 6)
        hw z.1 (z.2 7) (z.2 6) hq).mp (hz 6)
  · rintro ⟨hs,hq,ha,hb⟩ i
    fin_cases i
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 4
    · exact (anchored_composition (physicalField l) Q (w 7) (w 5)
        hw z.1 (z.2 7) (z.2 5) hq).mpr ha
    · exact (anchored_composition (fieldSquare l) Q (w 7) (w 6)
        hw z.1 (z.2 7) (z.2 6) hq).mpr hb
    · exact hq

theorem weighted_jointGraph_closed (w : Fin 8 → ℂ) (hw : w 7 ≠ 0) :
    IsClosed (jointGraph F w : Set (Hilbert × Output (Fin 8) Hilbert)) := by
  rw [joint_description ε hε h v l w hw]
  apply anchoredSet_closed
  · intro i
    fin_cases i
    · exact (KFCausalClockFloorClockHalf.clockHalf_selfAdjoint ε).isClosed
    · exact KFCausalClockFloorAntisymmetricGraph.clockMomentum_closed ε hε h (v 0)
    · exact KFCausalClockFloorAntisymmetricGraph.clockMomentum_closed ε hε h (v 1)
    · exact KFCausalClockFloorAntisymmetricGraph.clockMomentum_closed ε hε h (v 2)
    · exact KFCausalClockFloorAntisymmetricGraph.clockMomentum_closed ε hε h (v 3)
  · exact KFCausalClockFloorBoundedInverse.orderedExponential_closed ε hε h
  · exact (physicalField_selfAdjoint l).isClosed
  · exact (fieldSquare_selfAdjoint l).isClosed

theorem jointGraph_closed (hκ : 0 < κ) :
    IsClosed (jointGraph F c : Set (Hilbert × Output (Fin 8) Hilbert)) :=
  weighted_jointGraph_closed ε hε h v l c (vacuum_weight_ne m g κ t hκ)

theorem closedEnergy_eq_initialEnergy (hκ : 0 < κ) :
    closedEnergy ε hε h v l m g κ t=initialEnergy ε hε h v l m g κ t := by
  unfold closedEnergy initialEnergy KFCausalFiniteJointGraph.jointClosed KFCausalFiniteJointGraph.jointInitial
  rw [(jointGraph_closed ε hε h v l m g κ t hκ).submodule_topologicalClosure_eq]

theorem closedEnergy_graph_iff (hκ : 0 < κ) (f : Hilbert) (z : Output (Fin 8) Hilbert) :
    (f,z) ∈ (closedEnergy ε hε h v l m g κ t).graph ↔
      ∀ i, (c i • f,z i) ∈ (F i).graph := by
  rw [closedEnergy_eq_initialEnergy ε hε h v l m g κ t hκ,
    initialEnergy,KFCausalFiniteJointGraph.joint_initial_graph]
  rfl

theorem closedEnergy_domain_iff (hκ : 0 < κ) (f : Hilbert) :
    f ∈ (closedEnergy ε hε h v l m g κ t).domain ↔
      ∀ i, c i • f ∈ (F i).domain := by
  rw [closedEnergy_eq_initialEnergy ε hε h v l m g κ t hκ]
  exact KFCausalClockFloorJointEnergy.initialEnergy_domain ε hε h v l m g κ t f

#print axioms weighted_jointGraph_closed
#print axioms jointGraph_closed
#print axioms closedEnergy_eq_initialEnergy
#print axioms closedEnergy_graph_iff
#print axioms closedEnergy_domain_iff
end
end UnifiedTheory.Audit.KFCausalClockFloorPositiveVacuumJointClosed
