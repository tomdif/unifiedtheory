/- The dressed family is total, and its span lies in an actual dense
domain for the ordered clock and longitudinal/first-transverse factors.
Other matter weights and charge averaging are not included. -/
import UnifiedTheory.Audit.KFCausalClockDressedActions
import UnifiedTheory.Audit.KFCausalWeightedProductTotality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockDressedDomain
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalCoupledProductDomain
open UnifiedTheory.Audit.KFCausalClockTrialWeights
open UnifiedTheory.Audit.KFCausalClockDressedProducts
open UnifiedTheory.Audit.KFCausalClockDressedActions
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalCoupledJointDomain
open UnifiedTheory.Audit.KFCausalWeightedProductTotality

theorem clockTrial_modulate (ε a : ℝ) (hε : 0 < ε) (p b : ℝ) :
    clockTrial ε a hε p b = modulate p (clockTrial ε a hε 0 b) := by
  funext q
  simp only [clockTrial,modulate,zero_mul,AddChar.map_zero_eq_one,Circle.coe_one,one_mul]
  ring

private theorem productState_congr_clock (ε : ℝ) (hε : 0 < ε) (g g' : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg : MemLp g 2) (hg' : MemLp g' 2) (hψ : MemLp ψ 2) (he : g=g') :
    productState ε hε g ψ hg hψ = productState ε hε g' ψ hg' hψ := by
  subst g'
  rfl

def dressedFamily (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (v : ℝ × SchwartzMap TailSpace ℂ) : Hilbert :=
  dressedState ε a v.1 hε ha v.2 (v.2.memLp 2 volume)

theorem weightedFamily_eq_dressed (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (v : ℝ × SchwartzMap TailSpace ℂ) :
    physicalFamily ε hε (clockTrial ε a hε 0 (1/2)) (clockTrial_half_memLp ε a hε ha 0) v =
      dressedFamily ε a hε ha v :=
  productState_congr_clock ε hε _ _ v.2
    (modulate_memLp _ (clockTrial_half_memLp ε a hε ha 0) v.1)
    (clockTrial_half_memLp ε a hε ha v.1) (v.2.memLp 2 volume) (clockTrial_modulate ε a hε v.1 (1/2)).symm

theorem dense_dressed_span (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (dressedFamily ε a hε ha))).topologicalClosure=⊤ := by
  have hd := dense_physical_span ε hε (clockTrial ε a hε 0 (1/2)) (clockTrial_half_memLp ε a hε ha 0)
    (clockTrial_ne_zero ε a hε 0 (1/2))
  have he : physicalFamily ε hε (clockTrial ε a hε 0 (1/2)) (clockTrial_half_memLp ε a hε ha 0) =
      dressedFamily ε a hε ha := funext (weightedFamily_eq_dressed ε a hε ha)
  rw [he] at hd
  exact hd

def preimageSpace (T : Hilbert →ₗ.[ℂ] Hilbert) (V : Submodule ℂ Hilbert) : Submodule ℂ Hilbert where
  carrier := {f | ∃ g : Hilbert, (f,g) ∈ T.graph ∧ g ∈ V}
  zero_mem' := ⟨0,T.graph.zero_mem,V.zero_mem⟩
  add_mem' := by
    rintro f₁ f₂ ⟨g₁,h₁,hv₁⟩ ⟨g₂,h₂,hv₂⟩
    exact ⟨g₁+g₂,T.graph.add_mem h₁ h₂,V.add_mem hv₁ hv₂⟩
  smul_mem' := by
    rintro c f ⟨g,hg,hv⟩
    exact ⟨c • g,T.graph.smul_mem c hg,V.smul_mem c hv⟩

theorem preimageSpace_conditions (T : Hilbert →ₗ.[ℂ] Hilbert) (V : Submodule ℂ Hilbert) (f : Hilbert) :
    f ∈ preimageSpace T V ↔ ∃ hf : f ∈ T.domain, T ⟨f,hf⟩ ∈ V := by
  constructor
  · rintro ⟨g,hg,hv⟩
    have hf := LinearPMap.mem_domain_of_mem_graph hg
    refine ⟨hf,?_⟩
    rw [T.mem_graph_snd_inj (T.mem_graph ⟨f,hf⟩) hg rfl]
    exact hv
  · rintro ⟨hf,hv⟩
    exact ⟨T ⟨f,hf⟩,T.mem_graph ⟨f,hf⟩,hv⟩

def orderedSpace (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : Submodule ℂ Hilbert :=
  (clockPower (1/2)).domain ⊓ preimageSpace (clockPower (-(1/2))) (jointSpace ε hε hbar)

theorem dressedFamily_mem_orderedSpace (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| < Real.pi*ε) (v : ℝ × SchwartzMap TailSpace ℂ) :
    dressedFamily ε a hε ha v ∈ orderedSpace ε hε hbar :=
  ⟨dressed_clock_domain ε a v.1 hε ha v.2 (v.2.memLp 2 volume),
    trialState ε a v.1 hε ha v.2 (v.2.memLp 2 volume),
    dressed_inverse_graph ε a v.1 hε ha v.2 (v.2.memLp 2 volume),
    trialFamily_mem_jointSpace ε a hbar hε ha hh v⟩

theorem orderedSpace_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| < Real.pi*ε) :
    (orderedSpace ε hε hbar).topologicalClosure=⊤ := by
  have hs : Submodule.span ℂ (Set.range (dressedFamily ε 1 hε zero_lt_one)) ≤ orderedSpace ε hε hbar := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,rfl⟩
    exact dressedFamily_mem_orderedSpace ε 1 hbar hε zero_lt_one hh v
  have hc := Submodule.topologicalClosure_mono hs
  rw [dense_dressed_span ε 1 hε zero_lt_one] at hc
  exact top_unique hc

theorem orderedSpace_conditions (ε hbar : ℝ) (hε : 0 < ε) (f : Hilbert) :
    f ∈ orderedSpace ε hε hbar ↔ f ∈ (clockPower (1/2)).domain ∧
      ∃ hf : f ∈ (clockPower (-(1/2))).domain, clockPower (-(1/2)) ⟨f,hf⟩ ∈ jointSpace ε hε hbar := by
  change (_ ∧ f ∈ preimageSpace _ _) ↔ _
  rw [preimageSpace_conditions]
  rfl

#print axioms clockTrial_modulate
#print axioms weightedFamily_eq_dressed
#print axioms dense_dressed_span
#print axioms preimageSpace_conditions
#print axioms dressedFamily_mem_orderedSpace
#print axioms orderedSpace_dense
#print axioms orderedSpace_conditions

end
end UnifiedTheory.Audit.KFCausalClockDressedDomain
