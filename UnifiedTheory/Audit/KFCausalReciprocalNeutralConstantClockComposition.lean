/- Actual pure-clock momentum graphs of the clock-half outputs of sourced
reciprocal packets with constant neutral polynomial. The graph is constructed
from the sourced Gaussian composition and reciprocal transport, then summed.
Complex sources may vary; no signed potential estimate is inferred here. -/
import UnifiedTheory.Audit.KFCausalPolynomialClockComposition
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSuperposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralConstantClockComposition
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorPureClockKinetic (correction)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalReciprocalSqueezeTransport (transport)
open KFCausalReciprocalGaussianDomain (baseWidth baseWidth_positive baseWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalNeutralExponentialProfiles (neutralSource)

private theorem input_one (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) :
    KFCausalVariableWidthPolynomialDomain.input ε a α β hε ha hα hβ hw C p b 4 1 =
      KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hw C p b := by
  apply Lp.ext
  filter_upwards [KFCausalVariableWidthPolynomialDomain.input_coe ε a α β hε ha hα hβ hw C p b 4 1,
    KFCausalClockFloorSourcedClockMomentum.state_coe ε a α β hε ha hα hβ hw C p b] with x hx hy
  rw [hx,hy]
  simp

theorem packet_clock_domain (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b : ℂ)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b 1 hb 0 ∈
      (pureMomentum ε hε h).domain := by
  let τ := Real.log w/2
  have hτ : 0 ≤ τ := div_nonneg (Real.log_nonneg hw) (by norm_num)
  let α := groundWidth h
  let β := baseWidth h τ
  have hα : 0 < α := groundWidth_positive h hh
  have hβ : 0 < β := baseWidth_positive h hh τ
  have hwidth : 32*β ≤ α := baseWidth_bound h hh τ hτ
  let d := neutralSource ((Real.exp (-τ):ℂ)*b)
  let k : ℂ := Real.exp (-τ/2)
  let f := KFCausalClockFloorSourcedClockMomentum.state ε a α β hε ha hα hβ hwidth C p d
  let g := KFCausalClockFloorSourcedClockMomentum.clockOutput ε a α β hε ha hα hβ hwidth C p d
  have he : KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b 1 =
      k • transport (-τ) f := by
    unfold KFCausalReciprocalNeutralPackets.state
    simp only [KFCausalReciprocalNeutralPackets.rescaledPolynomial,Polynomial.one_comp]
    rw [input_one]
  have hg0 : (f,g) ∈ (energyFactor ε hε h modelDirections pointField 0).graph :=
    KFCausalClockFloorSourcedClockMomentum.clockOutput_graph ε a α β hε ha hα hβ hwidth C p d
  have hg := (energyFactor ε hε h modelDirections pointField 0).graph.smul_mem k
    (KFCausalReciprocalSqueezeEnergy.factor_graph ε hε h (-τ) 0 f g hg0)
  simp only [KFCausalReciprocalSqueezeEnergy.factorScale,KFCausalReciprocalSqueezeEnergy.degree,
    Matrix.cons_val_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,one_smul] at hg
  have hout : KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b 1 hb 0 =
      k • transport (-τ) g :=
    (energyFactor ε hε h modelDirections pointField 0).mem_graph_snd_inj'
      (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw C p b 1 hb 0) hg he
  have hc := KFCausalPolynomialClockComposition.sourced_composition_graph
    ε a α β h hε ha hα hβ hwidth hh hb C p d
  have ht := (pureMomentum ε hε h).graph.smul_mem k
    (KFCausalReciprocalGaussianMomentum.pure_graph_transport ε hε h hh (-τ) _ _ hc)
  rw [hout]
  exact LinearPMap.mem_domain_of_mem_graph ht

theorem packet_clock_graph (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b : ℂ)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    (KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b 1 hb 0,
      KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw C p b 1 hb 0-
        correction ε hε h (KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b 1 hb 0)) ∈
      (pureMomentum ε hε h).graph := by
  let g := KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b 1 hb 0
  let k := KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw C p b 1 hb 0
  have hd : g ∈ (pureMomentum ε hε h).domain := packet_clock_domain ε a h w hε ha hh hw C p b hb
  let bg := (pureMomentum ε hε h) ⟨g,hd⟩
  have hbg : (g,bg) ∈ (pureMomentum ε hε h).graph := (pureMomentum ε hε h).mem_graph ⟨g,hd⟩
  have hc := KFCausalClockFloorPureClockClockResponse.commutator ε hε h hh _ g _ k bg
    (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw C p b 1 hb 0)
    (KFCausalReciprocalNeutralPackets.momentum_graph ε a h w hε ha hh hw C p b 1)
    (KFCausalReciprocalNeutralPackets.momentumOutput_graph ε a h w hε ha hh hw C p b 1 hb 0) hbg
  have he : bg=k-correction ε hε h g := by
    simpa only [sub_eq_add_neg,add_comm] using sub_eq_iff_eq_add.mp hc
  rw [he] at hbg
  exact hbg

theorem finite_clock_graph (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
    (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    (KFCausalReciprocalNeutralSuperposition.output n ε h a w p C b (fun _ => 1) hε ha hh hw hb 0,
      KFCausalReciprocalNeutralSuperposition.momentumOutput n ε h a w p C b (fun _ => 1) hε ha hh hw hb 0-
        correction ε hε h (KFCausalReciprocalNeutralSuperposition.output n ε h a w p C b
          (fun _ => 1) hε ha hh hw hb 0)) ∈ (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    packet_clock_graph ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) hb)
  simpa only [KFCausalReciprocalNeutralSuperposition.output,
    KFCausalReciprocalNeutralSuperposition.momentumOutput,← prod_mk_sum,Finset.sum_sub_distrib,map_sum] using hs

theorem finite_clock_domain (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
    (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    KFCausalReciprocalNeutralSuperposition.output n ε h a w p C b (fun _ => 1) hε ha hh hw hb 0 ∈
      (pureMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (finite_clock_graph n ε h a w p C b hε ha hh hw hb)

#print axioms packet_clock_domain
#print axioms packet_clock_graph
#print axioms finite_clock_graph
#print axioms finite_clock_domain
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralConstantClockComposition
