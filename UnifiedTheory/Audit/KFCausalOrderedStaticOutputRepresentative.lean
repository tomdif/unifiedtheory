/- The original Q(T psi) output of a finite sourced packet has an explicit
common-coordinate representative. The two radial moments and neutral
second derivative remain linked to the same original packet. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialClockMomentRepresentative
import UnifiedTheory.Audit.KFCausalFiniteOrderedStaticOutput
import UnifiedTheory.Audit.KFCausalFiniteLpRepresentatives

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalOrderedStaticOutputRepresentative
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint split)
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalNeutralLinePackets (step)
open KFCausalIndependentRadialMomentInput (numerator left right)
open KFCausalIndependentRadialHolomorphicQuotient (baselineVector)
open KFCausalGaussianHolomorphicClockWeight (clockPower)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalClockFloorOrderedStaticPacket (combination orderedOutput)
open KFCausalIndependentRadialClockMomentRepresentative (clockMomentOutput_clockMixed)

def profile (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (q : ℂ) (x : Joint 2 4) : ℂ :=
  (1/2:ℂ)*clockPower ε false q*numerator ε a (groundWidth h) wL wR (momentumScale h) C p b P 0 0 q x +
  (2*(h:ℂ)^2*(groundWidth h:ℂ)*(1/wL:ℝ)+2*(h:ℂ)^2*(groundWidth h:ℂ)*(wR:ℂ))*
    clockPower ε true q*numerator ε a (groundWidth h) wL wR (momentumScale h) C p b P 0 0 q x +
  (-2*(h:ℂ)^2*((groundWidth h:ℂ)*(1/wL:ℝ))^2)*clockPower ε true q*
    numerator ε a (groundWidth h) wL wR (momentumScale h) C p b P 1 0 q x +
  (-2*(h:ℂ)^2*((groundWidth h:ℂ)*(wR:ℂ))^2)*clockPower ε true q*
    numerator ε a (groundWidth h) wL wR (momentumScale h) C p b P 0 1 q x +
  (-(h:ℂ)^2/2)*clockPower ε true q*
    numerator ε a (groundWidth h) wL wR (momentumScale h) C p b
      (step (neutralWidth h) b (step (neutralWidth h) b P)) 0 0 q x

theorem profile_factored (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (q : ℂ) (x : Joint 2 4) :
    profile ε a h wL wR C p b P q x=
      ((1/2:ℂ)*clockPower ε false q + clockPower ε true q*
        (2*(h:ℂ)^2*(groundWidth h:ℂ)*((1/wL:ℝ)+(wR:ℂ))-
          2*(h:ℂ)^2*((groundWidth h:ℂ)*(1/wL:ℝ))^2*
            left (groundWidth h) wL (baselineVector ε (groundWidth h) wL wR (momentumScale h) q x)-
          2*(h:ℂ)^2*((groundWidth h:ℂ)*(wR:ℂ))^2*
            right (groundWidth h) wR (baselineVector ε (groundWidth h) wL wR (momentumScale h) q x)))*
        numerator ε a (groundWidth h) wL wR (momentumScale h) C p b P 0 0 q x-
      (h:ℂ)^2/2*clockPower ε true q*
        numerator ε a (groundWidth h) wL wR (momentumScale h) C p b
          (step (neutralWidth h) b (step (neutralWidth h) b P)) 0 0 q x := by
  simp only [profile,numerator,pow_zero,pow_one,one_mul,mul_one]
  ring

private theorem combination_representative (ε h wL wR : ℝ) (hε : 0<ε)
    (b : ℂ) (P : Polynomial ℂ) (F : Bool→ℕ→ℕ→Polynomial ℂ→Hilbert)
    (G : Bool→ℕ→ℕ→Polynomial ℂ→Product→ℂ)
    (hG : ∀ i m n R, clockMixed ε hε (F i m n R) =ᵐ[volume] G i m n R) :
    clockMixed ε hε (combination h wL wR b P F) =ᵐ[volume] fun x =>
      (1/2:ℂ)*G false 0 0 P x+
      (2*(h:ℂ)^2*(groundWidth h:ℂ)*(1/wL:ℝ)+2*(h:ℂ)^2*(groundWidth h:ℂ)*(wR:ℂ))*G true 0 0 P x+
      (-2*(h:ℂ)^2*((groundWidth h:ℂ)*(1/wL:ℝ))^2)*G true 1 0 P x+
      (-2*(h:ℂ)^2*((groundWidth h:ℂ)*(wR:ℂ))^2)*G true 0 1 P x+
      (-(h:ℂ)^2/2)*G true 0 0 (step (neutralWidth h) b (step (neutralWidth h) b P)) x := by
  let d : Fin 5→ℂ := ![1/2,
    2*(h:ℂ)^2*(groundWidth h:ℂ)*(1/wL:ℝ)+2*(h:ℂ)^2*(groundWidth h:ℂ)*(wR:ℂ),
    -2*(h:ℂ)^2*((groundWidth h:ℂ)*(1/wL:ℝ))^2,
    -2*(h:ℂ)^2*((groundWidth h:ℂ)*(wR:ℂ))^2,-(h:ℂ)^2/2]
  let f : Fin 5→Hilbert := ![F false 0 0 P,F true 0 0 P,F true 1 0 P,F true 0 1 P,
    F true 0 0 (step (neutralWidth h) b (step (neutralWidth h) b P))]
  let g : Fin 5→Product→ℂ := ![G false 0 0 P,G true 0 0 P,G true 1 0 P,G true 0 1 P,
    G true 0 0 (step (neutralWidth h) b (step (neutralWidth h) b P))]
  have hg (i : Fin 5) : clockMixed ε hε (f i) =ᵐ[volume] g i := by
    fin_cases i <;> exact hG _ _ _ _
  have he : combination h wL wR b P F=∑ i,d i • f i := by
    simp [combination,d,f,Fin.sum_univ_succ,add_assoc]
  rw [he,map_sum]
  simp only [map_smul]
  have ht := KFCausalFiniteLpRepresentatives.weighted_sum_coe volume d
    (fun i => clockMixed ε hε (f i)) g hg
  simpa only [d,g,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,add_zero,add_assoc] using ht

theorem orderedOutput_clockMixed (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ)
    (b : ℂ) (P : Polynomial ℂ) (hε : 0<ε) (ha : 0<a) (hh : h≠0)
    (hL : 1≤wL) (hR : 1≤wR) (hb : |h|≤ε/10) :
    clockMixed ε hε (orderedOutput ε a h wL wR C p b P hε ha hh hL hR hb) =ᵐ[volume]
      fun x : Product => profile ε a h wL wR C p b P
        (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x) := by
  have ht := combination_representative ε h wL wR hε b P
    (fun inverse m n R => KFCausalClockFloorOrderedStaticPacket.clockMomentOutput
      ε a h wL wR C p b R hε ha hh hL hR hb inverse m n)
    (fun inverse m n R x => clockPower ε inverse (shift (h/2) (x.2 0:ℂ))*
      numerator ε a (groundWidth h) wL wR (momentumScale h) C p b R m n
        (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x))
    (fun inverse m n R => clockMomentOutput_clockMixed
      ε a h wL wR C p b R hε ha hh hL hR hb inverse m n)
  simpa only [orderedOutput,profile,mul_assoc] using ht

theorem finite_orderedOutput_clockMixed (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ)
    (C b : Fin n→ℂ) (P : Fin n→Polynomial ℂ) (hε : 0<ε) (ha : ∀i,0<a i)
    (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤ε/10) :
    clockMixed ε hε
      (KFCausalFiniteOrderedStaticOutput.orderedOutput n ε h a w p C b P hε ha hh hw hb) =ᵐ[volume]
      fun x : Product => ∑ i,profile ε (a i) h (w i) (w i) (C i) (p i) (b i) (P i)
        (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x) := by
  unfold KFCausalFiniteOrderedStaticOutput.orderedOutput
  rw [map_sum]
  have ht := KFCausalFiniteLpRepresentatives.weighted_sum_coe volume (fun _ : Fin n => (1:ℂ))
    (fun i => clockMixed ε hε (orderedOutput ε (a i) h (w i) (w i) (C i) (p i) (b i) (P i)
      hε (ha i) hh (hw i) (hw i) hb))
    (fun i x => profile ε (a i) h (w i) (w i) (C i) (p i) (b i) (P i)
      (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x))
    (fun i => orderedOutput_clockMixed ε (a i) h (w i) (w i) (C i) (p i) (b i) (P i)
      hε (ha i) hh (hw i) (hw i) hb)
  simpa only [one_smul,one_mul] using ht

theorem actual_ordered_static_graph_representative (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ)
    (C b : Fin n→ℂ) (P : Fin n→Polynomial ℂ) (hε : 0<ε) (ha : ∀i,0<a i)
    (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤ε/10) :
    ∃ z : Hilbert,
      (KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw,z) ∈
        (KFCausalOrderedOperatorComposition.composition
          (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h)
          (KFCausalClockFloorStaticOperator.operator ε hε h)).graph ∧
      clockMixed ε hε z =ᵐ[volume] fun x : Product =>
        ∑ i,profile ε (a i) h (w i) (w i) (C i) (p i) (b i) (P i)
          (shift (h/2) (x.2 0:ℂ)) ((split 2 4).symm x) :=
  ⟨_,KFCausalFiniteOrderedStaticOutput.ordered_static_graph n ε h a w p C b P hε ha hh hw hb,
    finite_orderedOutput_clockMixed n ε h a w p C b P hε ha hh hw hb⟩

#print axioms profile_factored
#print axioms orderedOutput_clockMixed
#print axioms finite_orderedOutput_clockMixed
#print axioms actual_ordered_static_graph_representative
end
end UnifiedTheory.Audit.KFCausalOrderedStaticOutputRepresentative
