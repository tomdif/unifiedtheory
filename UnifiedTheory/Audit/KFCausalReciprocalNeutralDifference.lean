/- Exact differences of finite physical packets and their joint Gram
representations. Both reciprocal widths remain independently variable. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralPositiveEnergy
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralDifference
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity profileSum)
open KFCausalCorrelatedClusteredDensity (energyOf)
open KFCausalClusteredClockFactors (F G Z N)

def join {A : Type*} {n m : ℕ} (a : Fin n → A) (b : Fin m → A) : Fin (n+m) → A := Fin.addCases a b

theorem join_property {A : Type*} {n m : ℕ} (a : Fin n → A) (b : Fin m → A) (P : A → Prop)
    (ha : ∀ i, P (a i)) (hb : ∀ j, P (b j)) : ∀ k, P (join a b k) := by
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simpa only [join,Fin.addCases_left] using ha i
  · intro j
    simpa only [join,Fin.addCases_right] using hb j

theorem state_neg (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
    (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) :
    KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw (-C) p b P =
      -KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P := by
  apply Lp.ext
  filter_upwards [KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw (-C) p b P,
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw C p b P,
    Lp.coeFn_neg (KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P)] with x hn hp he
  rw [hn,he,Pi.neg_apply,hp]
  simp only [KFCausalReciprocalNeutralPackets.profile,neg_mul]

theorem output_neg (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
    (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (hb : |h| ≤ 2*Real.pi*ε/3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw (-C) p b P hb j =
      -KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b P hb j := by
  have hn := KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw (-C) p b P hb j
  have hp := (KFCausalClockFloorCommonDomain.energyFactor ε hε h
    KFCausalPhysicalEnergyFactors.modelDirections KFCausalMatterOrderedDomain.pointField j).graph.neg_mem
    (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw C p b P hb j)
  rw [state_neg] at hn
  exact (KFCausalClockFloorCommonDomain.energyFactor ε hε h
    KFCausalPhysicalEnergyFactors.modelDirections KFCausalMatterOrderedDomain.pointField j).mem_graph_snd_inj' hn hp rfl

theorem output_difference (n m : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (a' w' p' : Fin m → ℝ) (C' b' : Fin m → ℂ)
    (P' : Fin m → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (ha' : ∀ i, 0 < a' i)
    (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hw' : ∀ i, 1 ≤ w' i) (hb : |h| ≤ 2*Real.pi*ε/3)
    (j : Fin 8) :
    KFCausalReciprocalNeutralSuperposition.output (n+m) ε h (join a a') (join w w') (join p p')
      (join C (fun i => -C' i)) (join b b') (join P P') hε
      (join_property a a' (fun t => 0 < t) ha ha') hh (join_property w w' (fun t => 1 ≤ t) hw hw') hb j =
    KFCausalReciprocalNeutralSuperposition.output n ε h a w p C b P hε ha hh hw hb j-
      KFCausalReciprocalNeutralSuperposition.output m ε h a' w' p' C' b' P' hε ha' hh hw' hb j := by
  unfold KFCausalReciprocalNeutralSuperposition.output
  rw [Fin.sum_univ_add]
  simp only [join,Fin.addCases_left,Fin.addCases_right,output_neg,Finset.sum_neg_distrib,sub_eq_add_neg]

theorem positiveDensity_factors (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (c : Fin n → ℂ) (Q : Fin n → ℂ → ℂ) (p : Joint) :
    positiveDensity n α β w r c Q p =
      energyOf (fun k => (F r p:ℂ)^k*Complex.exp (G β r p:ℂ)*profileSum n w c Q (Z α r p) (N r p)) := by
  have hg : (Real.exp (G β r p))^2 = Real.exp (-2*β*(p.1.2 1)^2+8*β*r.im^2*(p.1.2 0)^2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    unfold G
    ring
  unfold energyOf
  simp only [norm_mul,mul_pow,norm_pow,Complex.norm_exp,Complex.ofReal_re,Complex.norm_real,
    Real.norm_eq_abs,pow_zero,pow_one,one_mul,sq_abs,hg]
  unfold positiveDensity KFCausalReciprocalNeutralLaplace.weight KFCausalQuarticPlaneDomination.potential
  simp only [F,Z,N]
  ring

theorem profileSum_difference (n m : ℕ) (w : Fin n → ℝ) (w' : Fin m → ℝ)
    (c : Fin n → ℂ) (c' : Fin m → ℂ) (Q : Fin n → ℂ → ℂ) (Q' : Fin m → ℂ → ℂ) (z ζ : ℂ) :
    profileSum (n+m) (join w w') (join c (fun i => -c' i)) (join Q Q') z ζ =
      profileSum n w c Q z ζ-profileSum m w' c' Q' z ζ := by
  unfold profileSum KFCausalReciprocalWedgeLaplace.laplaceSum
  rw [Fin.sum_univ_add]
  simp only [join,Fin.addCases_left,Fin.addCases_right,neg_mul,Finset.sum_neg_distrib,sub_eq_add_neg]

#print axioms join_property
#print axioms state_neg
#print axioms output_neg
#print axioms output_difference
#print axioms positiveDensity_factors
#print axioms profileSum_difference
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralDifference
