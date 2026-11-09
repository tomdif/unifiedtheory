/- Packet-level and superposition-level linearity of reciprocal-neutral quantum
states, momenta, energy factor outputs, momentum factor outputs, second factor
outputs, form lifts, and strong Hamiltonian outputs with respect to the neutral
polynomial profile `P`, together with amplitude absorption for `Polynomial.C (d i) * P i`
and the exact constant-plus-linear decomposition for affine neutral polynomials
`P i = Polynomial.C (d₀ i) + Polynomial.C (d₁ i) * Polynomial.X`. -/
import UnifiedTheory.Audit.KFCausalCommonComplexScalarPolynomialHamiltonianResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexAffineNeutralPolynomialDecomposition
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalReciprocalNeutralSuperposition (state momentum output momentumOutput)
open KFCausalReciprocalNeutralHamiltonian
  (inputLift momentumLift inputLift_embedding momentumLift_embedding)
open KFCausalReciprocalNeutralStrongHamiltonian
  (seconds hamiltonianOutput hamiltonian_graph hamiltonian_domain hamiltonian_action)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse
  (scaleAmplitude packet_state_constant packet_momentum_constant
   packet_output_constant packet_momentumOutput_constant packet_second_constant
   state_constant_eq momentum_constant_eq output_constant_eq momentumOutput_constant_eq)
open KFCausalCommonComplexScalarPolynomialHamiltonianResponse
  (seconds_scalar_polynomial_eq hamiltonianOutput_scalar_polynomial_eq
   inputLift_scalar_polynomial_eq momentumLift_scalar_polynomial_eq)

/-! ### 1. Single-Packet Additivity and Scalar Multiplication in the Neutral Polynomial `P` -/

theorem packet_state_add (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b : ℂ) (P₁ P₂ : Polynomial ℂ) :
    KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b (P₁ + P₂) =
      KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P₁ +
        KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P₂ := by
  let s₁ := KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P₁
  let s₂ := KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P₂
  apply MeasureTheory.Lp.ext
  filter_upwards [
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw C p b (P₁ + P₂),
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw C p b P₁,
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw C p b P₂,
    MeasureTheory.Lp.coeFn_add s₁ s₂] with x hx12 hx1 hx2 hadd
  change _ = (s₁ + s₂) x
  rw [hadd, Pi.add_apply, hx12, hx1, hx2]
  unfold KFCausalReciprocalNeutralPackets.profile
  simp only [Polynomial.eval_add]
  ring

theorem packet_state_scale (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ) (P : Polynomial ℂ) :
    KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b (Polynomial.C c * P) =
      KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw (C * c) p b P := by
  apply MeasureTheory.Lp.ext
  filter_upwards [
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw C p b (Polynomial.C c * P),
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw (C * c) p b P] with x hx1 hx2
  rw [hx1, hx2]
  unfold KFCausalReciprocalNeutralPackets.profile
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem packet_state_smul (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ) (P : Polynomial ℂ) :
    KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b (Polynomial.C c * P) =
      c • KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P := by
  let s := KFCausalReciprocalNeutralPackets.state ε a h w hε ha hh hw C p b P
  apply MeasureTheory.Lp.ext
  filter_upwards [
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw C p b (Polynomial.C c * P),
    KFCausalReciprocalNeutralPackets.state_coe ε a h w hε ha hh hw C p b P,
    MeasureTheory.Lp.coeFn_smul c s] with x hx1 hx2 hsmul
  change _ = (c • s) x
  rw [hsmul, Pi.smul_apply, smul_eq_mul, hx1, hx2]
  unfold KFCausalReciprocalNeutralPackets.profile
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem packet_momentum_add (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b : ℂ) (P₁ P₂ : Polynomial ℂ) :
    KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw C p b (P₁ + P₂) =
      KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw C p b P₁ +
        KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw C p b P₂ :=
  (pureMomentum ε hε h).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.momentum_graph ε a h w hε ha hh hw C p b (P₁ + P₂))
    ((pureMomentum ε hε h).graph.add_mem
      (KFCausalReciprocalNeutralPackets.momentum_graph ε a h w hε ha hh hw C p b P₁)
      (KFCausalReciprocalNeutralPackets.momentum_graph ε a h w hε ha hh hw C p b P₂))
    (packet_state_add ε a h w hε ha hh hw C p b P₁ P₂)

theorem packet_momentum_scale (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ) (P : Polynomial ℂ) :
    KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw C p b (Polynomial.C c * P) =
      KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw (C * c) p b P :=
  (pureMomentum ε hε h).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.momentum_graph ε a h w hε ha hh hw C p b (Polynomial.C c * P))
    (KFCausalReciprocalNeutralPackets.momentum_graph ε a h w hε ha hh hw (C * c) p b P)
    (packet_state_scale ε a h w hε ha hh hw C p b c P)

theorem packet_momentum_smul (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ) (P : Polynomial ℂ) :
    KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw C p b (Polynomial.C c * P) =
      c • KFCausalReciprocalNeutralPackets.momentum ε a h w hε ha hh hw C p b P :=
  (pureMomentum ε hε h).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.momentum_graph ε a h w hε ha hh hw C p b (Polynomial.C c * P))
    ((pureMomentum ε hε h).graph.smul_mem c
      (KFCausalReciprocalNeutralPackets.momentum_graph ε a h w hε ha hh hw C p b P))
    (packet_state_smul ε a h w hε ha hh hw C p b c P)

theorem packet_output_add (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b : ℂ) (P₁ P₂ : Polynomial ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b (P₁ + P₂) hb j =
      KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b P₁ hb j +
        KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b P₂ hb j :=
  (energyFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw C p b (P₁ + P₂) hb j)
    ((energyFactor ε hε h modelDirections pointField j).graph.add_mem
      (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw C p b P₁ hb j)
      (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw C p b P₂ hb j))
    (packet_state_add ε a h w hε ha hh hw C p b P₁ P₂)

theorem packet_output_scale (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ) (P : Polynomial ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b (Polynomial.C c * P) hb j =
      KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw (C * c) p b P hb j :=
  (energyFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw C p b (Polynomial.C c * P) hb j)
    (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw (C * c) p b P hb j)
    (packet_state_scale ε a h w hε ha hh hw C p b c P)

theorem packet_output_smul (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ) (P : Polynomial ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b (Polynomial.C c * P) hb j =
      c • KFCausalReciprocalNeutralPackets.output ε a h w hε ha hh hw C p b P hb j :=
  (energyFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw C p b (Polynomial.C c * P) hb j)
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c
      (KFCausalReciprocalNeutralPackets.output_graph ε a h w hε ha hh hw C p b P hb j))
    (packet_state_smul ε a h w hε ha hh hw C p b c P)

theorem packet_momentumOutput_add (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b : ℂ) (P₁ P₂ : Polynomial ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw C p b (P₁ + P₂) hb j =
      KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw C p b P₁ hb j +
        KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw C p b P₂ hb j :=
  (energyFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.momentumOutput_graph ε a h w hε ha hh hw C p b (P₁ + P₂) hb j)
    ((energyFactor ε hε h modelDirections pointField j).graph.add_mem
      (KFCausalReciprocalNeutralPackets.momentumOutput_graph ε a h w hε ha hh hw C p b P₁ hb j)
      (KFCausalReciprocalNeutralPackets.momentumOutput_graph ε a h w hε ha hh hw C p b P₂ hb j))
    (packet_momentum_add ε a h w hε ha hh hw C p b P₁ P₂)

theorem packet_momentumOutput_scale (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ) (P : Polynomial ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw C p b (Polynomial.C c * P) hb j =
      KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw (C * c) p b P hb j :=
  (energyFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.momentumOutput_graph ε a h w hε ha hh hw C p b (Polynomial.C c * P) hb j)
    (KFCausalReciprocalNeutralPackets.momentumOutput_graph ε a h w hε ha hh hw (C * c) p b P hb j)
    (packet_momentum_scale ε a h w hε ha hh hw C p b c P)

theorem packet_momentumOutput_smul (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (C : ℂ) (p : ℝ) (b c : ℂ) (P : Polynomial ℂ)
    (hb : |h| ≤ 2 * Real.pi * ε / 3) (j : Fin 8) :
    KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw C p b (Polynomial.C c * P) hb j =
      c • KFCausalReciprocalNeutralPackets.momentumOutput ε a h w hε ha hh hw C p b P hb j :=
  (energyFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralPackets.momentumOutput_graph ε a h w hε ha hh hw C p b (Polynomial.C c * P) hb j)
    ((energyFactor ε hε h modelDirections pointField j).graph.smul_mem c
      (KFCausalReciprocalNeutralPackets.momentumOutput_graph ε a h w hε ha hh hw C p b P hb j))
    (packet_momentum_smul ε a h w hε ha hh hw C p b c P)

theorem packet_second_add (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (hb : |h| ≤ Real.pi * ε / 3) (C : ℂ) (p : ℝ) (b : ℂ)
    (P₁ P₂ : Polynomial ℂ) (j : Fin 8) :
    KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb C p b (P₁ + P₂) j =
      KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb C p b P₁ j +
        KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb C p b P₂ j :=
  (reverseFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralSecondFactors.reverse_graph ε a h w hε ha hh hw hb C p b (P₁ + P₂) j)
    ((reverseFactor ε hε h modelDirections pointField j).graph.add_mem
      (KFCausalReciprocalNeutralSecondFactors.reverse_graph ε a h w hε ha hh hw hb C p b P₁ j)
      (KFCausalReciprocalNeutralSecondFactors.reverse_graph ε a h w hε ha hh hw hb C p b P₂ j))
    (packet_output_add ε a h w hε ha hh hw C p b P₁ P₂ (original_strip ε h hε hb) j)

theorem packet_second_scale (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (hb : |h| ≤ Real.pi * ε / 3) (C : ℂ) (p : ℝ) (b c : ℂ)
    (P : Polynomial ℂ) (j : Fin 8) :
    KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb C p b (Polynomial.C c * P) j =
      KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb (C * c) p b P j :=
  (reverseFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralSecondFactors.reverse_graph ε a h w hε ha hh hw hb C p b (Polynomial.C c * P) j)
    (KFCausalReciprocalNeutralSecondFactors.reverse_graph ε a h w hε ha hh hw hb (C * c) p b P j)
    (packet_output_scale ε a h w hε ha hh hw C p b c P (original_strip ε h hε hb) j)

theorem packet_second_smul (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hw : 1 ≤ w) (hb : |h| ≤ Real.pi * ε / 3) (C : ℂ) (p : ℝ) (b c : ℂ)
    (P : Polynomial ℂ) (j : Fin 8) :
    KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb C p b (Polynomial.C c * P) j =
      c • KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb C p b P j :=
  (reverseFactor ε hε h modelDirections pointField j).mem_graph_snd_inj'
    (KFCausalReciprocalNeutralSecondFactors.reverse_graph ε a h w hε ha hh hw hb C p b (Polynomial.C c * P) j)
    ((reverseFactor ε hε h modelDirections pointField j).graph.smul_mem c
      (KFCausalReciprocalNeutralSecondFactors.reverse_graph ε a h w hε ha hh hw hb C p b P j))
    (packet_output_smul ε a h w hε ha hh hw C p b c P (original_strip ε h hε hb) j)

/-! ### 2. Multi-Packet Superposition Additivity and Amplitude Scaling in `P : Fin n → Polynomial ℂ` -/

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b d : Fin n → ℂ)
  (P P₁ P₂ : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ 2 * Real.pi * ε / 3)

theorem state_poly_add :
    state n ε h a w p C b (fun i => P₁ i + P₂ i) hε ha hh hw =
      state n ε h a w p C b P₁ hε ha hh hw +
        state n ε h a w p C b P₂ hε ha hh hw := by
  unfold state
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ =>
    packet_state_add ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P₁ i) (P₂ i))

theorem state_poly_scale :
    state n ε h a w p C b (fun i => Polynomial.C (d i) * P i) hε ha hh hw =
      state n ε h a w p (scaleAmplitude C d) b P hε ha hh hw := by
  unfold state scaleAmplitude
  exact Finset.sum_congr rfl (fun i _ =>
    packet_state_scale ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (d i) (P i))

theorem state_poly_smul (c : ℂ) :
    state n ε h a w p C b (fun i => Polynomial.C c * P i) hε ha hh hw =
      c • state n ε h a w p C b P hε ha hh hw := by
  unfold state
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    packet_state_smul ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) c (P i))

theorem momentum_poly_add :
    momentum n ε h a w p C b (fun i => P₁ i + P₂ i) hε ha hh hw =
      momentum n ε h a w p C b P₁ hε ha hh hw +
        momentum n ε h a w p C b P₂ hε ha hh hw := by
  unfold momentum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ =>
    packet_momentum_add ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P₁ i) (P₂ i))

theorem momentum_poly_scale :
    momentum n ε h a w p C b (fun i => Polynomial.C (d i) * P i) hε ha hh hw =
      momentum n ε h a w p (scaleAmplitude C d) b P hε ha hh hw := by
  unfold momentum scaleAmplitude
  exact Finset.sum_congr rfl (fun i _ =>
    packet_momentum_scale ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (d i) (P i))

theorem momentum_poly_smul (c : ℂ) :
    momentum n ε h a w p C b (fun i => Polynomial.C c * P i) hε ha hh hw =
      c • momentum n ε h a w p C b P hε ha hh hw := by
  unfold momentum
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    packet_momentum_smul ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) c (P i))

theorem output_poly_add (j : Fin 8) :
    output n ε h a w p C b (fun i => P₁ i + P₂ i) hε ha hh hw hb j =
      output n ε h a w p C b P₁ hε ha hh hw hb j +
        output n ε h a w p C b P₂ hε ha hh hw hb j := by
  unfold output
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ =>
    packet_output_add ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P₁ i) (P₂ i) hb j)

theorem output_poly_scale (j : Fin 8) :
    output n ε h a w p C b (fun i => Polynomial.C (d i) * P i) hε ha hh hw hb j =
      output n ε h a w p (scaleAmplitude C d) b P hε ha hh hw hb j := by
  unfold output scaleAmplitude
  exact Finset.sum_congr rfl (fun i _ =>
    packet_output_scale ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (d i) (P i) hb j)

theorem output_poly_smul (c : ℂ) (j : Fin 8) :
    output n ε h a w p C b (fun i => Polynomial.C c * P i) hε ha hh hw hb j =
      c • output n ε h a w p C b P hε ha hh hw hb j := by
  unfold output
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    packet_output_smul ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) c (P i) hb j)

theorem momentumOutput_poly_add (j : Fin 8) :
    momentumOutput n ε h a w p C b (fun i => P₁ i + P₂ i) hε ha hh hw hb j =
      momentumOutput n ε h a w p C b P₁ hε ha hh hw hb j +
        momentumOutput n ε h a w p C b P₂ hε ha hh hw hb j := by
  unfold momentumOutput
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ =>
    packet_momentumOutput_add ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (P₁ i) (P₂ i) hb j)

theorem momentumOutput_poly_scale (j : Fin 8) :
    momentumOutput n ε h a w p C b (fun i => Polynomial.C (d i) * P i) hε ha hh hw hb j =
      momentumOutput n ε h a w p (scaleAmplitude C d) b P hε ha hh hw hb j := by
  unfold momentumOutput scaleAmplitude
  exact Finset.sum_congr rfl (fun i _ =>
    packet_momentumOutput_scale ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) (d i) (P i) hb j)

theorem momentumOutput_poly_smul (c : ℂ) (j : Fin 8) :
    momentumOutput n ε h a w p C b (fun i => Polynomial.C c * P i) hε ha hh hw hb j =
      c • momentumOutput n ε h a w p C b P hε ha hh hw hb j := by
  unfold momentumOutput
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    packet_momentumOutput_smul ε (a i) h (w i) hε (ha i) hh (hw i) (C i) (p i) (b i) c (P i) hb j)

theorem seconds_poly_add (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (fun i => P₁ i + P₂ i) hε ha hh hw hb_narrow j =
      seconds n ε h a w p C b P₁ hε ha hh hw hb_narrow j +
        seconds n ε h a w p C b P₂ hε ha hh hw hb_narrow j := by
  unfold seconds
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ =>
    packet_second_add ε (a i) h (w i) hε (ha i) hh (hw i) hb_narrow (C i) (p i) (b i) (P₁ i) (P₂ i) j)

theorem seconds_poly_scale (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (fun i => Polynomial.C (d i) * P i) hε ha hh hw hb_narrow j =
      seconds n ε h a w p (scaleAmplitude C d) b P hε ha hh hw hb_narrow j := by
  unfold seconds scaleAmplitude
  exact Finset.sum_congr rfl (fun i _ =>
    packet_second_scale ε (a i) h (w i) hε (ha i) hh (hw i) hb_narrow (C i) (p i) (b i) (d i) (P i) j)

theorem seconds_poly_smul (hb_narrow : |h| ≤ Real.pi * ε / 3) (c : ℂ) (j : Fin 8) :
    seconds n ε h a w p C b (fun i => Polynomial.C c * P i) hε ha hh hw hb_narrow j =
      c • seconds n ε h a w p C b P hε ha hh hw hb_narrow j := by
  unfold seconds
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    packet_second_smul ε (a i) h (w i) hε (ha i) hh (hw i) hb_narrow (C i) (p i) (b i) c (P i) j)

theorem hamiltonianOutput_poly_add (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (fun i => P₁ i + P₂ i) hε ha hh hw hb_narrow
        mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p C b P₁ hε ha hh hw hb_narrow mass2 quartic vacuum t +
        hamiltonianOutput n ε h a w p C b P₂ hε ha hh hw hb_narrow mass2 quartic vacuum t :=
  (hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t).mem_graph_snd_inj'
    (hamiltonian_graph n ε h a w p C b (fun i => P₁ i + P₂ i) hε ha hh hw hb_narrow
      mass2 quartic vacuum t)
    ((hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t).graph.add_mem
      (hamiltonian_graph n ε h a w p C b P₁ hε ha hh hw hb_narrow mass2 quartic vacuum t)
      (hamiltonian_graph n ε h a w p C b P₂ hε ha hh hw hb_narrow mass2 quartic vacuum t))
    (state_poly_add n ε h a w p C b P₁ P₂ hε ha hh hw)

theorem hamiltonianOutput_poly_scale (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (fun i => Polynomial.C (d i) * P i)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p (scaleAmplitude C d) b P
        hε ha hh hw hb_narrow mass2 quartic vacuum t := by
  unfold hamiltonianOutput
  rw [funext (seconds_poly_scale n ε h a w p C b d P hε ha hh hw hb_narrow)]

theorem hamiltonianOutput_poly_smul (hb_narrow : |h| ≤ Real.pi * ε / 3)
    (c : ℂ) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (fun i => Polynomial.C c * P i)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      c • hamiltonianOutput n ε h a w p C b P
        hε ha hh hw hb_narrow mass2 quartic vacuum t :=
  (hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t).mem_graph_snd_inj'
    (hamiltonian_graph n ε h a w p C b (fun i => Polynomial.C c * P i) hε ha hh hw hb_narrow
      mass2 quartic vacuum t)
    ((hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t).graph.smul_mem c
      (hamiltonian_graph n ε h a w p C b P hε ha hh hw hb_narrow mass2 quartic vacuum t))
    (state_poly_smul n ε h a w p C b P hε ha hh hw c)

theorem inputLift_poly_add (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (fun i => P₁ i + P₂ i) hε ha hh hw hb mass2 quartic vacuum t =
      inputLift n ε h a w p C b P₁ hε ha hh hw hb mass2 quartic vacuum t +
        inputLift n ε h a w p C b P₂ hε ha hh hw hb mass2 quartic vacuum t := by
  apply KFCausalClockFloorAveragedFormTransport.embedding_injective ε hε h hh hb mass2 quartic vacuum t
  rw [map_add, inputLift_embedding, inputLift_embedding, inputLift_embedding]
  exact state_poly_add n ε h a w p C b P₁ P₂ hε ha hh hw

theorem inputLift_poly_scale (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (fun i => Polynomial.C (d i) * P i)
        hε ha hh hw hb mass2 quartic vacuum t =
      inputLift n ε h a w p (scaleAmplitude C d) b P
        hε ha hh hw hb mass2 quartic vacuum t := by
  apply KFCausalClockFloorAveragedFormTransport.embedding_injective ε hε h hh hb mass2 quartic vacuum t
  exact state_poly_scale n ε h a w p C b d P hε ha hh hw

theorem inputLift_poly_smul (c : ℂ) (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (fun i => Polynomial.C c * P i)
        hε ha hh hw hb mass2 quartic vacuum t =
      c • inputLift n ε h a w p C b P
        hε ha hh hw hb mass2 quartic vacuum t := by
  apply KFCausalClockFloorAveragedFormTransport.embedding_injective ε hε h hh hb mass2 quartic vacuum t
  rw [map_smul, inputLift_embedding, inputLift_embedding]
  exact state_poly_smul n ε h a w p C b P hε ha hh hw c

theorem momentumLift_poly_add (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (fun i => P₁ i + P₂ i) hε ha hh hw hb mass2 quartic vacuum t =
      momentumLift n ε h a w p C b P₁ hε ha hh hw hb mass2 quartic vacuum t +
        momentumLift n ε h a w p C b P₂ hε ha hh hw hb mass2 quartic vacuum t := by
  apply KFCausalClockFloorAveragedFormTransport.embedding_injective ε hε h hh hb mass2 quartic vacuum t
  rw [map_add, momentumLift_embedding, momentumLift_embedding, momentumLift_embedding]
  exact momentum_poly_add n ε h a w p C b P₁ P₂ hε ha hh hw

theorem momentumLift_poly_scale (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (fun i => Polynomial.C (d i) * P i)
        hε ha hh hw hb mass2 quartic vacuum t =
      momentumLift n ε h a w p (scaleAmplitude C d) b P
        hε ha hh hw hb mass2 quartic vacuum t := by
  apply KFCausalClockFloorAveragedFormTransport.embedding_injective ε hε h hh hb mass2 quartic vacuum t
  exact momentum_poly_scale n ε h a w p C b d P hε ha hh hw

theorem momentumLift_poly_smul (c : ℂ) (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (fun i => Polynomial.C c * P i)
        hε ha hh hw hb mass2 quartic vacuum t =
      c • momentumLift n ε h a w p C b P
        hε ha hh hw hb mass2 quartic vacuum t := by
  apply KFCausalClockFloorAveragedFormTransport.embedding_injective ε hε h hh hb mass2 quartic vacuum t
  rw [map_smul, momentumLift_embedding, momentumLift_embedding]
  exact momentum_poly_smul n ε h a w p C b P hε ha hh hw c

/-! ### 3. Exact Affine Neutral Polynomial Decomposition (`C (d₀ i) + C (d₁ i) * X`) -/

def affinePolynomial {n : ℕ} (d₀ d₁ : Fin n → ℂ) : Fin n → Polynomial ℂ :=
  fun i => Polynomial.C (d₀ i) + Polynomial.C (d₁ i) * Polynomial.X

theorem state_affine_poly_eq (d₀ d₁ : Fin n → ℂ) :
    state n ε h a w p C b (affinePolynomial d₀ d₁) hε ha hh hw =
      state n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw +
        state n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw := by
  unfold affinePolynomial
  rw [state_poly_add, state_constant_eq, state_poly_scale]

theorem momentum_affine_poly_eq (d₀ d₁ : Fin n → ℂ) :
    momentum n ε h a w p C b (affinePolynomial d₀ d₁) hε ha hh hw =
      momentum n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw +
        momentum n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw := by
  unfold affinePolynomial
  rw [momentum_poly_add, momentum_constant_eq, momentum_poly_scale]

theorem output_affine_poly_eq (d₀ d₁ : Fin n → ℂ) (j : Fin 8) :
    output n ε h a w p C b (affinePolynomial d₀ d₁) hε ha hh hw hb j =
      output n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw hb j +
        output n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw hb j := by
  unfold affinePolynomial
  rw [output_poly_add, output_constant_eq, output_poly_scale]

theorem momentumOutput_affine_poly_eq (d₀ d₁ : Fin n → ℂ) (j : Fin 8) :
    momentumOutput n ε h a w p C b (affinePolynomial d₀ d₁) hε ha hh hw hb j =
      momentumOutput n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw hb j +
        momentumOutput n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw hb j := by
  unfold affinePolynomial
  rw [momentumOutput_poly_add, momentumOutput_constant_eq, momentumOutput_poly_scale]

theorem seconds_affine_poly_eq (d₀ d₁ : Fin n → ℂ) (hb_narrow : |h| ≤ Real.pi * ε / 3) (j : Fin 8) :
    seconds n ε h a w p C b (affinePolynomial d₀ d₁) hε ha hh hw hb_narrow j =
      seconds n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw hb_narrow j +
        seconds n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw hb_narrow j := by
  unfold affinePolynomial
  rw [seconds_poly_add, seconds_scalar_polynomial_eq, seconds_poly_scale]

theorem hamiltonianOutput_affine_poly_eq (d₀ d₁ : Fin n → ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b (affinePolynomial d₀ d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum t =
      hamiltonianOutput n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t +
        hamiltonianOutput n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb_narrow mass2 quartic vacuum t := by
  unfold affinePolynomial
  rw [hamiltonianOutput_poly_add, hamiltonianOutput_scalar_polynomial_eq,
    hamiltonianOutput_poly_scale]

theorem inputLift_affine_poly_eq (d₀ d₁ : Fin n → ℂ) (mass2 quartic vacuum t : ℝ) :
    inputLift n ε h a w p C b (affinePolynomial d₀ d₁) hε ha hh hw hb mass2 quartic vacuum t =
      inputLift n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t +
        inputLift n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb mass2 quartic vacuum t := by
  unfold affinePolynomial
  rw [inputLift_poly_add, inputLift_scalar_polynomial_eq, inputLift_poly_scale]

theorem momentumLift_affine_poly_eq (d₀ d₁ : Fin n → ℂ) (mass2 quartic vacuum t : ℝ) :
    momentumLift n ε h a w p C b (affinePolynomial d₀ d₁) hε ha hh hw hb mass2 quartic vacuum t =
      momentumLift n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb mass2 quartic vacuum t +
        momentumLift n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb mass2 quartic vacuum t := by
  unfold affinePolynomial
  rw [momentumLift_poly_add, momentumLift_scalar_polynomial_eq, momentumLift_poly_scale]

theorem hamiltonian_affine_poly_action (d₀ d₁ : Fin n → ℂ)
    (hb_narrow : |h| ≤ Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb_narrow) mass2 quartic vacuum t;
    let ψ := state n ε h a w p C b (affinePolynomial d₀ d₁) hε ha hh hw;
    let ψ₀ := state n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1) hε ha hh hw;
    let ψ₁ := state n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X) hε ha hh hw;
    H ⟨ψ, hamiltonian_domain n ε h a w p C b (affinePolynomial d₀ d₁)
        hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ =
      H ⟨ψ₀, hamiltonian_domain n ε h a w p (scaleAmplitude C d₀) b (fun _ => 1)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ +
        H ⟨ψ₁, hamiltonian_domain n ε h a w p (scaleAmplitude C d₁) b (fun _ => Polynomial.X)
          hε ha hh hw hb_narrow mass2 quartic vacuum t⟩ := by
  dsimp only
  rw [hamiltonian_action, hamiltonian_action, hamiltonian_action]
  exact hamiltonianOutput_affine_poly_eq n ε h a w p C b hε ha hh hw d₀ d₁ hb_narrow
    mass2 quartic vacuum t

#print axioms packet_state_add
#print axioms packet_state_scale
#print axioms packet_state_smul
#print axioms packet_momentum_add
#print axioms packet_momentum_scale
#print axioms packet_momentum_smul
#print axioms packet_output_add
#print axioms packet_output_scale
#print axioms packet_output_smul
#print axioms packet_momentumOutput_add
#print axioms packet_momentumOutput_scale
#print axioms packet_momentumOutput_smul
#print axioms packet_second_add
#print axioms packet_second_scale
#print axioms packet_second_smul
#print axioms state_poly_add
#print axioms state_poly_scale
#print axioms state_poly_smul
#print axioms momentum_poly_add
#print axioms momentum_poly_scale
#print axioms momentum_poly_smul
#print axioms output_poly_add
#print axioms output_poly_scale
#print axioms output_poly_smul
#print axioms momentumOutput_poly_add
#print axioms momentumOutput_poly_scale
#print axioms momentumOutput_poly_smul
#print axioms seconds_poly_add
#print axioms seconds_poly_scale
#print axioms seconds_poly_smul
#print axioms hamiltonianOutput_poly_add
#print axioms hamiltonianOutput_poly_scale
#print axioms hamiltonianOutput_poly_smul
#print axioms inputLift_poly_add
#print axioms inputLift_poly_scale
#print axioms inputLift_poly_smul
#print axioms momentumLift_poly_add
#print axioms momentumLift_poly_scale
#print axioms momentumLift_poly_smul
#print axioms state_affine_poly_eq
#print axioms momentum_affine_poly_eq
#print axioms output_affine_poly_eq
#print axioms momentumOutput_affine_poly_eq
#print axioms seconds_affine_poly_eq
#print axioms hamiltonianOutput_affine_poly_eq
#print axioms inputLift_affine_poly_eq
#print axioms momentumLift_affine_poly_eq
#print axioms hamiltonian_affine_poly_action
end
end UnifiedTheory.Audit.KFCausalCommonComplexAffineNeutralPolynomialDecomposition
