/- A second action of the actual vacuum square on sourced physical packets.
The smaller strip is explicit. The intervening inverse clock is handled by
the full-domain defect intertwining, not by commuting it with the exponential.
This is one fourth-factor graph, not the square of the averaged Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalGaussianVacuumSquare
import UnifiedTheory.Audit.KFCausalClockFloorDefectFullDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalGaussianVacuumFourth
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorBoundedInverse (inverseL inverseL_eq inverseAction_norm_bound)
open KFCausalClockFloorClockHalf (inverseAction_coe)
open KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe defectOperator_norm_le)
open KFCausalClockFloorShiftedDefect (shiftedDefect shiftedDefect_norm_bound)
open KFCausalClockFloorExponential
open KFCausalClockFloorVacuumSquare (square square_graph exponential_rescale)
open KFCausalClockFloorSourcedClockMomentum (state dampedState_eq_inverseAction)
open KFCausalClockFloorSourcedSpectral (shiftedOutput shiftedOutput_graph)
open KFCausalGaussianVacuumSquare (squareOutput squareOutput_graph doubleOutput)
open KFCausalOrderedOperatorComposition (composition composition_graph)

theorem inverseL_twice (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    inverseL ε hε (inverseL ε hε f) = (ε : ℂ)⁻¹ • defectOperator ε hε f := by
  apply Lp.ext
  filter_upwards [inverseAction_coe ε hε (inverseL ε hε f),
    inverseAction_coe ε hε f, defectOperator_coe ε hε f,
    Lp.coeFn_smul (ε : ℂ)⁻¹ (defectOperator ε hε f)] with x h1 h0 hd hs
  change (inverseL ε hε (inverseL ε hε f)) x = _ at h1
  change (inverseL ε hε f) x = _ at h0
  rw [h1, h0, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hd, KFCausalClockFloorCanonicalDefect.defect,
    KFCausalClockFloorFlow.clock, Complex.ofReal_div, Complex.ofReal_add,
    Complex.ofReal_exp]
  have hsqr : (Real.sqrt (Real.exp x.1 + ε) : ℂ)^2 = (Real.exp x.1 + ε : ℝ) := by
    norm_cast
    exact Real.sq_sqrt (by positivity)
  have he : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  rw [← mul_assoc, ← mul_inv, ← pow_two, hsqr]
  field_simp
  simp only [Complex.ofReal_add, Complex.ofReal_exp]

theorem full_exponential_defect (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hb : |2*h| ≤ 2*Real.pi*ε/3) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε h 1).graph) :
    (defectOperator ε hε f, shiftedDefect ε hε (2*h) hb g) ∈
      (longitudinalExponential ε hε h 1).graph := by
  have hs := (exponential_rescale ε hε h 2 (1/2) f g)
  have hi : (f,g) ∈ (longitudinalExponential ε hε (2*h) (1/2)).graph := by
    apply hs.mpr
    simpa only [show (1/2:ℝ)*2=1 by norm_num] using hfg
  have hd := KFCausalClockFloorDefectFullDomain.graph_defect ε hε (2*h) hb f g hi
  simpa only [show (1/2:ℝ)*2=1 by norm_num] using
    (exponential_rescale ε hε h 2 (1/2) _ _).mp hd

def fourthFrom (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hb : |2*h| ≤ 2*Real.pi*ε/3) (z : Hilbert) : Hilbert :=
  (ε : ℂ)⁻¹ • inverseL ε hε (shiftedDefect ε hε (2*h) hb z)

theorem fourth_graph_of_exponential (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hb : |2*h| ≤ 2*Real.pi*ε/3) (f z : Hilbert)
    (hfg : (inverseL ε hε f,z) ∈ (longitudinalExponential ε hε h 2).graph) :
    (f, fourthFrom ε hε h hb z) ∈ (composition (square ε hε h) (square ε hε h)).graph := by
  have hsplit := KFCausalSpectralExponentialSquare.exponential_square_graph
    (KFCausalClockFloorFourierCoordinates.coupledFourier ε hε)
    (KFCausalClockFloorFourierMultiplier.symbol h) (symbol_measurable h) 1
    (inverseL ε hε f) z
  obtain ⟨g,hg,hz⟩ := hsplit.mp (by simpa only [mul_one] using hfg)
  have hQ : (f,inverseL ε hε g) ∈ (square ε hε h).graph :=
    (square_graph ε hε h f _).mpr ⟨g,hg,rfl⟩
  have hd := full_exponential_defect ε hε h hb g z hz
  have he := (longitudinalExponential ε hε h 1).graph.smul_mem (ε : ℂ)⁻¹ hd
  have hQQ : (inverseL ε hε g, fourthFrom ε hε h hb z) ∈ (square ε hε h).graph := by
    apply (square_graph ε hε h _ _).mpr
    refine ⟨(ε : ℂ)⁻¹ • shiftedDefect ε hε (2*h) hb z, ?_, ?_⟩
    · rw [inverseL_twice]
      exact he
    · simp only [fourthFrom, map_smul]
  exact (composition_graph _ _ _ _).mpr ⟨_,hQ,hQQ⟩

theorem fourthFrom_norm_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (hb : |2*h| ≤ 2*Real.pi*ε/3) (z : Hilbert) :
    ‖fourthFrom ε hε h hb z‖ ≤ (2 / (ε * Real.sqrt ε)) * ‖z‖ := by
  have hZ := (shiftedDefect_norm_bound ε hε (2*h) hb z).trans
    (mul_le_mul_of_nonneg_left (defectOperator_norm_le ε hε z) (by norm_num : (0:ℝ) ≤ 2))
  have hI := inverseAction_norm_bound ε hε (shiftedDefect ε hε (2*h) hb z)
  change ‖inverseL ε hε (shiftedDefect ε hε (2*h) hb z)‖ ≤ _ at hI
  rw [fourthFrom, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  calc
    _ ≤ ε⁻¹ * ((Real.sqrt ε)⁻¹ * (2 * ‖z‖)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hε.le)
      exact hI.trans (mul_le_mul_of_nonneg_left hZ (inv_nonneg.mpr (Real.sqrt_nonneg ε)))
    _ = _ := by ring

theorem quadruple_strip (ε h : ℝ) (hb : |2*h| ≤ Real.pi*ε/3) :
    |4*h| ≤ 2*Real.pi*ε/3 := by
  have he : |4*h| = 2*|2*h| := by
    rw [show 4*h=2*(2*h) by ring, abs_mul]
    norm_num
  rw [he]
  linarith

theorem full_strip (ε h : ℝ) (hε : 0 < ε) (hb : |2*h| ≤ Real.pi*ε/3) :
    |2*h| ≤ 2*Real.pi*ε/3 := by
  have hp := mul_pos Real.pi_pos hε
  linarith

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
  (hβ : 0 < β) (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
  (h : ℝ) (hb : |2*h| ≤ Real.pi*ε/3)

local notation "S" => state ε a α β hε ha hα hβ hw C p b

def quadrupleOutput : Hilbert :=
  shiftedOutput ε a α β hε ha hα hβ hw C p b (4*h) (quadruple_strip ε h hb)

def fourthOutput : Hilbert :=
  fourthFrom ε hε h (full_strip ε h hε hb)
    (quadrupleOutput ε a α β hε ha hα hβ hw C p b h hb)

theorem quadrupleOutput_graph :
    (inverseL ε hε S, quadrupleOutput ε a α β hε ha hα hβ hw C p b h hb) ∈
      (longitudinalExponential ε hε h 2).graph := by
  have hg := shiftedOutput_graph ε a α β hε ha hα hβ hw C p b
    (4*h) (quadruple_strip ε h hb)
  rw [dampedState_eq_inverseAction] at hg
  simpa only [show (1/2:ℝ)*4=2 by norm_num] using
    (exponential_rescale ε hε h 4 (1/2) _ _).mp hg

theorem fourthOutput_graph :
    (S, fourthOutput ε a α β hε ha hα hβ hw C p b h hb) ∈
      (composition (square ε hε h) (square ε hε h)).graph :=
  fourth_graph_of_exponential ε hε h (full_strip ε h hε hb) S _
    (quadrupleOutput_graph ε a α β hε ha hα hβ hw C p b h hb)

include hb in
theorem state_fourth_domain :
    S ∈ (composition (square ε hε h) (square ε hε h)).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (fourthOutput_graph ε a α β hε ha hα hβ hw C p b h hb)

theorem fourthOutput_adjoint_graph :
    (S, fourthOutput ε a α β hε ha hα hβ hw C p b h hb) ∈
      (composition
        (composition (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).adjoint
          (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h))
        (composition (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).adjoint
          (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h))).graph := by
  obtain ⟨g,hg,hz⟩ := (composition_graph _ _ _ _).mp
    (fourthOutput_graph ε a α β hε ha hα hβ hw C p b h hb)
  have hp : |h| ≤ Real.pi*ε := by
    have hp0 := mul_pos Real.pi_pos hε
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] at hb
    linarith
  exact (composition_graph _ _ _ _).mpr ⟨g,
    KFCausalClockFloorVacuumSquare.square_adjoint_graph ε hε h hp _ _ hg,
    KFCausalClockFloorVacuumSquare.square_adjoint_graph ε hε h hp _ _ hz⟩

include hb in
theorem state_adjoint_fourth_domain :
    S ∈ (composition
        (composition (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).adjoint
          (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h))
        (composition (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h).adjoint
          (KFCausalClockFloorTrialSpectralDomain.orderedExponential ε hε h))).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (fourthOutput_adjoint_graph ε a α β hε ha hα hβ hw C p b h hb)

#print axioms inverseL_twice
#print axioms full_exponential_defect
#print axioms fourth_graph_of_exponential
#print axioms fourthFrom_norm_bound
#print axioms quadruple_strip
#print axioms full_strip
#print axioms quadrupleOutput_graph
#print axioms fourthOutput_graph
#print axioms state_fourth_domain
#print axioms fourthOutput_adjoint_graph
#print axioms state_adjoint_fourth_domain
end
end UnifiedTheory.Audit.KFCausalGaussianVacuumFourth
