/- The actual pure-clock momentum of every sourced Gaussian also has the
second vacuum action. Rescaling the momentum parameter keeps the same
physical state while using the doubled spectral parameter. -/
import UnifiedTheory.Audit.KFCausalGaussianVacuumSquare
import UnifiedTheory.Audit.KFCausalSourcedMomentumFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalGaussianMomentumVacuumSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalSourcedMomentumFactors (pureOutput factorOutput factorOutput_graph)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorBoundedInverse (inverseL ordered_graph_iff)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalClockFloorVacuumSquare
open KFCausalGaussianVacuumSquare (double_strip)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α)
  (hβ : 0 < β) (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
  (h : ℝ)

theorem pureOutput_double :
    (1/2:ℂ) • pureOutput ε a α β hε ha hα hβ hw C p b (2*h) =
      pureOutput ε a α β hε ha hα hβ hw C p b h := by
  unfold pureOutput KFCausalPureClockOutputMultipliers.outputMap
  rw [smul_smul]
  congr 1
  push_cast
  ring

variable (hh : h ≠ 0) (hb : |h| ≤ Real.pi*ε/3)
local notation "Bψ" => pureOutput ε a α β hε ha hα hβ hw C p b h

def doubleOutput : Hilbert := (1/2:ℂ) •
  factorOutput ε a α β hε ha hα hβ hw C p b (2*h) (double_strip ε h hb)
    0 0 7

def squareOutput : Hilbert := inverseL ε hε
  (doubleOutput ε a α β hε ha hα hβ hw C p b h hb)

include hh in
theorem doubleOutput_graph :
    (inverseL ε hε Bψ,doubleOutput ε a α β hε ha hα hβ hw C p b h hb) ∈
      (longitudinalExponential ε hε h 1).graph := by
  have hg : (pureOutput ε a α β hε ha hα hβ hw C p b (2*h),
      factorOutput ε a α β hε ha hα hβ hw C p b (2*h) (double_strip ε h hb) 0 0 7) ∈
      (orderedExponential ε hε (2*h)).graph :=
    factorOutput_graph ε a α β hε ha hα hβ hw C p b (2*h)
      (mul_ne_zero (by norm_num) hh) (double_strip ε h hb) 0 0 7
  have hs := (orderedExponential ε hε (2*h)).graph.smul_mem (1/2:ℂ) hg
  change ((1/2:ℂ) • pureOutput ε a α β hε ha hα hβ hw C p b (2*h),
    doubleOutput ε a α β hε ha hα hβ hw C p b h hb) ∈ _ at hs
  rw [pureOutput_double] at hs
  have hr := (exponential_rescale ε hε h 2 (1/2) _ _).mp
    ((ordered_graph_iff ε hε (2*h) _ _).mp hs)
  simpa only [show (1/2:ℝ)*2=1 by norm_num] using hr

include hh in
theorem squareOutput_graph :
    (Bψ,squareOutput ε a α β hε ha hα hβ hw C p b h hb) ∈ (square ε hε h).graph :=
  (square_graph ε hε h Bψ _).mpr
    ⟨_,doubleOutput_graph ε a α β hε ha hα hβ hw C p b h hh hb,rfl⟩

include hh hb in
theorem momentum_square_domain : Bψ ∈ (square ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (squareOutput_graph ε a α β hε ha hα hβ hw C p b h hh hb)

#print axioms pureOutput_double
#print axioms doubleOutput_graph
#print axioms squareOutput_graph
#print axioms momentum_square_domain
end
end UnifiedTheory.Audit.KFCausalGaussianMomentumVacuumSquare
