/- Every existing second energy output, integrated over a bounded source
curve at fixed real clock frequency, lies in the actual pure-clock domain.
Both components of each closed graph are continuous before integration. -/
import UnifiedTheory.Audit.KFCausalSourcedKineticSecondPureClock
import UnifiedTheory.Audit.KFCausalFullClockPureSourceCurves
import UnifiedTheory.Audit.KFCausalShiftedGaussianPureSourceCurves
import UnifiedTheory.Audit.KFCausalMixedFieldCoherentPureClock
import UnifiedTheory.Audit.KFCausalClockFloorPureClockInverseHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCoherentSecondPureDomains
noncomputable section
open MeasureTheory
open KFCausalClockFloorPureClockMomentum (pureMomentum pure_selfAdjoint)
open KFCausalClockFloorPureClockInverseHalf (inverse_momentum_domain)
open KFCausalProjectedKineticResponse (integral_closed_graph)
open KFCausalCoherentSecondCurves
open KFCausalClockFloorCoherentBounds (sourceSize)
open KFCausalPhysicalEnergyFactors (modelDirections)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ Real.pi*ε/3)
  (p B : ℝ) (C : ℝ → ℂ) (b : ℝ → Fin 5 → ℂ)
  (hCc : Continuous C) (hbc : Continuous b) (hC : ∀ θ, ‖C θ‖ ≤ 1)
  (hB : ∀ θ, sourceSize (b θ) ≤ B)
local notation "L" => pureMomentum ε hε h

include hh hCc hbc hC hB in
theorem clock_domain : meanClock ε a α β hε ha hα hβ hw C (fun _ => p) b ∈ (L).domain :=
  LinearPMap.mem_domain_of_mem_graph (integral_closed_graph L (pure_selfAdjoint ε hε h hh).isClosed _ _
    (clock_continuous ε a α β hε ha hα hβ hw B C (fun _ => p) b hCc continuous_const hbc hC hB)
    (KFCausalFullClockPureSourceCurves.output_continuous ε a α β hε ha hα hβ hw p B C b hCc hbc hC hB h)
    (fun θ => KFCausalFullClockPureSourceCurves.graph ε a α β hε ha hα hβ hw p h hh (C θ) (b θ)))

include hh hCc hbc hC hB in
theorem kinetic_domain (i : Fin 4) : meanKinetic ε a α β hε ha hα hβ hw h C (fun _ => p) b i ∈ (L).domain := by
  apply inverse_momentum_domain ε hε h hh
  exact LinearPMap.mem_domain_of_mem_graph (integral_closed_graph L (pure_selfAdjoint ε hε h hh).isClosed _ _
    (kinetic_continuous ε a α β hε ha hα hβ hw h B C (fun _ => p) b hCc continuous_const hbc hC hB i)
    (KFCausalSourcedKineticSecondPureClock.output_continuous ε a α β hε ha hα hβ hw p B C b hCc hbc hB h
      (modelDirections i))
    (fun θ => KFCausalSourcedKineticSecondPureClock.graph ε a α β hε ha hα hβ hw p h hh
      (modelDirections i) (C θ) (b θ)))

include hh hCc hbc hC hB in
theorem vacuum_domain : meanVacuum ε a α β hε ha hα hβ hw h hb C (fun _ => p) b ∈ (L).domain := by
  have hy := KFCausalClockFloorShiftedOutput.shift_bound ε (2*h) (KFCausalGaussianVacuumSquare.double_strip ε h hb)
  apply inverse_momentum_domain ε hε h hh
  exact LinearPMap.mem_domain_of_mem_graph (integral_closed_graph L (pure_selfAdjoint ε hε h hh).isClosed _ _
    (vacuum_continuous ε a α β hε ha hα hβ hw h hb |p| B C (fun _ => p) b hCc continuous_const hbc hC
      (fun _ => le_rfl) hB)
    (KFCausalShiftedGaussianPureSourceCurves.output_continuous ε a α β p (-(2*h)/2) hε ha hα hβ hw hy
      B C b hCc hbc hB h)
    (fun θ => KFCausalShiftedGaussianPureSourceCurves.graph ε a α β p (-(2*h)/2) hε ha hα hβ hw hy
      h hh (C θ) (b θ)))

include hh hCc hbc hB in
theorem matter_domain (j : Fin 2) :
    KFCausalCoherentMatterCurve.meanOutput ε a α β hε ha hα hβ hw h hb C (fun _ => p) b j ∈ (L).domain := by
  have hs := KFCausalMixedFieldGaussianContour.strip_pair ε (-h/2) |-h/2| (-h/2)
    (KFCausalMixedFieldGaussianContour.double_shift_bound ε h hb) le_rfl
  apply inverse_momentum_domain ε hε h hh
  exact LinearPMap.mem_domain_of_mem_graph (integral_closed_graph L (pure_selfAdjoint ε hε h hh).isClosed _ _
    (KFCausalCoherentMatterCurve.spectral_continuous ε a α β hε ha hα hβ hw h hb |p| B
      C (fun _ => p) b hCc continuous_const hbc (fun _ => le_rfl) hB j)
    (KFCausalMixedFieldCoherentPureClock.output_continuous ε a α β (-h/2) p (-h/2)
      hε ha hα hβ hw hs.1 hs.2 B C b hCc hbc hB h j)
    (fun θ => KFCausalMixedFieldCoherentPureClock.graph ε a α β (-h/2) p (-h/2)
      hε ha hα hβ hw hs.1 hs.2 h hh (C θ) (b θ) j))

include hh hCc hbc hC hB in
theorem meanSecond_domain (j : Fin 8) :
    meanSecond ε a α β hε ha hα hβ hw h hb C (fun _ => p) b j ∈ (L).domain := by
  fin_cases j
  · exact clock_domain ε a α β hε ha hα hβ hw h hh p B C b hCc hbc hC hB
  · exact kinetic_domain ε a α β hε ha hα hβ hw h hh p B C b hCc hbc hC hB 0
  · exact kinetic_domain ε a α β hε ha hα hβ hw h hh p B C b hCc hbc hC hB 1
  · exact kinetic_domain ε a α β hε ha hα hβ hw h hh p B C b hCc hbc hC hB 2
  · exact kinetic_domain ε a α β hε ha hα hβ hw h hh p B C b hCc hbc hC hB 3
  · exact matter_domain ε a α β hε ha hα hβ hw h hh hb p B C b hCc hbc hB 0
  · exact matter_domain ε a α β hε ha hα hβ hw h hh hb p B C b hCc hbc hB 1
  · exact vacuum_domain ε a α β hε ha hα hβ hw h hh hb p B C b hCc hbc hC hB

#print axioms clock_domain
#print axioms kinetic_domain
#print axioms vacuum_domain
#print axioms matter_domain
#print axioms meanSecond_domain
end
end UnifiedTheory.Audit.KFCausalCoherentSecondPureDomains
