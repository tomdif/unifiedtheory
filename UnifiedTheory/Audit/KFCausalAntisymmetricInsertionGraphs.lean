/- Actual maximal momentum graphs between bounded insertion outputs. -/
import UnifiedTheory.Audit.KFCausalAntisymmetricInsertionAction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalAntisymmetricInsertionGraphs
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalAntisymmetricMomentumCoordinates (antiDirection)
open KFCausalClockMixedAntisymmetricGraph (momentum_graph_iff)
open KFCausalAntisymmetricInsertionCoordinate (coefficient_real)
open KFCausalAntisymmetricInsertionAction (action action_clockMixed)

variable (ε h a W w : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (k n : ℕ) (i : Fin 2) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a)
  (hw : 1 ≤ w) (hW : w ≤ W) (hb : |h| ≤ ε/10)

theorem momentum_graph (θ : ℝ) (f : Hilbert) :
    (action ε h a W w C p b P k n i hε hh ha hw hW hb θ 0 (by simp) f,
      action ε h a W w C p b P k (n+1) i hε hh ha hw hW hb θ 0 (by simp) f) ∈
        (transverseMomentum h (antiDirection i)).graph := by
  apply (momentum_graph_iff ε hε h hh i _ _).mpr
  filter_upwards [action_clockMixed ε h a W w C p b P k n i hε hh ha hw hW hb θ 0 (by simp) f,
    action_clockMixed ε h a W w C p b P k (n+1) i hε hh ha hw hW hb θ 0 (by simp) f] with x hn hs
  rw [hn,hs]
  simp only [KFCausalAntisymmetricInsertionMultiplier.multiplier,
    Complex.ofReal_zero,zero_mul,add_zero,Complex.ofReal_re,coefficient_real ε hε h i x,pow_succ]
  ring

#print axioms momentum_graph
end
end UnifiedTheory.Audit.KFCausalAntisymmetricInsertionGraphs
