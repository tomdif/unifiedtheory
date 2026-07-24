/-
  Audit/KFCausalCSpecEffectiveGlobalization.lean   (arc file 8/6 — globalization)

  EFFECTIVE CSPEC GLOBALIZATION — construct-then-forget

  Goal: realize the already-proved connected four-state S3 chart complex as ONE
  finite CSpec whose INTRINSIC census recovers the two adjacent transpositions,
  yielding surjective S3 monodromy, no global sheet section, and the instantiated
  twisted gap.  The strategy is to BUILD the carrier from the known voltage /
  monodromy data and then FORGET the construction labels, forcing the census
  (files 1-7) to re-derive them from the global causal order alone.

  PROOF LADDER (this file opens it):
    1. three-sheet cover of the four-state base  ...................  [THIS FILE]
    2. thicken each fibre by the native Boolean B_3 chart
    3. one finite specialization poset / causal algebra (Grothendieck)
    4. antisymmetry + enumerate away unintended splice relations   [KEYSTONE]
    5. CSpec regular neighborhoods recover the four Boolean charts
    6. recompute overlap scores from the GLOBAL causal order only  [ANTI-CIRC.]
    7. invoke booleanCube_isCanonical / restrictionStable to recover transitions
    8. compute the two loop products as (01) and (12)
    9. conclude MonodromyImage = univ, NoGlobalSheetSection, TwistedKernel = 0

  ANTI-CIRCULARITY CONTRACT (step 6): the recovery theorem must receive only the
  global carrier's causal/CSpec data, never the permutations used to build it.
  Enforced by keeping the construction behind an opaque boundary.

  SCOPE: order/conformal sector only.  Even when complete this does NOT touch the
  volume-sector certificate or the quantitative Hauptvermutung (Malament: an
  order-derived census is blind to the scale factor).

  STEP 1 is concrete here and reuses the proven witness, so the TARGET monodromy
  is fixed before any poset is built.  Steps 2-9 are the substantive remainder.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalSheetHolonomyWitness

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecEffectiveGlobalization

open UnifiedTheory.Audit.KFCausalSheetHolonomyWitness
open UnifiedTheory.Audit.KFCausalSheetConnectionLaplacian

/-! ## Step 1 — the three-sheet cover of the four-state base -/

/-- A point of the cover: a base state paired with one of the three sheets
(= directions). -/
abbrev CoverPoint := WitnessState × Fin 3

/-- Sheet transport along one base edge `i → j`: the witnessed edge permutation. -/
def edgeSheet (i j : WitnessState) (s : Fin 3) : Fin 3 := witnessSheetTransport i j s

/-- Sheet transport along a positive base path (the cover's parallel transport). -/
noncomputable def pathSheet {a b : WitnessState}
    (p : PositiveConnectionPath fullS3WitnessConnection a b) : Equiv.Perm (Fin 3) :=
  positivePathSheetTransport fullS3WitnessConnection p

/-- The first base cycle `0 → 1 → 3 → 0` transports the fibre by `(0 1)`. -/
theorem cycle1_transposition : pathSheet swapZeroOneLoop = swapZeroOne :=
  swapZeroOneLoop_holonomy

/-- The second base cycle `0 → 2 → 3 → 0` transports the fibre by `(1 2)`. -/
theorem cycle2_transposition : pathSheet swapOneTwoLoop = swapOneTwo :=
  swapOneTwoLoop_holonomy

/-- The two cycle holonomies are the adjacent transpositions generating `S3`. -/
theorem cover_two_generating_transpositions :
    pathSheet swapZeroOneLoop = swapZeroOne ∧ pathSheet swapOneTwoLoop = swapOneTwo :=
  ⟨cycle1_transposition, cycle2_transposition⟩

/-- **The cover carries full `S3` monodromy over the base point `0`.**  Inherited
from the witnessed connection, this fixes the TARGET monodromy of the
globalization before any poset is constructed: every fibre permutation is the
transport of some positive closed base path. -/
theorem cover_hasFullS3Monodromy : HasFullS3Holonomy fullS3WitnessConnection 0 :=
  fullS3WitnessConnection_hasFullS3Holonomy

#print axioms cover_two_generating_transpositions
#print axioms cover_hasFullS3Monodromy

end UnifiedTheory.Audit.KFCausalCSpecEffectiveGlobalization
