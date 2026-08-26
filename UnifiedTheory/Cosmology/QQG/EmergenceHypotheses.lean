/-
  Cosmology/QQG/EmergenceHypotheses.lean
  ──────────────────────────────────────────────

  Explicit ledger of the assumptions the paper makes that are NOT
  proved in the paper itself, and therefore cannot be proved in Lean
  without going beyond the paper's content.

  Each is encoded as an externally supplied predicate in
  `QQGEmergenceClaims`.  A value of `QQGEmergenceHypotheses claims` must
  then provide evidence for those predicates.  This separation is important:
  the predicates are not fixed definitions returning `True`, so the formal
  interface itself supplies no emergence witness.  Callers remain responsible
  for choosing non-vacuous physical meanings and justifying their evidence.

  This file mirrors the "scope caveat" lists in the other Cosmology/QQG
  modules and is the load-bearing IOU of the QQG-cosmology bridge.
-/

import UnifiedTheory.Cosmology.QQG.Couplings
import UnifiedTheory.Cosmology.QQG.LargeNSolution

set_option relaxedAutoImplicit false

namespace UnifiedTheory.Cosmology.QQG

/-! ## 1. External physical-content predicates -/

/-- The six physical claims required by the QQG emergence story.  The fields
are predicates, not theorem values.  A concrete physical model must define
what each predicate means before evidence can be supplied. -/
structure QQGEmergenceClaims where
  /-- Quantum containment of the spin-2 ghost, indexed by bare coupling and
  matter weight. -/
  ghostResolution : ℝ → ℝ → Prop
  /-- Consistency of Weyl perturbations with the intended cosmological
  constraints, indexed by 't Hooft coupling and e-fold count. -/
  weylPerturbationConsistency : ℝ → ℝ → Prop
  /-- Correctness of the selected physical beta-function scheme. -/
  physicalBetaScheme : QQGCouplings → Prop
  /-- Realization of the proposed no-boundary initial state. -/
  noBoundaryInitialState : ℝ → ℝ → Prop
  /-- Coincidence of the tachyon crossing, strong coupling, and reheating. -/
  strongCouplingCoincidence : ℝ → Prop
  /-- Emergence of general relativity at a matching scale. -/
  emergentGR : ℝ → Prop

/-! ## 2. The bundled hypothesis structure -/

/-- Evidence for a specified QQG emergence claim ledger.  Each downstream
theorem that depends on the QQG-to-GR-EFT story must quantify over an explicit
`claims` value and take this evidence as a hypothesis. -/
structure QQGEmergenceHypotheses (claims : QQGEmergenceClaims) : Prop where
  /-- The spin-2 ghost is contained. -/
  ghost_resolved : ∀ lam₀ N, claims.ghostResolution lam₀ N
  /-- Weyl-perturbation analysis works out. -/
  weyl_perturbations_ok :
    ∀ lam_tH N_e, claims.weylPerturbationConsistency lam_tH N_e
  /-- We are using the "physical" β-functions of ref [50]. -/
  physical_beta_scheme : ∀ c, claims.physicalBetaScheme c
  /-- Initial state is no-boundary. -/
  no_boundary_initial_state :
    ∀ lam₀ N, claims.noBoundaryInitialState lam₀ N
  /-- Tachyon-divide crossing coincides with strong coupling / reheating. -/
  strong_coupling_coincidence :
    ∀ lam_tH, claims.strongCouplingCoincidence lam_tH
  /-- GR emerges as IR EFT below the matching surface. -/
  emergent_gr : ∀ matchingScale, claims.emergentGR matchingScale

/-! ## 3. The "viability" constraints (paper §5) -/

/-- The paper's viable parameter window: λ_tH ∈ (0.1, 1] and
    N_matter ∈ [10⁵, 10⁶].  These are *observationally* preferred
    by the CMB+BAO data combination in the paper (Fig. 3), not
    derived from first principles. -/
structure QQGViableParameters where
  lam_tH : ℝ
  N_matter : ℝ
  lam_tH_pos : 0 < lam_tH
  lam_tH_le_one : lam_tH ≤ 1
  lam_tH_ge_tenth : 1/10 ≤ lam_tH
  N_matter_lower : 100000 ≤ N_matter
  N_matter_upper : N_matter ≤ 1000000

/-! ## 4. No-built-in-witness sanity check -/

/-- A deliberately impossible claim ledger.  It witnesses that the interface
does not make every emergence ledger automatically inhabitable. -/
def QQGEmergenceClaims.impossible : QQGEmergenceClaims where
  ghostResolution := fun _ _ => False
  weylPerturbationConsistency := fun _ _ => False
  physicalBetaScheme := fun _ => False
  noBoundaryInitialState := fun _ _ => False
  strongCouplingCoincidence := fun _ => False
  emergentGR := fun _ => False

/-- Unlike the former fixed `True`-valued placeholder encoding, this API does
not supply evidence for every ledger.  This theorem does not prevent a caller
from defining a different ledger whose predicates themselves are vacuous. -/
theorem impossible_emergence_claims_not_satisfied :
    ¬ QQGEmergenceHypotheses QQGEmergenceClaims.impossible := by
  intro hyp
  exact hyp.ghost_resolved 1 1

end UnifiedTheory.Cosmology.QQG
