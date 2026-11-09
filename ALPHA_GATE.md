# The alpha = ln(5/3)/70 falsification gate (restated 2026-08-16)

STATUS: OPEN - the oldest unfinished audit of the program.

CLAIM (project_unifiedtheory, 2026-05): alpha(0) = ln(5/3)/70
matches CODATA to 0.0021%.  RG audit (2026-07-23) registered the
gate: the claim is numerology UNLESS the discrete structure derives
the ADJOINT representation content of the SM gauge group (the 70
must be a computed group-theoretic weight, not a fitted integer).

WHAT THE NEW STRUCTURE OFFERS (2026-08 arc), honestly assessed:
  - The species group derived from k-factor composites is Z2^k
    (fermion parity sectors) - ABELIAN.  No route to nonabelian
    adjoints is visible from the JW/Clifford tower as built.
  - The Z8 octant clock decays dynamically to Z2; nothing in the
    growth law manufactures SU(3)xSU(2)xU(1) weights.
  - 70 = C(8,4) is suggestive next to the octant clock (8 levels),
    but we have NO derivation connecting binomial(8,4) to the
    energy-level structure; recording the coincidence is not
    evidence.
GATE (unchanged): produce a derivation of adjoint content from the
growth law, or the alpha claim is FALSIFIED-BY-DEFAULT and must be
dropped from the ToE ledger.  Current arc's structures do NOT close
it; they narrow it (any derivation must break the abelian Z2^k
pattern, i.e. must come from the coupled r>0 regime or from
structure above the flat law).

## Precision + look-elsewhere audit (2026-09-16)

1. EXACT IDENTITY EXCLUDED (Lean, axiom-clean):
   `Audit/FineStructureIRPrecisionExclusion.lean` proves
   70/ln(5/3) < 137.034, i.e. > 9×10⁴ σ below CODATA 137.035999177(21)
   (true miss 0.00294 ≈ 1.4×10⁵ σ). The older `prediction_brackets_PDG`
   was a bracket-width artifact. Any surviving claim is "leading term",
   and must name the origin of a 2.1×10⁻⁵ relative correction.
2. LOOK-ELSEWHERE (alpha_look_elsewhere.py, 200k log-uniform null
   targets within an octave of alpha, hit = rel. error ≤ 2.14×10⁻⁵):
   - γ₄/q, q 7-smooth ≤ 5000 (265 forms):   p = 8.3×10⁻⁴ per target
   - recorded search p/q ∪ √(p/q) ∪ γ₄/q:   p = 1.3×10⁻²
   - with ≥ 7 scanned observables:          p_global ≈ 0.006 (γ₄/q) / 0.09 (union)
   - with 20:                               p_global ≈ 0.016 / 0.23
   Reading: taken as a γ₄/q-family hit, p ≈ 0.006 (≈2.5σ) after a 7-observable trials factor —
   not negligible, not decisive, and it cannot substitute for the
   adjoint-content derivation above. Gate status unchanged: OPEN.

## Closed 2026-10-25: FALSIFIED-BY-DEFAULT
See GAUGE_AND_ALPHA_GATES_2026-10-25.md. Adjoint content is not derivable from the order
(Audit/CausalOrderGaugeUniversality.lean; minimal chiral search finds 5/12/14-fermion
theories beating the SM). The framework's own unification boundary conditions with SM content
hit an alpha_3 Landau pole above M_Z (unification_running_test.py), so there is no
dynamical origin for ln(5/3)/70 or its 2.1e-5 correction.
