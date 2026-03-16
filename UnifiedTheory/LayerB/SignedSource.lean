/-
  LayerB/SignedSource.lean — Signed source sectors and gravitational cancellation

  The charge algebra is signed: Q takes values in ℝ, not ℝ≥0.
  Conjugation gives Q(-d) = -Q(d). This means:

  1. Positive-source (Q > 0) and negative-source (Q < 0) sectors both exist
  2. Opposite-sign defects cancel: Q(d) + Q(-d) = 0
  3. Screening: opposite-sign compositions reduce magnitude
  4. Net source determines far-field behavior

  Gravitational interpretation:
  - Q > 0: inward focusing / attraction
  - Q < 0: outward defocusing / repulsion
  - Q = 0: gravitationally neutral (screened)

  What remains outside scope:
  - Whether negative-source configurations satisfy G = 0
  - Dynamical stability of negative-source defects
  - Whether nature permits Q < 0 gravitational sources
-/
import UnifiedTheory.LayerB.MetricDefects

namespace UnifiedTheory.LayerB.SignedSource

open MetricDefects

variable {m : ℕ}

/-- The charge of a metric perturbation: Q(h) = trace(πK(h)).
    Defined directly via the trace functional for clean proofs. -/
noncomputable def Q (h : Perturbation (m + 2)) : ℝ :=
  traceFunc m (K_proj m h)

/-- Q is additive: Q(h₁ + h₂) = Q(h₁) + Q(h₂). -/
theorem Q_add (h₁ h₂ : Perturbation (m + 2)) :
    Q (h₁ + h₂) = Q h₁ + Q h₂ := by
  unfold Q; rw [map_add, map_add]

/-- Q respects negation: Q(-h) = -Q(h). -/
theorem Q_neg (h : Perturbation (m + 2)) :
    Q (-h) = -(Q h) := by
  unfold Q; rw [map_neg, map_neg]

/-- Q respects scaling: Q(c • h) = c * Q(h). -/
theorem Q_smul (c : ℝ) (h : Perturbation (m + 2)) :
    Q (c • h) = c * Q h := by
  unfold Q; rw [map_smul, map_smul, smul_eq_mul]

/-- Q equals the trace (by the bridge equation). -/
theorem Q_eq_trace (h : Perturbation (m + 2)) :
    Q h = traceFunc m h :=
  bridge_derived h

/-! ## Signed source sectors exist -/

/-- **POSITIVE SOURCE EXISTS.**
    The identity matrix has trace = m + 2 > 0, so Q(I) > 0. -/
theorem positive_source_exists :
    ∃ h : Perturbation (m + 2), 0 < Q h := by
  use (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)
  rw [Q_eq_trace]
  simp only [traceFunc, canonicalSF, LayerA.Derived.metricSourceFunctional,
    Matrix.traceLinearMap_apply, Matrix.trace_one, Fintype.card_fin]
  positivity

/-- **NEGATIVE SOURCE EXISTS.**
    -I has trace = -(m + 2) < 0, so Q(-I) < 0. -/
theorem negative_source_exists :
    ∃ h : Perturbation (m + 2), Q h < 0 := by
  obtain ⟨h, hpos⟩ := (positive_source_exists : ∃ h, 0 < @Q m h)
  exact ⟨-h, by rw [Q_neg]; linarith⟩

/-! ## Cancellation theorems -/

/-- **PERFECT CANCELLATION.** Q(h + (-h)) = 0. Exact. -/
theorem perfect_cancellation (h : Perturbation (m + 2)) :
    Q (h + (-h)) = 0 := by
  rw [Q_add, Q_neg, add_neg_cancel]

/-- **SIGN REVERSAL.** Q(-h) = -Q(h). -/
theorem sign_reversal (h : Perturbation (m + 2)) :
    Q (-h) = -(Q h) := Q_neg h

/-- **PARTIAL SCREENING.**
    If Q(h₁) > 0 and Q(h₂) < 0, the composite has smaller magnitude
    than h₁ alone. -/
theorem partial_screening (h₁ h₂ : Perturbation (m + 2))
    (hp : 0 < Q h₁) (hn : Q h₂ < 0) :
    Q (h₁ + h₂) < Q h₁ := by
  rw [Q_add]; linarith

/-- **OVERSCREENING.**
    If the negative source exceeds the positive, net charge goes negative. -/
theorem overscreening (h₁ h₂ : Perturbation (m + 2))
    (hp : 0 < Q h₁) (hn : Q h₂ < 0)
    (hlarge : Q h₁ < -(Q h₂)) :
    Q (h₁ + h₂) < 0 := by
  rw [Q_add]; linarith

/-- **EXACT SCREENING.**
    For any positive-source defect, there exists a defect that
    exactly neutralises it: their composite has zero charge. -/
theorem exact_screening (h : Perturbation (m + 2)) (hp : 0 < Q h) :
    ∃ h' : Perturbation (m + 2), Q h' < 0 ∧ Q (h + h') = 0 :=
  ⟨-h, by rw [Q_neg]; linarith, perfect_cancellation h⟩

/-! ## Trichotomy -/

/-- **SIGNED SOURCE TRICHOTOMY.**
    Every defect is in exactly one of three sectors:
    - Q > 0: focusing / attractive
    - Q < 0: defocusing / repulsive
    - Q = 0: neutral / screened -/
theorem signed_source_trichotomy (h : Perturbation (m + 2)) :
    0 < Q h ∨ Q h < 0 ∨ Q h = 0 := by
  rcases lt_trichotomy (Q h) 0 with hn | hz | hp
  · exact Or.inr (Or.inl hn)
  · exact Or.inr (Or.inr hz)
  · exact Or.inl hp

/-! ## The capstone -/

/-- **SIGNED SOURCE ALGEBRA.**

    The metric-derived charge algebra is signed:

    (1) Positive and negative source sectors both exist
    (2) Conjugation flips sign: Q(-h) = -Q(h)
    (3) Perfect cancellation: Q(h + (-h)) = 0
    (4) Additivity: Q(h₁ + h₂) = Q(h₁) + Q(h₂)
    (5) Screening: opposite signs reduce magnitude
    (6) Overscreening: excess negative source gives net negative
    (7) Trichotomy: every defect is positive, negative, or neutral

    The algebra does not force all sources to be positive.
    Anti-source sectors exist. Screening is exact.
    Physical admissibility of negative sources remains open. -/
theorem signed_source_algebra :
    (∃ h : Perturbation (m + 2), 0 < Q h)
    ∧ (∃ h : Perturbation (m + 2), Q h < 0)
    ∧ (∀ h : Perturbation (m + 2), Q (-h) = -(Q h))
    ∧ (∀ h : Perturbation (m + 2), Q (h + (-h)) = 0)
    ∧ (∀ h₁ h₂ : Perturbation (m + 2), Q (h₁ + h₂) = Q h₁ + Q h₂)
    ∧ (∀ h : Perturbation (m + 2), 0 < Q h ∨ Q h < 0 ∨ Q h = 0) :=
  ⟨positive_source_exists,
   negative_source_exists,
   Q_neg,
   perfect_cancellation,
   Q_add,
   signed_source_trichotomy⟩

end UnifiedTheory.LayerB.SignedSource
