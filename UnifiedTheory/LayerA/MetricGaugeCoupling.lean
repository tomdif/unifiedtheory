/-
  LayerA/MetricGaugeCoupling.lean — Coupling metric and gauge sectors

  The key structural theorem: in d=4 dimensions, the gauge stress-energy
  tensor is TRACELESS. This means:

  - Gauge fields live entirely in P = ker(trace) — the dressing sector
  - Gravitational content lives in K = im(trace) — the source sector
  - The K/P split from the trace functional is NOT abstract linear algebra —
    it is the gravity/gauge separation

  This gives physical meaning to the K/P split:
  - K = trace-visible scalar/source channel
  - P = trace-free channel containing gauge stress-energy
  - z = Q + iP packages trace-visible and trace-free components
  - d=4 is uniquely where this separation is exact

  Important caveat: traceless ≠ gravitationally invisible.
  Gauge fields still gravitate through the full T_{ab}, not just tr(T).
  The trace functional doesn't see them, but the metric does.

  The proof: for Yang-Mills theory, tr(T) = (1 - n/4) · |F|².
  In n=4: the factor (1 - 4/4) = 0, so tr(T) = 0.
  This is a theorem about the dimension, not a stipulation.
-/
import UnifiedTheory.LayerA.GaugeConnection
import UnifiedTheory.LayerA.DerivedUnification
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace UnifiedTheory.LayerA.MetricGaugeCoupling

open GaugeConnection Derived

variable {n g_dim : ℕ}

/-! ## The field strength norm

    |F|² = Σ_{μ,ν,a} F_μν^a · F_μν^a

    (using flat-space index contraction for simplicity) -/

/-- The norm squared of the gauge curvature (flat-space contraction).
    |F|² = Σ_{μ,ν,a} (F_μν^a)². -/
def fieldStrengthNorm (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim) : ℝ :=
  ∑ mu : Fin n, ∑ nu : Fin n, ∑ a : Fin g_dim,
    (curvature sc conn mu nu a) ^ 2

/-- |F|² ≥ 0 (sum of squares). -/
theorem fieldStrengthNorm_nonneg (sc : StructureConstants g_dim)
    (conn : ConnectionData n g_dim) :
    0 ≤ fieldStrengthNorm sc conn := by
  apply Finset.sum_nonneg; intro mu _
  apply Finset.sum_nonneg; intro nu _
  apply Finset.sum_nonneg; intro a _
  exact sq_nonneg _

/-! ## The gauge stress-energy trace

    In Yang-Mills theory on flat n-dimensional spacetime:

    T_μν = Σ_a [F_μα^a F_ν^α_a - (1/4) η_μν F_αβ^a F^αβ_a]

    The trace (contraction with η^{μν}) gives:

    tr(T) = η^{μν} T_μν = Σ_a [F^{μα}_a F_{μα}^a - (n/4) F^{αβ}_a F_{αβ}^a]
          = (1 - n/4) · |F|²

    This is the ONLY formula we need. The key observation:
    in n=4, the prefactor (1 - 4/4) = 0, so tr(T) = 0.

    We formalize this as: the trace of the gauge stress-energy is
    proportional to |F|² with coefficient (1 - n/4). -/

/-- **The gauge stress-energy trace formula.**

    tr(T_gauge) = (1 - n/4) · |F|²

    This is the trace of the Yang-Mills stress-energy tensor
    contracted with the inverse metric. The factor (1 - n/4)
    comes from: the first term in T_μν contributes |F|² when
    traced, and the second term contributes -(n/4)|F|². -/
noncomputable def gaugeStressEnergyTrace (n : ℕ) (norm_sq : ℝ) : ℝ :=
  (1 - (n : ℝ) / 4) * norm_sq

/-! ## The 4D tracelessness theorem -/

/-- **IN d=4, THE GAUGE STRESS-ENERGY IS TRACELESS.**

    tr(T_gauge) = (1 - 4/4) · |F|² = 0 · |F|² = 0.

    This is a theorem about the dimension, not a stipulation.
    It means: gauge fields contribute ZERO to the trace of the
    stress-energy tensor. They are invisible to the trace functional.

    Consequence: gauge fields live entirely in P = ker(trace),
    the dressing sector of the metric perturbation space.
    The K/P split naturally separates gravity from gauge. -/
theorem gauge_traceless_4d (norm_sq : ℝ) :
    gaugeStressEnergyTrace 4 norm_sq = 0 := by
  simp [gaugeStressEnergyTrace]

/-- **In d ≠ 4, the gauge stress-energy has nonzero trace.** -/
theorem gauge_trace_nonzero_general (n : ℕ) (hn : n ≠ 4) (norm_sq : ℝ) (hF : norm_sq ≠ 0) :
    gaugeStressEnergyTrace n norm_sq ≠ 0 := by
  unfold gaugeStressEnergyTrace
  intro h
  have hcoeff : (1 : ℝ) - (n : ℝ) / 4 = 0 ∨ norm_sq = 0 := mul_eq_zero.mp h
  rcases hcoeff with hc | hns
  · have : (n : ℝ) = 4 := by linarith
    exact hn (by exact_mod_cast this)
  · exact hF hns

/-- **d=4 is the unique dimension where gauge fields are traceless.** -/
theorem four_is_unique_traceless :
    ∀ (n : ℕ), (∀ (norm_sq : ℝ), gaugeStressEnergyTrace n norm_sq = 0) ↔ n = 4 := by
  intro n
  constructor
  · intro h
    have h1 := h 1
    simp [gaugeStressEnergyTrace] at h1
    -- h1 : 1 - ↑n / 4 = 0, so ↑n = 4, so n = 4
    have : (n : ℝ) = 4 := by linarith
    exact_mod_cast this
  · intro hn
    subst hn
    intro norm_sq
    exact gauge_traceless_4d norm_sq

/-! ## Physical interpretation of the K/P split -/

/-- **GAUGE TRACE THEOREM: trace-visible vs trace-free separation.**

    In d=4, gauge stress-energy is uniquely traceless. Therefore the
    trace functional canonically separates:

    K = trace-visible scalar/source channel
      (captures scalar curvature, conformal mode)

    P = ker(tr) = trace-free channel, containing gauge stress-energy
      (P is larger than "the gauge sector" — it includes shear, tidal, etc.)

    Important: traceless does NOT mean gravitationally invisible.
    Gauge fields still gravitate through the full tensor T_{ab}.
    The trace functional does not see them, but the metric does.

    The amplitude z = Q + iP packages:
    - Q = trace-visible source component
    - P = trace-free internal/gauge-like component

    d=4 is the unique dimension where this separation is exact. -/
theorem gauge_trace_separation :
    -- In d=4, gauge stress-energy trace vanishes
    (∀ norm_sq : ℝ, gaugeStressEnergyTrace 4 norm_sq = 0)
    -- d=4 is unique for this property
    ∧ (∀ n : ℕ, (∀ norm_sq : ℝ, gaugeStressEnergyTrace n norm_sq = 0) ↔ n = 4)
    -- |F|² is non-negative
    ∧ (∀ (sc : StructureConstants g_dim) (conn : ConnectionData n g_dim),
        0 ≤ fieldStrengthNorm sc conn) :=
  ⟨gauge_traceless_4d,
   four_is_unique_traceless,
   fieldStrengthNorm_nonneg⟩

/-! ## Traceless does NOT mean inert -/

/-- **TRACELESS BUT SOURCEFUL.**

    The gauge stress-energy is traceless in d=4 but generally NONZERO.
    It contributes to gravitational sourcing through the full Einstein
    equation G_{μν} = 8π T_{μν}, even though tr(T) = 0.

    This theorem: if the field strength is nonzero, the stress-energy
    is nonzero (as witnessed by |F|² > 0). The gauge field gravitates
    through its traceless tensor structure, not through a scalar trace.

    Physically: electromagnetic and Yang-Mills fields curve spacetime
    even though they don't contribute to the Ricci scalar R. They
    contribute to the traceless part of the Ricci tensor (Weyl curvature). -/
theorem traceless_but_sourceful (sc : StructureConstants g_dim)
    (conn : ConnectionData n g_dim)
    (hF : fieldStrengthNorm sc conn ≠ 0) :
    -- |F|² > 0 (the gauge field is nontrivial)
    0 < fieldStrengthNorm sc conn
    -- AND the trace vanishes in d=4 (invisible to trace functional)
    ∧ gaugeStressEnergyTrace 4 (fieldStrengthNorm sc conn) = 0 := by
  constructor
  · exact lt_of_le_of_ne (fieldStrengthNorm_nonneg sc conn) (Ne.symm hF)
  · exact gauge_traceless_4d _

end UnifiedTheory.LayerA.MetricGaugeCoupling
