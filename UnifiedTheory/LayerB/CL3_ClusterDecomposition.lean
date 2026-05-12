/-
  LayerB/CL3_ClusterDecomposition.lean — Cluster decomposition (M6) for the
                                          discrete chamber-projected Yang-Mills
                                          measure.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST SCOPE — read this first.

  In `LayerB/CL3_ConstructiveMeasure.lean` we tagged property M6 (cluster
  decomposition of the YM measure) as `NeedsClusterExp`.  This file
  TIGHTENS that classification on the chamber sector by proving
  cluster decomposition AS AN ALGEBRAIC CONSEQUENCE OF THE CHAMBER MASS
  GAP.

  The argument is the standard QFT one:

    For a transfer-matrix theory with vacuum eigenvalue λ_top and a
    spectral gap above the vacuum γ > 0, the connected two-point
    correlator decays exponentially:

         |⟨W₁(x) W₂(y)⟩ − ⟨W₁⟩⟨W₂⟩|  ≤  C · exp(−γ · t(x,y)),

    where t(x,y) is the causal-set distance.  In particular, as
    t(x,y) → ∞, the connected correlator vanishes — this IS cluster
    decomposition.

  WHAT THIS FILE PROVES (PROVED, no estimates, no asymptotics):

    (1) A spectral two-point correlator on the chamber sector,
        defined as the standard transfer-matrix sum
              W(t) = Σₙ |cₙ|² · (λₙ / λ_top)^t,
        with three eigenstates (vacuum λ_top = 3/5, excited
        (5+√7)/30, excited (5−√7)/30).

    (2) The connected two-point correlator
              W_conn(t) = W(t) − |c_top|² (vacuum factorization)
        is a finite sum of exponentially decaying terms with rate
        bounded BELOW by the chamber gap γ_chamber = (13 − √7)/30 in
        the additive form, OR ln(5 − √7) in the log/mass form.

    (3) EXPONENTIAL DECAY: |W_conn(t)| ≤ C · exp(− γ_log · t) for
        all t ≥ 0, where γ_log = ln(5 − √7) > 0 and
        C = |c_2|² + |c_3|².

    (4) CLUSTER DECOMPOSITION: ∀ ε > 0, ∃ T₀ such that for every
        t ≥ T₀, |W_conn(t)| < ε.

    (5) MASTER theorem `chamber_cluster_decomposition` bundling all
        of the above.

  WHAT THIS FILE DOES NOT PROVE.

    (X1) Cluster decomposition for the FULL Hilbert space — only the
         chamber sector is treated.  Bath sector control is the open
         problem (X2) of `LayerB/CL1_ContinuumLimit`.
    (X2) Continuum cluster decomposition.  Lifting the discrete
         chamber result to ℝ⁴ requires CL1 + the Glimm-Jaffe
         cluster-expansion machinery in the bath sector.
    (X3) The "Wilson functional" Wₓ is not concretely constructed —
         the sum coefficients |cₙ|² appear as abstract non-negative
         data of any chamber-sector observable.  This matches the
         declarative `WilsonExpectation` interface of
         `CL3_ConstructiveMeasure`.

  HONEST CLASSIFICATION (formalized at the end of this file as
  `M6_chamber_status`):

    M6 (cluster decomposition) was previously `NeedsClusterExp`
    in `CL3_ConstructiveMeasure`.  After this file:

      M6 on the CHAMBER SECTOR  → `DiscreteOnly` (PROVED here).
      M6 on the FULL Hilbert space → still `NeedsClusterExp`.
      M6 in the CONTINUUM         → still `NeedsClusterExp` + `ConditionalCL1`.

  The framework's contribution: an EXACT decay rate (the chamber
  gap, in closed form) for the chamber-sector connected correlator.
  No estimates, no asymptotics — just a finite spectral sum and the
  elementary fact that a < b implies aᵗ ≤ bᵗ for t ≥ 0 when 0 < a, b < 1.

  Zero sorry.  Zero custom axioms.  Built only from Mathlib +
  prior framework files (FeshbachJ4, YangMillsCausalAttack,
  CL3_ConstructiveMeasure).

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Sqrt
import UnifiedTheory.LayerA.FeshbachJ4
import UnifiedTheory.LayerB.YangMillsCausalAttack
import UnifiedTheory.LayerB.CL3_ConstructiveMeasure

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.CL3_ClusterDecomposition

open Real
open UnifiedTheory.LayerA.FeshbachJ4
open UnifiedTheory.LayerB.YangMillsCausalAttack
open UnifiedTheory.LayerB.CL3_ConstructiveMeasure

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  THE CHAMBER SPECTRUM (RE-EXPORT)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The chamber Hamiltonian H_chamber on the 3-channel Yang-Mills
    chamber subspace has eigenvalues

       λ_top = 3/5,    λ_2 = (5+√7)/30,    λ_3 = (5−√7)/30.

    All three are strictly positive and distinct.  The TOP eigenvalue
    plays the role of the vacuum (largest transfer-matrix eigenvalue),
    and the other two are the EXCITED states above the vacuum.

    The transfer-matrix interpretation: the discrete YM transfer matrix
    T_β = exp(−β H_disc) projected to the chamber has these three
    eigenvalues as its principal singular values; the LARGEST one
    (here 3/5) sets the vacuum; the gap to the next is the inverse
    correlation length.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Vacuum eigenvalue (top of chamber spectrum). -/
noncomputable def lam_vac : ℝ := 3 / 5

/-- First excited eigenvalue (5+√7)/30 (parameterized by s = √7). -/
noncomputable def lam_exc1 (s : ℝ) : ℝ := (5 + s) / 30

/-- Second excited eigenvalue (5−√7)/30. -/
noncomputable def lam_exc2 (s : ℝ) : ℝ := (5 - s) / 30

/-- The vacuum is positive. -/
theorem lam_vac_pos : 0 < lam_vac := by unfold lam_vac; norm_num

/-- The first excited state has positive eigenvalue. -/
theorem lam_exc1_pos (s : ℝ) (hs_pos : 0 < s) : 0 < lam_exc1 s := by
  unfold lam_exc1; linarith

/-- The second excited state has positive eigenvalue. -/
theorem lam_exc2_pos (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    0 < lam_exc2 s := by
  unfold lam_exc2
  have h := sqrt7_lt_3 s hs hs_pos
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  RATIOS λ_n / λ_top AND THEIR LOGARITHMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The transfer-matrix spectral decomposition writes

         W(t) = Σ_n |c_n|² · (λ_n / λ_top)^t

    where (λ_n / λ_top) ∈ (0, 1) for excited states (n ≥ 2).  The
    rate of exponential decay is then
         m_n = − ln(λ_n / λ_top) = ln(λ_top / λ_n).

    From `FeshbachJ4`:
      ratio_lambda1_lambda2 :  λ_top / lam_exc1 = 5 − √7
      ratio_lambda1_lambda3 :  λ_top / lam_exc2 = 5 + √7
      five_minus_sqrt7_gt_one :  5 − √7 > 1
      five_plus_sqrt7_gt_one :  5 + √7 > 1

    Hence the inverse ratios lam_exc1/λ_top = 1/(5−√7) ∈ (0,1) and
    lam_exc2/λ_top = 1/(5+√7) ∈ (0,1), with logarithms
         m_1 = ln(5 − √7) > 0      (the chamber MASS GAP)
         m_2 = ln(5 + √7) > 0      (heavier excited mass)
    Both are positive; m_1 ≤ m_2 since (5−√7) ≤ (5+√7).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Ratio lam_exc1 / λ_top = 1 / (5 − √7).
    Re-derived from `ratio_lambda1_lambda2`. -/
theorem ratio_exc1_vac (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    lam_exc1 s / lam_vac = 1 / (5 - s) := by
  unfold lam_exc1 lam_vac
  have h5ps : (5 : ℝ) + s ≠ 0 := by linarith
  have h5ms_pos : (0 : ℝ) < 5 - s := by
    have := sqrt7_lt_3 s hs hs_pos; linarith
  have h5ms : (5 : ℝ) - s ≠ 0 := ne_of_gt h5ms_pos
  field_simp
  nlinarith [hs]

/-- Ratio lam_exc2 / λ_top = 1 / (5 + √7).
    Re-derived from `ratio_lambda1_lambda3`. -/
theorem ratio_exc2_vac (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    lam_exc2 s / lam_vac = 1 / (5 + s) := by
  unfold lam_exc2 lam_vac
  have h5ps : (5 : ℝ) + s ≠ 0 := by linarith
  have h5ms_pos : (0 : ℝ) < 5 - s := by
    have := sqrt7_lt_3 s hs hs_pos; linarith
  have h5ms : (5 : ℝ) - s ≠ 0 := ne_of_gt h5ms_pos
  field_simp
  nlinarith [hs]

/-- The first excited ratio is in (0, 1): exponentially decaying. -/
theorem ratio_exc1_in_open_unit_interval
    (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    0 < lam_exc1 s / lam_vac ∧ lam_exc1 s / lam_vac < 1 := by
  refine ⟨?_, ?_⟩
  · exact div_pos (lam_exc1_pos s hs_pos) lam_vac_pos
  · rw [ratio_exc1_vac s hs hs_pos]
    have h_gt_one : 1 < 5 - s := five_minus_sqrt7_gt_one s hs hs_pos
    rw [div_lt_one (by linarith : (0:ℝ) < 5 - s)]
    linarith

/-- The second excited ratio is in (0, 1): exponentially decaying. -/
theorem ratio_exc2_in_open_unit_interval
    (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    0 < lam_exc2 s / lam_vac ∧ lam_exc2 s / lam_vac < 1 := by
  refine ⟨?_, ?_⟩
  · exact div_pos (lam_exc2_pos s hs hs_pos) lam_vac_pos
  · rw [ratio_exc2_vac s hs hs_pos]
    have h_gt_one : 1 < 5 + s := five_plus_sqrt7_gt_one s hs_pos
    rw [div_lt_one (by linarith : (0:ℝ) < 5 + s)]
    linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  MASS GAPS AND THE CLUSTER DECAY RATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The "mass" of an excited state n is
         m_n = − ln(λ_n / λ_top) = ln(λ_top / λ_n).

    For our chamber spectrum:
         m_1 = ln(5 − √7) ≈ ln(2.354) ≈ 0.856
         m_2 = ln(5 + √7) ≈ ln(7.646) ≈ 2.034

    The cluster decay rate is the SMALLEST excited-state mass:
         γ_cluster := min(m_1, m_2) = m_1 = ln(5 − √7).

    Since 5 − √7 < 5 + √7 (because √7 > 0), we have m_1 < m_2,
    so γ_cluster = m_1.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The mass of the first excited state: m_1 = ln(λ_top / lam_exc1) = ln(5 − √7). -/
noncomputable def m_exc1 (s : ℝ) : ℝ := Real.log (5 - s)

/-- The mass of the second excited state: m_2 = ln(λ_top / lam_exc2) = ln(5 + √7). -/
noncomputable def m_exc2 (s : ℝ) : ℝ := Real.log (5 + s)

/-- m_1 = ln(5 − √7) is positive (the chamber mass gap). -/
theorem m_exc1_pos (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    0 < m_exc1 s := by
  unfold m_exc1
  exact Real.log_pos (five_minus_sqrt7_gt_one s hs hs_pos)

/-- m_2 = ln(5 + √7) is positive. -/
theorem m_exc2_pos (s : ℝ) (hs_pos : 0 < s) :
    0 < m_exc2 s := by
  unfold m_exc2
  exact Real.log_pos (five_plus_sqrt7_gt_one s hs_pos)

/-- The cluster decay rate: γ_cluster := m_1 = ln(5 − √7).
    This is the SMALLEST excited-state mass and hence the
    rate at which the connected two-point correlator decays. -/
noncomputable def γ_cluster (s : ℝ) : ℝ := Real.log (5 - s)

/-- γ_cluster = m_exc1 by definition. -/
theorem γ_cluster_eq_m_exc1 (s : ℝ) : γ_cluster s = m_exc1 s := rfl

/-- The cluster decay rate is positive. -/
theorem γ_cluster_pos (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    0 < γ_cluster s := m_exc1_pos s hs hs_pos

/-- m_1 ≤ m_2: the FIRST excited mass is smaller than the second.
    Reason: 5 − √7 < 5 + √7, hence ln(5 − √7) < ln(5 + √7). -/
theorem m_exc1_lt_m_exc2 (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    m_exc1 s < m_exc2 s := by
  unfold m_exc1 m_exc2
  have h5ms_pos : (0 : ℝ) < 5 - s := by
    have := sqrt7_lt_3 s hs hs_pos; linarith
  apply Real.log_lt_log h5ms_pos
  linarith

/-- γ_cluster ≤ m_2: the cluster rate bounds m_2 from below. -/
theorem γ_cluster_le_m_exc2 (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    γ_cluster s ≤ m_exc2 s :=
  le_of_lt (m_exc1_lt_m_exc2 s hs hs_pos)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  THE COMPARISON BETWEEN ADDITIVE AND LOG GAPS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The framework records TWO formulations of the chamber gap:

      Additive form:  γ_add = (13 − √7)/30 ≈ 0.345
      Log/mass form:  γ_log = ln(5 − √7) ≈ 0.856

    Both are strictly positive.  For exponential decay of correlators,
    the LOG form is the physically meaningful "mass gap" — it is the
    decay rate per unit time in
         exp(−γ_log · t) = (lam_exc1 / λ_top)^t = 1/(5 − √7)^t.
    The ADDITIVE form (13 − √7)/30 is the difference of eigenvalues,
    which is the relevant quantity for energy-level gaps in a
    Hamiltonian-time formulation.

    Both gaps live in the same field ℚ(√7) (with the log being a
    transcendental function of an algebraic integer).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Additive chamber gap: γ_add = λ_top − lam_exc1 = (13 − √7)/30. -/
noncomputable def γ_add (s : ℝ) : ℝ := lam_vac - lam_exc1 s

/-- The additive gap equals (13 − √7)/30. -/
theorem γ_add_formula (s : ℝ) : γ_add s = (13 - s) / 30 := by
  unfold γ_add lam_vac lam_exc1
  ring

/-- The additive gap is positive. -/
theorem γ_add_pos (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    0 < γ_add s := by
  unfold γ_add lam_vac lam_exc1
  exact additive_gap_positive s hs hs_pos

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  SPECTRAL REPRESENTATION OF THE TWO-POINT CORRELATOR
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    GENERAL TRANSFER-MATRIX SPECTRAL REPRESENTATION:

         W(t)  =  ⟨Ω| O T^t O |Ω⟩  /  ⟨Ω| T^t |Ω⟩
              =  Σ_n |⟨Ω| O |n⟩|² · (λ_n / λ_top)^t

    where the sum is over eigenstates |n⟩ of T (and equivalently of
    H = − ln T).  Decomposing into vacuum (n = 0, eigenvalue λ_top)
    and excited states:

         W(t)  =  c_top  +  Σ_{n ≥ 1} c_n · (λ_n / λ_top)^t,

    with c_n = |⟨Ω| O |n⟩|² ≥ 0.  The CONNECTED correlator subtracts
    the vacuum piece:

         W_conn(t)  =  W(t) − c_top  =  Σ_{n ≥ 1} c_n · (λ_n / λ_top)^t.

    For the 3-channel chamber sector this is a SUM OF TWO
    EXPONENTIALS:

         W_conn(t) = c_1 · (lam_exc1 / λ_top)^t  +  c_2 · (lam_exc2 / λ_top)^t
                   = c_1 · exp(−m_1 · t)       +  c_2 · exp(−m_2 · t)

    The connected correlator decays exponentially, with rate at LEAST
    γ_cluster = min(m_1, m_2) = m_1 = ln(5 − √7).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The spectral two-point correlator on the chamber sector.

    `t` is the causal-set spacelike distance (a non-negative real),
    `c_top, c_1, c_2` are the squared modulus matrix elements
    |⟨Ω | O | n⟩|² ≥ 0 of the operator O between vacuum and the n-th
    eigenstate.  `s` is the algebraic parameter √7 ∈ ℝ.

    Definition matches the standard transfer-matrix formula:

       W(t) = c_top + c_1 · (lam_exc1/λ_top)^t + c_2 · (lam_exc2/λ_top)^t.

    Using ratio_exc1_vac and ratio_exc2_vac, this is
       W(t) = c_top + c_1 · (1/(5−s))^t + c_2 · (1/(5+s))^t. -/
noncomputable def two_point_correlator
    (s : ℝ) (c_top c_1 c_2 : ℝ) (t : ℝ) : ℝ :=
  c_top
    + c_1 * Real.exp (- m_exc1 s * t)
    + c_2 * Real.exp (- m_exc2 s * t)

/-- The CONNECTED two-point correlator: subtracts the vacuum piece. -/
noncomputable def two_point_connected
    (s : ℝ) (c_1 c_2 : ℝ) (t : ℝ) : ℝ :=
  c_1 * Real.exp (- m_exc1 s * t)
    + c_2 * Real.exp (- m_exc2 s * t)

/-- DECOMPOSITION: W(t) = c_top + W_conn(t). -/
theorem two_point_decomp (s : ℝ) (c_top c_1 c_2 t : ℝ) :
    two_point_correlator s c_top c_1 c_2 t =
      c_top + two_point_connected s c_1 c_2 t := by
  unfold two_point_correlator two_point_connected
  ring

/-- The connected correlator at t = 0 equals c_1 + c_2 (sum of squared
    overlaps with excited states). -/
theorem two_point_connected_at_zero (s : ℝ) (c_1 c_2 : ℝ) :
    two_point_connected s c_1 c_2 0 = c_1 + c_2 := by
  unfold two_point_connected
  simp [Real.exp_zero]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  EXPONENTIAL DECAY OF THE CONNECTED CORRELATOR
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    KEY ESTIMATE:  for non-negative coefficients c_1, c_2 and t ≥ 0,

       |W_conn(t)|  =  W_conn(t)
                    =  c_1 · exp(−m_1 t) + c_2 · exp(−m_2 t)
                    ≤  (c_1 + c_2) · exp(−m_1 t)
                    =  C · exp(−γ_cluster · t)

    where C = c_1 + c_2 and γ_cluster = m_1 = ln(5 − √7).

    Reason: m_1 ≤ m_2 ⇒ exp(−m_2 t) ≤ exp(−m_1 t) for t ≥ 0.

    All steps are elementary applications of monotonicity of exp.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The connected correlator is non-negative when the spectral weights
    c_1, c_2 are non-negative.  This is the standard Källén-Lehmann
    positivity statement on the chamber sector. -/
theorem two_point_connected_nonneg
    (s : ℝ) (c_1 c_2 : ℝ) (t : ℝ)
    (hc_1 : 0 ≤ c_1) (hc_2 : 0 ≤ c_2) :
    0 ≤ two_point_connected s c_1 c_2 t := by
  unfold two_point_connected
  have h1 : 0 ≤ c_1 * Real.exp (- m_exc1 s * t) :=
    mul_nonneg hc_1 (le_of_lt (Real.exp_pos _))
  have h2 : 0 ≤ c_2 * Real.exp (- m_exc2 s * t) :=
    mul_nonneg hc_2 (le_of_lt (Real.exp_pos _))
  linarith

/-- KEY ESTIMATE: exp(−m_2 t) ≤ exp(−m_1 t) for t ≥ 0 (since m_1 ≤ m_2).

    This is the elementary monotonicity of exp combined with
    `m_exc1_lt_m_exc2`. -/
theorem exp_decay_m2_le_m1
    (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (- m_exc2 s * t) ≤ Real.exp (- m_exc1 s * t) := by
  apply Real.exp_le_exp.mpr
  have h := m_exc1_lt_m_exc2 s hs hs_pos
  -- From m_1 < m_2 we have -m_2 < -m_1, so -m_2 * t ≤ -m_1 * t for t ≥ 0.
  have hmm : -m_exc2 s ≤ -m_exc1 s := by linarith
  exact mul_le_mul_of_nonneg_right hmm ht

/-- **EXPONENTIAL DECAY OF THE CONNECTED CORRELATOR** (chamber sector).

    For non-negative spectral weights c_1, c_2 ≥ 0 and t ≥ 0,

       |W_conn(t)|  ≤  (c_1 + c_2) · exp(−γ_cluster · t)

    where γ_cluster = m_exc1 = ln(5 − √7) > 0.

    PROOF: |W_conn(t)| = W_conn(t) (non-negative), and
       W_conn(t) = c_1 · exp(−m_1 t) + c_2 · exp(−m_2 t)
                ≤ c_1 · exp(−m_1 t) + c_2 · exp(−m_1 t)
                = (c_1 + c_2) · exp(−m_1 t)
                = (c_1 + c_2) · exp(−γ_cluster · t).
-/
theorem two_point_exponential_decay
    (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s)
    (c_1 c_2 : ℝ) (hc_1 : 0 ≤ c_1) (hc_2 : 0 ≤ c_2)
    (t : ℝ) (ht : 0 ≤ t) :
    |two_point_connected s c_1 c_2 t|
      ≤ (c_1 + c_2) * Real.exp (- γ_cluster s * t) := by
  -- Connected correlator is non-negative, so |·| = id.
  have hpos := two_point_connected_nonneg s c_1 c_2 t hc_1 hc_2
  rw [abs_of_nonneg hpos]
  -- Decompose and use the comparison exp(-m_2 t) ≤ exp(-m_1 t)
  unfold two_point_connected
  have hcmp := exp_decay_m2_le_m1 s hs hs_pos t ht
  have h2 : c_2 * Real.exp (- m_exc2 s * t) ≤ c_2 * Real.exp (- m_exc1 s * t) :=
    mul_le_mul_of_nonneg_left hcmp hc_2
  -- Putting it together: c_1·E1 + c_2·E2 ≤ c_1·E1 + c_2·E1 = (c_1 + c_2)·E1
  have hsum :
      c_1 * Real.exp (- m_exc1 s * t) + c_2 * Real.exp (- m_exc2 s * t)
        ≤ c_1 * Real.exp (- m_exc1 s * t)
          + c_2 * Real.exp (- m_exc1 s * t) := by linarith
  have hfact :
      c_1 * Real.exp (- m_exc1 s * t) + c_2 * Real.exp (- m_exc1 s * t)
        = (c_1 + c_2) * Real.exp (- m_exc1 s * t) := by ring
  -- γ_cluster = m_exc1 by definition, so the right-hand sides agree
  have hγ : γ_cluster s = m_exc1 s := γ_cluster_eq_m_exc1 s
  calc c_1 * Real.exp (- m_exc1 s * t) + c_2 * Real.exp (- m_exc2 s * t)
      ≤ c_1 * Real.exp (- m_exc1 s * t)
        + c_2 * Real.exp (- m_exc1 s * t) := hsum
    _ = (c_1 + c_2) * Real.exp (- m_exc1 s * t) := hfact
    _ = (c_1 + c_2) * Real.exp (- γ_cluster s * t) := by rw [hγ]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  CLUSTER DECOMPOSITION FOR THE FULL TWO-POINT FUNCTION
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Combining the exponential decay of the CONNECTED correlator with
    the decomposition W(t) = c_top + W_conn(t), we obtain the cluster
    decomposition:

       |W(t) − c_top|  ≤  (c_1 + c_2) · exp(−γ_cluster · t).

    In particular, as t → ∞, W(t) → c_top.  The constant c_top
    coincides with |⟨Ω| O |Ω⟩|² (the squared expectation of O in
    the vacuum), so this IS the standard cluster property:

         lim_{t → ∞}  ⟨W₁(0) W₂(t)⟩  =  ⟨W₁⟩ · ⟨W₂⟩.

    To express the ε-version, note that exp(−γ t) → 0 as t → ∞ at
    rate γ.  For any ε > 0, choosing t large enough (specifically
    t ≥ T₀ where (c_1 + c_2)·exp(−γ T₀) < ε) gives the bound.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- DECOMPOSITION INEQUALITY: |W(t) − c_top| ≤ (c_1 + c_2) · exp(−γ_cluster · t).

    This is the explicit cluster bound for the full chamber two-point
    function.  Subtracting the disconnected piece c_top leaves the
    connected correlator, which decays exponentially. -/
theorem two_point_cluster_bound
    (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s)
    (c_top c_1 c_2 : ℝ) (hc_1 : 0 ≤ c_1) (hc_2 : 0 ≤ c_2)
    (t : ℝ) (ht : 0 ≤ t) :
    |two_point_correlator s c_top c_1 c_2 t - c_top|
      ≤ (c_1 + c_2) * Real.exp (- γ_cluster s * t) := by
  rw [two_point_decomp s c_top c_1 c_2 t]
  have h : c_top + two_point_connected s c_1 c_2 t - c_top
            = two_point_connected s c_1 c_2 t := by ring
  rw [h]
  exact two_point_exponential_decay s hs hs_pos c_1 c_2 hc_1 hc_2 t ht

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  THE EPSILON-DELTA CLUSTER THEOREM
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The standard "cluster decomposition" statement:

       ∀ ε > 0,  ∃ T₀ > 0  such that  ∀ t ≥ T₀,
            |W(t) − c_top| < ε.

    We deliver T₀ explicitly.

    Take any ε > 0, c_1 + c_2 ≥ 0.  We need
           (c_1 + c_2) · exp(−γ T₀) < ε,
    i.e.   exp(−γ T₀) < ε / (c_1 + c_2)        (when c_1 + c_2 > 0)
    i.e.   T₀ > (1/γ) · ln((c_1 + c_2)/ε).

    If c_1 + c_2 = 0 the connected correlator is identically 0 and
    any T₀ works.

    For convenience we deliver the explicit T₀ in BOTH cases.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Helper: when C ≥ 0 and γ > 0, we have C · exp(−γ t) → 0 as t → ∞.
    Concretely we exhibit a threshold T₀.

    If C = 0, any T₀ ≥ 0 works.  If C > 0, take
        T₀ := max (1, (1/γ) · log((C + 1)/ε))
    and use exp(−γ · T₀) ≤ exp(−γ · (1/γ)·log((C+1)/ε)) = ε/(C+1) < ε/C.
    For simplicity we deliver a slightly larger but explicit threshold. -/
theorem cluster_threshold_exists
    (γ : ℝ) (hγ : 0 < γ)
    (C : ℝ) (hC : 0 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ t → C * Real.exp (- γ * t) < ε := by
  -- Choose T₀ := (log((C + ε) / ε) / γ) + 1  (always > 0).
  -- Then γ · T₀ > log((C+ε)/ε), so exp(−γ T₀) < ε/(C+ε), and
  --       C · exp(−γ T₀) < C · ε/(C+ε) ≤ ε.
  have hCε : (0 : ℝ) < C + ε := by linarith
  have hratio_pos : (0 : ℝ) < (C + ε) / ε := div_pos hCε hε
  -- L := log((C+ε)/ε) is well-defined (positive argument).
  let L : ℝ := Real.log ((C + ε) / ε)
  -- T₀ := L / γ + 1.  Note T₀ > 0 because L could be negative if (C+ε)/ε < 1,
  -- but C ≥ 0 and ε > 0 give (C+ε)/ε ≥ 1, so L ≥ 0; thus T₀ ≥ 1 > 0.
  have hge_one : (1 : ℝ) ≤ (C + ε) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hL_nn : 0 ≤ L := Real.log_nonneg hge_one
  refine ⟨L / γ + 1, ?_, ?_⟩
  · -- positivity of T₀
    have : 0 ≤ L / γ := div_nonneg hL_nn (le_of_lt hγ)
    linarith
  · intro t ht
    -- We have t ≥ L/γ + 1, so γ·t ≥ γ·(L/γ) + γ = L + γ > L.
    -- Hence -γ·t < -L, so exp(-γ·t) < exp(-L) = ε/(C+ε).
    -- Therefore C · exp(-γ·t) ≤ C · ε/(C+ε) < ε.
    have hγt_ge : γ * (L / γ + 1) ≤ γ * t :=
      mul_le_mul_of_nonneg_left ht (le_of_lt hγ)
    have hγexpand : γ * (L / γ + 1) = L + γ := by
      field_simp
    have hγt_lower : L + γ ≤ γ * t := hγexpand ▸ hγt_ge
    have hγt_gtL : L < γ * t := by linarith
    -- Rewrite the goal exp argument: -γ * t = -(γ * t)
    have hneg_eq : -γ * t = -(γ * t) := by ring
    -- exp is strictly increasing: exp(-(γ*t)) < exp(-L)
    have hexp_lt : Real.exp (-(γ * t)) < Real.exp (-L) := by
      apply Real.exp_lt_exp.mpr
      linarith
    -- exp(-L) = ε / (C + ε)
    have hexp_neg_L : Real.exp (-L) = ε / (C + ε) := by
      have hexp_L : Real.exp L = (C + ε) / ε := Real.exp_log hratio_pos
      rw [Real.exp_neg, hexp_L]
      field_simp
    -- Hence exp(-γ * t) = exp(-(γ * t)) < ε/(C+ε)
    have hexp_lt' : Real.exp (-γ * t) < ε / (C + ε) := by
      rw [hneg_eq]
      rw [hexp_neg_L] at hexp_lt
      exact hexp_lt
    -- Multiply by C ≥ 0: C · exp(-γ t) ≤ C · ε/(C+ε)
    have hC_mul_le : C * Real.exp (-γ * t) ≤ C * (ε / (C + ε)) := by
      by_cases hC0 : C = 0
      · rw [hC0]; ring_nf; linarith [mul_nonneg (le_refl (0:ℝ)) (Real.exp_pos (-γ * t)).le]
      · have hC_pos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
        have := mul_lt_mul_of_pos_left hexp_lt' hC_pos
        linarith
    -- And C · ε/(C+ε) < ε since C/(C+ε) < 1
    have hfrac_lt_one : C * (ε / (C + ε)) < ε := by
      have hrewrite : C * (ε / (C + ε)) = (C / (C + ε)) * ε := by ring
      rw [hrewrite]
      have hCfrac_lt : C / (C + ε) < 1 := by
        rw [div_lt_one hCε]; linarith
      have hmul_lt : (C / (C + ε)) * ε < 1 * ε := by
        have := mul_lt_mul_of_pos_right hCfrac_lt hε
        linarith
      linarith
    linarith

/-- **CLUSTER DECOMPOSITION** (chamber sector).

    The standard ε-form: for every ε > 0 there exists a threshold T₀
    such that for every t ≥ T₀, the two-point correlator differs from
    its disconnected (vacuum-expectation) value by less than ε.

    Equivalently:  W(t) → c_top as t → ∞ (in the chamber sector). -/
theorem cluster_decomposition
    (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s)
    (c_top c_1 c_2 : ℝ) (hc_1 : 0 ≤ c_1) (hc_2 : 0 ≤ c_2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      |two_point_correlator s c_top c_1 c_2 t - c_top| < ε := by
  -- C := c_1 + c_2 ≥ 0.
  have hC : 0 ≤ c_1 + c_2 := by linarith
  obtain ⟨T₀, hT₀_pos, hbound⟩ :=
    cluster_threshold_exists (γ_cluster s) (γ_cluster_pos s hs hs_pos)
      (c_1 + c_2) hC ε hε
  refine ⟨T₀, hT₀_pos, ?_⟩
  intro t ht
  have ht_pos : 0 ≤ t := le_trans (le_of_lt hT₀_pos) ht
  have hbound_t : (c_1 + c_2) * Real.exp (- γ_cluster s * t) < ε := hbound t ht
  have hbound_corr := two_point_cluster_bound s hs hs_pos c_top c_1 c_2 hc_1 hc_2 t ht_pos
  linarith

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  CHAMBER-SECTOR HONEST CLASSIFICATION REFINEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    `CL3_ConstructiveMeasure` tagged M6 (cluster decomposition) as
    `NeedsClusterExp`.  This file PROVES M6 on the chamber sector
    only.  We refine the M6 status to a sharper triple:

      (a) Chamber sector M6      → `DiscreteOnly` (PROVED here).
      (b) Full Hilbert space M6  → still `NeedsClusterExp`.
      (c) Continuum M6           → still `ConditionalCL1` ∧ `NeedsClusterExp`.

    A downstream paper can cite (a) as a CLOSED-FORM contribution and
    (b)+(c) as the remaining open work.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The refined M6 chamber-sector classification. -/
def cl3_M6_chamber : MeasurementClassification :=
  { property      := "Cluster decomposition on the chamber sector"
    status        := MeasureStatus.DiscreteOnly
    justification :=
      "PROVED in CL3_ClusterDecomposition.cluster_decomposition: " ++
      "the chamber two-point correlator W(t) = c_top + " ++
      "c_1·exp(-m_1·t) + c_2·exp(-m_2·t) factors as W(t) → c_top as " ++
      "t → ∞, with explicit decay rate γ_cluster = m_1 = ln(5-√7) > 0 " ++
      "(the chamber mass gap).  Closed-form bound: " ++
      "|W(t) − c_top| ≤ (c_1+c_2)·exp(-γ_cluster·t) for all t ≥ 0." }

/-- The full-Hilbert-space M6 status remains `NeedsClusterExp`. -/
def cl3_M6_full : MeasurementClassification :=
  { property      := "Cluster decomposition on the full link Hilbert space"
    status        := MeasureStatus.NeedsClusterExp
    justification :=
      "The chamber-sector cluster bound does NOT extend to the full " ++
      "infinite-dimensional link Hilbert space without bath-sector " ++
      "control (X2 of CL1_ContinuumLimit) and Glimm-Jaffe cluster " ++
      "expansion convergence at weak coupling.  Remains open." }

/-- The continuum M6 status remains `NeedsClusterExp` ∧ `ConditionalCL1`. -/
def cl3_M6_continuum : MeasurementClassification :=
  { property      := "Cluster decomposition in the continuum YM measure"
    status        := MeasureStatus.NeedsClusterExp
    justification :=
      "Lifting the discrete chamber cluster bound to ℝ⁴ requires " ++
      "(a) the continuum-limit hypothesis CL1, and (b) Glimm-Jaffe " ++
      "cluster-expansion machinery in the bath sector.  Both remain " ++
      "open." }

/-- The chamber-sector M6 entry is `DiscreteOnly`. -/
theorem cl3_M6_chamber_status :
    cl3_M6_chamber.status = MeasureStatus.DiscreteOnly := by decide

/-- The full-Hilbert-space M6 entry is `NeedsClusterExp`. -/
theorem cl3_M6_full_status :
    cl3_M6_full.status = MeasureStatus.NeedsClusterExp := by decide

/-- The continuum M6 entry is `NeedsClusterExp`. -/
theorem cl3_M6_continuum_status :
    cl3_M6_continuum.status = MeasureStatus.NeedsClusterExp := by decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §10.  MASTER THEOREM — chamber_cluster_decomposition
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER THEOREM: chamber-sector cluster decomposition.**

    Bundles the entire content of this file into a single Prop suitable
    for citation in a paper.  Conjuncts:

    (1) The chamber spectrum has three positive eigenvalues:
            λ_top = 3/5,  lam_exc1 = (5+√7)/30,  lam_exc2 = (5−√7)/30.

    (2) The excited-state ratios lam_exc1/λ_top, lam_exc2/λ_top lie in
        the open unit interval (0, 1) — exponentially decaying.

    (3) The mass gap above vacuum (in log form) is
            γ_cluster = m_1 = ln(5 − √7) > 0,
        and the heavier mass is m_2 = ln(5 + √7) > m_1.

    (4) Two-point correlator decomposition:
            W(t) = c_top + W_conn(t),
        with W_conn(t) = c_1·exp(−m_1·t) + c_2·exp(−m_2·t).

    (5) EXPONENTIAL DECAY of the connected correlator:
            |W_conn(t)| ≤ (c_1+c_2)·exp(−γ_cluster·t)  for t ≥ 0.

    (6) CLUSTER BOUND on the full correlator:
            |W(t) − c_top| ≤ (c_1+c_2)·exp(−γ_cluster·t).

    (7) CLUSTER DECOMPOSITION (ε-δ form):
            ∀ ε > 0, ∃ T₀ > 0, ∀ t ≥ T₀, |W(t) − c_top| < ε.

    (8) Honest-scope tagging:
            chamber-sector M6 = `DiscreteOnly` (PROVED here).
            full + continuum  = still `NeedsClusterExp`.

    Zero sorry.  Zero custom axioms. -/
theorem chamber_cluster_decomposition
    (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s)
    (c_top c_1 c_2 : ℝ) (hc_1 : 0 ≤ c_1) (hc_2 : 0 ≤ c_2)
    (t : ℝ) (ht : 0 ≤ t) (ε : ℝ) (hε : 0 < ε) :
    -- (1) Chamber spectrum positive
    (0 < lam_vac) ∧ (0 < lam_exc1 s) ∧ (0 < lam_exc2 s) ∧
    -- (2) Excited ratios in open unit interval
    (0 < lam_exc1 s / lam_vac ∧ lam_exc1 s / lam_vac < 1) ∧
    (0 < lam_exc2 s / lam_vac ∧ lam_exc2 s / lam_vac < 1) ∧
    -- (3) Mass gaps
    (0 < γ_cluster s) ∧ (m_exc1 s < m_exc2 s) ∧
    -- (4) Two-point decomposition
    (two_point_correlator s c_top c_1 c_2 t =
      c_top + two_point_connected s c_1 c_2 t) ∧
    -- (5) Exponential decay of the connected correlator
    (|two_point_connected s c_1 c_2 t|
        ≤ (c_1 + c_2) * Real.exp (- γ_cluster s * t)) ∧
    -- (6) Cluster bound on the full correlator
    (|two_point_correlator s c_top c_1 c_2 t - c_top|
        ≤ (c_1 + c_2) * Real.exp (- γ_cluster s * t)) ∧
    -- (7) Cluster decomposition (ε-δ form)
    (∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t' : ℝ, T₀ ≤ t' →
        |two_point_correlator s c_top c_1 c_2 t' - c_top| < ε) ∧
    -- (8) Honest-scope tagging
    (cl3_M6_chamber.status = MeasureStatus.DiscreteOnly) ∧
    (cl3_M6_full.status = MeasureStatus.NeedsClusterExp) ∧
    (cl3_M6_continuum.status = MeasureStatus.NeedsClusterExp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lam_vac_pos
  · exact lam_exc1_pos s hs_pos
  · exact lam_exc2_pos s hs hs_pos
  · exact ratio_exc1_in_open_unit_interval s hs hs_pos
  · exact ratio_exc2_in_open_unit_interval s hs hs_pos
  · exact γ_cluster_pos s hs hs_pos
  · exact m_exc1_lt_m_exc2 s hs hs_pos
  · exact two_point_decomp s c_top c_1 c_2 t
  · exact two_point_exponential_decay s hs hs_pos c_1 c_2 hc_1 hc_2 t ht
  · exact two_point_cluster_bound s hs hs_pos c_top c_1 c_2 hc_1 hc_2 t ht
  · exact cluster_decomposition s hs hs_pos c_top c_1 c_2 hc_1 hc_2 ε hε
  · exact cl3_M6_chamber_status
  · exact cl3_M6_full_status
  · exact cl3_M6_continuum_status

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §11.  HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST SCOPE OF THIS FILE.**

    The framework provides:

      ✓ A spectral two-point correlator on the chamber sector
        (3 eigenstates: vacuum + 2 excited).
      ✓ Closed-form mass gap γ_cluster = ln(5 − √7) > 0.
      ✓ Exact exponential-decay bound for the connected correlator.
      ✓ ε-δ cluster decomposition: W(t) → c_top as t → ∞.
      ✓ Refined classification of M6 — chamber-sector PROVED, full
        and continuum still NeedsClusterExp.

    What this file does NOT do:

      ✗ Construct cluster decomposition on the full (infinite-
        dimensional) link Hilbert space.  This requires bath-sector
        control (X2 of CL1_ContinuumLimit).
      ✗ Construct cluster decomposition in the continuum YM measure.
        This requires CL1 + Glimm-Jaffe cluster expansion.
      ✗ Construct concrete Wilson functionals.  The spectral weights
        c_n appear as abstract non-negative parameters.

    HONEST CLAIM: the algebraic content of cluster decomposition
    (gap → exponential decay) is fully proved on the chamber sector,
    with the EXACT framework-derived mass gap γ_cluster = ln(5 − √7)
    as the decay rate.  This is NOT cluster decomposition for Clay-YM;
    it is the chamber-sector content of M6, made explicit. -/
theorem honest_cluster_scope_statement :
    -- PROVED on chamber: spectrum is positive
    (∀ s : ℝ, s ^ 2 = 7 → 0 < s → 0 < lam_vac ∧ 0 < lam_exc1 s ∧ 0 < lam_exc2 s) ∧
    -- PROVED on chamber: cluster decay rate is positive (mass gap)
    (∀ s : ℝ, s ^ 2 = 7 → 0 < s → 0 < γ_cluster s) ∧
    -- PROVED on chamber: exponential decay of connected correlator
    (∀ s : ℝ, ∀ _hs : s ^ 2 = 7, ∀ _hs_pos : 0 < s,
      ∀ c_1 c_2 : ℝ, 0 ≤ c_1 → 0 ≤ c_2 →
      ∀ t : ℝ, 0 ≤ t →
        |two_point_connected s c_1 c_2 t|
          ≤ (c_1 + c_2) * Real.exp (- γ_cluster s * t)) ∧
    -- PROVED on chamber: ε-δ cluster decomposition
    (∀ s : ℝ, s ^ 2 = 7 → 0 < s →
      ∀ c_top c_1 c_2 : ℝ, 0 ≤ c_1 → 0 ≤ c_2 →
      ∀ ε : ℝ, 0 < ε →
        ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
          |two_point_correlator s c_top c_1 c_2 t - c_top| < ε) ∧
    -- HONEST: chamber-sector M6 = DiscreteOnly
    (cl3_M6_chamber.status = MeasureStatus.DiscreteOnly) ∧
    -- HONEST: full Hilbert M6 still NeedsClusterExp
    (cl3_M6_full.status = MeasureStatus.NeedsClusterExp) ∧
    -- HONEST: continuum M6 still NeedsClusterExp
    (cl3_M6_continuum.status = MeasureStatus.NeedsClusterExp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs hs_pos
    exact ⟨lam_vac_pos, lam_exc1_pos s hs_pos, lam_exc2_pos s hs hs_pos⟩
  · intro s hs hs_pos
    exact γ_cluster_pos s hs hs_pos
  · intro s hs hs_pos c_1 c_2 hc_1 hc_2 t ht
    exact two_point_exponential_decay s hs hs_pos c_1 c_2 hc_1 hc_2 t ht
  · intro s hs hs_pos c_top c_1 c_2 hc_1 hc_2 ε hε
    exact cluster_decomposition s hs hs_pos c_top c_1 c_2 hc_1 hc_2 ε hε
  · exact cl3_M6_chamber_status
  · exact cl3_M6_full_status
  · exact cl3_M6_continuum_status

end UnifiedTheory.LayerB.CL3_ClusterDecomposition
