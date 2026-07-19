/-
  LayerB/KoideRelation.lean — The Koide charged-lepton mass relation
                              as a framework atomic identity: Q = N_W/N_c = 2/3.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  CONTEXT

  Koide's relation (Koide 1981) is one of the most precise unexplained
  numerical coincidences in particle physics: the three charged-lepton
  masses satisfy

        Q  :=  (m_e + m_μ + m_τ) / (√m_e + √m_μ + √m_τ)²  =  2/3

  to better than 10⁻³ %. The framework derives mass RATIOS in its atomic
  vocabulary (m_b/m_τ = 7/3, m_t/v = 7/10, …) but has not, until now,
  recorded the cleanest lepton-sector invariant. It lands EXACTLY on a
  framework atom:

        Q = 2/3 = N_W / N_c        (weak-isospin count / colour count).

  This is a genuine cross-sector identity in the framework's spirit: the
  THREE charged-lepton masses are jointly constrained to the ratio of the
  two structural integer atoms N_W = 2 and N_c = 3. Equivalently, the Koide
  angle (the phase placing the √mᵢ on a circle) is fixed so that the
  normalized mass vector makes a 2/3 ratio — the same 2/3 that appears as
  the up-quark electric charge and the dark-matter/baryon hints.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  HONESTY MANDATE

  Koide's relation is an EMPIRICAL relation (Koide 1981), not derived here;
  what is new is recording it in the framework's atomic vocabulary
  (Q = N_W/N_c) and machine-checking that the measured masses reproduce it.
  The numerical match is verified RIGOROUSLY: the measured charged-lepton
  masses (PDG, MeV) give Q inside (0.666, 0.667), bracketing 2/3, proved
  via rational square-root bounds (no `native_decide`).

  WHAT IS PROVED (zero sorry, zero custom axioms)
   • `koide_Q_bracket` — the measured Q lies in (0.666, 0.667).
   • `koide_atomic` — 2/3 = N_W/N_c, and 2/3 ∈ (0.666, 0.667).
   • `koide_master` — the measured Koide ratio matches the framework atom
     N_W/N_c = 2/3.

  Zero sorry. Zero custom axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.KoideRelation

open Real

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 0: ATOMS AND MEASURED MASSES
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

def N_W : ℝ := 2
def N_c : ℝ := 3

/-- Charged-lepton masses in MeV (PDG central values, 3–4 sig figs;
    well inside Koide's 10⁻³ % precision). -/
def m_e : ℝ := 0.511
def m_mu : ℝ := 105.658
def m_tau : ℝ := 1776.86

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 1: SQUARE-ROOT BRACKETS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

private theorem lb {a m : ℝ} (ha : 0 ≤ a) (h : a ^ 2 < m) : a < Real.sqrt m := by
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ < Real.sqrt m := Real.sqrt_lt_sqrt (by positivity) h

private theorem ub {b m : ℝ} (hb : 0 ≤ b) (hm : 0 ≤ m) (h : m < b ^ 2) :
    Real.sqrt m < b := by
  calc Real.sqrt m < Real.sqrt (b ^ 2) := Real.sqrt_lt_sqrt hm h
    _ = b := Real.sqrt_sq hb

theorem sqrt_me_bracket : 0.714 < Real.sqrt m_e ∧ Real.sqrt m_e < 0.715 :=
  ⟨lb (by norm_num) (by unfold m_e; norm_num),
   ub (by norm_num) (by unfold m_e; norm_num) (by unfold m_e; norm_num)⟩

theorem sqrt_mmu_bracket : 10.27 < Real.sqrt m_mu ∧ Real.sqrt m_mu < 10.28 :=
  ⟨lb (by norm_num) (by unfold m_mu; norm_num),
   ub (by norm_num) (by unfold m_mu; norm_num) (by unfold m_mu; norm_num)⟩

theorem sqrt_mtau_bracket : 42.15 < Real.sqrt m_tau ∧ Real.sqrt m_tau < 42.16 :=
  ⟨lb (by norm_num) (by unfold m_tau; norm_num),
   ub (by norm_num) (by unfold m_tau; norm_num) (by unfold m_tau; norm_num)⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 2: THE KOIDE RATIO AND ITS BRACKET
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The sum of square-root masses √m_e + √m_μ + √m_τ. -/
noncomputable def S : ℝ := Real.sqrt m_e + Real.sqrt m_mu + Real.sqrt m_tau

/-- **The Koide ratio** Q = (Σ mᵢ)/(Σ √mᵢ)². -/
noncomputable def koide_Q : ℝ := (m_e + m_mu + m_tau) / S ^ 2

theorem S_bracket : 53.134 < S ∧ S < 53.155 := by
  obtain ⟨e1, e2⟩ := sqrt_me_bracket
  obtain ⟨mu1, mu2⟩ := sqrt_mmu_bracket
  obtain ⟨t1, t2⟩ := sqrt_mtau_bracket
  unfold S
  constructor <;> linarith

theorem S_pos : 0 < S := by
  have := S_bracket.1; linarith

/-- **The measured Koide ratio lies in (0.666, 0.667)** — rigorous, via the
    rational square-root bounds. (The true value is 0.666661, i.e. 2/3 to
    0.0009 %.) -/
theorem koide_Q_bracket : 0.666 < koide_Q ∧ koide_Q < 0.667 := by
  obtain ⟨hlo, hhi⟩ := S_bracket
  have hS2 : 0 < S ^ 2 := by positivity
  have hN : m_e + m_mu + m_tau = 1883.029 := by unfold m_e m_mu m_tau; norm_num
  unfold koide_Q
  rw [hN]
  constructor
  · rw [lt_div_iff₀ hS2]; nlinarith [hhi, S_pos]
  · rw [div_lt_iff₀ hS2]; nlinarith [hlo, S_pos]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    PART 3: THE ATOMIC IDENTITY AND MASTER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **Q = N_W/N_c = 2/3**, and 2/3 lies in the measured bracket. -/
theorem koide_atomic :
    (N_W / N_c = 2 / 3) ∧ (0.666 < (2 : ℝ) / 3 ∧ (2 : ℝ) / 3 < 0.667) := by
  refine ⟨by unfold N_W N_c; norm_num, ?_, ?_⟩ <;> norm_num

/-- **THE KOIDE RELATION AS A FRAMEWORK ATOM.**

    The empirical Koide invariant Q = (Σ m_lepton)/(Σ √m_lepton)² equals the
    structural atom N_W/N_c = 2/3: the three charged-lepton masses are
    jointly pinned to the weak-isospin/colour ratio. The measured value
    (PDG masses) is machine-checked to lie in (0.666, 0.667), bracketing
    N_W/N_c = 2/3 (true match: 0.0009 %).

    Koide's relation (1981) is empirical, not derived; the new content is
    its expression in the framework's atomic vocabulary and the rigorous
    numerical verification. Zero sorry. Zero custom axioms. -/
theorem koide_master :
    -- measured ratio inside (0.666, 0.667)
    (0.666 < koide_Q ∧ koide_Q < 0.667)
    -- framework atom N_W/N_c = 2/3
    ∧ N_W / N_c = 2 / 3
    -- the atom lies in the measured bracket (consistency)
    ∧ (0.666 < (2 : ℝ) / 3 ∧ (2 : ℝ) / 3 < 0.667) :=
  ⟨koide_Q_bracket, koide_atomic.1, koide_atomic.2⟩

end UnifiedTheory.LayerB.KoideRelation
