/-
  Audit/KFCausalHopfOctant.lean

  THE pi/4 LAW AS A HOPF / PANCHARATNAM PHASE

  Context.  `KFCausalBornQuadraturePhase.root_phase_is_pi_div_four` shows
  that the bi-normalized law (coherent sum  sum mu a = 1  and Born sum
  sum mu |a|^2 = 1) forces the growth root's phase to pi/4.  This file
  gives that number a geometric reading through the Hopf map
  S^3 -> S^2 (Bloch sphere).

  1. `bargmann_amplitude` (any number K of child classes).  Write the
     parent's state as psi_k = sqrt(mu_k) a_k and the reference state as
     s_k = sqrt(mu_k).  The coherent sum says <s|psi> = 1, a positive real
     (a Pancharatnam-parallel gauge).  Then the three-vertex Bargmann
     invariant of (s, psi, e_j) is
         <s|psi> <psi|e_j> <e_j|s> = mu_j * conj(a_j),
     so `bargmann_phase`: arg(Bargmann) = - arg(a_j).  Every amplitude
     phase of the law is (minus) a geometric phase of a triangle in
     projective Hilbert space whose vertices are s, psi and e_j.

  2. `root_bloch_*` and `root_bargmann_octant` (the root, K = 2).  At the
     root amplitudes a = ((1+i)/2, (1-i)/2) (= (sqrt2/2) e^{+-i pi/4}), the
     Bloch vectors of |0>, |+> and psi are (0,0,1), (1,0,0), (0,-1,0):
     mutually orthogonal, i.e. the corners of one octant of S^2, with
     triple product -1.  Their normalized Bargmann invariant is
         <0|+><+|psi><psi|0> = (1 - i)/4 = (sqrt2/4) e^{-i pi/4},
     which agrees with the exact qubit formula
         (1 + n1.n2 + n2.n3 + n3.n1 + i n1.(n2 x n3)) / 4
     (`root_bargmann_matches_bloch_formula`).

     Not formalized (cited): Pancharatnam/Berry, arg(Bargmann) = -Omega/2
     for the geodesic triangle, and Girard's theorem, Omega(octant) =
     3(pi/2) - pi = pi/2.  With them, the pi/4 law reads: the root phase
     is half the solid angle of a Bloch-sphere octant.  What IS proved
     here is the exact value e^{-i pi/4} of the Bargmann phase and the
     octant (mutual orthogonality) of the three vertices.

  3. `two_gap_root_phase`.  A parent whose children carry only action
     gaps +1 (total multiplicity mu+) and -1 (mu-), with sin phi /= 0,
     forces 4 cos^2 phi = 1/mu+ + 1/mu-.  (mu+, mu-) = (1,1) is the
     physical root (cos^2 = 1/2, pi/4).  (2,2) would give pi/3; (1,2)
     gives cos^2 = 3/8, not a rational multiple of pi (Niven-type; not
     formalized).  Companion numerics: in the full depth-8 tree (2450
     parents) the root is the ONLY two-class parent; every other parent
     has >= 3 classes and an open feasible phi-window, so it never pins
     a phase (scripts/hopf_kchild_check.py, scripts/hopf_kcount8.py, scripts/hopf_pi4_octant.py; run from repo root).

  Zero sorry.  Zero custom axioms.  Imports Mathlib only; not yet in the
  root import.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHopfOctant

open Complex Finset

/-! ## 1. Amplitude phase = Bargmann (geometric) phase, any K -/

/-- With `psi_k = sqrt(mu_k) a_k`, `s_k = sqrt(mu_k)` and the coherent
sum `sum mu a = 1`, the Bargmann triple product of `(s, psi, e_j)`
equals `mu_j * conj (a_j)`. -/
theorem bargmann_amplitude {K : ℕ} (μ : Fin K → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (a : Fin K → ℂ) (hcoh : ∑ k, (μ k : ℂ) * a k = 1) (j : Fin K) :
    (∑ k, (Real.sqrt (μ k) : ℂ) * ((Real.sqrt (μ k) : ℂ) * a k)) *
        (starRingEnd ℂ ((Real.sqrt (μ j) : ℂ) * a j)) * (Real.sqrt (μ j) : ℂ)
      = (μ j : ℂ) * starRingEnd ℂ (a j) := by
  have hsq : ∀ k, (Real.sqrt (μ k) : ℂ) * (Real.sqrt (μ k) : ℂ) = (μ k : ℂ) := by
    intro k
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hμ k)]
  have hsum : ∑ k, (Real.sqrt (μ k) : ℂ) * ((Real.sqrt (μ k) : ℂ) * a k) = 1 := by
    rw [← hcoh]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← mul_assoc, hsq k]
  rw [hsum, one_mul, map_mul, Complex.conj_ofReal]
  calc (Real.sqrt (μ j) : ℂ) * starRingEnd ℂ (a j) * (Real.sqrt (μ j) : ℂ)
      = ((Real.sqrt (μ j) : ℂ) * (Real.sqrt (μ j) : ℂ)) * starRingEnd ℂ (a j) := by ring
    _ = (μ j : ℂ) * starRingEnd ℂ (a j) := by rw [hsq j]

/-- The Bargmann phase is minus the amplitude phase (away from the
branch cut `arg a_j = pi`). -/
theorem bargmann_phase {K : ℕ} (μ : Fin K → ℝ) (hμ : ∀ k, 0 ≤ μ k)
    (a : Fin K → ℂ) (hcoh : ∑ k, (μ k : ℂ) * a k = 1) (j : Fin K)
    (hμj : 0 < μ j) (hcut : arg (a j) ≠ Real.pi) :
    arg ((∑ k, (Real.sqrt (μ k) : ℂ) * ((Real.sqrt (μ k) : ℂ) * a k)) *
        (starRingEnd ℂ ((Real.sqrt (μ j) : ℂ) * a j)) * (Real.sqrt (μ j) : ℂ))
      = - arg (a j) := by
  rw [bargmann_amplitude μ hμ a hcoh j, Complex.arg_real_mul _ hμj,
    Complex.arg_conj, if_neg hcut]

/-! ## 2. The root: an octant of the Bloch sphere -/

/-- Bloch vector of a (normalized) qubit `(u, v)`. -/
noncomputable def blochX (u v : ℂ) : ℝ := 2 * (starRingEnd ℂ u * v).re
noncomputable def blochY (u v : ℂ) : ℝ := 2 * (starRingEnd ℂ u * v).im
noncomputable def blochZ (u v : ℂ) : ℝ := Complex.normSq u - Complex.normSq v

/-- The root amplitudes `(sqrt2/2) e^{+- i pi/4}`. -/
noncomputable def rootA : ℂ := (1 + I) / 2
noncomputable def rootB : ℂ := (1 - I) / 2

theorem rootA_eq : rootA = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * exp ((Real.pi / 4 : ℝ) * I) := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four,
    rootA]
  apply Complex.ext <;> simp <;> ring_nf <;>
    simp [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] <;> norm_num

theorem root_coherent : rootA + rootB = 1 := by
  rw [rootA, rootB]; ring

theorem root_born : Complex.normSq rootA + Complex.normSq rootB = 1 := by
  simp [rootA, rootB, Complex.normSq_apply]; norm_num

theorem conj_rootA : starRingEnd ℂ rootA = rootB := by
  rw [rootA, rootB, map_div₀, map_add, map_one, Complex.conj_I, map_ofNat]; ring

theorem rootB_sq : rootB * rootB = -I / 2 := by
  rw [rootB]; ring_nf; rw [Complex.I_sq]; ring

/-- Bloch vector of the root state: `(0, -1, 0)`. -/
theorem root_bloch_psi :
    blochX rootA rootB = 0 ∧ blochY rootA rootB = -1 ∧ blochZ rootA rootB = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [blochX, conj_rootA, rootB_sq]; simp
  · rw [blochY, conj_rootA, rootB_sq]; simp; norm_num
  · simp [blochZ, rootA, rootB, Complex.normSq_apply]

/-- Bloch vector of `|0>`: `(0, 0, 1)`. -/
theorem root_bloch_zero :
    blochX 1 0 = 0 ∧ blochY 1 0 = 0 ∧ blochZ 1 0 = 1 := by
  simp [blochX, blochY, blochZ]

/-- Bloch vector of `|+> = (s, s)`, `s = sqrt2/2`: `(1, 0, 0)`. -/
theorem root_bloch_plus :
    let s : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)
    blochX s s = 1 ∧ blochY s s = 0 ∧ blochZ s s = 0 := by
  intro s
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · simp only [blochX, s, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    nlinarith [h2]
  · simp only [blochY, s, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_im]
    ring
  · simp [blochZ, s]

/-- The three Bloch vectors `(0,0,1)`, `(1,0,0)`, `(0,-1,0)` are mutually
orthogonal (one octant of S^2) with triple product `-1`. -/
theorem root_octant_vertices :
    let n0 : Fin 3 → ℝ := ![0, 0, 1]
    let np : Fin 3 → ℝ := ![1, 0, 0]
    let nψ : Fin 3 → ℝ := ![0, -1, 0]
    (∑ i, n0 i * np i = 0) ∧ (∑ i, np i * nψ i = 0) ∧ (∑ i, nψ i * n0 i = 0) ∧
    n0 0 * (np 1 * nψ 2 - np 2 * nψ 1) + n0 1 * (np 2 * nψ 0 - np 0 * nψ 2)
      + n0 2 * (np 0 * nψ 1 - np 1 * nψ 0) = -1 := by
  simp [Fin.sum_univ_three]

/-- The normalized Bargmann invariant `<0|+><+|psi><psi|0>` at the root
equals `(1 - i)/4 = (sqrt2/4) e^{-i pi/4}`: its phase is exactly
`-pi/4`, minus half the solid angle `4 pi / 8` of an octant. -/
theorem root_bargmann_octant :
    let s : ℂ := ((Real.sqrt 2 / 2 : ℝ) : ℂ)
    (starRingEnd ℂ 1 * s + starRingEnd ℂ 0 * s) *
        (starRingEnd ℂ s * rootA + starRingEnd ℂ s * rootB) *
        (starRingEnd ℂ rootA * 1 + starRingEnd ℂ rootB * 0)
      = (1 - I) / 4 ∧
    (1 - I) / 4 = ((Real.sqrt 2 / 4 : ℝ) : ℂ) * exp ((-(Real.pi / 4) : ℝ) * I) := by
  intro s
  have h2 : (s * s : ℂ) = 1 / 2 := by
    simp only [s, ← Complex.ofReal_mul]
    rw [show Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = (Real.sqrt 2 * Real.sqrt 2) / 4 by ring,
      Real.mul_self_sqrt (by norm_num)]
    push_cast; norm_num
  refine ⟨?_, ?_⟩
  · have hs : starRingEnd ℂ s = s := Complex.conj_ofReal _
    rw [hs, conj_rootA, map_one, map_zero]
    have : s * rootA + s * rootB = s := by rw [← mul_add, root_coherent, mul_one]
    calc (1 * s + 0 * s) * (s * rootA + s * rootB) * (rootB * 1 + starRingEnd ℂ rootB * 0)
        = (s * s) * rootB := by rw [this]; ring
      _ = (1 - I) / 4 := by rw [h2, rootB]; ring
  · rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
    apply Complex.ext <;> simp <;> ring_nf <;>
      simp [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] <;> norm_num

/-- Consistency with the exact qubit Bargmann formula
`(1 + n1.n2 + n2.n3 + n3.n1 + i n1.(n2 x n3)) / 4` for the octant
vertices (all dot products 0, triple product -1). -/
theorem root_bargmann_matches_bloch_formula :
    ((1 + 0 + 0 + 0 : ℝ) : ℂ) / 4 + I * ((-1 : ℝ) : ℂ) / 4 = (1 - I) / 4 := by
  push_cast; ring

/-! ## 3. Two-gap parents: the general phase law -/

/-- A parent whose children carry only action gaps `+1` (total weight
`xp = mu+ rho+`) and `-1` (`xm = mu- rho-`): the imaginary, real and Born
equations with `sin phi /= 0` force `4 cos^2 phi = 1/mu+ + 1/mu-`. -/
theorem two_gap_root_phase (μp μm xp xm φ : ℝ)
    (hsin : Real.sin φ ≠ 0)
    (him : (xp - xm) * Real.sin φ = 0)
    (hre : (xp + xm) * Real.cos φ = 1)
    (hborn : xp ^ 2 / μp + xm ^ 2 / μm = 1) :
    4 * Real.cos φ ^ 2 = 1 / μp + 1 / μm := by
  have hx : xp = xm := by
    have := (mul_eq_zero.mp him).resolve_right hsin
    linarith
  subst hx
  have h1 : 4 * Real.cos φ ^ 2 * xp ^ 2 = 1 := by
    linear_combination ((xp + xp) * Real.cos φ + 1) * hre
  have h2 : xp ^ 2 * (1 / μp + 1 / μm) = 1 := by
    calc xp ^ 2 * (1 / μp + 1 / μm) = xp ^ 2 / μp + xp ^ 2 / μm := by ring
      _ = 1 := hborn
  linear_combination (-(4 * Real.cos φ ^ 2)) * h2 + (1 / μp + 1 / μm) * h1

/-- The physical root `(mu+, mu-) = (1, 1)` recovers `cos^2 phi = 1/2`. -/
theorem two_gap_root_phase_unit (xp xm φ : ℝ) (hsin : Real.sin φ ≠ 0)
    (him : (xp - xm) * Real.sin φ = 0) (hre : (xp + xm) * Real.cos φ = 1)
    (hborn : xp ^ 2 + xm ^ 2 = 1) :
    Real.cos φ ^ 2 = 1 / 2 := by
  have := two_gap_root_phase 1 1 xp xm φ hsin him hre (by simpa using hborn)
  linarith

/-- The doubled root `(mu+, mu-) = (2, 2)` would force `cos^2 phi = 1/4`
(phase `pi/3`): the octant value is specific to unit multiplicities. -/
theorem two_gap_root_phase_double (xp xm φ : ℝ) (hsin : Real.sin φ ≠ 0)
    (him : (xp - xm) * Real.sin φ = 0) (hre : (xp + xm) * Real.cos φ = 1)
    (hborn : xp ^ 2 / 2 + xm ^ 2 / 2 = 1) :
    Real.cos φ ^ 2 = 1 / 4 := by
  have := two_gap_root_phase 2 2 xp xm φ hsin him hre hborn
  linarith

end UnifiedTheory.Audit.KFCausalHopfOctant
