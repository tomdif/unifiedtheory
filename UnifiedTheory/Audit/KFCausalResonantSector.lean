/-
  Audit/KFCausalResonantSector.lean
  — THE RESONANT-SECTOR KILL CERTIFICATES (phi = 8pi, eps = 1/4)

  At the resonant phase phi = 8pi with smearing eps = 1/4 (2D smeared
  weights W(0) = 1/2, W(1) = 1/8, W(2) = -1/16, W(3) = -9/64, exact
  dyadic rationals), phase reality of a growth stage with N_k links of
  interval size k reads N₁ - N₂/2 - 9 N₃/8 ∈ ℤ, i.e.

      4 N₂ + N₃ ≡ 0  (mod 8)     [k ≥ 4 links carry 2-adically deeper
                                  denominators and are separately fatal
                                  at any reachable count]

  The gate's survivor set through n = 7 (phi8pi_survivor.py,
  set-equality verified) is the N₃ = 0 branch: every downset has even
  N₂ and no link has interval ≥ 3.  SCOPE: the branches N₃ ≡ 4 with N₂
  odd and N₃ ≡ 0 mod 8 with N₂ even are combinatorially unreachable at
  n ≤ 7, so the n ≤ 7 iff does not by itself decide them; whether every
  hereditary path into N₃ ≥ 4 passes through a congruence-violating
  downset (which would make the N₃ = 0 branch exact at all n, and the
  height ≤ 4 cap a theorem) is the open blocking lemma.  The kill
  mechanism at N₃ ∈ {1, 2, 3} is arithmetic (n3_small_violates below);
  the per-equation engine is the LONE IMAGINARY CHANNEL: a sum-rule
  equation in which exactly one surviving channel carries a non-real
  phase forces that channel's amplitude to zero.

  This file proves:
  1.  lone_imaginary_channel — the abstract two-line certificate: if
      nonnegative amplitudes satisfy the imaginary part of a sum rule
      whose channel sines all vanish except one, that channel dies.
  2.  four_chain_dies_at_8pi — the concrete minimal kill: the 3-chain's
      four growth channels at eps = 1/4, phi = 8pi have phase angles
      8pi (disjoint point), 4pi (bottom cover), 3pi (2-chain cover) and
      7pi/2 (full cover -> the 4-chain), with sines 0, 0, 0, -1: the
      4-chain is the lone imaginary channel of its parent equation and
      its amplitude vanishes.  With downward closure this kills every
      pure chain of length >= 4 at the resonance — one of the two
      minimal seeds of the height <= 4 ("arrested time") cap observed
      through n = 7.

  Gap arithmetic feeding theorem 2 (exact, eps = 1/4):
    gap(disjoint)  = 1                    -> 8pi   -> sin = 0
    gap(bottom)    = 1 - W(0) = 1/2       -> 4pi   -> sin = 0
    gap(2-cover)   = 1 - W(0) - W(1) = 3/8            -> 3pi -> sin = 0
    gap(full)      = 1 - W(0) - W(1) - W(2) = 7/16    -> 7pi/2 -> sin = -1

  Zero sorry.  Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalResonantSector

open Real

/-- **The lone-imaginary-channel certificate.**  If amplitudes
`a₁ … a₄` satisfy the imaginary part of a sum rule whose first three
channel sines vanish and whose fourth is negative, the fourth
amplitude is zero.  (Neither the real part of the sum rule nor
nonnegativity of the amplitude is needed for the kill.) -/
theorem lone_imaginary_channel
    (a₁ a₂ a₃ a₄ θ₁ θ₂ θ₃ θ₄ : ℝ)
    (s₁ : Real.sin θ₁ = 0) (s₂ : Real.sin θ₂ = 0) (s₃ : Real.sin θ₃ = 0)
    (s₄ : Real.sin θ₄ < 0)
    (im : a₁ * Real.sin θ₁ + a₂ * Real.sin θ₂ + a₃ * Real.sin θ₃
          + a₄ * Real.sin θ₄ = 0) :
    a₄ = 0 := by
  rw [s₁, s₂, s₃] at im
  have h : a₄ * Real.sin θ₄ = 0 := by linarith
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · exact absurd h' (ne_of_lt s₄)

/-- The four channel angles of the 3-chain at eps = 1/4, phi = 8pi:
sin (8π) = 0, sin (4π) = 0, sin (3π) = 0, sin (7π/2) = -1. -/
theorem sin_eight_pi : Real.sin (8 * π) = 0 := by
  have h := Real.sin_int_mul_pi 8
  push_cast at h
  exact h

theorem sin_four_pi : Real.sin (4 * π) = 0 := by
  have h := Real.sin_int_mul_pi 4
  push_cast at h
  exact h

theorem sin_three_pi : Real.sin (3 * π) = 0 := by
  have h := Real.sin_int_mul_pi 3
  push_cast at h
  exact h

theorem sin_seven_pi_div_two : Real.sin (7 * π / 2) = -1 := by
  have h : (7 : ℝ) * π / 2 = 3 * π + π / 2 := by ring
  rw [h]
  have h2 : (3 : ℝ) * π + π / 2 = π / 2 + 3 * π := by ring
  rw [h2]
  have key : ∀ x : ℝ, Real.sin (x + 3 * π) = -Real.sin x := by
    intro x
    have : x + 3 * π = (x + π) + 2 * π := by ring
    rw [this, Real.sin_add_two_pi, Real.sin_add_pi]
  rw [key, Real.sin_pi_div_two]

/-- **The 4-chain dies at the resonance.**  The 3-chain's sum rule at
eps = 1/4, phi = 8pi (channels: disjoint point, bottom cover, 2-chain
cover, full cover = the 4-chain, with the exact dyadic gap angles
8π, 4π, 3π, 7π/2) forces the 4-chain amplitude to zero: it is the
lone imaginary channel of its parent equation. -/
theorem four_chain_dies_at_8pi
    (aDisj aBot aMid aChain4 : ℝ)
    (im : aDisj * Real.sin (8 * π) + aBot * Real.sin (4 * π)
          + aMid * Real.sin (3 * π) + aChain4 * Real.sin (7 * π / 2) = 0) :
    aChain4 = 0 :=
  lone_imaginary_channel aDisj aBot aMid aChain4 _ _ _ _
    sin_eight_pi sin_four_pi sin_three_pi
    (by rw [sin_seven_pi_div_two]; norm_num) im

/-- **Small-N₃ arithmetic kill.**  The reality congruence
4 N₂ + N₃ ≡ 0 (mod 8) has no solution with N₃ ∈ {1, 2, 3}: a growth
stage carrying one, two or three interval-3 links is never
phase-real, whatever its interval-2 census.  (The first live branches
beyond N₃ = 0 are N₃ = 4 with N₂ odd and N₃ = 8 with N₂ even —
combinatorially unreachable at n ≤ 7.) -/
theorem n3_small_violates (N₂ N₃ : ℕ) (h : N₃ = 1 ∨ N₃ = 2 ∨ N₃ = 3) :
    (4 * N₂ + N₃) % 8 ≠ 0 := by omega

/-- **The dust telescope** (arithmetic heart of the composability
no-go).  At any resonance (W₀φ ∈ 2πℤ, φ ∈ 2πℤ) every channel from the
n-antichain to a claw_d ⊔ points child carries phase +1, so the
n-antichain's sum rule under orbit-factorization (antichains forced to
amplitude 1) reads 1 = 1 + Σ_d C(n, d+1)·a(d+1) with a(d) = the claw_d
amplitude: every claw dies.  Combined with support downward-closure
(every non-antichain causet has a height-2 element whose principal
downset is a claw), this forces the pure dust spine: composability is
incompatible with branching in the resonant sector (orbit convention;
DUST_THEOREM.md). -/
theorem dust_telescope (n : ℕ) (a : ℕ → ℝ) (hpos : ∀ d, 0 ≤ a d)
    (heq : (1 : ℝ) = 1 + ∑ d ∈ Finset.range n,
      (n.choose (d + 1) : ℝ) * a (d + 1)) :
    ∀ d ∈ Finset.range n, a (d + 1) = 0 := by
  have hsum : ∑ d ∈ Finset.range n,
      (n.choose (d + 1) : ℝ) * a (d + 1) = 0 := by linarith
  have hterm : ∀ d ∈ Finset.range n,
      (n.choose (d + 1) : ℝ) * a (d + 1) = 0 := by
    intro d hd
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (by positivity) (hpos (i + 1)))).mp hsum
    exact this d hd
  intro d hd
  have h := hterm d hd
  have hdn : d < n := Finset.mem_range.mp hd
  have hc : (0 : ℝ) < (n.choose (d + 1) : ℝ) := by
    have : 0 < n.choose (d + 1) :=
      Nat.choose_pos (by omega : d + 1 ≤ n)
    exact_mod_cast this
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' (ne_of_gt hc)
  · exact h'

#print axioms lone_imaginary_channel
#print axioms four_chain_dies_at_8pi
#print axioms n3_small_violates
#print axioms dust_telescope

end UnifiedTheory.Audit.KFCausalResonantSector
