/-
  Audit/KFCausalCSpecStatisticalLoopBand.lean   (Volume sector — the welded statistical band)

  ONE theorem attaching the deterministic loop-holonomy band to the Poisson tail bound.

  The deterministic band (`loop_holonomy_band`) says: on the good event where every
  edge error factor lies in `[L, R]`, the loop holonomy is squeezed into `[L^m, R^m]`.
  The Poisson bound (`poisson_count_concentration`) says each count deviates by `>= eps`
  with probability `<= 1/(lambda eps^2)`, and a union bound
  (`loop_failure_union_bound`) sums these over the loop.

  Welding them gives a single probabilistic guarantee on the diagnostic itself:

      Pr( H_gamma escapes [L^m, R^m] )  <=  sum over loop edges of  1/(lambda eps^2).

  With `L = ((1-eps)/(1+eps))^(1/d) = U^(-1/d)` and `R = U^(1/d)` from `ratio_band`
  (`U = (1+eps)/(1-eps)`), the band is `[U^(-m/d), U^(m/d)]`.  The two interface
  hypotheses are exactly what the committed results discharge:
    * `hgood` — good counts put every edge factor in `[L, R]` — is `ratio_band` per edge;
    * `htail` — each bad-count event has measure `<= 1/(lambda eps^2)` — is
      `poisson_count_concentration` per count (via `edge_failure_bound` for the two
      counts of an edge).

  So a nontrivial holonomy `H_gamma != 1` that escapes the band is, with the stated
  probability bound, NOT attributable to Poisson count noise — the quantitative form of
  the discrete Weyl-integrability test.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecLoopHolonomyBand
import UnifiedTheory.Audit.KFCausalCSpecCountConcentration

set_option autoImplicit false

open MeasureTheory
open UnifiedTheory.Audit.KFCausalCSpecEdgeScaleDefect
open UnifiedTheory.Audit.KFCausalCSpecLoopHolonomyBand
open UnifiedTheory.Audit.KFCausalCSpecCountConcentration

namespace UnifiedTheory.Audit.KFCausalCSpecStatisticalLoopBand

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {V : Type*}

/-- **Statistical loop-holonomy band (the welded theorem).**  For a closed loop with
exact potential `f` and a random measured edge cochain `Ê`, the probability that the
loop holonomy `H_gamma` escapes the deterministic band `[L^m, R^m]` is at most the
summed per-count Poisson tail `sum_i 1/(lambda i eps^2)`.

`hgood` (good counts ⟹ every edge factor in `[L, R]`) is supplied by `ratio_band`;
`htail` (each bad-count event `<= 1/(lambda eps^2)`) by `poisson_count_concentration`.
Combines `loop_holonomy_band` (deterministic) with `loop_failure_union_bound`. -/
theorem holonomy_escape_le_poisson_tail
    (u : V) (l : List V) (hclosed : l.getLastD u = u)
    (f : V → ℝ) (hf : ∀ v, 0 < f v)
    (L R : ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (Ê : Ω → V → V → ℝ)
    {ι : Type*} (s : Finset ι) (Bad : ι → Set Ω) (lam : ι → ℝ) (ε : ℝ)
    (htail : ∀ i ∈ s, μ (Bad i) ≤ ENNReal.ofReal (1 / (lam i * ε ^ 2)))
    (hgood : ∀ ω, (∀ i ∈ s, ω ∉ Bad i) → ∀ a b, L ≤ Ê ω a b ∧ Ê ω a b ≤ R) :
    μ {ω | chainProduct (fun a b => (f a / f b) * Ê ω a b) u l < L ^ l.length
          ∨ R ^ l.length < chainProduct (fun a b => (f a / f b) * Ê ω a b) u l}
      ≤ ∑ i ∈ s, ENNReal.ofReal (1 / (lam i * ε ^ 2)) := by
  have hsub : {ω | chainProduct (fun a b => (f a / f b) * Ê ω a b) u l < L ^ l.length
        ∨ R ^ l.length < chainProduct (fun a b => (f a / f b) * Ê ω a b) u l}
      ⊆ ⋃ i ∈ s, Bad i := by
    intro ω hω
    by_contra hcon
    have hgc : ∀ i ∈ s, ω ∉ Bad i := fun i hi hb => hcon (Set.mem_biUnion hi hb)
    obtain ⟨hb1, hb2⟩ := loop_holonomy_band f hf (Ê ω) L R hL hR
      (fun a b => (hgood ω hgc a b).1) (fun a b => (hgood ω hgc a b).2) u l hclosed
    rcases hω with h | h
    · exact absurd hb1 (not_le.mpr h)
    · exact absurd hb2 (not_le.mpr h)
  exact le_trans (measure_mono hsub)
    (loop_failure_union_bound s Bad (fun i => ENNReal.ofReal (1 / (lam i * ε ^ 2))) htail)

#print axioms holonomy_escape_le_poisson_tail

end UnifiedTheory.Audit.KFCausalCSpecStatisticalLoopBand
