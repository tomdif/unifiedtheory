/-
  Audit/KFCausalCSpecGlobalization.lean   (Steps 5-9 — sealed assembly)

  Instantiates the bridge-poset keystone on the concrete four-state base and
  assembles the first-half globalization headline.

  ANTI-CIRCULARITY SEAL.  This file imports ONLY BridgePoset / Monodromy /
  TwistedGap — none of which transitively imports `KFCausalSheetHolonomyWitness`,
  so `witnessSheetTransport` is never in scope.  The four-state transports are
  defined DIRECTLY (`swap 0 1`, `swap 1 2`, `id`), and the transitions are
  recovered from the global causal order via `bridge_incidence_recovers_transport`
  (the transport appears only in the recovered VALUE, never in a hypothesis).

  SCOPE: order/conformal sector only.  No metric, volume, or Hauptvermutung claim.

  Zero sorry. Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecBridgePoset
import UnifiedTheory.Audit.KFCausalCSpecMonodromy
import UnifiedTheory.Audit.KFCausalCSpecTwistedGap

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecGlobalization

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBridgePoset
open UnifiedTheory.Audit.KFCausalCSpecMonodromy
open UnifiedTheory.Audit.KFCausalCSpecTwistedGap

/-! ## The four-state base graph — transports defined directly (sealed) -/

/-- The five directed edges of the four-state base (two loops `0-1-3-0`, `0-2-3-0`). -/
inductive E4 | e01 | e02 | e13 | e23 | e30
  deriving DecidableEq

/-- The base graph.  The two nontrivial transports are the adjacent transpositions;
the rest are the identity.  Defined WITHOUT reference to `witnessSheetTransport`. -/
def fourState : BaseGraph (Fin 4) E4 where
  src := fun | .e01 => 0 | .e02 => 0 | .e13 => 1 | .e23 => 2 | .e30 => 3
  dst := fun | .e01 => 1 | .e02 => 2 | .e13 => 3 | .e23 => 3 | .e30 => 0
  perm := fun | .e01 => Equiv.swap 0 1 | .e02 => Equiv.swap 1 2 | _ => 1

/-- Holonomy of the first loop `0 → 1 → 3 → 0`. -/
def loop1 : Equiv.Perm (Fin 3) := fourState.perm .e30 * fourState.perm .e13 * fourState.perm .e01
/-- Holonomy of the second loop `0 → 2 → 3 → 0`. -/
def loop2 : Equiv.Perm (Fin 3) := fourState.perm .e30 * fourState.perm .e23 * fourState.perm .e02

theorem loop1_eq : loop1 = Equiv.swap 0 1 := by simp [loop1, fourState]
theorem loop2_eq : loop2 = Equiv.swap 1 2 := by simp [loop2, fourState]

/-! ## MonodromyImage = ⊤ : the two loop holonomies generate S3 -/

theorem monodromy_full :
    Subgroup.closure {Equiv.swap (0:Fin 3) 1, Equiv.swap (1:Fin 3) 2} = ⊤ := by
  have h1 : Equiv.swap (0:Fin 3) 1 ∈
      Subgroup.closure {Equiv.swap (0:Fin 3) 1, Equiv.swap (1:Fin 3) 2} :=
    Subgroup.subset_closure (Or.inl rfl)
  have h2 : Equiv.swap (1:Fin 3) 2 ∈
      Subgroup.closure {Equiv.swap (0:Fin 3) 1, Equiv.swap (1:Fin 3) 2} :=
    Subgroup.subset_closure (Or.inr rfl)
  have h02 : Equiv.swap (0:Fin 3) 2 ∈
      Subgroup.closure {Equiv.swap (0:Fin 3) 1, Equiv.swap (1:Fin 3) 2} := by
    have he : Equiv.swap (0:Fin 3) 2
        = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by decide
    rw [he]; exact mul_mem (mul_mem h1 h2) h1
  -- all transpositions generate S3; the three Fin-3 swaps are all in our closure
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨x, y, hxy, rfl⟩
  simp only [SetLike.mem_coe]
  have hcase : Equiv.swap x y = Equiv.swap 0 1 ∨ Equiv.swap x y = Equiv.swap 1 2
      ∨ Equiv.swap x y = Equiv.swap 0 2 := by
    fin_cases x <;> fin_cases y <;> revert hxy <;> decide
  rcases hcase with h | h | h
  · rw [h]; exact h1
  · rw [h]; exact h2
  · rw [h]; exact h02

/-! ## The headline -/

/-- **`exists_global_cspec_fullS3` (first-half globalization).**  There is a finite
acyclic global carrier whose:
  * two loop holonomies are the adjacent transpositions `(0 1)`, `(1 2)`;
  * MonodromyImage is all of `S3` (they generate it);
  * there is NO nonzero global sheet section (no consistent global labeling);
  * the twisted kernel is trivial (`V^{S3} = 0`);
  * every edge transport is recovered from the GLOBAL CAUSAL ORDER incidence alone
    — the transport never appears in a hypothesis, only in the recovered value.

  Sealed: no `witnessSheetTransport`.  Order/conformal sector only. -/
theorem exists_global_cspec_fullS3 :
    ∃ (E : Type) (base : BaseGraph (Fin 4) E) (γ₁ γ₂ : Equiv.Perm (Fin 3)),
      (γ₁ = Equiv.swap 0 1 ∧ γ₂ = Equiv.swap 1 2)
      ∧ Subgroup.closure {γ₁, γ₂} = ⊤
      ∧ (∀ x : Fin 3 → ℝ, (∑ i, x i = 0) → x ∘ γ₁ = x → x ∘ γ₂ = x → x = 0)
      ∧ (∀ x : Fin 3 → ℝ, (∀ σ : Equiv.Perm (Fin 3), x ∘ σ = x) → (∑ i, x i = 0) → x = 0)
      ∧ (∀ (e : E) (a b : Fin 3),
          Cov base (GPoint.atom (base.dst e) b) (GPoint.bridge e a) →
          base.src e ≠ base.dst e → b = base.perm e a) := by
  refine ⟨E4, fourState, loop1, loop2, ⟨loop1_eq, loop2_eq⟩, ?_, ?_, ?_, ?_⟩
  · rw [loop1_eq, loop2_eq]; exact monodromy_full
  · rw [loop1_eq, loop2_eq]
    intro x hsum h1 h2
    exact no_global_section x h1 h2 hsum
  · intro x hinv hsum
    exact invariant_zerosum_eq_zero x hinv hsum
  · intro e a b h hne
    exact bridge_incidence_recovers_transport fourState e a b h hne

#print axioms exists_global_cspec_fullS3

end UnifiedTheory.Audit.KFCausalCSpecGlobalization
