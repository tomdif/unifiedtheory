/- Bosonic occupation Hilbert space, its dense finite-particle core, and
normalized creation/annihilation maps. This is the occupation realization
over a specified orthonormal mode index; no finite particle cutoff is used. -/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalBosonicOccupationSpace
noncomputable section
open scoped BigOperators
variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq _

abbrev Occupation (ι : Type*) := ι →₀ ℕ
abbrev Core (ι : Type*) := Occupation ι →₀ ℂ
abbrev Fock (ι : Type*) := lp (fun _ : Occupation ι => ℂ) 2

def embed : Core ι →ₗ[ℂ] Fock ι :=
  Finsupp.lsum ℂ (fun n => (lp.singleContinuousLinearMap ℂ
    (fun _ : Occupation ι => ℂ) 2 n).toLinearMap)

@[simp] theorem embed_single (n : Occupation ι) (c : ℂ) :
    embed (Finsupp.single n c) = lp.single 2 n c :=
  Finsupp.lsum_single _ _ _ _

@[simp] theorem embed_apply (u : Core ι) (n : Occupation ι) : embed u n = u n := by
  classical
  simp [embed, Finsupp.lsum_apply, Finsupp.sum, lp.single_apply]
  intro hz
  exact hz.symm

theorem embed_injective : Function.Injective (embed (ι := ι)) := by
  intro u v huv
  ext n
  simpa using congrArg (fun w : Fock ι => w n) huv

theorem core_dense : DenseRange (embed (ι := ι)) := by
  classical
  intro u
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num) u)
  apply Filter.Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ n ∈ s, Finsupp.single n (u n), ?_⟩
  simp

def vacuum : Fock ι := lp.single 2 0 1
def vacuumCore : Core ι := Finsupp.single 0 1

@[simp] theorem embed_vacuum : embed (vacuumCore (ι := ι)) = vacuum := embed_single _ _

theorem vacuum_norm : ‖vacuum (ι := ι)‖ = 1 := by
  simp [vacuum, lp.norm_single]

theorem vacuum_nonzero : vacuum (ι := ι) ≠ 0 := by
  intro hz
  have hn := vacuum_norm (ι := ι)
  rw [hz, norm_zero] at hn
  norm_num at hn

def raise (i : ι) (n : Occupation ι) : Occupation ι := n + Finsupp.single i 1
def lower (i : ι) (n : Occupation ι) : Occupation ι := n - Finsupp.single i 1
def amplitude (n : ℕ) : ℂ := (Real.sqrt n : ℂ)

@[simp] theorem amplitude_zero : amplitude 0 = 0 := by simp [amplitude]
@[simp] theorem amplitude_one : amplitude 1 = 1 := by simp [amplitude]
@[simp] theorem amplitude_square (n : ℕ) : amplitude n * amplitude n = (n : ℂ) := by
  rw [amplitude, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  norm_cast

def creation (i : ι) : Core ι →ₗ[ℂ] Core ι :=
  Finsupp.lsum ℂ (fun n => (amplitude (n i + 1)) • Finsupp.lsingle (raise i n))

def annihilation (i : ι) : Core ι →ₗ[ℂ] Core ι :=
  Finsupp.lsum ℂ (fun n => (amplitude (n i)) • Finsupp.lsingle (lower i n))

@[simp] theorem creation_single (i : ι) (n : Occupation ι) (c : ℂ) :
    creation i (Finsupp.single n c) = Finsupp.single (raise i n) (amplitude (n i + 1) * c) := by
  simp [creation, Finsupp.lsum_single, Finsupp.smul_single, smul_eq_mul]

@[simp] theorem annihilation_single (i : ι) (n : Occupation ι) (c : ℂ) :
    annihilation i (Finsupp.single n c) = Finsupp.single (lower i n) (amplitude (n i) * c) := by
  simp [annihilation, Finsupp.lsum_single, Finsupp.smul_single, smul_eq_mul]

@[simp] theorem annihilation_vacuum (i : ι) : annihilation i vacuumCore = 0 := by
  simp [vacuumCore]

@[simp] theorem creation_vacuum (i : ι) :
    creation i vacuumCore = Finsupp.single (Finsupp.single i 1) 1 := by
  simp [vacuumCore, raise]

@[simp] theorem lower_raise (i : ι) (n : Occupation ι) : lower i (raise i n) = n := by
  simp [lower, raise]

theorem raise_lower (i : ι) (n : Occupation ι) (hn : n i ≠ 0) :
    raise i (lower i n) = n := by
  classical
  ext j
  by_cases hj : j = i
  · subst j
    simp [raise, lower]
    omega
  · simp [raise, lower, hj]

theorem same_mode_ccr (i : ι) (u : Core ι) :
    annihilation i (creation i u) - creation i (annihilation i u) = u := by
  classical
  have hmap : (annihilation i).comp (creation i) -
      (creation i).comp (annihilation i) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro n c
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, creation_single,
      annihilation_single, lower_raise, LinearMap.id_apply]
    have hr : raise i n i = n i + 1 := by simp [raise]
    rw [hr, ← mul_assoc, amplitude_square]
    by_cases hn : n i = 0
    · simp [hn]
    · have hl : lower i n i + 1 = n i := by simp [lower]; omega
      rw [raise_lower i n hn, hl, ← mul_assoc, amplitude_square,
        ← Finsupp.single_sub]
      congr 1
      push_cast
      ring
  exact congrArg (fun T : Core ι →ₗ[ℂ] Core ι => T u) hmap

end
end UnifiedTheory.Audit.KFCausalBosonicOccupationSpace
