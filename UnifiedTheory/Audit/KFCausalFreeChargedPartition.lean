/- Convergent thermal sum over the actual zero-charge circular energy shells.
The clock and neutral momentum are fixed fiber parameters, not traced out. -/
import UnifiedTheory.Audit.KFCausalFreeCircularSpectralDomain
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalFreeChargedPartition
noncomputable section
open KFCausalCircularZeroLevelCounting
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalClockFloorFlow (clock)

theorem square_choose (n : ℕ) : ((n:ℝ)+1)^2 =
    2*((n+2).choose 2:ℝ)-((n+1).choose 1:ℝ) := by
  have he := Nat.add_one_mul_choose_eq (n+1) 1
  simp only [Nat.choose_one_right] at he
  have hr : 2*((n+2).choose 2:ℝ) = ((n:ℝ)+1)*((n:ℝ)+2) := by
    exact_mod_cast (by nlinarith [he] : 2*((n+2).choose 2) = (n+1)*(n+2))
  rw [Nat.choose_one_right,hr]
  push_cast
  ring

theorem pair_hasSum (u : ℝ) (hu : |u| < 1) :
    HasSum (fun n : ℕ => ((n:ℝ)+1)^2*u^n) ((1+u)/(1-u)^3) := by
  have h2 := (hasSum_choose_mul_geometric_of_norm_lt_one 2 (by simpa using hu : ‖u‖ < 1)).mul_left 2
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one 1 (by simpa using hu : ‖u‖ < 1)
  have he := h2.sub h1
  have hn : 1-u ≠ 0 := by have h := (abs_lt.mp hu).2; linarith
  convert he using 1
  · funext n
    rw [square_choose]
    ring
  · norm_num
    field_simp
    <;> ring

def gap (ε h t s : ℝ) : ℝ := 2*h*Real.exp t/clock ε s

def ground (ε h t s ξ : ℝ) : ℝ :=
  clock ε s/2 + (2*Real.pi*h)^2*ξ^2/(2*clock ε s)+gap ε h t s

def levelEnergy (ε h t s ξ : ℝ) (p : ℕ) : ℝ := ground ε h t s ξ+gap ε h t s*p

theorem physical_level (ε h t : ℝ) (p : ℕ) (i : Level p) (x : Block 2) :
    KFCausalFreeCircularSpectral.fiberEnergy ε h t i.val x = levelEnergy ε h t (x 0) (x 1) p := by
  rw [KFCausalFreeCircularSpectral.zero_level_fiber]
  unfold levelEnergy ground gap
  ring

theorem gap_positive (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h) (t s : ℝ) :
    0 < gap ε h t s := by
  unfold gap
  exact div_pos (mul_pos (mul_pos (by norm_num) hh) (Real.exp_pos t))
    (KFCausalClockFloorCanonicalDefect.clock_positive ε s hε.le)

def partition (ε h t s ξ β : ℝ) : ℝ :=
  ∑' p : ℕ, (Fintype.card (Level p):ℝ)*Real.exp (-β*levelEnergy ε h t s ξ p)

theorem boltzmann_factor (ε h t s ξ β : ℝ) (p : ℕ) :
    Real.exp (-β*levelEnergy ε h t s ξ p) =
      Real.exp (-β*ground ε h t s ξ)*Real.exp (-β*gap ε h t s)^p := by
  rw [← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  unfold levelEnergy
  ring

theorem partition_hasSum (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t s ξ β : ℝ) (hβ : 0 < β) :
    HasSum (fun p : ℕ => (Fintype.card (Level p):ℝ)*Real.exp (-β*levelEnergy ε h t s ξ p))
      (Real.exp (-β*ground ε h t s ξ)*
        ((1+Real.exp (-β*gap ε h t s))/(1-Real.exp (-β*gap ε h t s))^3)) := by
  have hu : |Real.exp (-β*gap ε h t s)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]
    simpa only [neg_mul] using neg_neg_of_pos (mul_pos hβ (gap_positive ε hε h hh t s))
  have he := (pair_hasSum (Real.exp (-β*gap ε h t s)) hu).mul_left
    (Real.exp (-β*ground ε h t s ξ))
  convert he using 1
  funext p
  rw [level_card,boltzmann_factor]
  push_cast
  ring

theorem partition_eq (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t s ξ β : ℝ) (hβ : 0 < β) : partition ε h t s ξ β =
      Real.exp (-β*ground ε h t s ξ)*
        ((1+Real.exp (-β*gap ε h t s))/(1-Real.exp (-β*gap ε h t s))^3) :=
  (partition_hasSum ε hε h hh t s ξ β hβ).tsum_eq

#print axioms pair_hasSum
#print axioms physical_level
#print axioms partition_hasSum
#print axioms partition_eq
end
end UnifiedTheory.Audit.KFCausalFreeChargedPartition
