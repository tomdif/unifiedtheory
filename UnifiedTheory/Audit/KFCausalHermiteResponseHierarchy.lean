/- Exact Hermite matrix elements and the uniform-bound obligation.
All finite cutoffs with a common constant are equivalent to the bound
on every finite neutral polynomial. No such constant is asserted to
exist; finite numerical samples are not promoted to a uniform estimate. -/
import UnifiedTheory.Audit.KFCausalNeutralHermiteBasis
import UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalHermiteResponseHierarchy
noncomputable section
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalNeutralHermiteDomain (multiplier)
open UnifiedTheory.Audit.KFCausalPolynomialLocalSuperposition (combination)
open UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse

def quadratic (N : ℕ) (M : ℕ → ℕ → ℂ) (c : ℕ → ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (star (c i)*c j)*M i j

theorem quadratic_affine (N : ℕ) (A D : ℕ → ℕ → ℂ) (c : ℕ → ℂ) (κ : ℝ) :
    quadratic N (fun i j => A i j+(κ:ℂ)*D i j) c =
      quadratic N A c+(κ:ℂ)*quadratic N D c := by
  unfold quadratic
  simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable (ε h : ℝ) (q k : Joint 2 4) (w : Fin 3 → ℝ) (B : ℝ)
local notation "H" => multiplier (neutralWidth h) B

def truncation (N : ℕ) (c : ℕ → ℂ) : Polynomial ℂ := combination (Finset.range N) H c
def kernelEntry (s : ℝ) (i j : ℕ) : ℂ := kernel ε h q k w (H i) (H j) s
def responseEntry (s : ℝ) (i j : ℕ) : ℂ := reducedResponse ε h q k w (H i) (H j) s
def PolynomialBound (κ s : ℝ) : Prop :=
  ∀ P : Polynomial ℂ, -κ*(kernel ε h q k w P P s).re ≤ (reducedResponse ε h q k w P P s).re
def CutoffBound (κ s : ℝ) (N : ℕ) : Prop :=
  ∀ c : ℕ → ℂ, -κ*(quadratic N (kernelEntry ε h q k w B s) c).re ≤
    (quadratic N (responseEntry ε h q k w B s) c).re

variable (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

include hh in
theorem exists_truncation (P : Polynomial ℂ) :
    ∃ N : ℕ, ∃ c : ℕ → ℂ, P = truncation h B N c :=
  KFCausalNeutralHermiteBasis.exists_truncation (neutralWidth h) B (neutralWidth_positive h hh) P

include hε hh hb in
theorem kernel_quadratic (N : ℕ) (c : ℕ → ℂ) (s : ℝ) :
    kernel ε h q k w (truncation h B N c) (truncation h B N c) s =
      quadratic N (kernelEntry ε h q k w B s) c :=
  kernel_combination ε h q k w hε hh hb (Finset.range N) (Finset.range N) H H c c s

include hε hh hb in
theorem response_quadratic (N : ℕ) (c : ℕ → ℂ) (s : ℝ) :
    reducedResponse ε h q k w (truncation h B N c) (truncation h B N c) s =
      quadratic N (responseEntry ε h q k w B s) c :=
  reducedResponse_combination ε h q k w hε hh hb (Finset.range N) (Finset.range N) H H c c s

include hε hh hb in
theorem kernelEntry_conj (s : ℝ) (i j : ℕ) :
    star (kernelEntry ε h q k w B s i j) = kernelEntry ε h q k w B s j i :=
  kernel_conj ε h q k w (H i) (H j) hε hh hb s

include hε hh hb in
theorem responseEntry_conj (s : ℝ) (i j : ℕ) :
    star (responseEntry ε h q k w B s i j) = responseEntry ε h q k w B s j i :=
  reducedResponse_conj ε h q k w (H i) (H j) hε hh hb s

include hε hh hb in
theorem kernel_quadratic_nonnegative (hw : ∀ n, 0 ≤ w n) (N : ℕ) (c : ℕ → ℂ) (s : ℝ) :
    0 ≤ (quadratic N (kernelEntry ε h q k w B s) c).re := by
  rw [← kernel_quadratic ε h q k w B hε hh hb]
  exact kernel_self_nonnegative ε h q k w (truncation h B N c) hε hh hb hw s

include hε hh hb in
theorem polynomial_bound_iff_cutoffs (κ s : ℝ) :
    PolynomialBound ε h q k w κ s ↔ ∀ N, CutoffBound ε h q k w B κ s N := by
  constructor
  · intro hp N c
    have hi := hp (truncation h B N c)
    rwa [kernel_quadratic ε h q k w B hε hh hb,response_quadratic ε h q k w B hε hh hb] at hi
  · intro hm P
    obtain ⟨N,c,rfl⟩ := exists_truncation h B hh P
    rw [kernel_quadratic ε h q k w B hε hh hb,response_quadratic ε h q k w B hε hh hb]
    exact hm N c

theorem cutoff_bound_iff_nonnegative (κ s : ℝ) (N : ℕ) :
    CutoffBound ε h q k w B κ s N ↔
      ∀ c : ℕ → ℂ, 0 ≤ (quadratic N
        (fun i j => responseEntry ε h q k w B s i j+(κ:ℂ)*kernelEntry ε h q k w B s i j) c).re := by
  unfold CutoffBound
  simp only [quadratic_affine,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  constructor <;> intro hi c <;> have hc := hi c <;> linarith

include hε hh hb in
theorem uniform_clock_bound_iff :
    (∃ κ : ℝ, 0 ≤ κ ∧ ∀ s, PolynomialBound ε h q k w κ s) ↔
      (∃ κ : ℝ, 0 ≤ κ ∧ ∀ s N, CutoffBound ε h q k w B κ s N) := by
  constructor
  · rintro ⟨κ,hκ,hp⟩
    exact ⟨κ,hκ,fun s => (polynomial_bound_iff_cutoffs ε h q k w B hε hh hb κ s).mp (hp s)⟩
  · rintro ⟨κ,hκ,hm⟩
    exact ⟨κ,hκ,fun s => (polynomial_bound_iff_cutoffs ε h q k w B hε hh hb κ s).mpr (hm s)⟩

#print axioms quadratic_affine
#print axioms exists_truncation
#print axioms kernel_quadratic
#print axioms response_quadratic
#print axioms kernelEntry_conj
#print axioms responseEntry_conj
#print axioms kernel_quadratic_nonnegative
#print axioms polynomial_bound_iff_cutoffs
#print axioms cutoff_bound_iff_nonnegative
#print axioms uniform_clock_bound_iff
end
end UnifiedTheory.Audit.KFCausalHermiteResponseHierarchy
