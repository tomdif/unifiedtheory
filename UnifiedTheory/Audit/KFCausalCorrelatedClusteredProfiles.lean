/- Finite correlated charged-polynomial/neutral-profile blocks, embedded
in the existing Fin-indexed reciprocal packet family with every term kept. -/
import UnifiedTheory.Audit.KFCausalClusteredResponseLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredProfiles
noncomputable section
open Filter
open scoped Topology
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalReciprocalNeutralPositiveForm (profileSum)
open KFCausalClusteredClockFactors (Z N F G)

structure Family (m : ℕ) where
  degree : Fin m → ℕ
  source : Fin m → ℂ
  polynomial : Fin m → Polynomial ℂ
  amplitude : Fin m → ℂ

variable {m : ℕ} (f : Family m)
abbrev Index := (i : Fin m) × Fin (f.degree i+1)
def count : ℕ := Fintype.card (Index f)
def index : Fin (count f) ≃ Index f := (Fintype.equivFin (Index f)).symm

def widths (δ : ℝ) (j : Fin (count f)) : ℝ :=
  KFCausalClusteredWidthProfiles.widths (f.degree (index f j).1) δ (index f j).2
def coefficients (δ : ℝ) (j : Fin (count f)) : ℂ :=
  f.amplitude (index f j).1*KFCausalClusteredWidthProfiles.coefficients (f.degree (index f j).1) δ (index f j).2
def sources (j : Fin (count f)) : ℂ := f.source (index f j).1
def polynomials (j : Fin (count f)) : Polynomial ℂ := f.polynomial (index f j).1

theorem sum_index (g : Index f → ℂ) :
    (∑ j, g (index f j)) = ∑ i, ∑ k, g ⟨i,k⟩ := by
  rw [(index f).sum_comp g,Fintype.sum_sigma]

theorem widths_admissible (δ : ℝ) (hδ : 0 ≤ δ) (j : Fin (count f)) : 1 ≤ widths f δ j :=
  KFCausalClusteredWidthProfiles.widths_admissible _ δ hδ _

theorem profileSum_blocks (δ : ℝ) (z ζ : ℂ) :
    profileSum (count f) (widths f δ) (coefficients f δ)
      (fun j => exponentialProfile (sources f j) 1 (polynomials f j)) z ζ =
      ∑ i, f.amplitude i*profileSum (f.degree i+1)
        (KFCausalClusteredWidthProfiles.widths (f.degree i) δ)
        (KFCausalClusteredWidthProfiles.coefficients (f.degree i) δ)
        (fun _ => exponentialProfile (f.source i) 1 (f.polynomial i)) z ζ := by
  unfold profileSum KFCausalReciprocalWedgeLaplace.laplaceSum widths coefficients sources polynomials
  rw [sum_index f (fun j =>
    (f.amplitude j.1*KFCausalClusteredWidthProfiles.coefficients (f.degree j.1) δ j.2*
      exponentialProfile (f.source j.1) 1 (f.polynomial j.1) ζ)*
      (KFCausalClusteredWidthProfiles.widths (f.degree j.1) δ j.2:ℂ)*
      Complex.exp (-(KFCausalClusteredWidthProfiles.widths (f.degree j.1) δ j.2:ℂ)*z))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def factor (k : ℕ) (α β δ : ℝ) (r : ℂ) (p : Joint) : ℂ :=
  ∑ i, f.amplitude i*KFCausalClusteredClockFactors.factor (f.degree i) k α β δ r (f.source i) (f.polynomial i) p
def slope (k : ℕ) (α β δ : ℝ) (r v : ℂ) (p : Joint) : ℂ :=
  ∑ i, f.amplitude i*KFCausalClusteredClockFactors.slope (f.degree i) k α β δ r v (f.source i) (f.polynomial i) p
def limitFactor (k : ℕ) (α β : ℝ) (r : ℂ) (p : Joint) : ℂ :=
  ∑ i, f.amplitude i*KFCausalClusteredClockFactors.limitFactor (f.degree i) k α β r (f.source i) (f.polynomial i) p
def limitSlope (k : ℕ) (α β : ℝ) (r v : ℂ) (p : Joint) : ℂ :=
  ∑ i, f.amplitude i*KFCausalClusteredClockFactors.limitSlope (f.degree i) k α β r v (f.source i) (f.polynomial i) p

theorem factor_joint (k : ℕ) (α β δ : ℝ) (hδ : 0 < δ) (r : ℂ) (p : Joint) :
    factor f k α β δ r p = (F r p:ℂ)^k*Complex.exp (G β r p:ℂ)*
      profileSum (count f) (widths f δ) (coefficients f δ)
        (fun j => exponentialProfile (sources f j) 1 (polynomials f j)) (Z α r p) (N r p) := by
  rw [profileSum_blocks,Finset.mul_sum]
  unfold factor
  apply Finset.sum_congr rfl
  intro i _
  rw [KFCausalClusteredClockDensity.factor_joint _ _ _ _ _ hδ]
  ring

theorem factor_derivative (k : ℕ) (α β δ : ℝ) (hδ : 0 < δ) (r : ℝ → ℂ)
    (v : ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => factor f k α β δ (r t) p) (slope f k α β δ (r s) v p) s :=
  HasDerivAt.fun_sum (fun i _ =>
    (KFCausalClusteredClockFactors.factor_derivative (f.degree i) k α β δ hδ r v
      (f.source i) (f.polynomial i) s p hr).const_mul (f.amplitude i))

theorem limitFactor_derivative (k : ℕ) (α β : ℝ) (r : ℝ → ℂ)
    (v : ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => limitFactor f k α β (r t) p) (limitSlope f k α β (r s) v p) s :=
  HasDerivAt.fun_sum (fun i _ =>
    (KFCausalClusteredClockFactors.limitFactor_derivative (f.degree i) k α β r v
      (f.source i) (f.polynomial i) s p hr).const_mul (f.amplitude i))

theorem factor_tendsto (k : ℕ) (α β : ℝ) (r : ℂ) (p : Joint) :
    Tendsto (fun δ => factor f k α β δ r p) (𝓝[>] 0) (𝓝 (limitFactor f k α β r p)) :=
  tendsto_finset_sum _ (fun i _ =>
    (KFCausalClusteredClockFactors.factor_tendsto (f.degree i) k α β r (f.source i) (f.polynomial i) p).const_mul _)

theorem slope_tendsto (k : ℕ) (α β : ℝ) (r v : ℂ) (p : Joint) :
    Tendsto (fun δ => slope f k α β δ r v p) (𝓝[>] 0) (𝓝 (limitSlope f k α β r v p)) :=
  tendsto_finset_sum _ (fun i _ =>
    (KFCausalClusteredClockFactors.slope_tendsto (f.degree i) k α β r v (f.source i) (f.polynomial i) p).const_mul _)

#print axioms sum_index
#print axioms widths_admissible
#print axioms profileSum_blocks
#print axioms factor_joint
#print axioms factor_derivative
#print axioms limitFactor_derivative
#print axioms factor_tendsto
#print axioms slope_tendsto
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredProfiles
