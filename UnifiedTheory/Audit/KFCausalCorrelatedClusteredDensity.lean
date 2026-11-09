/- Full correlated energy densities and their clock derivatives. Factors
are summed before squaring, so no cross term or cancellation is removed. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredDensity
noncomputable section
open Filter
open scoped Topology ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalCorrelatedClusteredProfiles
open KFCausalClusteredClockFactors (F G Z N)

variable {m : ℕ} (f : Family m)

def energyOf (A : ℕ → ℂ) : ℝ := ‖A 0‖^2+‖A 1‖^2/2+‖A 2‖^2/4
def responseOf (A D : ℕ → ℂ) : ℝ :=
  2*(conj (A 0)*D 0).re+2*(conj (A 1)*D 1).re/2+2*(conj (A 2)*D 2).re/4

def density (α β δ : ℝ) (r : ℂ) : Joint → ℝ :=
  KFCausalReciprocalNeutralPositiveForm.positiveDensity (count f) α β (widths f δ) r (coefficients f δ)
    (fun j => exponentialProfile (sources f j) 1 (polynomials f j))
def limitDensity (α β : ℝ) (r : ℂ) (p : Joint) : ℝ :=
  energyOf (fun k => limitFactor f k α β r p)
def response (α β δ : ℝ) (r v : ℂ) (p : Joint) : ℝ :=
  responseOf (fun k => factor f k α β δ r p) (fun k => slope f k α β δ r v p)
def limitResponse (α β : ℝ) (r v : ℂ) (p : Joint) : ℝ :=
  responseOf (fun k => limitFactor f k α β r p) (fun k => limitSlope f k α β r v p)

theorem density_factors (α β δ : ℝ) (hδ : 0 < δ) (r : ℂ) (p : Joint) :
    density f α β δ r p = energyOf (fun k => factor f k α β δ r p) := by
  dsimp only [energyOf]
  rw [factor_joint f 0 α β δ hδ,factor_joint f 1 α β δ hδ,factor_joint f 2 α β δ hδ]
  have hg : (Real.exp (G β r p))^2 = Real.exp (-2*β*(p.1.2 1)^2+8*β*r.im^2*(p.1.2 0)^2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    unfold G
    ring
  simp only [norm_mul,mul_pow,norm_pow,Complex.norm_exp,Complex.ofReal_re,Complex.norm_real,
    Real.norm_eq_abs,pow_zero,pow_one,one_mul,sq_abs,hg]
  unfold density KFCausalReciprocalNeutralPositiveForm.positiveDensity
    KFCausalReciprocalNeutralLaplace.weight KFCausalQuarticPlaneDomination.potential
  simp only [F,Z,N]
  ring

theorem density_derivative (α β δ : ℝ) (hδ : 0 < δ) (r : ℝ → ℂ)
    (v : ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => density f α β δ (r t) p) (response f α β δ (r s) v p) s := by
  have hk (k : ℕ) := KFCausalNeutralQuarticBoundary.norm_square_derivative
    (fun t => factor f k α β δ (r t) p) (fun _ => slope f k α β δ (r s) v p) s
    (factor_derivative f k α β δ hδ r v s p hr)
  convert ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4) using 1
  funext t
  exact density_factors f α β δ hδ (r t) p

theorem limitDensity_derivative (α β : ℝ) (r : ℝ → ℂ)
    (v : ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => limitDensity f α β (r t) p) (limitResponse f α β (r s) v p) s := by
  have hk (k : ℕ) := KFCausalNeutralQuarticBoundary.norm_square_derivative
    (fun t => limitFactor f k α β (r t) p) (fun _ => limitSlope f k α β (r s) v p) s
    (limitFactor_derivative f k α β r v s p hr)
  exact ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4)

theorem density_tendsto (α β : ℝ) (r : ℂ) (p : Joint) :
    Tendsto (fun δ => density f α β δ r p) (𝓝[>] 0) (𝓝 (limitDensity f α β r p)) := by
  have hk (k : ℕ) := (factor_tendsto f k α β r p).norm.pow 2
  apply Tendsto.congr' _ (((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (density_factors f α β δ hδ r p).symm

theorem response_tendsto (α β : ℝ) (r v : ℂ) (p : Joint) :
    Tendsto (fun δ => response f α β δ r v p) (𝓝[>] 0) (𝓝 (limitResponse f α β r v p)) := by
  have hk (k : ℕ) : Tendsto (fun δ => 2*(conj (factor f k α β δ r p)*slope f k α β δ r v p).re)
      (𝓝[>] 0) (𝓝 (2*(conj (limitFactor f k α β r p)*limitSlope f k α β r v p).re)) := by
    simpa only [Complex.star_def] using ((Complex.continuous_re.tendsto _).comp
      ((factor_tendsto f k α β r p).star.mul (slope_tendsto f k α β r v p))).const_mul 2
  exact ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4)

theorem density_continuous (α β δ : ℝ) (r : ℂ) : Continuous (density f α β δ r) := by
  unfold density KFCausalReciprocalNeutralPositiveForm.positiveDensity
    KFCausalReciprocalNeutralPositiveForm.profileSum KFCausalReciprocalWedgeLaplace.laplaceSum
    KFCausalReciprocalNeutralLaplace.weight KFCausalReciprocalWedgeGeometry.chart
    KFCausalReciprocalNeutralKernel.neutral exponentialProfile KFCausalQuarticPlaneDomination.potential
  fun_prop

theorem limitDensity_continuous (α β : ℝ) (r : ℂ) : Continuous (limitDensity f α β r) := by
  unfold limitDensity energyOf limitFactor KFCausalClusteredClockFactors.limitFactor
    KFCausalClusteredClockFactors.E KFCausalClusteredClockFactors.G F Z N
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
  fun_prop

theorem response_continuous (α β δ : ℝ) (r v : ℂ) : Continuous (response f α β δ r v) := by
  unfold response responseOf factor KFCausalCorrelatedClusteredProfiles.slope KFCausalClusteredClockFactors.factor
    KFCausalClusteredClockFactors.slope KFCausalClusteredClockFactors.B0 KFCausalClusteredClockFactors.B1
    KFCausalClusteredClockFactors.E KFCausalClusteredClockFactors.Ed KFCausalClusteredClockFactors.Zd
    KFCausalClusteredClockFactors.Nd KFCausalClusteredClockFactors.Fd KFCausalClusteredClockFactors.Gd F G Z N
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral KFCausalClusteredWidthProfiles.quotient
  fun_prop

theorem limitResponse_continuous (α β : ℝ) (r v : ℂ) : Continuous (limitResponse f α β r v) := by
  unfold limitResponse responseOf limitFactor limitSlope KFCausalClusteredClockFactors.limitFactor
    KFCausalClusteredClockFactors.limitSlope KFCausalClusteredClockFactors.B0 KFCausalClusteredClockFactors.B1
    KFCausalClusteredClockFactors.E KFCausalClusteredClockFactors.Ed KFCausalClusteredClockFactors.Zd
    KFCausalClusteredClockFactors.Nd KFCausalClusteredClockFactors.Fd KFCausalClusteredClockFactors.Gd F G Z N
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
  fun_prop

#print axioms density_factors
#print axioms density_derivative
#print axioms limitDensity_derivative
#print axioms density_tendsto
#print axioms response_tendsto
#print axioms density_continuous
#print axioms limitDensity_continuous
#print axioms response_continuous
#print axioms limitResponse_continuous
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredDensity
