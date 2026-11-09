/- Full linked geometric derivatives of genuine width/source differences.
The neutral source increment remains fixed while the clock varies. -/
import UnifiedTheory.Audit.KFCausalJointSourceConfluenceProfiles
import UnifiedTheory.Audit.KFCausalFiniteNeutralResponseIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointSourceConfluenceFactors
noncomputable section
open Filter
open scoped Topology ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalClusteredClockFactors (Z Zd N Nd F Fd G E B0)
open KFCausalClusteredWidthProfiles (quotient)
open KFCausalJointSourceConfluenceProfiles (widths sources coefficients)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity profileSum)
open KFCausalNeutralExponentialProfiles (exponentialProfile)

def Q (α : ℝ) (r ℓ : ℂ) (p : Joint) : ℂ := Z α r p-ℓ*N r p
def Qd (α : ℝ) (r v ℓ : ℂ) (p : Joint) : ℂ := Zd α r v p-ℓ*Nd v p
def B1 (n k : ℕ) (α : ℝ) (r v ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  (n:ℂ)*(F r p:ℂ)^k*Qd α r v ℓ p*P.eval (N r p)
def factor (n k : ℕ) (α β w0 δ : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  Complex.exp (E (w0*α) β r b p)*(F r p:ℂ)^k*quotient δ (Q α r ℓ p)^n*P.eval (N r p)
def limitFactor (n k : ℕ) (α β w0 : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  Complex.exp (E (w0*α) β r b p)*(F r p:ℂ)^k*Q α r ℓ p^n*P.eval (N r p)
def slope (n k : ℕ) (α β w0 δ : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  Complex.exp (E (w0*α) β r b p)*
    (quotient δ (Q α r ℓ p)^n*B0 k (w0*α) β r v b P p+
      quotient δ (Q α r ℓ p)^(n-1)*Complex.exp (-(δ:ℂ)*Q α r ℓ p)*B1 n k α r v ℓ P p)
def limitSlope (n k : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  Complex.exp (E (w0*α) β r b p)*
    (Q α r ℓ p^n*B0 k (w0*α) β r v b P p+
      Q α r ℓ p^(n-1)*B1 n k α r v ℓ P p)
def density (n : ℕ) (α β w0 δ : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  ‖factor n 0 α β w0 δ r b ℓ P p‖^2+
    ‖factor n 1 α β w0 δ r b ℓ P p‖^2/2+‖factor n 2 α β w0 δ r b ℓ P p‖^2/4
def limitDensity (n : ℕ) (α β w0 : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  ‖limitFactor n 0 α β w0 r b ℓ P p‖^2+
    ‖limitFactor n 1 α β w0 r b ℓ P p‖^2/2+‖limitFactor n 2 α β w0 r b ℓ P p‖^2/4
def component (n k : ℕ) (α β w0 δ : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  2*(conj (factor n k α β w0 δ r b ℓ P p)*slope n k α β w0 δ r v b ℓ P p).re
def limitComponent (n k : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  2*(conj (limitFactor n k α β w0 r b ℓ P p)*limitSlope n k α β w0 r v b ℓ P p).re
def response (n : ℕ) (α β w0 δ : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  component n 0 α β w0 δ r v b ℓ P p+
    component n 1 α β w0 δ r v b ℓ P p/2+component n 2 α β w0 δ r v b ℓ P p/4
def limitResponse (n : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) : ℝ :=
  limitComponent n 0 α β w0 r v b ℓ P p+
    limitComponent n 1 α β w0 r v b ℓ P p/2+limitComponent n 2 α β w0 r v b ℓ P p/4

theorem Q_derivative (α : ℝ) (r : ℝ → ℂ) (v ℓ : ℂ) (s : ℝ) (p : Joint)
    (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => Q α (r t) ℓ p) (Qd α (r s) v ℓ p) s :=
  (KFCausalClusteredClockFactors.Z_derivative α r v s p hr).sub
    ((KFCausalClusteredClockFactors.N_derivative r v s p hr).const_mul ℓ)

theorem factor_derivative (n k : ℕ) (α β w0 δ : ℝ) (hδ : 0 < δ)
    (r : ℝ → ℂ) (v b ℓ : ℂ) (P : Polynomial ℂ) (s : ℝ) (p : Joint)
    (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => factor n k α β w0 δ (r t) b ℓ P p)
      (slope n k α β w0 δ (r s) v b ℓ P p) s := by
  have hq := (KFCausalClusteredWidthChargedJet.quotient_derivative δ hδ.ne' (Q α (r s) ℓ p)).scomp s
    (Q_derivative α r v ℓ s p hr)
  have hp := (P.hasDerivAt (N (r s) p)).scomp s
    (KFCausalClusteredClockFactors.N_derivative r v s p hr)
  convert ((((KFCausalClusteredClockFactors.E_derivative (w0*α) β r v b s p hr).cexp.mul
    ((KFCausalClusteredClockFactors.F_derivative r v s p hr).ofReal_comp.pow k)).mul
      (hq.pow n)).mul hp) using 1
  dsimp [factor,slope,B0,B1]
  ring

theorem limitFactor_derivative (n k : ℕ) (α β w0 : ℝ)
    (r : ℝ → ℂ) (v b ℓ : ℂ) (P : Polynomial ℂ) (s : ℝ) (p : Joint)
    (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => limitFactor n k α β w0 (r t) b ℓ P p)
      (limitSlope n k α β w0 (r s) v b ℓ P p) s := by
  have hp := (P.hasDerivAt (N (r s) p)).scomp s
    (KFCausalClusteredClockFactors.N_derivative r v s p hr)
  convert ((((KFCausalClusteredClockFactors.E_derivative (w0*α) β r v b s p hr).cexp.mul
    ((KFCausalClusteredClockFactors.F_derivative r v s p hr).ofReal_comp.pow k)).mul
      ((Q_derivative α r v ℓ s p hr).pow n)).mul hp) using 1
  dsimp [limitFactor,limitSlope,B0,B1]
  ring

theorem factor_tendsto (n k : ℕ) (α β w0 : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    Tendsto (fun δ : ℝ => factor n k α β w0 δ r b ℓ P p) (𝓝[>] 0)
      (𝓝 (limitFactor n k α β w0 r b ℓ P p)) :=
  (((KFCausalClusteredWidthProfiles.quotient_tendsto (Q α r ℓ p)).pow n).const_mul
    (Complex.exp (E (w0*α) β r b p)*(F r p:ℂ)^k)).mul_const (P.eval (N r p))

theorem slope_tendsto (n k : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    Tendsto (fun δ : ℝ => slope n k α β w0 δ r v b ℓ P p) (𝓝[>] 0)
      (𝓝 (limitSlope n k α β w0 r v b ℓ P p)) := by
  have hq := KFCausalClusteredWidthProfiles.quotient_tendsto (Q α r ℓ p)
  have he : Tendsto (fun δ : ℝ => Complex.exp (-(δ:ℂ)*Q α r ℓ p)) (𝓝[>] 0) (𝓝 (1:ℂ)) := by
    have hc : ContinuousAt (fun δ : ℝ => Complex.exp (-(δ:ℂ)*Q α r ℓ p)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [slope,limitSlope,mul_one] using
    (((hq.pow n).mul_const (B0 k (w0*α) β r v b P p)).add
      (((hq.pow (n-1)).mul he).mul_const (B1 n k α r v ℓ P p))).const_mul
        (Complex.exp (E (w0*α) β r b p))

theorem density_tendsto (n : ℕ) (α β w0 : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    Tendsto (fun δ : ℝ => density n α β w0 δ r b ℓ P p) (𝓝[>] 0)
      (𝓝 (limitDensity n α β w0 r b ℓ P p)) := by
  have ht (k : ℕ) := (factor_tendsto n k α β w0 r b ℓ P p).norm.pow 2
  exact ((ht 0).add ((ht 1).div_const 2)).add ((ht 2).div_const 4)

theorem response_tendsto (n : ℕ) (α β w0 : ℝ) (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    Tendsto (fun δ : ℝ => response n α β w0 δ r v b ℓ P p) (𝓝[>] 0)
      (𝓝 (limitResponse n α β w0 r v b ℓ P p)) := by
  have ht (k : ℕ) : Tendsto (fun δ : ℝ => component n k α β w0 δ r v b ℓ P p)
      (𝓝[>] 0) (𝓝 (limitComponent n k α β w0 r v b ℓ P p)) :=
    ((Complex.continuous_re.tendsto _).comp
      (((Complex.continuous_conj.tendsto _).comp (factor_tendsto n k α β w0 r b ℓ P p)).mul
        (slope_tendsto n k α β w0 r v b ℓ P p))).const_mul 2
  exact ((ht 0).add ((ht 1).div_const 2)).add ((ht 2).div_const 4)

private theorem scaled_Z (α w0 : ℝ) (r : ℂ) (p : Joint) :
    Z (w0*α) r p = (w0:ℂ)*Z α r p := by
  unfold Z KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalWedgeGeometry.gamma
  push_cast
  simp only [map_div₀,map_mul,map_pow,Complex.conj_ofReal,map_ofNat]
  ring

theorem factor_joint (n k : ℕ) (α β w0 δ : ℝ) (hw0 : 1 ≤ w0) (hδ : 0 < δ)
    (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    factor n k α β w0 δ r b ℓ P p = (F r p:ℂ)^k*Complex.exp (G β r p:ℂ)*
      profileSum (n+1) (widths n w0 δ) (coefficients n w0 δ)
        (fun i => exponentialProfile (sources n δ b ℓ i) 1 P) (Z α r p) (N r p) := by
  rw [KFCausalJointSourceConfluenceProfiles.profileSum_exact n w0 δ hw0 hδ]
  simp only [factor,E,scaled_Z,Q,Complex.exp_add]
  simp only [neg_mul]
  ring

theorem density_joint (n : ℕ) (α β w0 δ : ℝ) (hw0 : 1 ≤ w0) (hδ : 0 < δ)
    (r b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    positiveDensity (n+1) α β (widths n w0 δ) r (coefficients n w0 δ)
      (fun i => exponentialProfile (sources n δ b ℓ i) 1 P) p = density n α β w0 δ r b ℓ P p := by
  unfold density
  rw [factor_joint n 0 α β w0 δ hw0 hδ,factor_joint n 1 α β w0 δ hw0 hδ,
    factor_joint n 2 α β w0 δ hw0 hδ]
  have hg : (Real.exp (G β r p))^2 =
      Real.exp (-2*β*(p.1.2 1)^2+8*β*r.im^2*(p.1.2 0)^2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    unfold G
    ring
  simp only [norm_mul,mul_pow,norm_pow,Complex.norm_exp,Complex.ofReal_re,Complex.norm_real,
    Real.norm_eq_abs,pow_zero,pow_one,one_mul,sq_abs,hg]
  unfold positiveDensity KFCausalReciprocalNeutralLaplace.weight KFCausalQuarticPlaneDomination.potential
  simp only [F,Z,N]
  ring

theorem density_derivative (n : ℕ) (α β w0 δ : ℝ) (hw0 : 1 ≤ w0) (hδ : 0 < δ)
    (r : ℝ → ℂ) (v b ℓ : ℂ) (P : Polynomial ℂ) (s : ℝ) (p : Joint)
    (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => positiveDensity (n+1) α β (widths n w0 δ) (r t) (coefficients n w0 δ)
      (fun i => exponentialProfile (sources n δ b ℓ i) 1 P) p)
      (response n α β w0 δ (r s) v b ℓ P p) s := by
  have hk (k : ℕ) := KFCausalNeutralQuarticBoundary.norm_square_derivative
    (fun t => factor n k α β w0 δ (r t) b ℓ P p)
    (fun _ => slope n k α β w0 δ (r s) v b ℓ P p) s
    (factor_derivative n k α β w0 δ hδ r v b ℓ P s p hr)
  convert ((hk 0).add ((hk 1).div_const 2)).add ((hk 2).div_const 4) using 1
  funext t
  exact density_joint n α β w0 δ hw0 hδ (r t) b ℓ P p

theorem spatial_response_eq (n : ℕ) (α β w0 δ : ℝ) (hw0 : 1 ≤ w0) (hδ : 0 < δ)
    (r v b ℓ : ℂ) (P : Polynomial ℂ) (p : Joint) :
    KFCausalJointNeutralFourierOuterDensity.spatialQuarticResponse (n+1) α β
      (widths n w0 δ) (sources n δ b ℓ) (coefficients n w0 δ) (fun _ => P)
      r v p.1.1 (p.1.2 0) p.2 (p.1.2 1) = response n α β w0 δ r v b ℓ P p := by
  rw [KFCausalFiniteNeutralResponseIntegrability.spatial_response_eq]
  let curve : ℝ → ℂ := fun t => r+(t:ℂ)*v
  have hr : HasDerivAt curve v 0 := by
    simpa only [curve,id_eq,Complex.ofReal_one,one_mul] using
      ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const v).const_add r
  have hd := KFCausalFiniteNeutralResponseIntegrability.density_derivative (n+1) α β
    (widths n w0 δ) (sources n δ b ℓ) (coefficients n w0 δ) (fun _ => P) curve v 0 p hr
  simpa only [curve,Complex.ofReal_zero,zero_mul,add_zero] using
    hd.unique (density_derivative n α β w0 δ hw0 hδ curve v b ℓ P 0 p hr)

#print axioms Q_derivative
#print axioms factor_derivative
#print axioms limitFactor_derivative
#print axioms factor_tendsto
#print axioms slope_tendsto
#print axioms density_tendsto
#print axioms response_tendsto
#print axioms factor_joint
#print axioms density_joint
#print axioms density_derivative
#print axioms spatial_response_eq
end
end UnifiedTheory.Audit.KFCausalJointSourceConfluenceFactors
