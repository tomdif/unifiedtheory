/- Complete clock differentiation of clustered joint density factors.
Charged, neutral, Gaussian and field motion are all retained. The spacing
limit here is pointwise; integral convergence is proved separately. -/
import UnifiedTheory.Audit.KFCausalClusteredWidthEnergyLimit
import UnifiedTheory.Audit.KFCausalClusteredWidthChargedJet
import UnifiedTheory.Audit.KFCausalNeutralQuarticBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalClusteredClockFactors
noncomputable section
open Filter
open scoped Topology ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalReciprocalWedgeGeometry (chart gamma)
open KFCausalReciprocalNeutralKernel (neutral)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalClusteredWidthProfiles (quotient widths coefficients limitDensity)

def Z (α : ℝ) (r : ℂ) (p : Joint) : ℂ := chart α r (p.1.1^2+(p.1.2 0)^2) p.2
def Zd (α : ℝ) (r v : ℂ) (p : Joint) : ℂ :=
  (α:ℂ)*r*v*((p.1.1^2+(p.1.2 0)^2:ℝ):ℂ)+conj ((α:ℂ)*r*v)*(p.2:ℂ)
def N (r : ℂ) (p : Joint) : ℂ := neutral r (p.1.2 0) (p.1.2 1)
def Nd (v : ℂ) (p : Joint) : ℂ := 2*(v.im:ℂ)*Complex.I*(p.1.2 0:ℂ)
def F (r : ℂ) (p : Joint) : ℝ := p.1.2 1+fieldSlope r*p.1.2 0
def Fd (v : ℂ) (p : Joint) : ℝ := -2*v.re*p.1.2 0
def G (β : ℝ) (r : ℂ) (p : Joint) : ℝ := -β*(p.1.2 1)^2+4*β*r.im^2*(p.1.2 0)^2
def Gd (β : ℝ) (r v : ℂ) (p : Joint) : ℝ := 8*β*r.im*v.im*(p.1.2 0)^2
def E (α β : ℝ) (r b : ℂ) (p : Joint) : ℂ := -Z α r p+(G β r p:ℂ)+b*N r p
def Ed (α β : ℝ) (r v b : ℂ) (p : Joint) : ℂ := -Zd α r v p+(Gd β r v p:ℂ)+b*Nd v p
def B0 (k : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  (k:ℂ)*(F r p:ℂ)^(k-1)*(Fd v p:ℂ)*P.eval (N r p)+
    (F r p:ℂ)^k*(P.derivative.eval (N r p)*Nd v p+Ed α β r v b p*P.eval (N r p))
def B1 (n k : ℕ) (α : ℝ) (r v : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  (n:ℂ)*(F r p:ℂ)^k*Zd α r v p*P.eval (N r p)
def factor (n k : ℕ) (α β δ : ℝ) (r b : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  Complex.exp (E α β r b p)*(F r p:ℂ)^k*quotient δ (Z α r p)^n*P.eval (N r p)
def limitFactor (n k : ℕ) (α β : ℝ) (r b : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  Complex.exp (E α β r b p)*(F r p:ℂ)^k*Z α r p^n*P.eval (N r p)
def slope (n k : ℕ) (α β δ : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  Complex.exp (E α β r b p)*(quotient δ (Z α r p)^n*B0 k α β r v b P p+
    quotient δ (Z α r p)^(n-1)*Complex.exp (-(δ:ℂ)*Z α r p)*B1 n k α r v P p)
def limitSlope (n k : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) : ℂ :=
  Complex.exp (E α β r b p)*(Z α r p^n*B0 k α β r v b P p+
    Z α r p^(n-1)*B1 n k α r v P p)

theorem Z_derivative (α : ℝ) (r : ℝ → ℂ) (v : ℂ) (s : ℝ) (p : Joint)
    (hr : HasDerivAt r v s) : HasDerivAt (fun t => Z α (r t) p) (Zd α (r s) v p) s := by
  have hg := ((hr.pow 2).const_mul (α:ℂ)).div_const 2
  have hd := (hg.mul_const ((p.1.1^2+(p.1.2 0)^2:ℝ):ℂ)).add (hg.star.mul_const (p.2:ℂ))
  convert hd using 1
  dsimp [Z,Zd,chart,gamma,Complex.star_def]
  push_cast
  ring

theorem N_derivative (r : ℝ → ℂ) (v : ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => N (r t) p) (Nd v p) s := by
  have hi := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hr).ofReal_comp
  convert (((hi.const_mul 2).mul_const Complex.I).mul_const (p.1.2 0:ℂ)).const_add (p.1.2 1:ℂ) using 1

theorem F_derivative (r : ℝ → ℂ) (v : ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => F (r t) p) (Fd v p) s := by
  have hd := (((Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hr).const_mul 2).const_sub 3).mul_const (p.1.2 0)
  convert hd.const_add (p.1.2 1) using 1
  dsimp [F,Fd,fieldSlope]
  ring

theorem G_derivative (β : ℝ) (r : ℝ → ℂ) (v : ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => G β (r t) p) (Gd β (r s) v p) s := by
  have hd := (((Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hr).pow 2).const_mul (4*β)).mul_const ((p.1.2 0)^2)
  convert hd.const_add (-β*(p.1.2 1)^2) using 1
  dsimp [G,Gd]
  ring

theorem E_derivative (α β : ℝ) (r : ℝ → ℂ) (v b : ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => E α β (r t) b p) (Ed α β (r s) v b p) s :=
  ((Z_derivative α r v s p hr).neg.add (G_derivative β r v s p hr).ofReal_comp).add
    ((N_derivative r v s p hr).const_mul b)

theorem factor_derivative (n k : ℕ) (α β δ : ℝ) (hδ : 0 < δ)
    (r : ℝ → ℂ) (v b : ℂ) (P : Polynomial ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => factor n k α β δ (r t) b P p) (slope n k α β δ (r s) v b P p) s := by
  have hq := (KFCausalClusteredWidthChargedJet.quotient_derivative δ hδ.ne' (Z α (r s) p)).scomp s
    (Z_derivative α r v s p hr)
  have hp := (P.hasDerivAt (N (r s) p)).scomp s (N_derivative r v s p hr)
  convert ((((E_derivative α β r v b s p hr).cexp.mul
    ((F_derivative r v s p hr).ofReal_comp.pow k)).mul (hq.pow n)).mul hp) using 1
  dsimp [factor,slope,B0,B1]
  ring

theorem limitFactor_derivative (n k : ℕ) (α β : ℝ)
    (r : ℝ → ℂ) (v b : ℂ) (P : Polynomial ℂ) (s : ℝ) (p : Joint) (hr : HasDerivAt r v s) :
    HasDerivAt (fun t => limitFactor n k α β (r t) b P p) (limitSlope n k α β (r s) v b P p) s := by
  have hp := (P.hasDerivAt (N (r s) p)).scomp s (N_derivative r v s p hr)
  convert ((((E_derivative α β r v b s p hr).cexp.mul
    ((F_derivative r v s p hr).ofReal_comp.pow k)).mul ((Z_derivative α r v s p hr).pow n)).mul hp) using 1
  dsimp [limitFactor,limitSlope,B0,B1]
  ring

theorem factor_tendsto (n k : ℕ) (α β : ℝ) (r b : ℂ) (P : Polynomial ℂ) (p : Joint) :
    Tendsto (fun δ : ℝ => factor n k α β δ r b P p) (𝓝[>] 0)
      (𝓝 (limitFactor n k α β r b P p)) := by
  exact (((KFCausalClusteredWidthProfiles.quotient_tendsto (Z α r p)).pow n).const_mul
    (Complex.exp (E α β r b p)*(F r p:ℂ)^k)).mul_const (P.eval (N r p))

theorem slope_tendsto (n k : ℕ) (α β : ℝ) (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) :
    Tendsto (fun δ : ℝ => slope n k α β δ r v b P p) (𝓝[>] 0)
      (𝓝 (limitSlope n k α β r v b P p)) := by
  have hq := KFCausalClusteredWidthProfiles.quotient_tendsto (Z α r p)
  have he : Tendsto (fun δ : ℝ => Complex.exp (-(δ:ℂ)*Z α r p)) (𝓝[>] 0) (𝓝 (1:ℂ)) := by
    have hc : ContinuousAt (fun δ : ℝ => Complex.exp (-(δ:ℂ)*Z α r p)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [slope,limitSlope,mul_one] using
    (((hq.pow n).mul_const (B0 k α β r v b P p)).add
      (((hq.pow (n-1)).mul he).mul_const (B1 n k α r v P p))).const_mul (Complex.exp (E α β r b p))

#print axioms Z_derivative
#print axioms N_derivative
#print axioms F_derivative
#print axioms G_derivative
#print axioms E_derivative
#print axioms factor_derivative
#print axioms limitFactor_derivative
#print axioms factor_tendsto
#print axioms slope_tendsto
end
end UnifiedTheory.Audit.KFCausalClusteredClockFactors
