/- Actual charged dilation prefactors and their derivatives are controlled
polynomials. Combined with positive Gaussian/Laplace width floors, this
supplies full-space local domination for arbitrary finite degrees. -/
import UnifiedTheory.Audit.KFCausalCorrelatedDilationEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalCorrelatedDilationPolynomials
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalCorrelatedDilationEnvelope (scale geometry)
open KFCausalClusteredClockFactors (Z Zd N Nd E Ed)
open KFCausalJointCompactPolynomialBounds

def velocity (ell : ℝ) (r : ℂ) (t : ℝ) : ℂ := (ell:ℂ)*geometry ell r t
def field (ell : ℝ) (r : ℂ) (t : ℝ) (p : Joint) : ℝ :=
  p.1.2 1+scale ell t*KFCausalChargedPairCoordinates.fieldSlope r*p.1.2 0
def fieldVelocity (ell : ℝ) (r : ℂ) (t : ℝ) (p : Joint) : ℝ :=
  ell*scale ell t*KFCausalChargedPairCoordinates.fieldSlope r*p.1.2 0

def prefactor (n j : ℕ) (α ell : ℝ) (r : ℂ) (P : Polynomial ℂ) (t : ℝ) (p : Joint) : ℂ :=
  (field ell r t p:ℂ)^j*Z α (geometry ell r t) p^n*P.eval (N (geometry ell r t) p)

def prefactorSlope (n j : ℕ) (α β ell : ℝ) (r b : ℂ) (P : Polynomial ℂ) (t : ℝ) (p : Joint) : ℂ :=
  (j:ℂ)*(field ell r t p:ℂ)^(j-1)*(fieldVelocity ell r t p:ℂ)*
      Z α (geometry ell r t) p^n*P.eval (N (geometry ell r t) p)+
    (field ell r t p:ℂ)^j*((n:ℂ)*Z α (geometry ell r t) p^(n-1)*
      Zd α (geometry ell r t) (velocity ell r t) p*P.eval (N (geometry ell r t) p)+
      Z α (geometry ell r t) p^n*(P.derivative.eval (N (geometry ell r t) p)*Nd (velocity ell r t) p+
        Ed α β (geometry ell r t) (velocity ell r t) b p*P.eval (N (geometry ell r t) p)))

def packet (n j : ℕ) (α β ell : ℝ) (r b : ℂ) (P : Polynomial ℂ) (t : ℝ) (p : Joint) : ℂ :=
  Complex.exp (E α β (geometry ell r t) b p)*prefactor n j α ell r P t p

def packetSlope (n j : ℕ) (α β ell : ℝ) (r b : ℂ) (P : Polynomial ℂ) (t : ℝ) (p : Joint) : ℂ :=
  Complex.exp (E α β (geometry ell r t) b p)*prefactorSlope n j α β ell r b P t p

theorem geometry_derivative (ell : ℝ) (r : ℂ) (t : ℝ) :
    HasDerivAt (geometry ell r) (velocity ell r t) t := by
  convert (((hasDerivAt_id t).const_mul ell).exp.ofReal_comp.mul_const r) using 1
  simp only [velocity,geometry,scale,id_eq]
  push_cast
  ring

theorem field_derivative (ell : ℝ) (r : ℂ) (t : ℝ) (p : Joint) :
    HasDerivAt (fun s => field ell r s p) (fieldVelocity ell r t p) t := by
  convert (((((hasDerivAt_id t).const_mul ell).exp.mul_const
    (KFCausalChargedPairCoordinates.fieldSlope r)).mul_const (p.1.2 0)).const_add (p.1.2 1)) using 1
  simp only [fieldVelocity,scale,id_eq]
  ring

theorem packet_derivative (n j : ℕ) (α β ell : ℝ) (r b : ℂ) (P : Polynomial ℂ) (t : ℝ) (p : Joint) :
    HasDerivAt (fun s => packet n j α β ell r b P s p)
      (packetSlope n j α β ell r b P t p) t := by
  have hr := geometry_derivative ell r t
  have hz := KFCausalClusteredClockFactors.Z_derivative α (geometry ell r) (velocity ell r t) t p hr
  have hn := KFCausalClusteredClockFactors.N_derivative (geometry ell r) (velocity ell r t) t p hr
  have he := KFCausalClusteredClockFactors.E_derivative α β (geometry ell r) (velocity ell r t) b t p hr
  have hp := (P.hasDerivAt (N (geometry ell r t) p)).scomp t hn
  convert (((he.cexp.mul ((field_derivative ell r t p).ofReal_comp.pow j)).mul (hz.pow n)).mul hp) using 1
  · funext s
    dsimp only [packet,prefactor,Pi.mul_apply,Pi.pow_apply,Function.comp_apply]
    ring
  · dsimp only [packetSlope,prefactorSlope,Pi.mul_apply,Pi.pow_apply,Function.comp_apply]
    rw [smul_eq_mul]
    ring

theorem prefactors_controlled (n j : ℕ) (α β ell : ℝ) (r b : ℂ) (P : Polynomial ℂ) :
    Controlled (Set.Icc (-1:ℝ) 1) (prefactor n j α ell r P) ∧
    Controlled (Set.Icc (-1:ℝ) 1) (prefactorSlope n j α β ell r b P) := by
  let K := Set.Icc (-1:ℝ) 1
  have hr : Continuous (geometry ell r) := by unfold geometry scale; fun_prop
  have hv : Continuous (velocity ell r) := by unfold velocity; fun_prop
  have co (f : ℝ → ℂ) (hf : Continuous f) := controlled_coefficient K isCompact_Icc f hf.continuousOn
  have cx (i : Fin 4) := controlled_coordinate K i
  have hf : Controlled K (fun t p => (field ell r t p:ℂ)) := by
    simpa only [field,Complex.ofReal_add,Complex.ofReal_mul,coords,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one] using
      (cx 2).add ((co (fun t => ((scale ell t*KFCausalChargedPairCoordinates.fieldSlope r:ℝ):ℂ))
        (by unfold scale; fun_prop)).mul (cx 1))
  have hfd : Controlled K (fun t p => (fieldVelocity ell r t p:ℂ)) := by
    simpa only [fieldVelocity,Complex.ofReal_mul,coords,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one] using
      (co (fun t => ((ell*scale ell t*KFCausalChargedPairCoordinates.fieldSlope r:ℝ):ℂ))
        (by unfold scale; fun_prop)).mul (cx 1)
  have hz : Controlled K (fun t p => Z α (geometry ell r t) p) := by
    have h := (KFCausalClusteredClockCompactEnvelope.polynomials_controlled K isCompact_Icc 1 0 α β
      (geometry ell r) (velocity ell r) hr hv b (1:Polynomial ℂ)).1
    simpa only [KFCausalClusteredWidthDensityIntegrability.factorPolynomial_eval,
      pow_zero,pow_one,one_mul,mul_one,Polynomial.eval_one] using h
  have hzd : Controlled K (fun t p => Zd α (geometry ell r t) (velocity ell r t) p) := by
    have h := (KFCausalClusteredClockCompactEnvelope.polynomials_controlled K isCompact_Icc 1 0 α β
      (geometry ell r) (velocity ell r) hr hv b (1:Polynomial ℂ)).2.2
    simpa only [KFCausalClusteredClockEnvelope.slopePolynomial1_eval,KFCausalClusteredClockFactors.B1,
      Nat.cast_one,pow_zero,one_mul,mul_one,Polynomial.eval_one,Nat.sub_self] using h
  have hn : Controlled K (fun t p => N (geometry ell r t) p) := by
    simpa [N,KFCausalReciprocalNeutralKernel.neutral,coords] using
      (cx 2).add ((co (fun t => 2*((geometry ell r t).im:ℂ)*Complex.I)
        (by unfold geometry scale; fun_prop)).mul (cx 1))
  have hnd : Controlled K (fun t p => Nd (velocity ell r t) p) := by
    simpa [Nd,coords] using
      (co (fun t => 2*((velocity ell r t).im:ℂ)*Complex.I)
        (by unfold velocity geometry scale; fun_prop)).mul (cx 1)
  have he : Controlled K (fun t p => Ed α β (geometry ell r t) (velocity ell r t) b p) := by
    have h := (KFCausalClusteredClockCompactEnvelope.polynomials_controlled K isCompact_Icc 0 0 α β
      (geometry ell r) (velocity ell r) hr hv b (1:Polynomial ℂ)).2.1
    simpa only [KFCausalClusteredClockEnvelope.slopePolynomial0_eval,KFCausalClusteredClockFactors.B0,
      Nat.cast_zero,pow_zero,one_mul,mul_one,zero_mul,zero_add,Polynomial.eval_one,
      Polynomial.derivative_one,Polynomial.eval_zero] using h
  constructor
  · exact ((hf.pow j).mul (hz.pow n)).mul (hn.eval P)
  · have h0 := ((((controlled_const K (j:ℂ)).mul (hf.pow (j-1))).mul hfd).mul (hz.pow n)).mul (hn.eval P)
    have h1 := (((controlled_const K (n:ℂ)).mul (hz.pow (n-1))).mul hzd).mul (hn.eval P)
    have h2 := ((hn.eval P.derivative).mul hnd).add (he.mul (hn.eval P))
    exact h0.add ((hf.pow j).mul (h1.add ((hz.pow n).mul h2)))

theorem packet_pair_envelope (n j : ℕ) (α β ell : ℝ) (r b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ t ∈ Set.Icc (-1:ℝ) 1, ∀ p, 0 ≤ p.2 →
        ‖packet n j α β ell r b P t p‖^2+‖packetSlope n j α β ell r b P t p‖^2 ≤ D p := by
  have h := prefactors_controlled n j α β ell r b P
  obtain ⟨A,hAi,hA0,hAf⟩ := KFCausalCorrelatedDilationEnvelope.prefactor_envelope
    α β ell r b hβ hA hC _ h.1
  obtain ⟨B,hBi,hB0,hBg⟩ := KFCausalCorrelatedDilationEnvelope.prefactor_envelope
    α β ell r b hβ hA hC _ h.2
  exact ⟨fun p => A p+B p,hAi.add hBi,fun p => add_nonneg (hA0 p) (hB0 p),
    fun t ht p hp => add_le_add (hAf t ht p hp) (hBg t ht p hp)⟩

#print axioms geometry_derivative
#print axioms field_derivative
#print axioms packet_derivative
#print axioms prefactors_controlled
#print axioms packet_pair_envelope
end
end UnifiedTheory.Audit.KFCausalCorrelatedDilationPolynomials
