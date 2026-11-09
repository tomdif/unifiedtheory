/- Entire transverse derivatives of the sourced independent-radial packet.
The five coordinate derivatives retain the actual neutral polynomial step;
complex shear pullback uses the inverse bilinear differential, not an adjoint. -/
import UnifiedTheory.Audit.KFCausalComplexShearGroup
import UnifiedTheory.Audit.KFCausalNeutralLinePackets

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialEntireLaplacian
noncomputable section
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalComplexShearGroup (flow_compose flow_zero)
open KFCausalNeutralLinePackets (entire step entire_derivative)

def radiusLeft (x : Space) : ℂ := x 0^2+x 2^2
def radiusRight (x : Space) : ℂ := x 1^2+x 3^2
def quadratic (A B : ℂ) (x : Space) : ℂ := A*radiusLeft x+B*radiusRight x
def rate (A B : ℂ) : Fin 5→ℂ := ![A,B,A,B,0]
def neutral (i : Fin 5) : ℂ := if i=4 then 1 else 0
def basis (i : Fin 5) : Space := WithLp.toLp 2 (Pi.single i 1)
def line (x : Space) (i : Fin 5) (t : ℂ) : Space := x+t • basis i

def profile (A B : ℂ) (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (x : Space) : ℂ :=
  Complex.exp (-quadratic A B x)*entire β b P (x 4)

def first (A B : ℂ) (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (i : Fin 5) (x : Space) : ℂ :=
  (-2*rate A B i*x i)*profile A B β b P x+neutral i*profile A B β b (step β b P) x

def second (A B : ℂ) (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (i : Fin 5) (x : Space) : ℂ :=
  (-2*rate A B i+4*(rate A B i)^2*(x i)^2)*profile A B β b P x-
    4*rate A B i*x i*neutral i*profile A B β b (step β b P) x+
    (neutral i)^2*profile A B β b (step β b (step β b P)) x

private theorem line_apply (x : Space) (i j : Fin 5) (t : ℂ) :
    line x i t j=x j+if j=i then t else 0 := by
  by_cases h : j=i
  · subst j
    simp [line,basis]
  · simp [line,basis,h]

private theorem quadratic_line (A B : ℂ) (x : Space) (i : Fin 5) (t : ℂ) :
    quadratic A B (line x i t)=quadratic A B x+rate A B i*(2*x i*t+t^2) := by
  fin_cases i <;> simp [quadratic,radiusLeft,radiusRight,rate,line_apply] <;> ring

private theorem neutral_line (x : Space) (i : Fin 5) (t : ℂ) :
    line x i t 4=x 4+neutral i*t := by
  fin_cases i <;> simp [line_apply,neutral]

theorem profile_first_derivative (A B : ℂ) (β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (i : Fin 5) (x : Space) :
    HasDerivAt (fun t : ℂ => profile A B β b P (line x i t)) (first A B β b P i x) 0 := by
  have hq : HasDerivAt (fun t : ℂ => quadratic A B (line x i t)) (2*rate A B i*x i) 0 := by
    simp only [quadratic_line]
    convert ((((hasDerivAt_id (0:ℂ)).const_mul (2*x i)).add
      ((hasDerivAt_id (0:ℂ)).pow 2)).const_mul (rate A B i)).const_add
        (quadratic A B x) using 1
    simp
    ring
  have hn : HasDerivAt (fun t : ℂ => entire β b P (line x i t 4))
      (entire β b (step β b P) (x 4)*neutral i) 0 := by
    simp only [neutral_line]
    convert (entire_derivative β b P (x 4+neutral i*0)).comp 0
      (((hasDerivAt_id (0:ℂ)).const_mul (neutral i)).const_add (x 4)) using 1
    simp
  have he := hq.neg.cexp.mul hn
  convert he using 1
  simp only [first,profile,line,zero_smul,add_zero,Pi.neg_apply]
  ring

theorem profile_second_derivative (A B : ℂ) (β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (i : Fin 5) (x : Space) :
    HasDerivAt (fun t : ℂ => first A B β b P i (line x i t)) (second A B β b P i x) 0 := by
  have hx : HasDerivAt (fun t : ℂ => line x i t i) 1 0 := by
    simp only [line_apply,ite_true]
    exact (hasDerivAt_id (0:ℂ)).const_add (x i)
  have he := ((hx.const_mul (-2*rate A B i)).mul
    (profile_first_derivative A B β b P i x)).add
    ((profile_first_derivative A B β b (step β b P) i x).const_mul (neutral i))
  convert he using 1
  simp only [first,second,line,zero_smul,add_zero]
  ring

theorem laplacian_sum (A B : ℂ) (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (x : Space) :
    (∑ i : Fin 5,second A B β b P i x)=
      (-4*(A+B)+4*A^2*radiusLeft x+4*B^2*radiusRight x)*profile A B β b P x+
        profile A B β b (step β b (step β b P)) x := by
  simp [Fin.sum_univ_succ,second,rate,neutral,radiusLeft,radiusRight]
  ring

theorem flow_inverse_line (σ : ℝ) (z : ℂ) (x : Space) (i : Fin 5) (t : ℂ) :
    flow σ z (x+t • flow σ (-z) (basis i))=line (flow σ z x) i t := by
  have hl : flow σ z (x+t • flow σ (-z) (basis i))=
      flow σ z x+t • flow σ z (flow σ (-z) (basis i)) := by
    ext j
    fin_cases j <;> simp [flow] <;> ring
  rw [hl,flow_compose,add_neg_cancel,flow_zero]
  rfl

theorem pulled_first_derivative (A B : ℂ) (β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (σ : ℝ) (z : ℂ) (i : Fin 5) (x : Space) :
    HasDerivAt (fun t : ℂ => profile A B β b P
      (flow σ z (x+t • flow σ (-z) (basis i))))
      (first A B β b P i (flow σ z x)) 0 := by
  simp only [flow_inverse_line]
  exact profile_first_derivative A B β b P i (flow σ z x)

theorem pulled_second_derivative (A B : ℂ) (β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (σ : ℝ) (z : ℂ) (i : Fin 5) (x : Space) :
    HasDerivAt (fun t : ℂ => first A B β b P i
      (flow σ z (x+t • flow σ (-z) (basis i))))
      (second A B β b P i (flow σ z x)) 0 := by
  simp only [flow_inverse_line]
  exact profile_second_derivative A B β b P i (flow σ z x)

#print axioms profile_first_derivative
#print axioms profile_second_derivative
#print axioms laplacian_sum
#print axioms flow_inverse_line
#print axioms pulled_first_derivative
#print axioms pulled_second_derivative
end
end UnifiedTheory.Audit.KFCausalIndependentRadialEntireLaplacian
