/- Exact bilinear Hessian transport for the physical complex shear.
The inverse metric cancels the full charged/neutral differential; no
Hermitian replacement or omitted neutral cross derivative is used. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialIntegralCompletion

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMetricLaplacian
noncomputable section
open KFCausalIndependentRadialPhysicalPolynomial (Poly physicalPoint packet)
open KFCausalIndependentRadialTransverseRegularity (RealSpace realPoint)
open KFCausalIndependentRadialTransverseIBP (direction exponent step family)
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalPhysicalClockMetric (metric shiftedClock)
open KFCausalPhysicalClockMetricCoefficients (coefficient basis)
open KFCausalPhysicalComplexShearMetric (gram transposeFlow)
open KFCausalPairedModeCoordinates (scale)

def coordinateVector (i : Fin 5) : Fin 5→ℂ := Pi.single i 1
def jet (E : Poly) (v : Fin 5→ℂ) (Q : Poly) : Poly :=
  direction v Q+Q*direction v E

private theorem direction_basis (i : Fin 5) (Q : Poly) :
    direction (coordinateVector i) Q=MvPolynomial.pderiv i Q := by
  unfold direction
  rw [Finset.sum_eq_single i]
  · simp [coordinateVector]
  · intro j _ hj
    simp [coordinateVector,hj]
  · simp

private theorem jet_add (E P Q : Poly) (v : Fin 5→ℂ) :
    jet E v (P+Q)=jet E v P+jet E v Q := by
  simp only [jet,direction,map_add,mul_add,add_mul,Finset.sum_add_distrib]
  ring

private theorem jet_C_mul (E Q : Poly) (v : Fin 5→ℂ) (c : ℂ) :
    jet E v (MvPolynomial.C c*Q)=MvPolynomial.C c*jet E v Q := by
  simp only [jet,direction,MvPolynomial.pderiv_C_mul,mul_add,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intros
    ring
  · ring

private theorem jet_sum {ι : Type*} (s : Finset ι) (E : Poly) (v : Fin 5→ℂ) (Q : ι→Poly) :
    jet E v (∑i∈s,Q i)=∑i∈s,jet E v (Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jet,direction]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,jet_add,ih]

private theorem jet_expand (E Q : Poly) (v : Fin 5→ℂ) :
    jet E v Q=∑i,MvPolynomial.C (v i)*jet E (coordinateVector i) Q := by
  simp only [jet,direction_basis]
  simp only [direction,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intros
  ring

private theorem second_expand (E Q : Poly) (u v : Fin 5→ℂ) :
    jet E u (jet E v Q)=∑ab:Fin 5×Fin 5,
      MvPolynomial.C (u ab.1*v ab.2)*jet E (coordinateVector ab.1) (jet E (coordinateVector ab.2) Q) := by
  rw [jet_expand E Q v,jet_sum]
  simp only [jet_C_mul]
  simp_rw [jet_expand E (jet E (coordinateVector _) Q) u]
  simp only [Finset.mul_sum,←mul_assoc,←map_mul,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm (v j) (u i)]

theorem metric_chain (ε s : ℝ) (δ : ℂ) (a b : Fin 5) :
    (∑ij:Fin 5×Fin 5,coefficient ε s δ ij.1 ij.2*
      flow (2*scale) δ (basis ij.1) a*flow (2*scale) δ (basis ij.2) b)=
      (shiftedClock ε s δ)⁻¹*(if a=b then 1 else 0) := by
  have he : Complex.exp (-δ/2)=(Complex.exp (δ/2))⁻¹ := by
    rw [show -δ/2=-(δ/2) by ring,Complex.exp_neg]
  fin_cases a <;> fin_cases b <;>
    simp [Fintype.sum_prod_type,Fin.sum_univ_succ,coefficient,metric,gram,transposeFlow,
      flow,basis,he,neg_neg] <;>
    field_simp [Complex.exp_ne_zero (δ/2)] <;> ring

theorem contracted_jet (ε s : ℝ) (δ : ℂ) (E Q : Poly) :
    (∑ij:Fin 5×Fin 5,MvPolynomial.C (coefficient ε s δ ij.1 ij.2)*
      jet E (fun a=>flow (2*scale) δ (basis ij.1) a)
        (jet E (fun a=>flow (2*scale) δ (basis ij.2) a) Q))=
      MvPolynomial.C ((shiftedClock ε s δ)⁻¹)*
        ∑a:Fin 5,jet E (coordinateVector a) (jet E (coordinateVector a) Q) := by
  conv_lhs =>
    arg 2
    ext ij
    rw [second_expand]
  simp only [Finset.mul_sum,←mul_assoc,←map_mul]
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul,←map_sum]
  simp_rw [metric_chain]
  simp only [Fintype.sum_prod_type]
  simp [apply_ite]

def entirePacket (α wL wR : ℝ) (b : ℂ) (Q : Poly) (y : Space) : ℂ :=
  MvPolynomial.eval (fun i=>y i) Q*Complex.exp (MvPolynomial.eval (fun i=>y i) (exponent α wL wR b))

theorem entirePacket_derivative (α wL wR : ℝ) (b : ℂ) (Q : Poly) (y : Space) (v : Fin 5→ℂ) :
    HasDerivAt (fun t:ℂ=>entirePacket α wL wR b Q (y+t • WithLp.toLp 2 v))
      (entirePacket α wL wR b (jet (exponent α wL wR b) v Q) y) 0 := by
  have hq := KFCausalIndependentRadialTransverseIBP.direction_derivative Q (fun i=>y i) v
  have he := (KFCausalIndependentRadialTransverseIBP.direction_derivative
    (exponent α wL wR b) (fun i=>y i) v).cexp
  convert hq.mul he using 1
  simp only [entirePacket,jet,map_add,map_mul,zero_mul,add_zero]
  ring

private theorem entirePacket_profile (α wL wR : ℝ) (b : ℂ) (P : Polynomial ℂ) (y : Space) :
    entirePacket α wL wR b (KFCausalIndependentRadialPhysicalPolynomial.neutralPolynomial P) y=
      KFCausalIndependentRadialEntireLaplacian.profile (α/wL:ℝ) (α*wR:ℝ) (α/32) b P y := by
  unfold entirePacket
  rw [KFCausalIndependentRadialPhysicalPolynomial.neutralPolynomial_eval,
    KFCausalIndependentRadialTransverseIBP.exponent_eval]
  simp only [KFCausalIndependentRadialEntireLaplacian.profile,KFCausalNeutralLinePackets.entire,
    KFCausalIndependentRadialTransverseLines.totalQuadratic,neg_add,Complex.exp_add]
  ring

theorem neutral_first (α wL wR : ℝ) (b : ℂ) (P : Polynomial ℂ) (i : Fin 5) (y : Space) :
    entirePacket α wL wR b (jet (exponent α wL wR b) (coordinateVector i)
      (KFCausalIndependentRadialPhysicalPolynomial.neutralPolynomial P)) y=
      KFCausalIndependentRadialEntireLaplacian.first (α/wL:ℝ) (α*wR:ℝ) (α/32) b P i y := by
  have h1 := entirePacket_derivative α wL wR b
    (KFCausalIndependentRadialPhysicalPolynomial.neutralPolynomial P) y (coordinateVector i)
  simp_rw [entirePacket_profile] at h1
  exact h1.unique (KFCausalIndependentRadialEntireLaplacian.profile_first_derivative
    (α/wL:ℝ) (α*wR:ℝ) (α/32) b P i y)

theorem neutral_second (α wL wR : ℝ) (b : ℂ) (P : Polynomial ℂ) (i : Fin 5) (y : Space) :
    entirePacket α wL wR b (jet (exponent α wL wR b) (coordinateVector i)
      (jet (exponent α wL wR b) (coordinateVector i)
        (KFCausalIndependentRadialPhysicalPolynomial.neutralPolynomial P))) y=
      KFCausalIndependentRadialEntireLaplacian.second (α/wL:ℝ) (α*wR:ℝ) (α/32) b P i y := by
  have h1 := entirePacket_derivative α wL wR b
    (jet (exponent α wL wR b) (coordinateVector i)
      (KFCausalIndependentRadialPhysicalPolynomial.neutralPolynomial P)) y (coordinateVector i)
  simp_rw [neutral_first] at h1
  exact h1.unique (KFCausalIndependentRadialEntireLaplacian.profile_second_derivative
    (α/wL:ℝ) (α*wR:ℝ) (α/32) b P i y)

private theorem packet_entire (α wL wR : ℝ) (δ b : ℂ) (Q : Poly) (x : RealSpace) :
    packet α wL wR δ b Q x=entirePacket α wL wR b Q (physicalPoint δ x) := by
  simp only [packet,entirePacket,KFCausalIndependentRadialTransverseIBP.exponent_eval]

private theorem step_jet (α wL wR : ℝ) (δ b : ℂ) (Q : Poly) (i : Fin 5) :
    step α wL wR δ b (KFCausalIndependentRadialWeightedContraction.basis i) Q=
      jet (exponent α wL wR b) (fun a=>flow (2*scale) δ (basis i) a) Q := by
  have he : physicalPoint δ (KFCausalIndependentRadialWeightedContraction.basis i)=
      flow (2*scale) δ (basis i) := by
    unfold physicalPoint
    congr 1
    ext j
    simp [KFCausalIndependentRadialWeightedContraction.basis,realPoint,basis,Pi.single_apply,apply_ite]
  simp only [step,jet,he]

theorem packet_laplacian (ε s α wL wR : ℝ) (δ b : ℂ) (Q : Poly) (x : RealSpace) :
    (∑ij:Fin 5×Fin 5,coefficient ε s δ ij.1 ij.2*
      packet α wL wR δ b
        (step α wL wR δ b (KFCausalIndependentRadialWeightedContraction.basis ij.1)
          (step α wL wR δ b (KFCausalIndependentRadialWeightedContraction.basis ij.2) Q)) x)=
      (shiftedClock ε s δ)⁻¹*∑i:Fin 5,entirePacket α wL wR b
        (jet (exponent α wL wR b) (coordinateVector i)
          (jet (exponent α wL wR b) (coordinateVector i) Q)) (physicalPoint δ x) := by
  have he := congrArg (MvPolynomial.eval (fun i=>physicalPoint δ x i))
    (contracted_jet ε s δ (exponent α wL wR b) Q)
  have hh := congrArg (fun z:ℂ=>z*Complex.exp
    (MvPolynomial.eval (fun i=>physicalPoint δ x i) (exponent α wL wR b))) he
  simpa only [step_jet,packet_entire,entirePacket,map_sum,map_mul,MvPolynomial.eval_C,
    Finset.sum_mul,Finset.mul_sum,mul_assoc] using hh

theorem family_neutral_laplacian (n : ℕ) (ε s α : ℝ) (wL wR : Fin n→ℝ)
    (δ : ℂ) (b C : Fin n→ℂ) (P : Fin n→Polynomial ℂ) (x : RealSpace) :
    KFCausalIndependentRadialWeightedContraction.laplacian n α wL wR δ b C
      (fun j=>KFCausalIndependentRadialPhysicalPolynomial.neutralPolynomial (P j))
      (coefficient ε s δ) x=
    (shiftedClock ε s δ)⁻¹*∑j:Fin n,C j*∑i:Fin 5,
      KFCausalIndependentRadialEntireLaplacian.second (α/wL j:ℝ) (α*wR j:ℝ)
        (α/32) (b j) (P j) i (physicalPoint δ x) := by
  simp only [KFCausalIndependentRadialWeightedContraction.laplacian,family,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he := packet_laplacian ε s α (wL j) (wR j) δ (b j)
    (KFCausalIndependentRadialPhysicalPolynomial.neutralPolynomial (P j)) x
  simp_rw [neutral_second] at he
  have hh := congrArg (fun z:ℂ=>C j*z) he
  simpa only [KFCausalIndependentRadialWeightedContraction.secondPolynomial,
    KFCausalIndependentRadialWeightedContraction.firstPolynomial,
    KFCausalIndependentRadialTransverseIBP.familyStep,Finset.mul_sum,mul_left_comm,mul_assoc] using hh

#print axioms metric_chain
#print axioms contracted_jet
#print axioms entirePacket_derivative
#print axioms neutral_first
#print axioms neutral_second
#print axioms packet_laplacian
#print axioms family_neutral_laplacian
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMetricLaplacian
