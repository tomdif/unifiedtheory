/- Actual kinetic and potential outputs on the complete charged circular basis. -/
import UnifiedTheory.Audit.KFCausalFourCircularOscillatorDomain
import UnifiedTheory.Audit.KFCausalPlaneKineticFourier
import UnifiedTheory.Audit.KFCausalJoinedMultiplierSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFourCircularKineticPotential
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (Block BlockHilbert)
open KFCausalHermiteProductBasis (Index)
open KFCausalJoinedMultiplierSum (joinProduct)
open KFCausalCircularOscillatorBasis (normalizedPolynomial normalized_state)
open KFCausalPlaneKineticFourier

variable (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b)
local notation "J" => KFCausalPlanePolynomialGaussian.state (b*c^2) b
  (KFCausalScaledCircularPolynomials.width_positive c b hc hb) hb
local notation "B₂" => KFCausalFourCircularChargeBasis.planeBasis c hc b hb
local notation "B₄" => KFCausalFourCircularChargeBasis.basis c hc b hb

def planeKinetic (i : ℕ × ℕ) : BlockHilbert 2 :=
  J (kinetic c b (normalizedPolynomial c hc b hb (Nat.pair i.1 i.2)))
def planePotential (i : ℕ × ℕ) : BlockHilbert 2 :=
  J (potential c b (normalizedPolynomial c hc b hb (Nat.pair i.1 i.2)))

theorem plane_sum (i : ℕ × ℕ) : planeKinetic c hc b hb i+planePotential c hc b hb i =
    (KFCausalCircularOscillatorTriangular.energy c b (Nat.pair i.1 i.2):ℂ) • B₂ i := by
  rw [KFCausalFourCircularChargeBasis.planeBasis_apply]
  simpa only [oscillator_split, map_add, planeKinetic, planePotential] using
    KFCausalCircularOscillatorBasis.basis_oscillator c hc b hb (Nat.pair i.1 i.2)

def kinetic4 (i : Index) : BlockHilbert 4 :=
  joinProduct 2 2 (planeKinetic c hc b hb i.1) (B₂ i.2)+
    joinProduct 2 2 (B₂ i.1) (planeKinetic c hc b hb i.2)
def potential4 (i : Index) : BlockHilbert 4 :=
  joinProduct 2 2 (planePotential c hc b hb i.1) (B₂ i.2)+
    joinProduct 2 2 (B₂ i.1) (planePotential c hc b hb i.2)

theorem basis_join (i : Index) : B₄ i = joinProduct 2 2 (B₂ i.1) (B₂ i.2) := by
  simp only [KFCausalFourCircularChargeBasis.basis, KFCausalHermiteProductBasis.mapBasis_apply,
    KFCausalProductHilbertExpansion.productBasis_apply, joinProduct]

theorem sum (i : Index) : kinetic4 c hc b hb i+potential4 c hc b hb i =
    (KFCausalFourCircularOscillatorDomain.energy4 c b i:ℂ) • B₄ i := by
  rw [basis_join]
  unfold kinetic4 potential4 joinProduct
  have he := congrArg (fun z : BlockHilbert 2 =>
    KFCausalHermiteProductBasis.joinCoordinates 2 2
      (KFCausalL2TensorEmbedding.productState volume volume z (B₂ i.2))) (plane_sum c hc b hb i.1)
  have hf := congrArg (fun z : BlockHilbert 2 =>
    KFCausalHermiteProductBasis.joinCoordinates 2 2
      (KFCausalL2TensorEmbedding.productState volume volume (B₂ i.1) z)) (plane_sum c hc b hb i.2)
  simp only [KFCausalL2TensorEmbedding.productState_add_left,
    KFCausalL2TensorEmbedding.productState_add_right,
    KFCausalL2TensorEmbedding.productState_smul_left,
    KFCausalL2TensorEmbedding.productState_smul_right, map_add, map_smul] at he hf
  rw [KFCausalFourCircularOscillatorDomain.energy4, Complex.ofReal_add, add_smul,
    ← he, ← hf]
  abel

theorem kinetic_fourier4 (i : Index) :
    (Lp.fourierTransformₗᵢ (Block 4) ℂ) (kinetic4 c hc b hb i) =ᵐ[volume] fun x =>
      (4*(Real.pi:ℂ)^2*((x 0:ℂ)^2+(c:ℂ)^2*(x 1:ℂ)^2+
        (x 2:ℂ)^2+(c:ℂ)^2*(x 3:ℂ)^2))*
        ((Lp.fourierTransformₗᵢ (Block 4) ℂ) (B₄ i)) x := by
  have hp (j : ℕ × ℕ) := kinetic_fourier c hc b hb
    (normalizedPolynomial c hc b hb (Nat.pair j.1 j.2))
  simp only [normalized_state, ← KFCausalFourCircularChargeBasis.planeBasis_apply] at hp
  have he := KFCausalJoinedMultiplierSum.sum_coe 2 2
    ((Lp.fourierTransformₗᵢ (Block 2) ℂ) (B₂ i.1))
    ((Lp.fourierTransformₗᵢ (Block 2) ℂ) (planeKinetic c hc b hb i.1))
    ((Lp.fourierTransformₗᵢ (Block 2) ℂ) (B₂ i.2))
    ((Lp.fourierTransformₗᵢ (Block 2) ℂ) (planeKinetic c hc b hb i.2))
    _ _ (hp i.1) (hp i.2)
  simp only [kinetic4, map_add, basis_join, KFCausalJoinedMultiplierSum.fourier 2 2]
  filter_upwards [he] with x hx
  rw [hx]
  have hsep : KFCausalJoinedFourierProduct.separate 2 2 x =
      (WithLp.toLp 2 ![x 0,x 1],WithLp.toLp 2 ![x 2,x 3]) := by
    apply Prod.ext <;> ext j <;> fin_cases j <;> rfl
  rw [hsep]
  simp only [WithLp.toLp_ofLp, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem potential_coe4 (i : Index) : potential4 c hc b hb i =ᵐ[volume] fun x =>
    (4*(b:ℂ)^2*(c:ℂ)^4*((x 0:ℂ)^2+(x 2:ℂ)^2)+
      4*(b:ℂ)^2*(c:ℂ)^2*((x 1:ℂ)^2+(x 3:ℂ)^2))*(B₄ i) x := by
  have hp (j : ℕ × ℕ) := potential_coe c hc b hb
    (normalizedPolynomial c hc b hb (Nat.pair j.1 j.2))
  simp only [normalized_state, ← KFCausalFourCircularChargeBasis.planeBasis_apply] at hp
  have he := KFCausalJoinedMultiplierSum.sum_coe 2 2
    (B₂ i.1) (planePotential c hc b hb i.1)
    (B₂ i.2) (planePotential c hc b hb i.2) _ _ (hp i.1) (hp i.2)
  simp only [potential4, basis_join]
  filter_upwards [he] with x hx
  rw [hx]
  have hsep : KFCausalJoinedFourierProduct.separate 2 2 x =
      (WithLp.toLp 2 ![x 0,x 1],WithLp.toLp 2 ![x 2,x 3]) := by
    apply Prod.ext <;> ext j <;> fin_cases j <;> rfl
  rw [hsep]
  simp only [WithLp.toLp_ofLp, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

#print axioms sum
#print axioms kinetic_fourier4
#print axioms potential_coe4
end
end UnifiedTheory.Audit.KFCausalFourCircularKineticPotential
