/- Exact weighted transverse-to-Wick normalization. All spectator Gaussian
coordinates are integrated with the original Jacobian; the coefficient
pi/4 times both charged widths is explicit. -/
import UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralCross
import UnifiedTheory.Audit.KFCausalGaussianWeightedSourceKernelDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
namespace UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralKernel
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalRelativeGaussianDifferential (position)
open KFCausalReciprocalGaussianCoordinates (exponent reconstruct)
open KFCausalReciprocalCrossGeometry (A B C)
open KFCausalComplexGaussianMoments (value gaussianValue)
open KFCausalCommonRealGaussianWeightedEnergy (potential)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalNeutralKernel (neutral swap integral_swap integral_head_product)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
variable (mass2 quartic vacuum : ℝ)
def density (α β w v : ℝ) (r : ℂ) (F G : ℂ → ℂ) (q : Transverse) : ℂ :=
  (potential mass2 quartic vacuum (pointField q):ℂ)*
    (conj (Complex.exp (exponent α β w r q))*Complex.exp (exponent α β v r q))*
    (conj (F (position r q 4))*G (position r q 4))
def kernel (α β w v : ℝ) (r : ℂ) (F G : ℂ → ℂ) : ℂ :=
  ∫ q, density mass2 quartic vacuum α β w v r F G q
def planeDensity (β : ℝ) (c r : ℂ) (F G : ℂ → ℂ) (u : Fin 2 → ℝ) : ℂ :=
  (potential mass2 quartic vacuum (u 1+fieldSlope r*u 0):ℂ)*
    Complex.exp (-c*(u 0:ℂ)^2-(2*(β:ℂ))*(u 1:ℂ)^2)*
    (conj (F (neutral r (u 0) (u 1)))*G (neutral r (u 0) (u 1)))
theorem density_factorization (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r : ℂ) (F G : ℂ → ℂ) (u : Transverse) :
    density mass2 quartic vacuum α β w v r F G (reconstruct 1 r (swap u)) =
      Complex.exp (-A α w v r*(u 0:ℂ)^2)*
        (Complex.exp (-B α w v r*(u 1:ℂ)^2)*
          (Complex.exp (-A α w v r*(u 2:ℂ)^2)*
            planeDensity mass2 quartic vacuum β (C α β w v r) r F G ![u 3,u 4])) := by
  rw [density,KFCausalReciprocalGaussianCoordinates.field_reconstruct,
    KFCausalReciprocalCrossGeometry.overlap_reconstruct α β w v hw hv,
    KFCausalReciprocalNeutralKernel.neutral_reconstruct,
    KFCausalReciprocalCrossGeometry.weight_exponential]
  simp only [one_mul]
  change (potential mass2 quartic vacuum (u 4+fieldSlope r*u 3):ℂ)*
      Complex.exp (-(A α w v r*(u 0:ℂ)^2+B α w v r*(u 1:ℂ)^2+
        C α β w v r*(u 3:ℂ)^2+A α w v r*(u 2:ℂ)^2+2*(β:ℂ)*(u 4:ℂ)^2))*
      (conj (F (neutral r (u 3) (u 4)))*G (neutral r (u 3) (u 4))) = _
  have he : -(A α w v r*(u 0:ℂ)^2+B α w v r*(u 1:ℂ)^2+
        C α β w v r*(u 3:ℂ)^2+A α w v r*(u 2:ℂ)^2+2*(β:ℂ)*(u 4:ℂ)^2) =
      -A α w v r*(u 0:ℂ)^2+(-B α w v r*(u 1:ℂ)^2+
        (-A α w v r*(u 2:ℂ)^2+(-C α β w v r*(u 3:ℂ)^2-2*(β:ℂ)*(u 4:ℂ)^2))) := by ring
  rw [he]
  simp only [Complex.exp_add]
  change _ = Complex.exp (-A α w v r*(u 0:ℂ)^2)*
    (Complex.exp (-B α w v r*(u 1:ℂ)^2)*
      (Complex.exp (-A α w v r*(u 2:ℂ)^2)*
        ((potential mass2 quartic vacuum (u 4+fieldSlope r*u 3):ℂ)*
          Complex.exp (-C α β w v r*(u 3:ℂ)^2-2*(β:ℂ)*(u 4:ℂ)^2)*
          (conj (F (neutral r (u 3) (u 4)))*G (neutral r (u 3) (u 4))))))
  ring

theorem kernel_plane_integral (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r : ℂ) (F G : ℂ → ℂ) :
    kernel mass2 quartic vacuum α β w v r F G =
      (1/4:ℂ)*value (A α w v r) 0^2*value (B α w v r) 0*
        ∫ u : Fin 2 → ℝ, planeDensity mass2 quartic vacuum β (C α β w v r) r F G u := by
  rw [kernel,KFCausalReciprocalCrossKernel.integral_coordinates r,integral_swap]
  simp_rw [density_factorization mass2 quartic vacuum α β w v hw hv]
  change (1/4:ℂ)*(∫ u : Fin (4+1) → ℝ,
    Complex.exp (-A α w v r*(u 0:ℂ)^2)*
    (fun z : Fin 4 → ℝ => Complex.exp (-B α w v r*(z 0:ℂ)^2)*
      (Complex.exp (-A α w v r*(z 1:ℂ)^2)*
        planeDensity mass2 quartic vacuum β (C α β w v r) r F G ![z 2,z 3])) (fun i => u i.succ)) = _
  rw [integral_head_product 4 (fun x => Complex.exp (-A α w v r*(x:ℂ)^2))
    (fun z => Complex.exp (-B α w v r*(z 0:ℂ)^2)*
      (Complex.exp (-A α w v r*(z 1:ℂ)^2)*
        planeDensity mass2 quartic vacuum β (C α β w v r) r F G ![z 2,z 3]))]
  change (1/4:ℂ)*((∫ x : ℝ, Complex.exp (-A α w v r*(x:ℂ)^2))*
    ∫ u : Fin (3+1) → ℝ, Complex.exp (-B α w v r*(u 0:ℂ)^2)*
      (fun z : Fin 3 → ℝ => Complex.exp (-A α w v r*(z 0:ℂ)^2)*
        planeDensity mass2 quartic vacuum β (C α β w v r) r F G ![z 1,z 2]) (fun i => u i.succ)) = _
  rw [integral_head_product 3 (fun x => Complex.exp (-B α w v r*(x:ℂ)^2))
    (fun z => Complex.exp (-A α w v r*(z 0:ℂ)^2)*
      planeDensity mass2 quartic vacuum β (C α β w v r) r F G ![z 1,z 2])]
  change (1/4:ℂ)*((∫ x : ℝ, Complex.exp (-A α w v r*(x:ℂ)^2))*
    ((∫ x : ℝ, Complex.exp (-B α w v r*(x:ℂ)^2))*
      ∫ u : Fin (2+1) → ℝ, Complex.exp (-A α w v r*(u 0:ℂ)^2)*
        (fun z : Fin 2 → ℝ => planeDensity mass2 quartic vacuum β (C α β w v r) r F G ![z 0,z 1]) (fun i => u i.succ))) = _
  rw [integral_head_product 2 (fun x => Complex.exp (-A α w v r*(x:ℂ)^2))
    (fun z => planeDensity mass2 quartic vacuum β (C α β w v r) r F G ![z 0,z 1])]
  have he : (fun z : Fin 2 → ℝ => planeDensity mass2 quartic vacuum β (C α β w v r) r F G ![z 0,z 1]) =
      planeDensity mass2 quartic vacuum β (C α β w v r) r F G := by
    funext z
    rw [show ![z 0,z 1] = z from by ext i; fin_cases i <;> rfl]
  rw [he]
  simp only [value,KFCausalComplexGaussianMoments.moment,pow_zero,one_mul]
  ring

theorem kernel_gaussian_marginal (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r : ℂ) (F G : ℂ → ℂ) (hA : 0 < (A α w v r).re) (hB : 0 < (B α w v r).re) :
    kernel mass2 quartic vacuum α β w v r F G =
      (1/4:ℂ)*gaussianValue (A α w v r)^2*gaussianValue (B α w v r)*
        ∫ u : Fin 2 → ℝ, planeDensity mass2 quartic vacuum β (C α β w v r) r F G u := by
  rw [kernel_plane_integral mass2 quartic vacuum α β w v hw hv,
    KFCausalComplexGaussianMoments.value_zero _ hA,
    KFCausalComplexGaussianMoments.value_zero _ hB]


theorem plane_identity (β : ℝ) (H r si sj : ℂ) (u : Fin 2 → ℝ) :
    planeDensity mass2 quartic vacuum β H r (exponentialProfile si 1 1) (exponentialProfile sj 1 1) u =
      KFCausalGaussianWeightedSourcePlaneKernel.density mass2 quartic vacuum H (2*(β:ℂ))
        (KFCausalGaussianSourceJointKernel.sourceV r si sj)
        (KFCausalGaussianSourceJointKernel.sourceX si sj) (fieldSlope r) u := by
  simp only [planeDensity,exponentialProfile,Polynomial.eval_one,mul_one,one_mul,
    ← Complex.exp_conj,map_mul,neutral,KFCausalGaussianSourceJointKernel.sourceV,
    KFCausalGaussianSourceJointKernel.sourceX,KFCausalGaussianWeightedSourcePlaneKernel.density]
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,map_ofNat,
    mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem kernel_pairKernel (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r si sj : ℂ) (hA : 0 < (A α w v r).re) (hB : 0 < (B α w v r).re)
    (hC : 0 < (C α β w v r).re) (hβ : 0 < β) :
    kernel mass2 quartic vacuum α β w v r (exponentialProfile si 1 1) (exponentialProfile sj 1 1)=
      ((Real.pi:ℂ)/4)*(w:ℂ)*(v:ℂ)*
        KFCausalGaussianWeightedSourceKernelDerivative.pairKernel mass2 quartic vacuum α β w v r si sj := by
  rw [kernel_gaussian_marginal mass2 quartic vacuum α β w v hw hv r _ _ hA hB,
    KFCausalReciprocalWedgeGeometry.broad_factor α w v hw hv]
  simp_rw [plane_identity]
  rw [KFCausalGaussianWeightedSourcePlaneKernel.density_integral _ _ _ _ _ _ _ hC
    (by simpa using (mul_pos (by norm_num : (0:ℝ)<2) hβ))]
  unfold KFCausalGaussianWeightedSourceKernelDerivative.pairKernel
    KFCausalGaussianWeightedSourceKernelDerivative.kernel
    KFCausalGaussianSourceKernelDerivative.prefactor KFCausalGaussianWeightedSourcePlaneKernel.formula
  ring

theorem density_decomposition (α β w v : ℝ) (r b d : ℂ) (P Q : Polynomial ℂ) (q : Transverse) :
    density mass2 quartic vacuum α β w v r (exponentialProfile b 1 P) (exponentialProfile d 1 Q) q =
      (vacuum:ℂ)*(conj (KFCausalReciprocalNeutralSliceIntegrability.factor α β w r b P 0 q)*
        KFCausalReciprocalNeutralSliceIntegrability.factor α β v r d Q 0 q)+
      (mass2:ℂ)*(conj (KFCausalReciprocalNeutralSliceIntegrability.factor α β w r b P 1 q)*
        KFCausalReciprocalNeutralSliceIntegrability.factor α β v r d Q 1 q)/2+
      (quartic:ℂ)*(conj (KFCausalReciprocalNeutralSliceIntegrability.factor α β w r b P 2 q)*
        KFCausalReciprocalNeutralSliceIntegrability.factor α β v r d Q 2 q)/4 := by
  simp only [density,potential,KFCausalReciprocalNeutralSliceIntegrability.factor,
    map_mul,map_pow,Complex.conj_ofReal,pow_zero,pow_one,one_mul]
  push_cast
  ring

theorem actual_kernel (ε y α β w v : ℝ) (b d : ℂ) (P Q : Polynomial ℂ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hw : 1 ≤ w) (hv : 1 ≤ v) (s : ℝ) :
    KFCausalWeightedReciprocalNeutralCross.actual mass2 quartic vacuum ε y α β w v b d P Q s=
      kernel mass2 quartic vacuum α β w v (KFCausalClockFloorRelativeShift.scale ε y s)
        (exponentialProfile b 1 P) (exponentialProfile d 1 Q) := by
  have hi (k : ℕ) := (KFCausalReciprocalNeutralCrossBounds.density_integrability
    ε y α β w v b d P Q hε hy hα hβ hwidth hw hv k s).1
  unfold kernel
  simp_rw [density_decomposition]
  change _ = ∫ q, (vacuum:ℂ)*KFCausalReciprocalNeutralCrossBounds.density ε y α β w v b d P Q 0 s q+
    (mass2:ℂ)*KFCausalReciprocalNeutralCrossBounds.density ε y α β w v b d P Q 1 s q/2+
    (quartic:ℂ)*KFCausalReciprocalNeutralCrossBounds.density ε y α β w v b d P Q 2 s q/4
  have h01 : Integrable (fun q => (vacuum:ℂ)*KFCausalReciprocalNeutralCrossBounds.density ε y α β w v b d P Q 0 s q+
    (mass2:ℂ)*KFCausalReciprocalNeutralCrossBounds.density ε y α β w v b d P Q 1 s q/2) :=
    ((hi 0).const_mul _).add (((hi 1).const_mul _).div_const _)
  rw [integral_add h01 (((hi 2).const_mul _).div_const _),
    integral_add ((hi 0).const_mul _) (((hi 1).const_mul _).div_const _)]
  simp only [integral_div,integral_const_mul]
  rfl

theorem actual_pairKernel (ε y α β w v : ℝ) (b d : ℂ)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hw : 1 ≤ w) (hv : 1 ≤ v) (s : ℝ) :
    KFCausalWeightedReciprocalNeutralCross.actual mass2 quartic vacuum ε y α β w v b d 1 1 s=
      ((Real.pi:ℂ)/4)*(w:ℂ)*(v:ℂ)*
        KFCausalGaussianWeightedSourceKernelDerivative.pairKernel mass2 quartic vacuum
          α β w v (KFCausalClockFloorRelativeShift.scale ε y s) b d := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  obtain ⟨hA,hB,hC,_⟩ := KFCausalReciprocalCrossGeometry.widths_positive α β w v _ hw hv ha hc hβ
  rw [actual_kernel mass2 quartic vacuum ε y α β w v b d 1 1 hε hy hα hβ hwidth hw hv s]
  exact kernel_pairKernel mass2 quartic vacuum α β w v (by linarith) (by linarith) _ b d hA hB hC hβ

#print axioms density_factorization
#print axioms kernel_plane_integral
#print axioms kernel_gaussian_marginal
#print axioms plane_identity
#print axioms kernel_pairKernel
#print axioms density_decomposition
#print axioms actual_kernel
#print axioms actual_pairKernel
end
end UnifiedTheory.Audit.KFCausalWeightedReciprocalNeutralKernel
