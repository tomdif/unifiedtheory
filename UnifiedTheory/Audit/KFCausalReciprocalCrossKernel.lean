/- Exact off-diagonal potential kernel for reciprocal Gaussian packets.
A single real coordinate change is used for both widths; all complex
phases survive. Positivity of the real Gaussian widths proves absolute
integrability before any integral or finite-sum manipulation. -/
import UnifiedTheory.Audit.KFCausalReciprocalCrossGeometry
import UnifiedTheory.Audit.KFCausalReciprocalGaussianKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalCrossKernel
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalGaussianCoordinates (exponent reconstruct coordinates coordinateEquiv area)
open KFCausalReciprocalCrossGeometry (A B C)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalQuarticPlaneDomination (potential)
open KFCausalMatterOrderedDomain (pointField)
open scoped ComplexConjugate

def density (α β w v : ℝ) (r : ℂ) (q : Transverse) : ℂ :=
  (potential (pointField q):ℂ)*
    (conj (Complex.exp (exponent α β w r q))*Complex.exp (exponent α β v r q))
def kernel (α β w v : ℝ) (r : ℂ) : ℂ := ∫ q, density α β w v r q

def formula (α β w v : ℝ) (r : ℂ) : ℂ :=
  (1/4:ℂ)*KFCausalComplexPotentialGaussian.formula
    (A α w v r) (B α w v r) (C α β w v r) (2*(β:ℂ)) (fieldSlope r)

theorem integral_coordinates (r : ℂ) (f : Transverse → ℂ) :
    ∫ q, f q = (1/4:ℂ)*∫ u, f (reconstruct 1 r u) := by
  have hm := (coordinateEquiv 1 one_ne_zero r).toContinuousLinearEquiv.toHomeomorph
    |>.measurableEmbedding.integral_map (μ := volume) (fun u => f (reconstruct 1 r u))
  have hfun : ((coordinateEquiv 1 one_ne_zero r).toContinuousLinearEquiv.toHomeomorph :
      Transverse → Transverse) = coordinates 1 r :=
    funext (KFCausalReciprocalGaussianCoordinates.coordinateMap_apply 1 r)
  rw [hfun,KFCausalReciprocalGaussianCoordinates.coordinates_volume 1 one_ne_zero,
    integral_smul_measure] at hm
  simpa only [KFCausalReciprocalGaussianCoordinates.reconstruct_coordinates 1 one_ne_zero,
    ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1/4:ℝ)),Complex.real_smul,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hm.symm

theorem integrable_coordinates (r : ℂ) (f : Transverse → ℂ) :
    Integrable f ↔ Integrable (fun u => f (reconstruct 1 r u)) := by
  have hm := (coordinateEquiv 1 one_ne_zero r).toContinuousLinearEquiv.toHomeomorph
    |>.measurableEmbedding.integrable_map_iff (μ := volume) (g := fun u => f (reconstruct 1 r u))
  have hfun : ((coordinateEquiv 1 one_ne_zero r).toContinuousLinearEquiv.toHomeomorph :
      Transverse → Transverse) = coordinates 1 r :=
    funext (KFCausalReciprocalGaussianCoordinates.coordinateMap_apply 1 r)
  rw [hfun,KFCausalReciprocalGaussianCoordinates.coordinates_volume 1 one_ne_zero,
    integrable_smul_measure (by norm_num) (by finiteness)] at hm
  simpa only [Function.comp_def,
    KFCausalReciprocalGaussianCoordinates.reconstruct_coordinates 1 one_ne_zero] using hm.symm

theorem density_reconstruct (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r : ℂ) (u : Transverse) :
    density α β w v r (reconstruct 1 r u) =
      KFCausalComplexPotentialGaussian.density
        (A α w v r) (B α w v r) (C α β w v r) (2*(β:ℂ)) (fieldSlope r) u := by
  rw [density,KFCausalReciprocalGaussianCoordinates.field_reconstruct,
    KFCausalReciprocalCrossGeometry.overlap_reconstruct α β w v hw hv]
  simp only [one_mul,KFCausalComplexPotentialGaussian.density]

theorem density_integrable (α β w v : ℝ) (r : ℂ) (hw : 1 ≤ w) (hv : 1 ≤ v)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    Integrable (density α β w v r) := by
  rw [integrable_coordinates r]
  simp_rw [density_reconstruct α β w v (by linarith) (by linarith)]
  obtain ⟨ha,hb,hc,hd⟩ := KFCausalReciprocalCrossGeometry.widths_positive α β w v r hw hv hA hC hβ
  exact KFCausalComplexPotentialGaussian.density_integrable _ _ _ _ ha hb hc hd _

theorem kernel_formula (α β w v : ℝ) (r : ℂ) (hw : 1 ≤ w) (hv : 1 ≤ v)
    (hA : 0 < α*area r) (hC : 0 < α*area r-8*β*r.im^2) (hβ : 0 < β) :
    kernel α β w v r = formula α β w v r := by
  rw [kernel,integral_coordinates r]
  simp_rw [density_reconstruct α β w v (by linarith) (by linarith)]
  obtain ⟨ha,hb,hc,hd⟩ := KFCausalReciprocalCrossGeometry.widths_positive α β w v r hw hv hA hC hβ
  rw [KFCausalComplexPotentialGaussian.density_integral _ _ _ _ ha hb hc hd]
  rfl

theorem actual_integrable (α β ε y s w v : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hw : 1 ≤ w) (hv : 1 ≤ v) :
    Integrable (density α β w v (KFCausalClockFloorRelativeShift.scale ε y s)) := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  exact density_integrable α β w v _ hw hv ha hc hβ

theorem actual_formula (α β ε y s w v : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hwidth : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hw : 1 ≤ w) (hv : 1 ≤ v) :
    kernel α β w v (KFCausalClockFloorRelativeShift.scale ε y s) =
      formula α β w v (KFCausalClockFloorRelativeShift.scale ε y s) := by
  have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y s hα hβ.le hwidth hε hy
  obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
  exact kernel_formula α β w v _ hw hv ha hc hβ

#print axioms integral_coordinates
#print axioms integrable_coordinates
#print axioms density_reconstruct
#print axioms density_integrable
#print axioms kernel_formula
#print axioms actual_integrable
#print axioms actual_formula
end
end UnifiedTheory.Audit.KFCausalReciprocalCrossKernel
