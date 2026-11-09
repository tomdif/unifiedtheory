/- Exact Fourier slices of the original shifted reciprocal packets in the
physical chart: both antisymmetric positions are transformed. The first
standing plane carries reciprocal width and the second carries width.
The neutral shear and field multiplier remain spectators. -/
import UnifiedTheory.Audit.KFCausalReciprocalComplexGaussianFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalShiftedPhysicalFourierSlices
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalReciprocalGaussianStates (quadratic)
open KFCausalShiftedNarrowFourierGeometry (neutral mixedField)
open KFCausalShiftedNarrowFourierSlices (neutralPacket fourier_mul_right)
open KFCausalReciprocalComplexGaussianFourier (product product_fourier)

def reconstruct (u : Block 2) (v : Block 4) : Transverse :=
  ![scale*(u 0+v 1),scale*(v 1-u 0),scale*(u 1+v 2),scale*(v 2-u 1),v 3]

def radius (A : ℂ) (w : ℝ) (u : Block 2) (v : Block 4) : ℂ :=
  (Real.pi:ℂ)^2/A*((u 0:ℂ)^2/(w:ℂ)+(w:ℂ)*(u 1:ℂ)^2)+
    A*((v 1:ℂ)^2/(w:ℂ)+(w:ℂ)*(v 2:ℂ)^2)

theorem reconstruct_quadratic (w : ℝ) (u : Block 2) (v : Block 4) :
    quadratic w (reconstruct u v) =
      w*(u 0)^2+(u 1)^2/w+(v 1)^2/w+w*(v 2)^2 := by
  dsimp [quadratic,KFCausalQuarticChargeProfiles.chargedRadius,
    KFCausalChargedPairCoordinates.pairPolynomial,reconstruct]
  ring_nf
  rw [scale_square]
  ring

theorem reconstruct_neutral (r : ℂ) (u : Block 2) (v : Block 4) :
    KFCausalRelativeGaussianDifferential.position r (reconstruct u v) 4 = neutral r v := by
  dsimp [KFCausalRelativeGaussianDifferential.position,reconstruct,neutral]
  push_cast
  ring

theorem reconstruct_field (t : ℂ) (u : Block 2) (v : Block 4) :
    KFCausalMixedFieldClockBounds.field t (reconstruct u v) = mixedField t v := by
  dsimp [KFCausalMixedFieldClockBounds.field,reconstruct,mixedField]
  push_cast
  ring

def physicalSlice (α β w : ℝ) (r t b : ℂ) (P : Polynomial ℂ) (k : ℕ)
    (v : Block 4) (u : Block 2) : ℂ :=
  KFCausalMixedFieldClockBounds.field t (reconstruct u v)^k*
    KFCausalReciprocalNeutralSliceIntegrability.factor α β w r b P 0 (reconstruct u v)

theorem physicalSlice_factor (α β w : ℝ) (r t b : ℂ) (P : Polynomial ℂ) (k : ℕ)
    (v : Block 4) (u : Block 2) :
    physicalSlice α β w r t b P k v u = product ((α:ℂ)*r^2) w u*
      (mixedField t v^k*Complex.exp (-((α:ℂ)*r^2)*
        ((v 1:ℂ)^2/(w:ℂ)+(w:ℂ)*(v 2:ℂ)^2))*neutralPacket β r b P v) := by
  simp only [physicalSlice,KFCausalReciprocalNeutralSliceIntegrability.factor,pow_zero,
    one_mul,KFCausalReciprocalGaussianCoordinates.exponent,reconstruct_quadratic,
    KFCausalNeutralExponentialProfiles.exponentialProfile,reconstruct_field,reconstruct_neutral,
    product,KFCausalGaussianSliceDomain.gaussian,neutralPacket]
  have hn : ((reconstruct u v 4:ℝ):ℂ)+2*(r-1)*
      ((reconstruct u v 2+reconstruct u v 3:ℝ):ℂ) = neutral r v := by
    simpa only [KFCausalRelativeGaussianDifferential.position,ite_true,Complex.ofReal_add] using
      reconstruct_neutral r u v
  rw [hn]
  push_cast
  rw [show -(α:ℂ)*r^2*((w:ℂ)*(u 0:ℂ)^2+(u 1:ℂ)^2/(w:ℂ)+
      (v 1:ℂ)^2/(w:ℂ)+(w:ℂ)*(v 2:ℂ)^2) =
    -((α:ℂ)*r^2*(w:ℂ))*(u 0:ℂ)^2-
    ((α:ℂ)*r^2/(w:ℂ))*(u 1:ℂ)^2-
    ((α:ℂ)*r^2)*((v 1:ℂ)^2/(w:ℂ)+(w:ℂ)*(v 2:ℂ)^2) by ring]
  simp only [sub_eq_add_neg,Complex.exp_add]
  ring

private theorem scalar_integrable (A : ℂ) (hA : 0 < A.re) :
    Integrable (KFCausalGaussianSliceDomain.gaussian A) := by
  have hi := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℝ) (b := A) hA 0 (0 : ℝ)
  have he : KFCausalGaussianSliceDomain.gaussian A =
      fun u : ℝ => Complex.exp (-A*(‖u‖:ℂ)^2) := by
    ext u
    simp [KFCausalGaussianSliceDomain.gaussian,Real.norm_eq_abs,← Complex.ofReal_pow,sq_abs]
  rw [he]
  simpa only [zero_mul,add_zero,neg_mul] using hi

theorem product_integrable (A : ℂ) (hA : 0 < A.re) (w : ℝ) (hw : 0 < w) :
    Integrable (product A w) := by
  have hmul : 0 < (A*(w:ℂ)).re := by simpa using mul_pos hA hw
  have hdiv : 0 < (A/(w:ℂ)).re := by simpa using div_pos hA hw
  have hi : ∀ i : Fin 2, Integrable (![KFCausalGaussianSliceDomain.gaussian (A*(w:ℂ)),
      KFCausalGaussianSliceDomain.gaussian (A/(w:ℂ))] i) volume := by
    intro i
    fin_cases i
    · exact scalar_integrable _ hmul
    · exact scalar_integrable _ hdiv
  have hp := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integrable_comp_of_integrable
    (Integrable.fintype_prod hi)
  simpa only [product,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Function.comp_apply] using hp

theorem physicalSlice_integrable (α β w : ℝ) (r t b : ℂ) (P : Polynomial ℂ) (k : ℕ)
    (hA : 0 < ((α:ℂ)*r^2).re) (hw : 0 < w) (v : Block 4) :
    Integrable (physicalSlice α β w r t b P k v) := by
  rw [funext (physicalSlice_factor α β w r t b P k v)]
  exact (product_integrable ((α:ℂ)*r^2) hA w hw).mul_const _

theorem physicalSlice_fourier (α β w : ℝ) (r t b : ℂ) (P : Polynomial ℂ) (k : ℕ)
    (hA : 0 < ((α:ℂ)*r^2).re) (hw : 0 < w) (v : Block 4) (u : Block 2) :
    (𝓕 (physicalSlice α β w r t b P k v)) u =
      ((Real.pi:ℂ)/((α:ℂ)*r^2))*mixedField t v^k*
        Complex.exp (-radius ((α:ℂ)*r^2) w u v)*neutralPacket β r b P v := by
  rw [funext (physicalSlice_factor α β w r t b P k v),fourier_mul_right,
    product_fourier _ hA w hw]
  simp only [KFCausalGaussianSliceDomain.gaussian]
  unfold radius
  rw [show -((Real.pi:ℂ)^2/((α:ℂ)*r^2)*
      ((u 0:ℂ)^2/(w:ℂ)+(w:ℂ)*(u 1:ℂ)^2)+
      (α:ℂ)*r^2*((v 1:ℂ)^2/(w:ℂ)+(w:ℂ)*(v 2:ℂ)^2)) =
    -((Real.pi:ℂ)^2/((α:ℂ)*r^2*(w:ℂ)))*(u 0:ℂ)^2-
    ((Real.pi:ℂ)^2/((α:ℂ)*r^2/(w:ℂ)))*(u 1:ℂ)^2-
    (α:ℂ)*r^2*((v 1:ℂ)^2/(w:ℂ)+(w:ℂ)*(v 2:ℂ)^2) by
      rw [← div_div,div_div_eq_mul_div]; ring]
  simp only [sub_eq_add_neg,Complex.exp_add]
  ring

#print axioms reconstruct_quadratic
#print axioms reconstruct_neutral
#print axioms reconstruct_field
#print axioms physicalSlice_factor
#print axioms product_integrable
#print axioms physicalSlice_integrable
#print axioms physicalSlice_fourier
end
end UnifiedTheory.Audit.KFCausalShiftedPhysicalFourierSlices
