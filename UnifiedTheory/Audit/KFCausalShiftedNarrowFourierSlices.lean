/- Exact Fourier integrals of the original mixed-shift physical profiles
in the two narrow modes. The complex Gaussian normalization is explicit. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowFourierGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalShiftedNarrowFourierSlices
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalShiftedNarrowFourierGeometry

def gaussian (A : ℂ) (u : Block 2) : ℂ := Complex.exp (-A*(‖u‖:ℂ)^2)

theorem gaussian_integrable (A : ℂ) (hA : 0 < A.re) : Integrable (gaussian A) := by
  change Integrable (fun u : Block 2 => Complex.exp (-A*(‖u‖:ℂ)^2))
  simpa only [zero_mul,add_zero,neg_mul] using
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Block 2) (b := A) hA 0 (0 : Block 2)

theorem gaussian_fourier (A : ℂ) (hA : 0 < A.re) (u : Block 2) :
    (𝓕 (gaussian A)) u = ((Real.pi:ℂ)/A)*gaussian ((Real.pi:ℂ)^2/A) u := by
  unfold gaussian
  rw [fourier_gaussian_innerProductSpace (b := A) hA]
  simp only [finrank_euclideanSpace,Fintype.card_fin,Nat.cast_ofNat]
  norm_num only [div_self (by norm_num : (2:ℂ) ≠ 0),Complex.cpow_one]
  congr 1
  congr 1
  ring

theorem fourier_mul_right (g : Block 2 → ℂ) (c : ℂ) (u : Block 2) :
    (𝓕 (fun x => g x*c)) u = (𝓕 g) u*c := by
  simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul,← mul_assoc,integral_mul_const]

def neutralPacket (β : ℝ) (r b : ℂ) (P : Polynomial ℂ) (v : Block 4) : ℂ :=
  Complex.exp (-(β:ℂ)*neutral r v^2+b*neutral r v)*P.eval (neutral r v)

def physicalSlice (α β w : ℝ) (r t b : ℂ) (P : Polynomial ℂ) (k : ℕ)
    (v : Block 4) (u : Block 2) : ℂ :=
  KFCausalMixedFieldClockBounds.field t (reconstruct u v)^k*
    KFCausalReciprocalNeutralSliceIntegrability.factor α β w r b P 0 (reconstruct u v)

theorem physicalSlice_factor (α β w : ℝ) (r t b : ℂ) (P : Polynomial ℂ) (k : ℕ)
    (v : Block 4) (u : Block 2) :
    physicalSlice α β w r t b P k v u = gaussian ((α:ℂ)*r^2/(w:ℂ)) u*
      (mixedField t v^k*Complex.exp (-((α:ℂ)*r^2)*(w:ℂ)*(broadRadius v:ℂ))*
        neutralPacket β r b P v) := by
  simp only [physicalSlice,KFCausalReciprocalNeutralSliceIntegrability.factor,pow_zero,
    one_mul,KFCausalReciprocalGaussianCoordinates.exponent,reconstruct_quadratic,
    KFCausalNeutralExponentialProfiles.exponentialProfile,reconstruct_field,reconstruct_neutral,
    gaussian,neutralPacket]
  have hn : ((reconstruct u v 4:ℝ):ℂ)+2*(r-1)*
      ((reconstruct u v 2+reconstruct u v 3:ℝ):ℂ) = neutral r v := by
    simpa only [KFCausalRelativeGaussianDifferential.position,ite_true,Complex.ofReal_add] using
      reconstruct_neutral r u v
  rw [hn]
  simp only [sub_eq_add_neg,Complex.exp_add]
  push_cast
  rw [show -(α:ℂ)*r^2*((‖u‖:ℂ)^2/(w:ℂ)+(w:ℂ)*(broadRadius v:ℂ)) =
    -((α:ℂ)*r^2/(w:ℂ))*(‖u‖:ℂ)^2+-((α:ℂ)*r^2)*(w:ℂ)*(broadRadius v:ℂ) by ring,
    Complex.exp_add]
  ring

theorem physicalSlice_integrable (α β w : ℝ) (r t b : ℂ) (P : Polynomial ℂ) (k : ℕ)
    (hA : 0 < ((α:ℂ)*r^2).re) (hw : 0 < w) (v : Block 4) :
    Integrable (physicalSlice α β w r t b P k v) := by
  have hp : 0 < ((α:ℂ)*r^2/(w:ℂ)).re := by simpa using div_pos hA hw
  rw [funext (physicalSlice_factor α β w r t b P k v)]
  exact
    (gaussian_integrable ((α:ℂ)*r^2/(w:ℂ)) hp).mul_const
      (mixedField t v^k*Complex.exp (-((α:ℂ)*r^2)*(w:ℂ)*(broadRadius v:ℂ))*neutralPacket β r b P v)

theorem physicalSlice_fourier (α β w : ℝ) (r t b : ℂ) (P : Polynomial ℂ) (k : ℕ)
    (hA : 0 < ((α:ℂ)*r^2).re) (hw : 0 < w) (v : Block 4) (u : Block 2) :
    (𝓕 (physicalSlice α β w r t b P k v)) u =
      ((Real.pi:ℂ)/((α:ℂ)*r^2))*(w:ℂ)*mixedField t v^k*
        Complex.exp (-(w:ℂ)*radius ((α:ℂ)*r^2) u v)*neutralPacket β r b P v := by
  have hp : 0 < ((α:ℂ)*r^2/(w:ℂ)).re := by simpa using div_pos hA hw
  rw [funext (physicalSlice_factor α β w r t b P k v)]
  rw [fourier_mul_right,gaussian_fourier _ hp]
  unfold gaussian radius
  rw [show -(w:ℂ)*((Real.pi:ℂ)^2/((α:ℂ)*r^2)*(‖u‖:ℂ)^2+
    (α:ℂ)*r^2*(broadRadius v:ℂ)) =
    -((Real.pi:ℂ)^2/((α:ℂ)*r^2/(w:ℂ)))*(‖u‖:ℂ)^2+
      -((α:ℂ)*r^2)*(w:ℂ)*(broadRadius v:ℂ) by
        rw [div_div_eq_mul_div]; ring,Complex.exp_add]
  rw [div_div_eq_mul_div]
  ring

#print axioms gaussian_integrable
#print axioms gaussian_fourier
#print axioms fourier_mul_right
#print axioms physicalSlice_factor
#print axioms physicalSlice_integrable
#print axioms physicalSlice_fourier
end
end UnifiedTheory.Audit.KFCausalShiftedNarrowFourierSlices
