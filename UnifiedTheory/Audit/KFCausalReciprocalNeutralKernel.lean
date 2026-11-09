/- Exact cross-width potential kernel retaining both neutral profiles.
Only the three Gaussian spectator coordinates are integrated out. The
remaining two-dimensional complex kernel keeps the neutral shear and
all off-diagonal phases; no uniform comparison is inferred. -/
import UnifiedTheory.Audit.KFCausalReciprocalCrossKernel
import UnifiedTheory.Audit.KFCausalNeutralPlaneMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralKernel
noncomputable section
open MeasureTheory
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalRelativeGaussianDifferential (position)
open KFCausalReciprocalGaussianCoordinates (exponent reconstruct)
open KFCausalReciprocalCrossGeometry (A B C)
open KFCausalComplexGaussianMoments (value gaussianValue)
open KFCausalQuarticPlaneDomination (potential)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalChargedPairCoordinates (fieldSlope)
open scoped ComplexConjugate

def neutral (r : ℂ) (y x : ℝ) : ℂ := (x:ℂ)+2*(r.im:ℂ)*Complex.I*(y:ℂ)

theorem neutral_reconstruct (r : ℂ) (u : Transverse) :
    position r (reconstruct 1 r u) 4 = neutral r (u 2) (u 4) := by
  simp only [position,ite_true,reconstruct,one_mul,div_one]
  unfold neutral
  apply Complex.ext <;> simp <;> ring_nf
  simp

def density (α β w v : ℝ) (r : ℂ) (F G : ℂ → ℂ) (q : Transverse) : ℂ :=
  KFCausalReciprocalCrossKernel.density α β w v r q *
    (conj (F (position r q 4))*G (position r q 4))

def kernel (α β w v : ℝ) (r : ℂ) (F G : ℂ → ℂ) : ℂ :=
  ∫ q, density α β w v r F G q

def planeDensity (β : ℝ) (c r : ℂ) (F G : ℂ → ℂ) (u : Fin 2 → ℝ) : ℂ :=
  (potential (u 1+fieldSlope r*u 0):ℂ)*
    Complex.exp (-c*(u 0:ℂ)^2-(2*(β:ℂ))*(u 1:ℂ)^2)*
    (conj (F (neutral r (u 0) (u 1)))*G (neutral r (u 0) (u 1)))

theorem density_reconstruct (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r : ℂ) (F G : ℂ → ℂ) (u : Transverse) :
    density α β w v r F G (reconstruct 1 r u) =
      KFCausalComplexPotentialGaussian.density
        (A α w v r) (B α w v r) (C α β w v r) (2*(β:ℂ)) (fieldSlope r) u *
          (conj (F (neutral r (u 2) (u 4)))*G (neutral r (u 2) (u 4))) := by
  rw [density,KFCausalReciprocalCrossKernel.density_reconstruct α β w v hw hv,
    neutral_reconstruct]

theorem integral_head_product (n : ℕ) (f : ℝ → ℂ) (g : (Fin n → ℝ) → ℂ) :
    (∫ u : Fin (n+1) → ℝ, f (u 0)*g (fun i => u i.succ)) =
      (∫ x, f x)*(∫ v, g v) := by
  rw [← ((volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm).integral_comp']
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Fin.insertNth_zero,Equiv.coe_fn_mk,Fin.cons_succ,Fin.zero_succAbove,
    cast_eq,Fin.cons_zero] using (integral_prod_mul f g)

def swap (u : Transverse) : Transverse := ![u 0,u 1,u 3,u 2,u 4]

theorem integral_swap (f : Transverse → ℂ) : (∫ u, f u) = ∫ u, f (swap u) := by
  have hm := (volume_measurePreserving_piCongrLeft (fun _ : Fin 5 => ℝ)
    (Equiv.swap (2:Fin 5) 3)).integral_comp' f
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin 5 => ℝ) (Equiv.swap (2:Fin 5) 3) :
      Transverse → Transverse) = swap := by
    funext u i
    fin_cases i <;> norm_num [swap,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft,
      Equiv.swap_apply_def,Fin.ext_iff]
    rfl
  rw [he] at hm
  exact hm.symm

theorem density_factorization (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r : ℂ) (F G : ℂ → ℂ) (u : Transverse) :
    density α β w v r F G (reconstruct 1 r (swap u)) =
      Complex.exp (-A α w v r*(u 0:ℂ)^2)*
        (Complex.exp (-B α w v r*(u 1:ℂ)^2)*
          (Complex.exp (-A α w v r*(u 2:ℂ)^2)*
            planeDensity β (C α β w v r) r F G ![u 3,u 4])) := by
  rw [density_reconstruct α β w v hw hv]
  rw [KFCausalComplexPotentialGaussian.density,
    KFCausalReciprocalCrossGeometry.weight_exponential]
  change (potential (u 4+fieldSlope r*u 3):ℂ)*
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
        ((potential (u 4+fieldSlope r*u 3):ℂ)*
          Complex.exp (-C α β w v r*(u 3:ℂ)^2-2*(β:ℂ)*(u 4:ℂ)^2)*
          (conj (F (neutral r (u 3) (u 4)))*G (neutral r (u 3) (u 4))))))
  ring

theorem kernel_plane_integral (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r : ℂ) (F G : ℂ → ℂ) :
    kernel α β w v r F G =
      (1/4:ℂ)*value (A α w v r) 0^2*value (B α w v r) 0*
        ∫ u : Fin 2 → ℝ, planeDensity β (C α β w v r) r F G u := by
  rw [kernel,KFCausalReciprocalCrossKernel.integral_coordinates r,integral_swap]
  simp_rw [density_factorization α β w v hw hv]
  change (1/4:ℂ)*(∫ u : Fin (4+1) → ℝ,
    Complex.exp (-A α w v r*(u 0:ℂ)^2)*
    (fun z : Fin 4 → ℝ => Complex.exp (-B α w v r*(z 0:ℂ)^2)*
      (Complex.exp (-A α w v r*(z 1:ℂ)^2)*
        planeDensity β (C α β w v r) r F G ![z 2,z 3])) (fun i => u i.succ)) = _
  rw [integral_head_product 4 (fun x => Complex.exp (-A α w v r*(x:ℂ)^2))
    (fun z => Complex.exp (-B α w v r*(z 0:ℂ)^2)*
      (Complex.exp (-A α w v r*(z 1:ℂ)^2)*
        planeDensity β (C α β w v r) r F G ![z 2,z 3]))]
  change (1/4:ℂ)*((∫ x : ℝ, Complex.exp (-A α w v r*(x:ℂ)^2))*
    ∫ u : Fin (3+1) → ℝ, Complex.exp (-B α w v r*(u 0:ℂ)^2)*
      (fun z : Fin 3 → ℝ => Complex.exp (-A α w v r*(z 0:ℂ)^2)*
        planeDensity β (C α β w v r) r F G ![z 1,z 2]) (fun i => u i.succ)) = _
  rw [integral_head_product 3 (fun x => Complex.exp (-B α w v r*(x:ℂ)^2))
    (fun z => Complex.exp (-A α w v r*(z 0:ℂ)^2)*
      planeDensity β (C α β w v r) r F G ![z 1,z 2])]
  change (1/4:ℂ)*((∫ x : ℝ, Complex.exp (-A α w v r*(x:ℂ)^2))*
    ((∫ x : ℝ, Complex.exp (-B α w v r*(x:ℂ)^2))*
      ∫ u : Fin (2+1) → ℝ, Complex.exp (-A α w v r*(u 0:ℂ)^2)*
        (fun z : Fin 2 → ℝ => planeDensity β (C α β w v r) r F G ![z 0,z 1]) (fun i => u i.succ))) = _
  rw [integral_head_product 2 (fun x => Complex.exp (-A α w v r*(x:ℂ)^2))
    (fun z => planeDensity β (C α β w v r) r F G ![z 0,z 1])]
  have he : (fun z : Fin 2 → ℝ => planeDensity β (C α β w v r) r F G ![z 0,z 1]) =
      planeDensity β (C α β w v r) r F G := by
    funext z
    rw [show ![z 0,z 1] = z from by ext i; fin_cases i <;> rfl]
  rw [he]
  simp only [value,KFCausalComplexGaussianMoments.moment,pow_zero,one_mul]
  ring

theorem kernel_gaussian_marginal (α β w v : ℝ) (hw : w ≠ 0) (hv : v ≠ 0)
    (r : ℂ) (F G : ℂ → ℂ) (hA : 0 < (A α w v r).re) (hB : 0 < (B α w v r).re) :
    kernel α β w v r F G =
      (1/4:ℂ)*gaussianValue (A α w v r)^2*gaussianValue (B α w v r)*
        ∫ u : Fin 2 → ℝ, planeDensity β (C α β w v r) r F G u := by
  rw [kernel_plane_integral α β w v hw hv,
    KFCausalComplexGaussianMoments.value_zero _ hA,
    KFCausalComplexGaussianMoments.value_zero _ hB]

#print axioms neutral_reconstruct
#print axioms density_reconstruct
#print axioms integral_head_product
#print axioms integral_swap
#print axioms density_factorization
#print axioms kernel_plane_integral
#print axioms kernel_gaussian_marginal
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralKernel
