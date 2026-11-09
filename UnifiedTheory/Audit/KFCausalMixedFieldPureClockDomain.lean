/- The actual mixed-shift spectral states are in the pure-clock momentum
 domain. All differentiated profiles are proved L2 on the closed strip. -/
import UnifiedTheory.Audit.KFCausalMixedFieldPureClockDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalMixedFieldPureClockDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalRadialMultipliers
open KFCausalMixedFieldPhysicalProfile (field profile)
open KFCausalMixedFieldPureClockDifferential (fieldRate)
open KFCausalClockFloorRelativeShift (scale argument)
open KFCausalShiftedGaussianLongitudinalDifferential (inverseClock)
open KFCausalShiftedGaussianPureDifferential
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalShiftedGaussianRadialMoments (shifted_radius_memLp shifted_moment_radius_memLp)
open KFCausalClockFloorPureClockDerivative (differential)
open KFCausalClockFloorPureClockMomentum (pureMomentum)

theorem field_controlled (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Controlled (fun x => field (scale ε y x.1) x.2) :=
  controlled_add _ _ (controlled_coordinate 4)
    (controlled_mul _ _ (controlled_sub _ _
      (controlled_mul _ _ (controlled_const 3) (scale_controlled ε y hε hy)) (controlled_const 2))
      (controlled_add _ _ (controlled_coordinate 2) (controlled_coordinate 3)))

theorem fieldRate_controlled (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) :
    Controlled (fieldRate ε y) :=
  controlled_mul _ _ (controlled_mul _ _ (controlled_mul _ _ (controlled_const (3/2))
    (controlled_sub _ _ (inverseClock_controlled ε y hε hy) (realInverse_controlled ε hε)))
    (scale_controlled ε y hε hy))
      (controlled_add _ _ (controlled_coordinate 2) (controlled_coordinate 3))

theorem profile_memLp (ε a α β δ y : ℝ) (k : ℕ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) :
    MemLp (profile ε a α β δ y k) 2 volume :=
  controlled_memLp _ _ (controlled_pow _ (field_controlled ε y hε hy) k)
    (shifted_radius_memLp ε a α β 0 (y+δ) 0 hε ha hα hβ hw hyr)

theorem weightedGaussian_differential_memLp (ε a α β p y : ℝ) (b : Fin 5 → ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (P : Configuration → ℂ) (hP : Controlled P) :
    MemLp (fun x => P x*differential ε
      (KFCausalRelativeGaussianDifferential.profile (clockAmplitude ε a p y) (scale ε y) α β b) x) 2 volume := by
  let Q : Configuration → ℂ := fun x =>
    ((p:ℂ)*Complex.I*inverseClock ε y x.1-realInverse ε x.1)+
      (inverseClock ε y x.1-realInverse ε x.1)*KFCausalRelativeGaussianDifferential.slope (scale ε y) α β b x
  have hQ : Controlled Q := controlled_add _ _
    (controlled_sub _ _ (controlled_mul _ _ (controlled_const ((p:ℂ)*Complex.I))
      (inverseClock_controlled ε y hε hy)) (realInverse_controlled ε hε))
    (controlled_mul _ _ (controlled_sub _ _ (inverseClock_controlled ε y hε hy) (realInverse_controlled ε hε))
      (slope_controlled _ (scale_controlled ε y hε hy) α β b))
  have h1 := controlled_memLp _ _ (controlled_mul P Q hP hQ)
    (shifted_radius_memLp ε a α β p y b hε ha hα hβ hw hy)
  have h2 := controlled_memLp P _ hP
    (shifted_moment_radius_memLp ε a α β p y b hε ha hα hβ hw hy)
  convert h1.sub (h2.const_mul (2*(a:ℂ))) using 1
  funext x
  rw [pure_differential ε a α β p y b hε hy]
  simp only [Pi.sub_apply,Q]
  ring

theorem profile_differential_memLp (ε a α β δ y : ℝ) (k : ℕ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) :
    MemLp (differential ε (profile ε a α β δ y k)) 2 volume := by
  have h1 := controlled_memLp _ _
    (controlled_mul _ _ (controlled_mul _ _ (controlled_const (k:ℂ))
      (controlled_pow _ (field_controlled ε y hε hy) (k-1))) (fieldRate_controlled ε y hε hy))
    (shifted_radius_memLp ε a α β 0 (y+δ) 0 hε ha hα hβ hw hyr)
  have h2 := weightedGaussian_differential_memLp ε a α β 0 (y+δ) 0 hε ha hα hβ hw hyr _
    (controlled_pow _ (field_controlled ε y hε hy) k)
  convert h1.add h2 using 1
  funext x
  exact KFCausalMixedFieldPureClockDifferential.profile_differential ε a α β δ y k hε hy hyr x

variable (ε a α β δ y : ℝ) (j : Fin 2) (hε : 0 < ε) (ha : 0 < a)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3)
local notation "F" => profile ε a α β δ y (KFCausalMixedFieldGaussianStrip.degree j)
local notation "hd" => profile_differential_memLp ε a α β δ y (KFCausalMixedFieldGaussianStrip.degree j) hε ha hα hβ hw hy hyr

def output (h : ℝ) : Hilbert := (-Complex.I*(h:ℂ)) • (hd).toLp (differential ε F)

theorem state_graph (h : ℝ) (hh : h ≠ 0) :
    (KFCausalMixedFieldGaussianSpectral.state ε a α β δ y j hε ha hα hβ hw hy hyr,
      output ε a α β δ y j hε ha hα hβ hw hy hyr h) ∈ (pureMomentum ε hε h).graph := by
  have hf := profile_memLp ε a α β δ y (KFCausalMixedFieldGaussianStrip.degree j) hε ha hα hβ hw hy hyr
  have he : KFCausalMixedFieldGaussianSpectral.state ε a α β δ y j hε ha hα hβ hw hy hyr = hf.toLp F :=
    Lp.ext ((KFCausalMixedFieldPhysicalProfile.state_profile ε a α β δ y j hε ha hα hβ hw hy hyr).trans
      hf.coeFn_toLp.symm)
  rw [he]
  exact KFCausalClockFloorPureClockDifferential.differential_graph ε hε h hh F hf hd
    ((KFCausalMixedFieldPhysicalProfile.profile_smooth ε a α β δ y _ hε hy hyr).differentiable (by norm_num))

theorem state_domain (h : ℝ) (hh : h ≠ 0) :
    KFCausalMixedFieldGaussianSpectral.state ε a α β δ y j hε ha hα hβ hw hy hyr ∈
      (pureMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (state_graph ε a α β δ y j hε ha hα hβ hw hy hyr h hh)

#print axioms field_controlled
#print axioms fieldRate_controlled
#print axioms profile_memLp
#print axioms weightedGaussian_differential_memLp
#print axioms profile_differential_memLp
#print axioms state_graph
#print axioms state_domain
end
end UnifiedTheory.Audit.KFCausalMixedFieldPureClockDomain
