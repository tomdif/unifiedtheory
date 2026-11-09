/- Exact complex sources of the physical charge modulation family. These
are computed from its partial Fourier representative, not postulated. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentSources
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block Joint)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCoordinates
open UnifiedTheory.Audit.KFCausalChargeGaussianProducts
open UnifiedTheory.Audit.KFCausalChargeGaussianIdentities (norm_two_square)
open UnifiedTheory.Audit.KFCausalFourierTranslation (phase)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStrip (clockPhase)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth clockFunction)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)

def constant (α : ℝ) (v : Block 2) : ℂ := Complex.exp (-(α:ℂ)*((v 0:ℂ)^2+(v 1:ℂ)^2))
def frequency (r : Block 4) : ℝ := 2*Real.pi*r 0

def coefficients (α : ℝ) (v : Block 2) (r : Block 4) : Fin 5 → ℂ :=
  ![(scale:ℂ)*(-2*α*v 0+2*Real.pi*Complex.I*r 1),
    (scale:ℂ)*(2*α*v 0+2*Real.pi*Complex.I*r 1),
    (scale:ℂ)*(-2*α*v 1+2*Real.pi*Complex.I*r 2),
    (scale:ℂ)*(2*α*v 1+2*Real.pi*Complex.I*r 2),
    2*Real.pi*Complex.I*r 3]

def linearSource (b : Fin 5 → ℂ) (x : Fin 5 → ℝ) : ℂ := ∑ i, b i*(x i:ℂ)

def configurationProfile (α β : ℝ) (g : ℝ → ℂ) (v : Block 2) (r : Block 4)
    (x : Configuration) : ℂ :=
  constant α v * clockPhase (frequency r) (x.1:ℂ) * Complex.exp (linearSource (coefficients α v r) x.2) *
    KFCausalChargeGaussianIdentities.configurationProfile α β g x

private theorem exp_product (A B C D E F G w : ℂ) (h : A+B+C = D+E+F+G) :
    Complex.exp A*(Complex.exp B*(w*Complex.exp C)) =
      Complex.exp D*Complex.exp E*Complex.exp F*(w*Complex.exp G) := by
  calc
    _ = w*Complex.exp (A+B+C) := by simp only [Complex.exp_add]; ring
    _ = w*Complex.exp (D+E+F+G) := congrArg (fun z => w*Complex.exp z) h
    _ = _ := by simp only [Complex.exp_add]; ring

theorem positionProfile_eq (α β : ℝ) (g : ℝ → ℂ) (v : Block 2) (r : Block 4)
    (x : KFCausalEuclideanConfiguration.Space) :
    KFCausalClockFloorCoherentCoordinates.positionProfile α β g v r x =
      configurationProfile α β g v r (KFCausalEuclideanConfiguration.split x) := by
  simp only [KFCausalClockFloorCoherentCoordinates.positionProfile,shiftedGaussian,gaussian,
    ← Complex.ofReal_pow,norm_two_square,modulatedSpectator,phase,Real.fourierChar_apply,
    spectator,PiLp.inner_apply,Fin.sum_univ_succ,RCLike.inner_apply,conj_trivial,
    configurationProfile,KFCausalChargeGaussianIdentities.configurationProfile,
    KFCausalEuclideanConfiguration.split_apply,KFCausalClockFloorShearBounds.physicalGaussian,
    constant,clockPhase,frequency,linearSource,coefficients]
  dsimp
  apply exp_product
  push_cast
  have hs : (scale:ℂ)^2 = (1/2:ℂ) := by
    rw [← Complex.ofReal_pow,scale_square]
    norm_num
  ring_nf
  rw [hs]
  ring

theorem state_configuration_coe (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k =ᵐ[volume]
      configurationProfile (groundWidth hbar) (neutralWidth hbar) (clockFunction ε a)
        (displacement hbar k) (spectatorParameter k) := by
  have h : (fun x : KFCausalEuclideanConfiguration.Space =>
      KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k
        (KFCausalEuclideanConfiguration.split x)) =ᵐ[volume]
      fun x => configurationProfile (groundWidth hbar) (neutralWidth hbar) (clockFunction ε a)
        (displacement hbar k) (spectatorParameter k) (KFCausalEuclideanConfiguration.split x) := by
    filter_upwards [KFCausalEuclideanConfiguration.euclideanPullback_coe
      (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k),
      state_position_coe ε a hbar hε ha hh k] with x hx hy
    exact hx.symm.trans (hy.trans (positionProfile_eq _ _ _ _ _ x))
  have ht := KFCausalEuclideanConfiguration.split_preserves_volume.symm.quasiMeasurePreserving.ae h
  filter_upwards [ht] with x hx
  simpa only [MeasurableEquiv.apply_symm_apply] using hx

theorem configurationProfile_memLp (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
    (k : Joint 2 4) :
    MemLp (configurationProfile (groundWidth hbar) (neutralWidth hbar) (clockFunction ε a)
      (displacement hbar k) (spectatorParameter k)) 2 :=
  (Lp.memLp (KFCausalClockFloorCoherentStates.state ε a hbar hε ha hh k)).ae_eq
    (state_configuration_coe ε a hbar hε ha hh k)

theorem constant_ne_zero (α : ℝ) (v : Block 2) : constant α v ≠ 0 := Complex.exp_ne_zero _

theorem constant_norm_le_one (α : ℝ) (hα : 0 ≤ α) (v : Block 2) : ‖constant α v‖ ≤ 1 := by
  have he : constant α v = ((Real.exp (-α*((v 0)^2+(v 1)^2)):ℝ):ℂ) := by
    simp [constant,Complex.ofReal_exp]
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) (add_nonneg (sq_nonneg _) (sq_nonneg _))

#print axioms positionProfile_eq
#print axioms state_configuration_coe
#print axioms configurationProfile_memLp
#print axioms constant_ne_zero
#print axioms constant_norm_le_one

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentSources
