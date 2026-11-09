/- The L2 derivatives already estimated for the physical trials are the
actions of the actual maximal self-adjoint transverse momenta. -/
import UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
import UnifiedTheory.Audit.KFCausalL2DirectionalDerivative
import UnifiedTheory.Audit.KFCausalFullTransverseEnergySpace
import UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative
noncomputable section
open MeasureTheory
open scoped ContDiff
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalTransverseTrialDerivative
open UnifiedTheory.Audit.KFCausalFullTransverseEnergySpace
open UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates
open UnifiedTheory.Audit.KFCausalL2DirectionalDerivative

theorem flatten_hasLineDerivAt (g : Configuration → ℂ) (v : Transverse)
    (hs : ∀ s, Differentiable ℝ (fun y : Transverse => g (s,y))) (x : Space) :
    HasLineDerivAt ℝ (g ∘ split) ((derivative v g ∘ split) x) x (transverseVector v) := by
  have hl := ((hs (split x).1) (split x).2).lineDifferentiableAt (v := v) |>.hasLineDerivAt
  change HasDerivAt (fun t : ℝ => g ((split x).1,(split x).2+t • v))
    (derivative v g (split x)) 0 at hl
  change HasDerivAt (fun t : ℝ => g (split (x+t • transverseVector v)))
    (derivative v g (split x)) 0
  simpa only [split_transverse_add] using hl

theorem physical_derivative_fourier (g : Configuration → ℂ) (v : Transverse)
    (hg : MemLp g 2 (volume : Measure Configuration))
    (hd : MemLp (derivative v g) 2 (volume : Measure Configuration))
    (hs : ∀ s, Differentiable ℝ (fun y : Transverse => g (s,y))) :
    fourierCoordinates (hd.toLp (derivative v g)) =ᵐ[volume] fun k =>
      (2*Real.pi*Complex.I)*(inner ℝ k (transverseVector v):ℂ)*
        (fourierCoordinates (hg.toLp g)) k := by
  rw [fourier_toLp g hg,fourier_toLp (derivative v g) hd]
  exact derivative_fourier _ _ _ (flatten_memLp g hg) (flatten_memLp _ hd)
    (flatten_hasLineDerivAt g v hs)

theorem derivative_momentum_graph (hbar : ℝ) (g : Configuration → ℂ) (v : Transverse)
    (hg : MemLp g 2 (volume : Measure Configuration))
    (hd : MemLp (derivative v g) 2 (volume : Measure Configuration))
    (hs : ∀ s, Differentiable ℝ (fun y : Transverse => g (s,y))) :
    (hg.toLp g,(-Complex.I*(hbar:ℂ)) • hd.toLp (derivative v g)) ∈
      (transverseMomentum hbar v).graph := by
  apply (transverseMomentum_graph hbar v _ _).mpr
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (-Complex.I*(hbar:ℂ))
    (fourierCoordinates (hd.toLp (derivative v g))),physical_derivative_fourier g v hg hd hs]
    with k hk hd'
  rw [hk]
  simp only [Pi.smul_apply,smul_eq_mul,hd',transverseSymbol,
    Complex.ofReal_mul,Complex.ofReal_ofNat]
  calc
    _ = -(Complex.I*Complex.I)*(2*(Real.pi:ℂ)*(hbar:ℂ)*
      (inner ℝ k (transverseVector v):ℂ)*(fourierCoordinates (hg.toLp g)) k) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem derivative_momentum_domain (hbar : ℝ) (g : Configuration → ℂ) (v : Transverse)
    (hg : MemLp g 2 (volume : Measure Configuration))
    (hd : MemLp (derivative v g) 2 (volume : Measure Configuration))
    (hs : ∀ s, Differentiable ℝ (fun y : Transverse => g (s,y))) :
    hg.toLp g ∈ (transverseMomentum hbar v).domain :=
  LinearPMap.mem_domain_of_mem_graph (derivative_momentum_graph hbar g v hg hd hs)

theorem derivative_momentum_action (hbar : ℝ) (g : Configuration → ℂ) (v : Transverse)
    (hg : MemLp g 2 (volume : Measure Configuration))
    (hd : MemLp (derivative v g) 2 (volume : Measure Configuration))
    (hs : ∀ s, Differentiable ℝ (fun y : Transverse => g (s,y))) :
    transverseMomentum hbar v ⟨hg.toLp g,derivative_momentum_domain hbar g v hg hd hs⟩ =
      (-Complex.I*(hbar:ℂ)) • hd.toLp (derivative v g) := by
  obtain ⟨u,hu,he⟩ := (LinearPMap.mem_graph_iff _).mp
    (derivative_momentum_graph hbar g v hg hd hs)
  exact (congrArg (transverseMomentum hbar v) (Subtype.ext hu.symm)).trans he

theorem allEnergySpace_le_momentum_domain (hbar : ℝ) (v : Transverse) :
    allEnergySpace ≤ (transverseMomentum hbar v).domain := by
  intro f hf
  rcases (mem_allEnergySpace_iff f).mp hf with ⟨g,hg,hs,hd,he⟩
  have he' : f=hg.toLp g := Lp.ext (he.trans hg.coeFn_toLp.symm)
  rw [he']
  exact derivative_momentum_domain hbar g v hg (hd v) (fun s => (hs s).differentiable (by simp))

theorem derivative_momentum_energy (hbar : ℝ) (g : Configuration → ℂ) (v : Transverse)
    (hg : MemLp g 2 (volume : Measure Configuration))
    (hd : MemLp (derivative v g) 2 (volume : Measure Configuration))
    (hs : ∀ s, Differentiable ℝ (fun y : Transverse => g (s,y))) :
    ‖transverseMomentum hbar v ⟨hg.toLp g,derivative_momentum_domain hbar g v hg hd hs⟩‖^2 =
      hbar^2 * ∫ z, ‖derivative v g z‖^2 := by
  have hi : ‖hd.toLp (derivative v g)‖^2 = ∫ z, ‖derivative v g z‖^2 := by
    rw [KFCausalPositiveMultiplierEnergy.l2_norm_square]
    apply integral_congr_ae
    filter_upwards [hd.coeFn_toLp] with z hz
    rw [hz]
  rw [derivative_momentum_action hbar g v hg hd hs,norm_smul,mul_pow,hi]
  simp only [norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]

#print axioms flatten_hasLineDerivAt
#print axioms physical_derivative_fourier
#print axioms derivative_momentum_graph
#print axioms derivative_momentum_domain
#print axioms derivative_momentum_action
#print axioms allEnergySpace_le_momentum_domain
#print axioms derivative_momentum_energy

end
end UnifiedTheory.Audit.KFCausalTransverseMomentumDerivative
