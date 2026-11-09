/- Paired-squeeze covariance on the full maximal transverse-momentum
graphs, and on their natural inverse-clock compositions. Both momentum
pairs are kept: their squeeze weights have opposite signs. -/
import UnifiedTheory.Audit.KFCausalPairedSqueezeFourier
import UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorSqueezeKinetic
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalPairedSqueezeFlow
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport transport_coe
  squeezeFlow squeezeFlow_apply squeezeFlow_quasiMeasurePreserving)
open UnifiedTheory.Audit.KFCausalPairedSqueezeEuclidean
open UnifiedTheory.Audit.KFCausalPairedSqueezeFourier (fourier_coe coefficient)
open UnifiedTheory.Audit.KFCausalFourierLinearChange
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)

theorem transverseVector_smul (c : ℝ) (v : Transverse) :
    transverseVector (c • v) = c • transverseVector v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [transverseVector]
  · simp [transverseVector]

theorem inverse_linearFlow_transverse (a : ℝ) (v : Transverse) :
    (linearFlow a).symm (transverseVector v) = transverseVector (squeeze a v) := by
  apply (linearFlow a).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply split.injective
  rw [split_linearFlow]
  change (0,v) = (0,squeeze (-a) (squeeze a v))
  rw [squeeze_reverse]

theorem dual_symbol (h a q : ℝ) (v : Transverse)
    (hv : squeeze a v = Real.exp q • v) (k : Space) :
    transverseSymbol h v (dualEquiv (linearFlow a) k) =
      Real.exp q * transverseSymbol h v k := by
  unfold transverseSymbol
  rw [real_inner_comm (transverseVector v) (dualEquiv (linearFlow a) k),dual_inner,
    inverse_linearFlow_transverse,hv,transverseVector_smul,real_inner_smul_left,
    real_inner_comm k (transverseVector v)]
  ring

theorem momentum_graph (h a q : ℝ) (v : Transverse)
    (hv : squeeze a v = Real.exp q • v) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h v).graph) :
    (transport a f,(Real.exp (-q):ℂ) • transport a g) ∈ (transverseMomentum h v).graph := by
  apply (transverseMomentum_graph h v _ _).mpr
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (Real.exp (-q):ℂ) (fourierCoordinates (transport a g)),
    fourier_coe a f,fourier_coe a g,
    (dual_quasiMeasurePreserving (linearFlow a)).ae
      ((transverseMomentum_graph h v f g).mp hfg)] with k hs hf hg he
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hg,he,hf,dual_symbol h a q v hv]
  simp only [Complex.ofReal_mul]
  have hc : (Real.exp (-q):ℂ)*(Real.exp q:ℂ) = 1 := by
    rw [← Complex.ofReal_mul,← Real.exp_add,neg_add_cancel,Real.exp_zero,Complex.ofReal_one]
  calc
    _ = ((Real.exp (-q):ℂ)*(Real.exp q:ℂ))*
        ((transverseSymbol h v k:ℂ)*(coefficient a*
          (fourierCoordinates f) (dualEquiv (linearFlow a) k))) := by ring
    _ = _ := by rw [hc,one_mul]

theorem half_graph (ε a : ℝ) (f g : Hilbert) (hfg : (f,g) ∈ (clockHalf ε).graph) :
    (transport a f,transport a g) ∈ (clockHalf ε).graph := by
  apply (clockHalf_graph ε _ _).mpr
  filter_upwards [transport_coe a f,transport_coe a g,
    (squeezeFlow_quasiMeasurePreserving a).ae ((clockHalf_graph ε f g).mp hfg)]
    with x hf hg he
  rw [hg,he,hf]
  simp only [halfWeight,squeezeFlow_apply]
  ring

theorem inverse_half_graph (ε a : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (inverseClockHalf ε).graph) :
    (transport a f,transport a g) ∈ (inverseClockHalf ε).graph := by
  apply (inverseClockHalf_graph ε _ _).mpr
  filter_upwards [transport_coe a f,transport_coe a g,
    (squeezeFlow_quasiMeasurePreserving a).ae ((inverseClockHalf_graph ε f g).mp hfg)]
    with x hf hg he
  rw [hg,he,hf]
  simp only [inverseWeight,halfWeight,squeezeFlow_apply]
  ring

theorem kinetic_graph (ε h a q : ℝ) (v : Transverse)
    (hv : squeeze a v = Real.exp q • v) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h v).graph) :
    (transport a f,(Real.exp (-q):ℂ) • transport a g) ∈ (clockMomentum ε h v).graph := by
  obtain ⟨u,hu,hg⟩ := (composition_graph _ _ f g).mp hfg
  exact (composition_graph _ _ _ _).mpr
    ⟨_,inverse_half_graph ε a f u hu,momentum_graph h a q v hv u g hg⟩

def kineticScale (a : ℝ) (i : Fin 4) : ℂ :=
  Real.exp (if i.val < 2 then -a else a)

theorem model_kinetic_graph (ε h a : ℝ) (i : Fin 4) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h (modelDirections i)).graph) :
    (transport a f,kineticScale a i • transport a g) ∈
      (clockMomentum ε h (modelDirections i)).graph := by
  by_cases hi : i.val < 2
  · have hv : squeeze a (modelDirections i) = Real.exp a • modelDirections i := by
      simpa [Fin.lt_def,hi] using squeeze_directions a i
    simpa only [kineticScale,hi,if_true] using kinetic_graph ε h a a _ hv f g hfg
  · have hv : squeeze a (modelDirections i) = Real.exp (-a) • modelDirections i := by
      simpa [Fin.lt_def,hi] using squeeze_directions a i
    simpa only [kineticScale,hi,if_false,neg_neg] using kinetic_graph ε h a (-a) _ hv f g hfg

#print axioms transverseVector_smul
#print axioms inverse_linearFlow_transverse
#print axioms dual_symbol
#print axioms momentum_graph
#print axioms half_graph
#print axioms inverse_half_graph
#print axioms kinetic_graph
#print axioms model_kinetic_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorSqueezeKinetic
