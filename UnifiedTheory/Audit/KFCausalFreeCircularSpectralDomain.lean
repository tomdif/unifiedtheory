/- The explicit square-integrability domain and joint charge/energy formulas
for the completed physical free Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalFreeCircularSpectral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalFreeCircularSpectralDomain
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates
open KFCausalHermiteProductBasis (Index)
open KFCausalFreeCircularSpectral

theorem weighted_norm_square (w : Block 2 → ℝ) (f g : BlockHilbert 2)
    (hg : g =ᵐ[volume] fun x => (w x:ℂ)*f x) :
    ‖g‖^2 = ∫ x, w x^2*‖f x‖^2 := by
  rw [KFCausalAveragedEnergyGraph.l2_norm_square]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hbound : |h| ≤ Real.pi*ε/3) (t : ℝ)

/-- Each weighted coefficient is L2 and the total squared energy norm is finite. -/
theorem domain_iff_weighted_integrals (f : Hilbert) :
    f ∈ (hamiltonian ε hε h hpos hbound t).domain ↔
      (∀ i, MemLp (fun x => (fiberEnergy ε h t i x:ℂ)*(transform h hpos t f i) x) 2) ∧
      Summable (fun i => ∫ x, (fiberEnergy ε h t i x)^2*‖(transform h hpos t f i) x‖^2) := by
  rw [domain_iff ε hε h hpos hbound t f]
  constructor
  · rintro ⟨G,hG,he⟩
    refine ⟨fun i => (Lp.memLp (G i)).ae_eq (he i),?_⟩
    have hs := (memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)).mp hG
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hs
    simpa only [weighted_norm_square _ _ _ (he _)] using hs
  · rintro ⟨hi,hs⟩
    let G : Index → BlockHilbert 2 := fun i => (hi i).toLp
      (fun x => (fiberEnergy ε h t i x:ℂ)*(transform h hpos t f i) x)
    have he i : G i =ᵐ[volume] fun x =>
        (fiberEnergy ε h t i x:ℂ)*(transform h hpos t f i) x := (hi i).coeFn_toLp
    refine ⟨G,?_,he⟩
    rw [memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)]
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    simpa only [weighted_norm_square _ _ _ (he _)] using hs

/-- The same transform diagonalizes the existing physical standing charge. -/
theorem charge_graph_iff (f g : Hilbert) :
    (f,g) ∈ (KFCausalStandingChargeOperator.standingCharge h hpos.ne').graph ↔
      ∀ i, transform h hpos t g i =
        (KFCausalFourCircularChargeBasis.charge i:ℂ) • transform h hpos t f i := by
  exact KFCausalCircularChargeDomain.graph_iff h hpos.ne'
    (width h t) (width_positive h hpos t) f g

#print axioms domain_iff_weighted_integrals
#print axioms charge_graph_iff
end
end UnifiedTheory.Audit.KFCausalFreeCircularSpectralDomain
