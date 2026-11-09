/- The complete four-mode circular basis diagonalizes the actual charged
coordinate action. Its labels are four natural occupation indices. -/
import UnifiedTheory.Audit.KFCausalCircularChargeBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFourCircularChargeBasis
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalMeasureUnitaryPullback
open KFCausalHermiteProductBasis (joinCoordinates mergeIsometry mapBasis mapBasis_apply Index)
open KFCausalL2TensorEmbedding (productState productState_coe)
open KFCausalCircularChargeBasis (phase phase_add)

variable (c : ℝ) (hc : c ≠ 0) (b : ℝ) (hb : 0 < b)

def planeBasis : HilbertBasis (ℕ × ℕ) ℂ (BlockHilbert 2) :=
  HilbertBasis.mk ((KFCausalCircularChargeBasis.basis c hc b hb).orthonormal.comp
    Nat.pairEquiv Nat.pairEquiv.injective) (by
    have he : Set.range (fun i : ℕ × ℕ => KFCausalCircularChargeBasis.basis c hc b hb (Nat.pair i.1 i.2)) =
        Set.range (KFCausalCircularChargeBasis.basis c hc b hb) :=
      Nat.pairEquiv.surjective.range_comp _
    change ⊤ ≤ (Submodule.span ℂ (Set.range (fun i : ℕ × ℕ =>
      KFCausalCircularChargeBasis.basis c hc b hb (Nat.pair i.1 i.2)))).topologicalClosure
    rw [he,(KFCausalCircularChargeBasis.basis c hc b hb).dense_span])

theorem planeBasis_apply (i : ℕ × ℕ) : planeBasis c hc b hb i =
    KFCausalCircularChargeBasis.basis c hc b hb (Nat.pair i.1 i.2) :=
  congrFun (HilbertBasis.coe_mk _ _) i

theorem planeBasis_action (θ : ℝ) (i : ℕ × ℕ) :
    KFCausalCircularChargeBasis.action c hc θ (planeBasis c hc b hb i) =
      phase ((i.1:ℤ)-(i.2:ℤ)) θ • planeBasis c hc b hb i := by
  rw [planeBasis_apply,KFCausalCircularChargeBasis.basis_action,KFCausalCircularChargeBasis.charge_pair]

def separate : Block 4 ≃ᵐ (Block 2 × Block 2) :=
  (mergeIsometry 2 2).symm.toMeasurableEquiv.trans (split 2 2)

theorem separate_apply (x : Block 4) :
    separate x = (WithLp.toLp 2 ![x 0,x 1],WithLp.toLp 2 ![x 2,x 3]) := by
  apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

theorem separate_preserves : MeasurePreserving separate :=
  (split_preserves_volume 2 2).comp (mergeIsometry 2 2).symm.measurePreserving

theorem join_coe (f : ProductHilbert 2 2) : joinCoordinates 2 2 f =ᵐ[volume] f ∘ separate := by
  filter_upwards [unitaryPullback_symm_coe (mergeIsometry 2 2).toMeasurableEquiv
      (mergeIsometry 2 2).measurePreserving (coordinates 2 2 f),
    (mergeIsometry 2 2).symm.measurePreserving.quasiMeasurePreserving.ae
      (coordinates_coe 2 2 f)] with x hx hy
  exact hx.trans hy

theorem product_join_coe (f g : BlockHilbert 2) :
    joinCoordinates 2 2 (productState volume volume f g) =ᵐ[volume]
      fun x => f (separate x).1*g (separate x).2 := by
  filter_upwards [join_coe (productState volume volume f g),
    separate_preserves.quasiMeasurePreserving.ae (productState_coe volume volume f g)] with x hx hy
  exact hx.trans hy

theorem separate_flow (θ : ℝ) (x : Block 4) :
    separate (KFCausalChargedSpectatorCoordinates.flow c hc θ x) =
      (KFCausalCircularChargeBasis.flow c hc θ (separate x).1,
       KFCausalCircularChargeBasis.flow c hc θ (separate x).2) := by
  simp only [separate_apply]
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [KFCausalChargedSpectatorCoordinates.flow_apply,
      KFCausalChargedSpectatorCoordinates.dilate,KFCausalChargedSpectatorCoordinates.rotate,
      KFCausalCircularChargeBasis.flow_apply,KFCausalCircularChargeBasis.dilate,
      KFCausalCircularChargeBasis.rotate]

theorem action_product (θ : ℝ) (f g : BlockHilbert 2) :
    KFCausalChargedSpectatorCoordinates.chargedAction c hc θ
      (joinCoordinates 2 2 (productState volume volume f g)) =
      joinCoordinates 2 2 (productState volume volume
        (KFCausalCircularChargeBasis.action c hc θ f) (KFCausalCircularChargeBasis.action c hc θ g)) := by
  apply Lp.ext
  filter_upwards [KFCausalChargedSpectatorCoordinates.chargedAction_coe c hc θ
      (joinCoordinates 2 2 (productState volume volume f g)),
    (KFCausalChargedSpectatorCoordinates.flow_preserves c hc θ).quasiMeasurePreserving.ae
      (product_join_coe f g),
    product_join_coe (KFCausalCircularChargeBasis.action c hc θ f)
      (KFCausalCircularChargeBasis.action c hc θ g),
    separate_preserves.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst.ae
      (KFCausalCircularChargeBasis.action_coe c hc θ f)),
    separate_preserves.quasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_snd.ae
      (KFCausalCircularChargeBasis.action_coe c hc θ g))] with x h1 h2 h3 h4 h5
  rw [h1]
  simp only [Function.comp_apply]
  rw [h2,h3,h4,h5,separate_flow]
  rfl

def basis : HilbertBasis Index ℂ (BlockHilbert 4) :=
  mapBasis (KFCausalProductHilbertExpansion.productBasis 2 2
    (planeBasis c hc b hb) (planeBasis c hc b hb)) (joinCoordinates 2 2)

def charge (i : Index) : ℤ := ((i.1.1:ℤ)-(i.1.2:ℤ))+((i.2.1:ℤ)-(i.2.2:ℤ))

theorem basis_action (θ : ℝ) (i : Index) :
    KFCausalChargedSpectatorCoordinates.chargedAction c hc θ (basis c hc b hb i) =
      phase (charge i) θ • basis c hc b hb i := by
  simp only [basis,mapBasis_apply,KFCausalProductHilbertExpansion.productBasis_apply]
  rw [action_product,planeBasis_action,planeBasis_action,
    KFCausalL2TensorEmbedding.productState_smul_left,
    KFCausalL2TensorEmbedding.productState_smul_right,map_smul,map_smul,smul_smul,
    ← phase_add]
  rfl

#print axioms planeBasis
#print axioms separate_flow
#print axioms action_product
#print axioms basis
#print axioms basis_action
end
end UnifiedTheory.Audit.KFCausalFourCircularChargeBasis
