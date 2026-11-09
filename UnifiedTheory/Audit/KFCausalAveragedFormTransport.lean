/- Bounded changes between underlying form spaces induce bounded changes
between their actual orbit-averaged domains, with the same physical state. -/
import UnifiedTheory.Audit.KFCausalAveragedFormSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAveragedFormTransport
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
open UnifiedTheory.Audit.KFCausalAveragedFormSpace

variable {H E F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  (U : StrongUnitaryGroup H) (T : ℝ) (J : E →L[ℂ] H) (K : F →L[ℂ] H)
  (R : E →L[ℂ] F) (hR : ∀ v, K (R v) = J v)

def ambientMap : Ambient (H := H) (E := E) →L[ℂ] Ambient (H := H) (E := F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H (Lp F 2 angleMeasure)).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℂ H).prodMap (R.compLpL 2 angleMeasure)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ H (Lp E 2 angleMeasure)).toContinuousLinearMap)

include hR

theorem comp_section (v : Lp E 2 angleMeasure) : K.compLp (R.compLp v) = J.compLp v := by
  apply Lp.ext
  filter_upwards [K.coeFn_compLp (R.compLp v), R.coeFn_compLp v,
    J.coeFn_compLp v] with θ hK hR' hJ
  rw [hK, hR', hJ, hR]

theorem ambient_mem (u : FormSpace U T J) : ambientMap R u.val ∈ formGraph U T K := by
  change K.compLp (R.compLp (sectionMap U T J u)) - orbit U T (embedding U T J u) = 0
  rw [comp_section J K R hR, compatibility, sub_self]

def transfer : FormSpace U T J →L[ℂ] FormSpace U T K where
  toFun u := ⟨ambientMap R u.val, ambient_mem U T J K R hR u⟩
  map_add' u v := by
    apply Subtype.ext
    exact (ambientMap R).map_add u.val v.val
  map_smul' c u := by
    apply Subtype.ext
    exact (ambientMap R).map_smul c u.val
  cont := ((ambientMap R).continuous.comp continuous_subtype_val).subtype_mk _

theorem transfer_embedding (u : FormSpace U T J) :
    embedding U T K (transfer U T J K R hR u) = embedding U T J u := rfl

theorem transfer_section (u : FormSpace U T J) :
    sectionMap U T K (transfer U T J K R hR u) = R.compLp (sectionMap U T J u) := rfl

theorem domain_le : domain U T J ≤ domain U T K := by
  rintro f ⟨u, rfl⟩
  exact ⟨transfer U T J K R hR u, rfl⟩

theorem transfer_inverse (hJ : Function.Injective J) (S : F →L[ℂ] E)
    (hS : ∀ v, J (S v) = K v) (u : FormSpace U T J) :
    transfer U T K J S hS (transfer U T J K R hR u) = u :=
  embedding_injective U T J hJ rfl

def transferEquiv (hJ : Function.Injective J) (hK : Function.Injective K)
    (S : F →L[ℂ] E) (hS : ∀ v, J (S v) = K v) : FormSpace U T J ≃L[ℂ] FormSpace U T K where
  toLinearEquiv := {
    toLinearMap := (transfer U T J K R hR).toLinearMap
    invFun := transfer U T K J S hS
    left_inv := transfer_inverse U T J K R hR hJ S hS
    right_inv := transfer_inverse U T K J S hS hK R hR }
  continuous_toFun := (transfer U T J K R hR).continuous
  continuous_invFun := (transfer U T K J S hS).continuous

#print axioms comp_section
#print axioms ambient_mem
#print axioms transfer_embedding
#print axioms transfer_section
#print axioms domain_le
#print axioms transfer_inverse
#print axioms transferEquiv

end
end UnifiedTheory.Audit.KFCausalAveragedFormTransport
