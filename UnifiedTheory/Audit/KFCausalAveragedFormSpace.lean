/- A concrete domain for orbit-averaged energy: a physical state together
with its L2 family of lifts into a complete form space. This is a closed
Hilbert subspace. No density or nontriviality is inferred from the density
of the original form domain. -/
import UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAveragedFormSpace
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalPeriodicUnitaryMean
open UnifiedTheory.Audit.KFCausalProbabilityL2Mean
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (U : StrongUnitaryGroup H) (T : ℝ) (J : E →L[ℂ] H)

abbrev Ambient := WithLp 2 (H × Lp E 2 angleMeasure)

def compatibilityMap : Ambient (H := H) (E := E) →L[ℂ] Lp H 2 angleMeasure :=
  (J.compLpL 2 angleMeasure).comp (WithLp.sndL 2 ℂ H (Lp E 2 angleMeasure)) -
    (orbit U T).toContinuousLinearMap.comp (WithLp.fstL 2 ℂ H (Lp E 2 angleMeasure))

def formGraph : Submodule ℂ (Ambient (H := H) (E := E)) :=
  (compatibilityMap U T J).ker

theorem formGraph_closed : IsClosed (formGraph U T J : Set (Ambient (H := H) (E := E))) :=
  (compatibilityMap U T J).isClosed_ker

abbrev FormSpace := formGraph U T J

instance formSpace_complete [CompleteSpace H] [CompleteSpace E] : CompleteSpace (FormSpace U T J) :=
  (formGraph_closed U T J).completeSpace_coe

def embedding : FormSpace U T J →L[ℂ] H :=
  (WithLp.fstL 2 ℂ H (Lp E 2 angleMeasure)).comp (formGraph U T J).subtypeL

def sectionMap : FormSpace U T J →L[ℂ] Lp E 2 angleMeasure :=
  (WithLp.sndL 2 ℂ H (Lp E 2 angleMeasure)).comp (formGraph U T J).subtypeL

theorem compatibility (u : FormSpace U T J) :
    J.compLp (sectionMap U T J u) = orbit U T (embedding U T J u) := by
  have h := u.property
  change J.compLp (sectionMap U T J u) - orbit U T (embedding U T J u) = 0 at h
  exact sub_eq_zero.mp h

theorem embedding_injective (hJ : Function.Injective J) : Function.Injective (embedding U T J) := by
  intro u v huv
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  apply Prod.ext huv
  apply compLp_injective angleMeasure J hJ
  change J.compLp (sectionMap U T J u) = J.compLp (sectionMap U T J v)
  rw [compatibility, compatibility, huv]

theorem norm_identity (u : FormSpace U T J) :
    ‖u‖^2 = ‖embedding U T J u‖^2 + ‖sectionMap U T J u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.val

theorem embedding_norm_le (u : FormSpace U T J) : ‖embedding U T J u‖ ≤ ‖u‖ :=
  WithLp.norm_fst_le H u.val

def domain : Submodule ℂ H := (embedding U T J).range

theorem mem_domain_iff (f : H) : f ∈ domain U T J ↔
    ∃ v : Lp E 2 angleMeasure, J.compLp v = orbit U T f := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨sectionMap U T J u, compatibility U T J u⟩
  · rintro ⟨v, hv⟩
    refine ⟨⟨WithLp.toLp 2 (f,v), ?_⟩, rfl⟩
    change J.compLp v - orbit U T f = 0
    exact sub_eq_zero.mpr hv

theorem compatibility_ae (u : FormSpace U T J) :
    ∀ᵐ θ ∂angleMeasure, J (sectionMap U T J u θ) = U.action (T*θ) (embedding U T J u) := by
  have he : J.compLp (sectionMap U T J u) =ᵐ[angleMeasure]
      orbit U T (embedding U T J u) := by rw [compatibility]
  filter_upwards [J.coeFn_compLp (sectionMap U T J u), he,
    orbitState_coe U T (embedding U T J u)] with θ hJ he ho
  exact hJ.symm.trans (he.trans ho)

variable [CompleteSpace H] [CompleteSpace E]

def meanLift (u : FormSpace U T J) : E := mean angleMeasure (sectionMap U T J u)

theorem embedding_meanLift (hT : T ≠ 0) (u : FormSpace U T J) :
    J (meanLift U T J u) = average U (embedding U T J u) T := by
  rw [meanLift, ← mean_comp, compatibility, orbit_mean U T hT]

theorem fixed_mem_domain_iff (hT : T ≠ 0) (f : H) (hf : f ∈ fixedSpace U) :
    f ∈ domain U T J ↔ f ∈ J.range := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨meanLift U T J u, (embedding_meanLift U T J hT u).trans
      (average_of_fixed U T hT _ hf)⟩
  · rintro ⟨v, rfl⟩
    apply (mem_domain_iff U T J (J v)).mpr
    refine ⟨Lp.const 2 angleMeasure v, ?_⟩
    rw [comp_const]
    exact (orbit_fixed U T _ hf).symm

#print axioms formGraph_closed
#print axioms formSpace_complete
#print axioms compatibility
#print axioms embedding_injective
#print axioms norm_identity
#print axioms embedding_norm_le
#print axioms mem_domain_iff
#print axioms compatibility_ae
#print axioms embedding_meanLift
#print axioms fixed_mem_domain_iff

end
end UnifiedTheory.Audit.KFCausalAveragedFormSpace
