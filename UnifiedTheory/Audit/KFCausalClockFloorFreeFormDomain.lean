/- In the actual free clock-floor model, the weighted joint energy graph is
already closed. On the zero-charge sector, the completed averaged form domain
is exactly the clock-half domain intersected with four weighted momentum
domains. No joint-core or closure-equality premise is assumed. -/
import UnifiedTheory.Audit.KFCausalActiveJointGraph
import UnifiedTheory.Audit.KFCausalClockFloorAntisymmetricGraph
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClockFloorFreeFormDomain
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorCommonDomain (energyFactor)
open KFCausalClockFloorClockHalf (clockHalf clockHalf_selfAdjoint)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalClockFloorAntisymmetricGraph (clockMomentum_closed)
open KFCausalClockFloorJointEnergy (initialEnergy closedEnergy initialEnergy_domain)
open KFCausalStandingChargeOperator (zeroSector)

variable (ε : ℝ) (hε : 0 < ε) (h t : ℝ)
local notation "T" => energyFactor ε hε h modelDirections pointField
local notation "E" => closedEnergy ε hε h modelDirections pointField 0 0 0 t

private theorem active_closed (i : Fin 8) (hi : energyWeight 0 0 0 t i ≠ 0) :
    (T i).IsClosed := by
  fin_cases i
  · exact (clockHalf_selfAdjoint ε).isClosed
  · exact clockMomentum_closed ε hε h (modelDirections 0)
  · exact clockMomentum_closed ε hε h (modelDirections 1)
  · exact clockMomentum_closed ε hε h (modelDirections 2)
  · exact clockMomentum_closed ε hε h (modelDirections 3)
  all_goals simp [energyWeight] at hi

theorem closedEnergy_eq_initial :
    E = initialEnergy ε hε h modelDirections pointField 0 0 0 t :=
  KFCausalActiveJointGraph.jointClosed_eq_initial T (energyWeight 0 0 0 t)
    (active_closed ε hε h t)

private theorem active_weight (i : Fin 8) (hi : i.val < 5) :
    energyWeight 0 0 0 t i ≠ 0 := by
  have hs : (Real.sqrt (1/2):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have ht : ((Real.exp t*Real.sqrt (1/2):ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos (Real.exp_pos t) (Real.sqrt_pos.mpr (by norm_num))).ne'
  fin_cases i
  · exact hs
  · exact hs
  · exact hs
  · exact ht
  · exact ht
  · norm_num at hi
  · norm_num at hi
  · norm_num at hi

theorem closedEnergy_domain_active (f : Hilbert) :
    f ∈ (E).domain ↔ ∀ i : Fin 8, i.val < 5 → f ∈ (T i).domain := by
  rw [closedEnergy_eq_initial,initialEnergy_domain]
  constructor
  · intro hf i hi
    exact (Submodule.smul_mem_iff _ (active_weight t i hi)).mp (hf i)
  · intro hf i
    by_cases hi : i.val < 5
    · exact (T i).domain.smul_mem _ (hf i hi)
    · have hw : energyWeight 0 0 0 t i = 0 := by
        fin_cases i <;> simp_all [energyWeight]
      rw [hw,zero_smul]
      exact (T i).domain.zero_mem

/-- The explicit natural free form domain, without a completion or auxiliary outputs. -/
def NaturalDomain (f : Hilbert) : Prop :=
  f ∈ (clockHalf ε).domain ∧ ∀ j : Fin 4, f ∈ (clockMomentum ε h (modelDirections j)).domain

theorem closedEnergy_domain (f : Hilbert) :
    f ∈ (E).domain ↔ NaturalDomain ε h f := by
  rw [closedEnergy_domain_active]
  constructor
  · intro hf
    refine ⟨hf 0 (by decide),?_⟩
    intro j
    fin_cases j
    · exact hf 1 (by decide)
    · exact hf 2 (by decide)
    · exact hf 3 (by decide)
    · exact hf 4 (by decide)
  · rintro ⟨hc,hp⟩ i hi
    fin_cases i <;> norm_num at hi
    · exact hc
    · exact hp 0
    · exact hp 1
    · exact hp 2
    · exact hp 3

variable (hb : |h| ≤ Real.pi*ε) (hne : h ≠ 0)

/-- For a charge-invariant state the actual averaged energy domain is precisely
the explicit five-factor domain, in both directions. -/
theorem zero_charge_form_domain (f : Hilbert) (hf : f ∈ zeroSector h hne) :
    f ∈ (KFCausalClockFloorAveragedEnergy.energyOperator ε hε h hb hne 0 0 0 t).domain ↔
      NaturalDomain ε h f := by
  rw [KFCausalClockFloorAveragedEnergy.zero_sector_energy_domain ε hε h hb hne 0 0 0 t f hf]
  have he : f ∈ (KFCausalClosedGraphForm.embedding
      (KFCausalClockFloorFormHamiltonian.formData ε hε h hb 0 0 0 t)).range ↔ f ∈ (E).domain := by
    constructor
    · rintro ⟨u,rfl⟩
      exact LinearPMap.mem_domain_of_mem_graph u.property
    · intro hdom
      exact ⟨KFCausalClosedGraphForm.graphVector _ ⟨f,hdom⟩,rfl⟩
  exact he.trans (closedEnergy_domain ε hε h t f)

#print axioms closedEnergy_eq_initial
#print axioms closedEnergy_domain
#print axioms zero_charge_form_domain
end
end UnifiedTheory.Audit.KFCausalClockFloorFreeFormDomain
