/- The full Hamiltonian frozen at a fixed physical time preserves its
complete energy form. Its weak equation holds for every form state,
with all static and growing factors retained. -/
import UnifiedTheory.Audit.KFCausalClockFloorFrozenEvolution
import UnifiedTheory.Audit.KFCausalUnitaryFormWeakEquation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFrozenFormEvolution
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedFormTransport (FormSpace)

private theorem output_norm_preserved {V H K : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] (J : V → H) (B : V → K)
    (E : V ≃ₗᵢ[ℂ] V) (U : H ≃ₗᵢ[ℂ] H) (he : ∀ v, J (E v)=U (J v))
    (hn : ∀ v, ‖v‖^2=‖J v‖^2+‖B v‖^2) (v : V) : ‖B (E v)‖=‖B v‖ := by
  have h₁ := hn (E v)
  rw [E.norm_map,he,U.norm_map] at h₁
  nlinarith only [h₁,hn v,norm_nonneg (B (E v)),norm_nonneg (B v)]

private theorem output_pairing_preserved {V H K : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (J : V → H) (B : V → K)
    (E : V ≃ₗᵢ[ℂ] V) (U : H ≃ₗᵢ[ℂ] H) (he : ∀ v, J (E v)=U (J v))
    (hn : ∀ v z, inner ℂ v z=inner ℂ (J v) (J z)+inner ℂ (B v) (B z)) (v z : V) :
    inner ℂ (B (E v)) (B (E z))=inner ℂ (B v) (B z) := by
  have hp := E.inner_map_map v z
  rw [hn,hn,he,he,U.inner_map_map] at hp
  exact add_left_cancel hp

private theorem closedGraph_weak {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (G : KFCausalClosedGraphForm.Data H K)
    (F : KFCausalUnitaryFormLift.Data (KFCausalClosedGraphForm.embedding G)
      (KFCausalClosedGraphForm.embedding_injective G) (KFCausalClosedGraphForm.embedding_dense G))
    (a : ℝ) (hder : ∀ x : (KFCausalClosedGraphForm.hamiltonian G).domain, ∀ t,
      HasDerivAt (fun u => F.physical u (x:H))
        ((-Complex.I*(a:ℂ)) • KFCausalClosedGraphForm.hamiltonian G (F.domainMap t x)) t)
    (v z : KFCausalClosedGraphForm.FormSpace G) (t : ℝ) :
    HasDerivAt (fun u => inner ℂ (F.physical u (KFCausalClosedGraphForm.embedding G v))
      (KFCausalClosedGraphForm.embedding G z))
      ((Complex.I*(a:ℂ))*inner ℂ
        (KFCausalClosedGraphForm.energyOutput G (KFCausalUnitaryFormLift.evolution
          (KFCausalClosedGraphForm.embedding G) (KFCausalClosedGraphForm.embedding_injective G)
          (KFCausalClosedGraphForm.embedding_dense G) F t v))
        (KFCausalClosedGraphForm.energyOutput G z)) t := by
  have hp := KFCausalUnitaryFormWeakEquation.weak_equation (KFCausalClosedGraphForm.embedding G)
    (KFCausalClosedGraphForm.embedding_injective G) (KFCausalClosedGraphForm.embedding_dense G) F
    (-Complex.I*(a:ℂ)) hder v z t
  have hc : star (-Complex.I*(a:ℂ))=Complex.I*(a:ℂ) := by simp
  rw [hc,KFCausalClosedGraphForm.form_inner_identity,add_sub_cancel_left] at hp
  exact hp

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k r η : ℝ)
local notation "D" => KFCausalClockFloorAveragedHamiltonian.formData ε hε h hne hb m g k r
local notation "W" => FormSpace ε hε h hne hb m g k r
local notation "J" => KFCausalClosedGraphForm.embedding D
local notation "B" => KFCausalClosedGraphForm.energyOutput D
local notation "hi" => KFCausalClosedGraphForm.embedding_injective D
local notation "hd" => KFCausalClosedGraphForm.embedding_dense D
local notation "U" => KFCausalClockFloorFrozenEvolution.evolution ε hε h hne hb m g k r η

def liftData : KFCausalUnitaryFormLift.Data J hi hd where
  physical := U
  initial := KFCausalClockFloorFrozenEvolution.evolution_initial ε hε h hne hb m g k r η
  compose := KFCausalClockFloorFrozenEvolution.evolution_compose ε hε h hne hb m g k r η
  continuous := KFCausalClockFloorFrozenEvolution.evolution_continuous ε hε h hne hb m g k r η
  domainMap := KFCausalClockFloorFrozenEvolution.domainEvolution ε hε h hne hb m g k r η
  domain_coe := KFCausalClockFloorFrozenEvolution.domainEvolution_coe ε hε h hne hb m g k r η
  intertwine := KFCausalClockFloorFrozenEvolution.hamiltonian_commutes ε hε h hne hb m g k r η

local notation "L" => liftData ε hε h hne hb m g k r η

def evolution (t : ℝ) : W ≃ₗᵢ[ℂ] W := KFCausalUnitaryFormLift.evolution J hi hd L t
local notation "E" => evolution ε hε h hne hb m g k r η

theorem evolution_embedding (t : ℝ) (v : W) : J (E t v)=U t (J v) :=
  KFCausalUnitaryFormLift.evolution_embedding J hi hd L t v

theorem evolution_initial (v : W) : E 0 v=v :=
  KFCausalUnitaryFormLift.evolution_initial J hi hd L v

theorem evolution_compose (s t : ℝ) (v : W) : E (s+t) v=E t (E s v) :=
  KFCausalUnitaryFormLift.evolution_compose J hi hd L s t v

theorem evolution_norm (t : ℝ) (v : W) : ‖E t v‖=‖v‖ := (E t).norm_map v

theorem evolution_continuous (v : W) : Continuous (fun t => E t v) :=
  KFCausalUnitaryFormLift.evolution_continuous J hi hd L v

theorem physical_norm (t : ℝ) (v : W) : ‖J (E t v)‖=‖J v‖ := by
  rw [evolution_embedding,(U t).norm_map]

theorem energy_preserved (t : ℝ) (v : W) : ‖B (E t v)‖=‖B v‖ :=
  output_norm_preserved J B (E t) (U t) (evolution_embedding ε hε h hne hb m g k r η t)
    (KFCausalClosedGraphForm.form_norm_identity D) v

theorem energy_pairing (t : ℝ) (v z : W) : inner ℂ (B (E t v)) (B (E t z))=inner ℂ (B v) (B z) :=
  output_pairing_preserved J B (E t) (U t) (evolution_embedding ε hε h hne hb m g k r η t)
    (KFCausalClosedGraphForm.form_inner_identity D) v z

theorem weak_schrodinger (v z : W) (t : ℝ) :
    HasDerivAt (fun u => inner ℂ (U u (J v)) (J z))
      ((Complex.I*(η:ℂ))*inner ℂ (B (E t v)) (B z)) t :=
  closedGraph_weak D L η
    (KFCausalClockFloorFrozenEvolution.schrodinger ε hε h hne hb m g k r η) v z t

#print axioms evolution_embedding
#print axioms evolution_initial
#print axioms evolution_compose
#print axioms evolution_norm
#print axioms evolution_continuous
#print axioms physical_norm
#print axioms energy_preserved
#print axioms energy_pairing
#print axioms weak_schrodinger
end
end UnifiedTheory.Audit.KFCausalClockFloorFrozenFormEvolution
