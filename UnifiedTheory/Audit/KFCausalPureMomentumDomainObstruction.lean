/- The zero-charge energy-form domain is not contained in the actual
pure-clock-momentum operator domain. The proof uses the complete averaged
form space, the closed graph theorem, and actual normalized packets.
This does not settle the weaker absolute-first-moment domain or invariance
of a smaller common domain under the full Hamiltonian propagator. -/
import UnifiedTheory.Audit.KFCausalNegativeFrequencyProjected
import Mathlib.Analysis.Normed.Operator.Banach

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalPureMomentumDomainObstruction
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
  (zeroProjection zeroProjection_fixes zeroProjection_mem zeroSector)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse
  (input inputLift momentumOutput)
open UnifiedTheory.Audit.KFCausalStructuredProjectedHamiltonian (projectedEnergy)
open UnifiedTheory.Audit.KFCausalNegativeFrequencyProjected
  (structured input_norm input_fixed projected_input_embedding bounded_energy_unbounded_momentum)

theorem closed_operator_pullback_bound
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (J : E →L[ℂ] H) (B : H →ₗ.[ℂ] H) (hB : B.IsClosed)
    (hd : ∀ u, J u ∈ B.domain) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : E) (b : H), (J u,b) ∈ B.graph → ‖b‖ ≤ K*‖u‖ := by
  let g : E →ₗ[ℂ] H := B.toFun.comp (J.toLinearMap.codRestrict B.domain hd)
  have hg (u : E) : (J u,g u) ∈ B.graph := B.mem_graph ⟨J u,hd u⟩
  have he : (g.graph : Set (E × H)) =
      (fun z : E × H => (J z.1,z.2)) ⁻¹' (B.graph : Set (H × H)) := by
    ext z
    change z.2 = g z.1 ↔ (J z.1,z.2) ∈ B.graph
    constructor
    · intro hz
      rw [hz]
      exact hg z.1
    · intro hz
      exact B.mem_graph_snd_inj' hz (hg z.1) rfl
  have hc : IsClosed (g.graph : Set (E × H)) := by
    rw [he]
    exact hB.preimage ((J.continuous.comp continuous_fst).prodMk continuous_snd)
  let G : E →L[ℂ] H := ContinuousLinearMap.ofIsClosedGraph hc
  refine ⟨‖G‖,norm_nonneg _,?_⟩
  intro u b hb
  have hv : b = G u := B.mem_graph_snd_inj' hb (hg u) rfl
  rw [hv]
  exact G.le_opNorm u

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hp : 0 < h)
  (hb : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
local notation "hh" => hp.ne'
local notation "hstrip" => KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε h hb
local notation "Full" => AveragedSpace ε hε h hstrip hh mass2 quartic vacuum t
local notation "embed" => embedding ε hε h hstrip hh mass2 quartic vacuum t
local notation "out" => energyOutput ε hε h hstrip hh mass2 quartic vacuum t
local notation "energy" => energyOperator ε hε h hstrip hh mass2 quartic vacuum t
local notation "P" => KFCausalZeroChargeStructuredResponse.project ε h hε hh hb mass2 quartic vacuum t
local notation "S" p:arg => structured a h p ha
local notation "f" p:arg => input ε h hε hh (S p)
local notation "Bf" p:arg => momentumOutput ε h hε hh (S p)
local notation "u" p:arg => P (inputLift ε h hε hh hb (S p) mass2 quartic vacuum t)
local notation "E" p:arg => projectedEnergy ε h hε hh hb (S p) mass2 quartic vacuum t

theorem projected_form_norm (p : ℝ) : ‖u p‖^2 = 2+E p := by
  have hn : ‖embed (u p)‖ = 1 :=
    (congrArg norm (projected_input_embedding ε a h hε ha hh hb p mass2 quartic vacuum t)).trans
      (input_norm ε a h hε ha hh p)
  have he : ‖u p‖^2 = 2*‖embed (u p)‖^2+E p :=
    graph_norm_identity ε hε h hstrip hh mass2 quartic vacuum t (u p)
  exact he.trans ((congrArg (fun r : ℝ => 2*r^2+E p) hn).trans (by ring))

include ha in
theorem exists_zero_charge_energy_state_outside_momentum :
    ∃ ψ : Hilbert, ψ ∈ (energy).domain ∧ ψ ∈ zeroSector h hh ∧
      ψ ∉ (pureMomentum ε hε h).domain := by
  by_contra hn
  push_neg at hn
  let J : Full →L[ℂ] Hilbert := (zeroProjection h hh).comp embed
  have hd (v : Full) : J v ∈ (pureMomentum ε hε h).domain := by
    apply hn
    · exact zeroProjection_mem_energy_domain ε hε h hstrip hh mass2 quartic vacuum t _
        ((energy_domain ε hε h hstrip hh mass2 quartic vacuum t _).mpr ⟨v,rfl⟩)
    · exact zeroProjection_mem h hh (embed v)
  obtain ⟨K,hK,hbound⟩ := closed_operator_pullback_bound J (pureMomentum ε hε h)
    (pure_closed ε hε h hh) hd
  obtain ⟨n,_,_,hgraph,henergy,hm⟩ := bounded_energy_unbounded_momentum ε a h hε ha hh hb hp
    mass2 quartic vacuum t (K*Real.sqrt (2+E 0))
  have hj : J (u (-(n:ℝ))) = f (-(n:ℝ)) := by
    change zeroProjection h hh (embed (u (-(n:ℝ)))) = _
    exact (congrArg (zeroProjection h hh)
      (projected_input_embedding ε a h hε ha hh hb (-(n:ℝ)) mass2 quartic vacuum t)).trans
      (zeroProjection_fixes h hh _ (input_fixed ε a h hε ha hh _))
  have hv : ‖u (-(n:ℝ))‖ ≤ Real.sqrt (2+E 0) := by
    calc
      _ = Real.sqrt (2+E (-(n:ℝ))) := by
        exact (Real.sqrt_sq (norm_nonneg (u (-(n:ℝ))))).symm.trans
          (congrArg Real.sqrt (projected_form_norm ε a h hε ha hp hb mass2 quartic vacuum t (-(n:ℝ))))
      _ ≤ _ := Real.sqrt_le_sqrt (add_le_add (le_refl (2:ℝ)) henergy)
  have hg : (J (u (-(n:ℝ))),Bf (-(n:ℝ))) ∈ (pureMomentum ε hε h).graph := by
    exact Eq.mp (congrArg (fun x : Hilbert => (x,Bf (-(n:ℝ))) ∈ (pureMomentum ε hε h).graph)
      hj.symm) hgraph
  have hsmall := (hbound _ _ hg).trans (mul_le_mul_of_nonneg_left hv hK)
  exact (not_lt_of_ge hsmall) hm

include ha in
theorem exists_normalized_zero_charge_energy_state_outside_momentum :
    ∃ ψ : Hilbert, ‖ψ‖ = 1 ∧ ψ ∈ (energy).domain ∧ ψ ∈ zeroSector h hh ∧
      ψ ∉ (pureMomentum ε hε h).domain := by
  obtain ⟨ψ,hf,hz,hnot⟩ := exists_zero_charge_energy_state_outside_momentum
    ε a h hε ha hp hb mass2 quartic vacuum t
  have hne : ψ ≠ 0 := by
    intro he
    apply hnot
    exact Eq.mpr (congrArg (fun x : Hilbert => x ∈ (pureMomentum ε hε h).domain) he)
      (pureMomentum ε hε h).domain.zero_mem
  have hn : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  let g : Hilbert := (‖ψ‖⁻¹:ℝ) • ψ
  have hback : (‖ψ‖:ℝ) • g = ψ := by
    dsimp only [g]
    rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
  refine ⟨g,?_,((energy).domain.restrictScalars ℝ).smul_mem _ hf,
    ((zeroSector h hh).restrictScalars ℝ).smul_mem _ hz,?_⟩
  · simp only [g,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hn]
  · intro hg
    apply hnot
    exact Eq.mp (congrArg (fun x : Hilbert => x ∈ (pureMomentum ε hε h).domain) hback)
      (((pureMomentum ε hε h).domain.restrictScalars ℝ).smul_mem _ hg)

#print axioms closed_operator_pullback_bound
#print axioms projected_form_norm
#print axioms exists_zero_charge_energy_state_outside_momentum
#print axioms exists_normalized_zero_charge_energy_state_outside_momentum
end
end UnifiedTheory.Audit.KFCausalPureMomentumDomainObstruction
