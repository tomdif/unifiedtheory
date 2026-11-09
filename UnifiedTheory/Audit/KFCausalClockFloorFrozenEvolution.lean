/- Autonomous evolution of the actual full Hamiltonian at a fixed
physical time, with arbitrary real time scale. All original factors
remain present. The operator domain and strong equation are identified. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
import UnifiedTheory.Audit.KFCausalPositiveResolventCommutation
import UnifiedTheory.Audit.KFCausalCommutingSkewFlowGenerator

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFrozenEvolution
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalClockFloorAveragedShiftedResolvent (shiftedResolvent resolventVector hamiltonian_resolvent shiftedResolvent_left)
open KFCausalClockFloorAveragedYosida (averaged_resolves averagedYosida averagedYosida_selfAdjoint averagedYosida_strong_limit)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k r η : ℝ)
local notation "T" => hamiltonian ε hε h hne hb m g k r
local notation "R" => fun a => shiftedResolvent ε hε h hne hb m g k a r
local notation "Y" => fun a => averagedYosida ε hε h hne hb m g k a r
local notation "c" => (-Complex.I*(η:ℂ))

theorem resolvents_commute (a b : ℝ) (ha : 0 < a) (hb' : 0 < b) : R a*R b=R b*R a :=
  KFCausalPositiveResolventCommutation.resolvents_commute T (R a) (R b) a b
    (averaged_resolves ε hε h hne hb m g k a r ha)
    (averaged_resolves ε hε h hne hb m g k b r hb')
    (shiftedResolvent_left ε hε h hne hb m g k a r ha)
    (shiftedResolvent_left ε hε h hne hb m g k b r hb')

def generator (n : ℕ) : Hilbert →L[ℂ] Hilbert := c • Y ((n:ℝ)+1)

theorem generator_skew (n : ℕ) :
    star (generator ε hε h hne hb m g k r η n) = -generator ε hε h hne hb m g k r η n := by
  have hs := averagedYosida_selfAdjoint ε hε h hne hb m g k ((n:ℝ)+1) r (by positivity)
  unfold generator
  rw [star_smul,hs]
  simp

theorem generator_commute (n q : ℕ) :
    generator ε hε h hne hb m g k r η n*generator ε hε h hne hb m g k r η q=
      generator ε hε h hne hb m g k r η q*generator ε hε h hne hb m g k r η n := by
  have hy : Y ((n:ℝ)+1)*Y ((q:ℝ)+1)=Y ((q:ℝ)+1)*Y ((n:ℝ)+1) :=
    KFCausalPositiveResolventCommutation.yosidas_commute _ _ _ _
      (resolvents_commute ε hε h hne hb m g k r _ _ (by positivity) (by positivity))
  simp only [generator,smul_mul_assoc,mul_smul_comm]
  rw [hy]

theorem generator_limit (x : (T).domain) :
    Tendsto (fun n => generator ε hε h hne hb m g k r η n (x:Hilbert)) atTop (𝓝 (c • T x)) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact ((averagedYosida_strong_limit ε hε h hne hb m g k r x).comp ht).const_smul c

def flowData : KFCausalCommutingSkewFlowLimit.Data Hilbert where
  generator := generator ε hε h hne hb m g k r η
  skew := generator_skew ε hε h hne hb m g k r η
  commute := generator_commute ε hε h hne hb m g k r η
  core := (T).domain
  dense := KFCausalClockFloorAveragedHamiltonian.hamiltonian_dense ε hε h hne hb m g k r
  cauchy := fun x hx => (generator_limit ε hε h hne hb m g k r η ⟨x,hx⟩).cauchySeq

local notation "D" => flowData ε hε h hne hb m g k r η

def evolution (t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert := KFCausalCommutingSkewFlowLimit.group D t
local notation "U" => evolution ε hε h hne hb m g k r η

theorem evolution_initial (x : Hilbert) : U 0 x=x := KFCausalCommutingSkewFlowLimit.value_initial D x

theorem evolution_compose (s t : ℝ) (x : Hilbert) : U (s+t) x=U t (U s x) :=
  KFCausalCommutingSkewFlowLimit.value_compose D s t x

theorem evolution_norm (t : ℝ) (x : Hilbert) : ‖U t x‖=‖x‖ := (U t).norm_map x

theorem evolution_continuous (x : Hilbert) : Continuous (fun t => U t x) :=
  KFCausalCommutingSkewFlowLimit.value_continuous D x

theorem approximants_uniform_limit (x : Hilbert) (L : ℝ) (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun n t => KFCausalCommutingSkewFlows.flow
      (generator ε hε h hne hb m g k r η n) (generator_skew ε hε h hne hb m g k r η n) t x)
      (fun t => U t x) atTop (Set.Icc (-L) L) :=
  KFCausalCommutingSkewFlowLimit.uniform_limit D x L hL

private theorem generator_commutes_one (n : ℕ) :
    R 1*generator ε hε h hne hb m g k r η n=generator ε hε h hne hb m g k r η n*R 1 := by
  have hy : Y ((n:ℝ)+1)*R 1=R 1*Y ((n:ℝ)+1) :=
    KFCausalPositiveResolventCommutation.yosida_commutes _ _ _
      (resolvents_commute ε hε h hne hb m g k r _ 1 (by positivity) zero_lt_one)
  simp only [generator,smul_mul_assoc,mul_smul_comm]
  exact congrArg (fun A : Hilbert →L[ℂ] Hilbert => c • A) hy.symm

theorem evolution_commutes_resolvent (t : ℝ) (x : Hilbert) : R 1 (U t x)=U t (R 1 x) :=
  KFCausalCommutingSkewFlowGenerator.commutes D (R 1)
    (generator_commutes_one ε hε h hne hb m g k r η) t x

def domainEvolution (t : ℝ) (x : (T).domain) : (T).domain :=
  resolventVector ε hε h hne hb m g k 1 r zero_lt_one (U t (T x+(x:Hilbert)))

theorem domainEvolution_coe (t : ℝ) (x : (T).domain) :
    (domainEvolution ε hε h hne hb m g k r η t x : Hilbert)=U t (x:Hilbert) := by
  have hl : R 1 (T x+(x:Hilbert))=x := by
    simpa only [one_smul] using shiftedResolvent_left ε hε h hne hb m g k 1 r zero_lt_one x
  change R 1 (U t (T x+(x:Hilbert)))=_
  rw [evolution_commutes_resolvent,hl]

theorem hamiltonian_commutes (t : ℝ) (x : (T).domain) :
    T (domainEvolution ε hε h hne hb m g k r η t x)=U t (T x) := by
  have hi := hamiltonian_resolvent ε hε h hne hb m g k 1 r zero_lt_one (U t (T x+(x:Hilbert)))
  change T (domainEvolution ε hε h hne hb m g k r η t x)=
    U t (T x+(x:Hilbert))-1 • (domainEvolution ε hε h hne hb m g k r η t x : Hilbert) at hi
  rw [one_smul,domainEvolution_coe,map_add,add_sub_cancel_right] at hi
  exact hi

theorem schrodinger (x : (T).domain) (t : ℝ) :
    HasDerivAt (fun u => U u (x:Hilbert))
      (c • T (domainEvolution ε hε h hne hb m g k r η t x)) t := by
  have hd := KFCausalCommutingSkewFlowGenerator.derivative D (x:Hilbert) (c • T x)
    (generator_limit ε hε h hne hb m g k r η x) t
  change HasDerivAt (fun u => U u (x:Hilbert)) (U t (c • T x)) t at hd
  rw [map_smul,← hamiltonian_commutes] at hd
  exact hd

#print axioms resolvents_commute
#print axioms generator_skew
#print axioms generator_commute
#print axioms generator_limit
#print axioms evolution_initial
#print axioms evolution_compose
#print axioms evolution_norm
#print axioms evolution_continuous
#print axioms approximants_uniform_limit
#print axioms evolution_commutes_resolvent
#print axioms domainEvolution_coe
#print axioms hamiltonian_commutes
#print axioms schrodinger
end
end UnifiedTheory.Audit.KFCausalClockFloorFrozenEvolution
