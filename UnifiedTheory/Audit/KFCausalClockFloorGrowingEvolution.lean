/- Autonomous unitary evolution of the actual growing Hamiltonian,
constructed as a limit of its Yosida flows. The original Hamiltonian
domain is invariant and the strong Schrodinger equation holds there. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingYosida
import UnifiedTheory.Audit.KFCausalCommutingSkewFlowGenerator

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingEvolution
noncomputable section
open Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorGrowingHamiltonian (hamiltonian)
open KFCausalClockFloorGrowingYosida (yosida yosida_selfAdjoint yosida_commute yosida_limit yosida_commutes_one)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "T" => hamiltonian ε hε h hne hb m g k
local notation "R" => KFCausalClockFloorFastResolvent.limitResolvent ε hε h hne hb m g k
local notation "c" => (-Complex.I*((1/(2*h):ℝ):ℂ))

def generator (n : ℕ) : Hilbert →L[ℂ] Hilbert := c • yosida ε hε h hne hb m g k ((n:ℝ)+1)

theorem generator_skew (n : ℕ) :
    star (generator ε hε h hne hb m g k n) = -generator ε hε h hne hb m g k n := by
  have hs := yosida_selfAdjoint ε hε h hne hb m g k ((n:ℝ)+1) (by positivity)
  unfold generator
  rw [star_smul,hs]
  simp

theorem generator_commute (n q : ℕ) :
    generator ε hε h hne hb m g k n*generator ε hε h hne hb m g k q=
      generator ε hε h hne hb m g k q*generator ε hε h hne hb m g k n := by
  simp only [generator,smul_mul_assoc,mul_smul_comm]
  rw [yosida_commute ε hε h hne hb m g k _ _ (by positivity) (by positivity)]

theorem generator_limit (x : (T).domain) :
    Tendsto (fun n => generator ε hε h hne hb m g k n (x:Hilbert)) atTop (𝓝 (c • T x)) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact ((yosida_limit ε hε h hne hb m g k x).comp ht).const_smul c

def flowData : KFCausalCommutingSkewFlowLimit.Data Hilbert where
  generator := generator ε hε h hne hb m g k
  skew := generator_skew ε hε h hne hb m g k
  commute := generator_commute ε hε h hne hb m g k
  core := (T).domain
  dense := KFCausalClockFloorGrowingHamiltonian.hamiltonian_dense ε hε h hne hb m g k
  cauchy := fun x hx => (generator_limit ε hε h hne hb m g k ⟨x,hx⟩).cauchySeq

local notation "D" => flowData ε hε h hne hb m g k

def evolution (t : ℝ) : Hilbert ≃ₗᵢ[ℂ] Hilbert := KFCausalCommutingSkewFlowLimit.group D t

theorem evolution_initial (x : Hilbert) : evolution ε hε h hne hb m g k 0 x=x :=
  KFCausalCommutingSkewFlowLimit.value_initial D x

theorem evolution_compose (s t : ℝ) (x : Hilbert) :
    evolution ε hε h hne hb m g k (s+t) x=
      evolution ε hε h hne hb m g k t (evolution ε hε h hne hb m g k s x) :=
  KFCausalCommutingSkewFlowLimit.value_compose D s t x

theorem evolution_norm (t : ℝ) (x : Hilbert) : ‖evolution ε hε h hne hb m g k t x‖=‖x‖ :=
  (evolution ε hε h hne hb m g k t).norm_map x

theorem evolution_continuous (x : Hilbert) : Continuous (fun t => evolution ε hε h hne hb m g k t x) :=
  KFCausalCommutingSkewFlowLimit.value_continuous D x

theorem approximants_uniform_limit (x : Hilbert) (L : ℝ) (hL : 0 ≤ L) :
    TendstoUniformlyOn (fun n t => KFCausalCommutingSkewFlows.flow
      (generator ε hε h hne hb m g k n) (generator_skew ε hε h hne hb m g k n) t x)
      (fun t => evolution ε hε h hne hb m g k t x) atTop (Set.Icc (-L) L) :=
  KFCausalCommutingSkewFlowLimit.uniform_limit D x L hL

private theorem generator_commutes_one (n : ℕ) :
    R*generator ε hε h hne hb m g k n=generator ε hε h hne hb m g k n*R := by
  simp only [generator,smul_mul_assoc,mul_smul_comm]
  exact congrArg (fun A : Hilbert →L[ℂ] Hilbert => c • A)
    (yosida_commutes_one ε hε h hne hb m g k _ (by positivity)).symm

theorem evolution_commutes_resolvent (t : ℝ) (x : Hilbert) :
    R (evolution ε hε h hne hb m g k t x)=evolution ε hε h hne hb m g k t (R x) :=
  KFCausalCommutingSkewFlowGenerator.commutes D R (generator_commutes_one ε hε h hne hb m g k) t x

def domainEvolution (t : ℝ) (x : (T).domain) : (T).domain :=
  KFCausalClockFloorFastResolventIdentification.limitPoint ε hε h hne hb m g k
    (evolution ε hε h hne hb m g k t (T x+(x:Hilbert)))

theorem domainEvolution_coe (t : ℝ) (x : (T).domain) :
    (domainEvolution ε hε h hne hb m g k t x : Hilbert)=evolution ε hε h hne hb m g k t (x:Hilbert) := by
  change R (evolution ε hε h hne hb m g k t (T x+(x:Hilbert)))=_
  rw [evolution_commutes_resolvent,KFCausalClockFloorFastResolventIdentification.limit_left_inverse]

theorem hamiltonian_commutes (t : ℝ) (x : (T).domain) :
    T (domainEvolution ε hε h hne hb m g k t x)=evolution ε hε h hne hb m g k t (T x) := by
  have hi := KFCausalClockFloorFastResolventIdentification.limit_right_inverse ε hε h hne hb m g k
    (evolution ε hε h hne hb m g k t (T x+(x:Hilbert)))
  change T (domainEvolution ε hε h hne hb m g k t x)+
    (domainEvolution ε hε h hne hb m g k t x : Hilbert)=
      evolution ε hε h hne hb m g k t (T x+(x:Hilbert)) at hi
  rw [domainEvolution_coe,map_add] at hi
  exact add_right_cancel hi

theorem schrodinger (x : (T).domain) (t : ℝ) :
    HasDerivAt (fun u => evolution ε hε h hne hb m g k u (x:Hilbert))
      (c • T (domainEvolution ε hε h hne hb m g k t x)) t := by
  have hd := KFCausalCommutingSkewFlowGenerator.derivative D (x:Hilbert) (c • T x)
    (generator_limit ε hε h hne hb m g k x) t
  change HasDerivAt (fun u => evolution ε hε h hne hb m g k u (x:Hilbert))
    (evolution ε hε h hne hb m g k t (c • T x)) t at hd
  rw [map_smul,← hamiltonian_commutes] at hd
  exact hd

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
end UnifiedTheory.Audit.KFCausalClockFloorGrowingEvolution
