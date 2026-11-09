/- Express transported initial fields through fixed bounded clock maps
and the already constructed polynomial field paths. This identifies the
actual mixed component before any charge integral or quadratic pairing. -/
import UnifiedTheory.Audit.KFCausalIntrinsicTransportedMatter

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalTransportedInitialAssembly
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (Weight fieldWeight)
open UnifiedTheory.Audit.KFCausalFieldEigenpolynomials
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition (Seed)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalFieldShearPathGraphs (state)
open UnifiedTheory.Audit.KFCausalActualPolynomialShearCurve (input_coe)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockProfileCalculus (transport transport_coe)
open UnifiedTheory.Audit.KFCausalActualTransportedField (profile)

abbrev Fields := (Transverse →L[ℝ] ℝ) → Fin 2 → Hilbert

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)

def clock (r : ℝ) : Hilbert →L[ℂ] Hilbert :=
  transport (((-Complex.I*(h:ℂ))*(r:ℂ)) • profile ε h hε hb hh) 0

def assemble (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (v : Fields) : Hilbert :=
  if i=0 then clock ε h hε hb hh 0 (v (constantField l) 0)+
    clock ε h hε hb hh (1/2) (v (scaleField l) 0)
  else clock ε h hε hb hh 0 (v (constantField l) 1)+
    clock ε h hε hb hh (1/2) (v (constantField l+scaleField l) 1-v (constantField l) 1-v (scaleField l) 1)+
    clock ε h hε hb hh 1 (v (scaleField l) 1)

def assembleL (l : Transverse →L[ℝ] ℝ) (i : Fin 2) : Fields →ₗ[ℂ] Hilbert where
  toFun := assemble ε h hε hb hh l i
  map_add' u v := by
    fin_cases i <;> simp [assemble,map_add,map_sub] <;> module
  map_smul' c u := by
    fin_cases i <;> simp [assemble,map_smul,smul_add,smul_sub]

theorem assemble_continuous (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (v : ℝ → Fields)
    (hv : ∀ m j, Continuous (fun θ => v θ m j)) :
    Continuous (fun θ => assemble ε h hε hb hh l i (v θ)) := by
  fin_cases i
  · change Continuous (fun θ => clock ε h hε hb hh 0 (v θ (constantField l) 0)+
      clock ε h hε hb hh (1/2) (v θ (scaleField l) 0))
    exact ((clock ε h hε hb hh 0).continuous.comp (hv _ _)).add
      ((clock ε h hε hb hh (1/2)).continuous.comp (hv _ _))
  · change Continuous (fun θ => clock ε h hε hb hh 0 (v θ (constantField l) 1)+
      clock ε h hε hb hh (1/2) (v θ (constantField l+scaleField l) 1-v θ (constantField l) 1-v θ (scaleField l) 1)+
      clock ε h hε hb hh 1 (v θ (scaleField l) 1))
    exact (((clock ε h hε hb hh 0).continuous.comp (hv _ _)).add
      ((clock ε h hε hb hh (1/2)).continuous.comp (((hv _ _).sub (hv _ _)).sub (hv _ _)))).add
      ((clock ε h hε hb hh 1).continuous.comp (hv _ _))

theorem assemble_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (u v : Fields)
    (hg : ∀ m j, (u m j,v m j) ∈ (shearMomentum h).graph) :
    (assemble ε h hε hb hh l i u,assemble ε h hε hb hh l i v) ∈ (shearMomentum h).graph := by
  have hc (r : ℝ) (f g : Hilbert) (hfg : (f,g) ∈ (shearMomentum h).graph) :
      (clock ε h hε hb hh r f,clock ε h hε hb hh r g) ∈ (shearMomentum h).graph :=
    KFCausalTransportedShearCurve.transported_graph _ h hh f g hfg 0
  fin_cases i
  · exact (shearMomentum h).graph.add_mem (hc 0 _ _ (hg _ _)) (hc (1/2) _ _ (hg _ _))
  · exact (shearMomentum h).graph.add_mem
      ((shearMomentum h).graph.add_mem (hc 0 _ _ (hg _ _))
        (hc (1/2) _ _ ((shearMomentum h).graph.sub_mem
          ((shearMomentum h).graph.sub_mem (hg _ _) (hg _ _)) (hg _ _))))
      (hc 1 _ _ (hg _ _))

omit hh in
theorem state_subtract (s : Seed) (P Q : Weight) (t : Interval) :
    state ε h hε hb s (subtract P Q) t = state ε h hε hb s P t-state ε h hε hb s Q t := by
  apply Lp.ext
  filter_upwards [input_coe (subtract P Q) ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    input_coe P ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    input_coe Q ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    Lp.coeFn_sub (state ε h hε hb s P t) (state ε h hε hb s Q t)] with x h0 h1 h2 hs
  change state ε h hε hb s (subtract P Q) t x = _ at h0
  change state ε h hε hb s P t x = _ at h1
  change state ε h hε hb s Q t x = _ at h2
  rw [h0,hs]
  simp only [Pi.sub_apply,h1,h2,subtract]
  ring

omit hh in
theorem state_zero (s : Seed) (t : Interval) : state ε h hε hb s zeroWeight.toWeight t = 0 := by
  apply Lp.ext
  filter_upwards [input_coe zeroWeight.toWeight ε s.a s.p h s.α s.β hε s.ha s.hα s.hβ s.hw hb s.b t,
    Lp.coeFn_zero ℂ 2 (volume : Measure KFCausalCoupledLongitudinalFlow.Configuration)] with x hx hz
  change state ε h hε hb s zeroWeight.toWeight t x = _ at hx
  rw [hx,hz]
  simp [zeroWeight,powerWeight,fieldWeight,KFCausalFieldShearDifferential.powerValue]

theorem seed_initial (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (s : Seed) :
    (∑ k, KFCausalActualTransportedField.input ε h hε hb hh s (modes l i k) 0) =
      assemble ε h hε hb hh l i (fun m j => state ε h hε hb s (fieldWeight m j) 0) := by
  have he (P : KFCausalEigenfieldShearGraphs.EigenWeight) :
      KFCausalActualTransportedField.input ε h hε hb hh s P 0 =
        clock ε h hε hb hh P.degree (state ε h hε hb s P.toWeight 0) := rfl
  simp_rw [he]
  have hz : state ε h hε hb s (fieldWeight 0 0) 0 = 0 :=
    state_zero ε h hε hb s ⟨0,by constructor <;> norm_num⟩
  have hs (P Q : Weight) : state ε h hε hb s (subtract P Q) 0 =
      state ε h hε hb s P 0-state ε h hε hb s Q 0 :=
    state_subtract ε h hε hb s P Q ⟨0,by constructor <;> norm_num⟩
  fin_cases i <;>
    simp [modes,Fin.sum_univ_succ,assemble,fixedPower,scalingPower,powerWeight,
      zeroWeight,hz,mixed,mixedWeight,hs,add_assoc]
  norm_num

#print axioms assemble_continuous
#print axioms assemble_graph
#print axioms state_subtract
#print axioms state_zero
#print axioms seed_initial
end
end UnifiedTheory.Audit.KFCausalTransportedInitialAssembly
