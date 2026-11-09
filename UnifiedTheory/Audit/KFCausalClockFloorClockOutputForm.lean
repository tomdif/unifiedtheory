/- The bounded eight-output clock correction and its antisymmetric
sesquilinear form. Actual clock graph pairings justify the form identity. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockEnergyCommutator
import UnifiedTheory.Audit.KFCausalUnitIntervalOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorClockOutputForm
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorClockOperator
open UnifiedTheory.Audit.KFCausalClockFloorClockEnergyCommutator
open UnifiedTheory.Audit.KFCausalClockFloorEnergyDefectAction

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : |h| ≤ 2*Real.pi*ε/3)
local notation "Y" => Lp (Output (Fin 8) Hilbert) 2 angleMeasure
local notation "R" => outputAction ε hε h hh

def deltaOutput : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert where
  toFun g := WithLp.toLp 2 (fun i => factorDifference ε hε h hh i (g i))
  map_add' f g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.add_apply,map_add]
  map_smul' c g := by
    apply PiLp.ext
    intro i
    simp only [PiLp.smul_apply,map_smul,RingHom.id_apply]
  cont := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => (factorDifference ε hε h hh i).continuous.comp (PiLp.continuous_apply 2 _ i)))

theorem deltaOutput_apply (g : Output (Fin 8) Hilbert) (i : Fin 8) :
    deltaOutput ε hε h hh g i = factorDifference ε hε h hh i (g i) := rfl

theorem deltaOutput_norm (g : Output (Fin 8) Hilbert) :
    ‖deltaOutput ε hε h hh g‖ ≤ |h| *‖g‖ := by
  simpa only [one_smul] using weighted_output_bound ε hε h hh (fun _ => 1) (fun i => g i)

def deltaLp : Y →L[ℂ] Y := (deltaOutput ε hε h hh).compLpL 2 angleMeasure

theorem deltaLp_norm (g : Y) : ‖deltaLp ε hε h hh g‖ ≤ |h| *‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(deltaOutput ε hε h hh).coeFn_compLpL g] with θ ht
  change deltaLp ε hε h hh g θ = deltaOutput ε hε h hh (g θ) at ht
  rw [ht]
  exact deltaOutput_norm ε hε h hh (g θ)

theorem clock_inner_graph (f cf g cg : Hilbert)
    (hf : (f,cf) ∈ (clockOperator ε hε).graph)
    (hg : (g,cg) ∈ (clockOperator ε hε).graph) : inner ℂ cf g = inner ℂ f cg := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(clockOperator_graph ε hε f cf).mp hf,
    (clockOperator_graph ε hε g cg).mp hg] with x hx hy
  rw [hx,hy]
  change inner ℂ ((KFCausalClockFloorFlow.clock ε x.1:ℂ) • f x) (g x) =
    inner ℂ (f x) ((KFCausalClockFloorFlow.clock ε x.1:ℂ) • g x)
  rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal]

theorem output_clock_inner (g cg k ck : Y)
    (hg : ∀ᵐ θ ∂angleMeasure, ∀ i, (g θ i,cg θ i) ∈ (clockOperator ε hε).graph)
    (hk : ∀ᵐ θ ∂angleMeasure, ∀ i, (k θ i,ck θ i) ∈ (clockOperator ε hε).graph) :
    inner ℂ cg k = inner ℂ g ck := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg,hk] with θ hgt hkt
  rw [PiLp.inner_apply,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact clock_inner_graph ε hε _ _ _ _ (hgt i) (hkt i)

theorem output_clock_graphs (w : Y) :
    ∀ᵐ θ ∂angleMeasure, ∀ i,
      ((R).compLp w θ i,((ε:ℂ) • w+deltaLp ε hε h hh ((R).compLp w)) θ i) ∈
        (clockOperator ε hε).graph := by
  filter_upwards [(R).coeFn_compLp w,
    Lp.coeFn_add ((ε:ℂ) • w) (deltaLp ε hε h hh ((R).compLp w)),
    Lp.coeFn_smul (ε:ℂ) w,(deltaOutput ε hε h hh).coeFn_compLpL ((R).compLp w)]
    with θ hr ha hs hd
  change deltaLp ε hε h hh ((R).compLp w) θ = deltaOutput ε hε h hh ((R).compLp w θ) at hd
  intro i
  simp only [ha,Pi.add_apply,hs,Pi.smul_apply,hd,hr,PiLp.add_apply,PiLp.smul_apply,
    deltaOutput_apply,outputAction_apply]
  exact clock_factorAction_graph ε hε h hh i (w θ i)

def response (g k : Y) : ℂ :=
  inner ℂ (deltaLp ε hε h hh g) k-inner ℂ g (deltaLp ε hε h hh k)

theorem response_norm (g k : Y) : ‖response ε hε h hh g k‖ ≤ 2*|h| *‖g‖*‖k‖ := by
  calc
    _ ≤ ‖inner ℂ (deltaLp ε hε h hh g) k‖+‖inner ℂ g (deltaLp ε hε h hh k)‖ := norm_sub_le _ _
    _ ≤ (|h| *‖g‖)*‖k‖+‖g‖*(|h| *‖k‖) := add_le_add
      ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (deltaLp_norm ε hε h hh g) (norm_nonneg k)))
      ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (deltaLp_norm ε hε h hh k) (norm_nonneg g)))
    _ = _ := by ring

theorem response_continuous : Continuous (fun z : Y × Y => response ε hε h hh z.1 z.2) :=
  (((deltaLp ε hε h hh).continuous.comp continuous_fst).inner continuous_snd).sub
    (continuous_fst.inner ((deltaLp ε hε h hh).continuous.comp continuous_snd))

theorem response_identity (g cg k ck : Y)
    (hg : ∀ᵐ θ ∂angleMeasure, ∀ i,
      (g θ i,(cg+deltaLp ε hε h hh g) θ i) ∈ (clockOperator ε hε).graph)
    (hk : ∀ᵐ θ ∂angleMeasure, ∀ i,
      (k θ i,(ck+deltaLp ε hε h hh k) θ i) ∈ (clockOperator ε hε).graph) :
    inner ℂ g ck-inner ℂ cg k = response ε hε h hh g k := by
  have he := output_clock_inner ε hε g (cg+deltaLp ε hε h hh g) k (ck+deltaLp ε hε h hh k) hg hk
  simp only [inner_add_left,inner_add_right] at he
  unfold response
  linear_combination -he

#print axioms deltaOutput_apply
#print axioms deltaOutput_norm
#print axioms deltaLp_norm
#print axioms clock_inner_graph
#print axioms output_clock_inner
#print axioms output_clock_graphs
#print axioms response_norm
#print axioms response_continuous
#print axioms response_identity
end
end UnifiedTheory.Audit.KFCausalClockFloorClockOutputForm
