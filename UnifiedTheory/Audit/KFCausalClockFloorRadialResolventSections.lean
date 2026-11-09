/- Strong convergence of the actual radial complement regularizers on L²
orbit sections. The uniform bounds and pointwise strong limits are actual
physical multiplier results; no graph-domain assumption is introduced. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventShifted
import UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventSections
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)

private theorem section_limit {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → E →L[ℂ] E) (B : ℝ)
    (hb : ∀ i x, ‖A i x‖ ≤ B*‖x‖)
    (hA : ∀ x, Tendsto (fun i=>A i x) atTop (𝓝 x)) (f : Lp E 2 μ) :
    Tendsto (fun i => (A i).compLpL 2 μ f) atTop (𝓝 f) := by
  have hF := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have ht : Tendsto (fun i => ∫ x, ‖A i (f x)-f x‖^2 ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := atTop)
      (F := fun i x => ‖A i (f x)-f x‖^2)
      (f := fun _ => (0:ℝ)) (bound := fun x => (B+1)^2*‖f x‖^2)
      (Eventually.of_forall (fun i =>
        (((A i).continuous.comp_aestronglyMeasurable
          (Lp.aestronglyMeasurable f)).sub (Lp.aestronglyMeasurable f)).norm.pow 2))
      (Eventually.of_forall (fun i => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        have hd : ‖A i (f x)-f x‖ ≤ (B+1)*‖f x‖ :=
          (norm_sub_le _ _).trans (by nlinarith [hb i (f x)])
        exact (pow_le_pow_left₀ (norm_nonneg _) hd 2).trans_eq (by ring))))
      (hF.const_mul _) (Eventually.of_forall (fun x => by
        simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using
          ((hA (f x)).sub_const (f x)).norm.pow 2))
    simpa only [integral_zero] using hh
  have he (i : ℕ) :
      ‖(A i).compLpL 2 μ f-f‖^2=
        ∫ x, ‖A i (f x)-f x‖^2 ∂μ := by
    rw [KFCausalAveragedEnergyGraph.l2_norm_square]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((A i).compLpL 2 μ f) f,
      (A i).coeFn_compLp f] with x hs hx
    rw [hs]
    change ‖((A i).compLp f) x-f x‖^2=_
    rw [hx]
  have hn : Tendsto (fun i => ‖(A i).compLpL 2 μ f-f‖^2) atTop (𝓝 0) := by
    simpa only [he] using ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs

theorem action_section_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ε : ℝ) (hε : 0<ε) (h : ℝ) (f : Lp Hilbert 2 μ) :
    Tendsto (fun n : ℕ=>
      (KFCausalClockFloorRadialResolventRegularizer.action ε hε h ((n:ℝ)+1)
        (by positivity)).compLpL 2 μ f) atTop (𝓝 f) :=
  section_limit μ _ 1
    (fun n x=>by simpa only [one_mul] using
      KFCausalClockFloorRadialResolventRegularizer.action_norm ε hε h ((n:ℝ)+1) (by positivity) x)
    (KFCausalClockFloorRadialResolventRegularizer.sequence_tendsto ε hε h) f

theorem shifted_section_tendsto {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ε : ℝ) (hε : 0<ε) (h y : ℝ) (hy : |y|≤Real.pi*ε/6)
    (f : Lp Hilbert 2 μ) :
    Tendsto (fun n : ℕ=>
      (KFCausalClockFloorRadialResolventShifted.shifted ε hε h ((n:ℝ)+1)
        (by positivity) y hy).compLpL 2 μ f) atTop (𝓝 f) := by
  let A : ℕ → Hilbert →L[ℂ] Hilbert := fun n=>
    KFCausalClockFloorRadialResolventShifted.shifted ε hε h ((n:ℝ)+1) (by positivity) y hy
  have hb : ∀ n x, ‖A n x‖≤2*‖x‖ := by
    intro n x
    exact KFCausalClockFloorRadialResolventShifted.shifted_norm ε hε h ((n:ℝ)+1) (by positivity) y hy x
  have ht : ∀ x, Tendsto (fun n=>A n x) atTop (𝓝 x) := by
    intro x
    exact KFCausalClockFloorRadialResolventShifted.shifted_sequence_tendsto ε hε h y hy x
  exact section_limit μ A 2 hb ht f

def outputAction (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
    (y : ℝ) (hy : |y|≤Real.pi*ε/6) :
      KFCausalFiniteJointGraph.Output (Fin 8) Hilbert →L[ℂ] KFCausalFiniteJointGraph.Output (Fin 8) Hilbert :=
  KFCausalJointGraphBoundedCorrection.outputMap (fun _ : Fin 8=>
    KFCausalClockFloorRadialResolventShifted.shifted ε hε h N hN y hy)

def outputActionLp (ε : ℝ) (hε : 0<ε) (h N : ℝ) (hN : 0<N)
    (y : ℝ) (hy : |y|≤Real.pi*ε/6) :=
  (outputAction ε hε h N hN y hy).compLpL 2 KFCausalUnitIntervalOrbit.angleMeasure

private theorem diagonal_limit (A : ℕ → Hilbert →L[ℂ] Hilbert)
    (hA : ∀ x, Tendsto (fun n=>A n x) atTop (𝓝 x))
    (z : KFCausalFiniteJointGraph.Output (Fin 8) Hilbert) :
    Tendsto (fun n=>KFCausalJointGraphBoundedCorrection.outputMap (fun _ : Fin 8=>A n) z)
      atTop (𝓝 z) := by
  have ht := tendsto_pi_nhds.mpr (fun i : Fin 8=>hA (z i))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 8=>Hilbert)).continuousAt.tendsto.comp ht

theorem output_section_tendsto (ε : ℝ) (hε : 0<ε) (h y : ℝ)
    (hy : |y|≤Real.pi*ε/6) (f : KFCausalAveragedOutputRescaling.EnergyOutputSpace) :
    Tendsto (fun n : ℕ=>outputActionLp ε hε h ((n:ℝ)+1) (by positivity) y hy f)
      atTop (𝓝 f) := by
  let A : ℕ → Hilbert →L[ℂ] Hilbert := fun n=>
    KFCausalClockFloorRadialResolventShifted.shifted ε hε h ((n:ℝ)+1) (by positivity) y hy
  let B : ℕ → KFCausalFiniteJointGraph.Output (Fin 8) Hilbert →L[ℂ]
      KFCausalFiniteJointGraph.Output (Fin 8) Hilbert :=
    fun n=>KFCausalJointGraphBoundedCorrection.outputMap (fun _ : Fin 8=>A n)
  have hA : ∀ n x, ‖A n x‖≤2*‖x‖ := by
    intro n x
    exact KFCausalClockFloorRadialResolventShifted.shifted_norm ε hε h ((n:ℝ)+1) (by positivity) y hy x
  have hb : ∀ n z, ‖B n z‖≤2*‖z‖ := by
    intro n z
    exact KFCausalJointGraphBoundedCorrection.outputMap_norm (fun _ : Fin 8=>A n) 2
      (by norm_num) (fun _ x=>hA n x) z
  have ht : ∀ z, Tendsto (fun n=>B n z) atTop (𝓝 z) := by
    apply diagonal_limit A
    intro x
    exact KFCausalClockFloorRadialResolventShifted.shifted_sequence_tendsto ε hε h y hy x
  exact section_limit KFCausalUnitIntervalOrbit.angleMeasure B 2 hb ht f

#print axioms action_section_tendsto
#print axioms shifted_section_tendsto
#print axioms output_section_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventSections
