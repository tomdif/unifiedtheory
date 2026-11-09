/- The seam mismatch minimized over the actual compact spatial gauge group.
An optimizer is used only to evaluate an invariant kernel. No regular gauge
fixing, adaptive Haar substitution, or small ground-law average is assumed. -/
import UnifiedTheory.Clay.YangMills.WilsonSeamCommutatorComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSeamGaugePenalty
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonSlabGauge WilsonCenterTwist
open WilsonSeamCommutatorGeometry WilsonGroundLocalComparison

variable (n : ℕ) [NeZero n]

theorem representative_continuous (i : Fin 3) (u : Slice n) :
    Continuous (fun h : SliceGauge n Q => rootMismatch n i (gaugeSlice h u)) := by
  apply (rootMismatch_continuous n i).comp
  unfold gaugeSlice
  fun_prop

theorem exists_minimizer (i : Fin 3) (u : Slice n) :
    ∃ h : SliceGauge n Q, ∀ k : SliceGauge n Q,
      rootMismatch n i (gaugeSlice h u) ≤ rootMismatch n i (gaugeSlice k u) := by
  obtain ⟨h, _, hh⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (SliceGauge n Q)).Nonempty)
    (representative_continuous n i u).continuousOn
  exact ⟨h, fun k => hh (Set.mem_univ k)⟩

def minimizer (i : Fin 3) (u : Slice n) : SliceGauge n Q := (exists_minimizer n i u).choose

def penalty (i : Fin 3) (u : Slice n) : ℝ :=
  rootMismatch n i (gaugeSlice (minimizer n i u) u)

theorem penalty_nonneg (i : Fin 3) (u : Slice n) : 0 ≤ penalty n i u :=
  rootMismatch_nonneg n i _

theorem penalty_le (i : Fin 3) (u : Slice n) (h : SliceGauge n Q) :
    penalty n i u ≤ rootMismatch n i (gaugeSlice h u) :=
  (exists_minimizer n i u).choose_spec h

theorem penalty_le_root (i : Fin 3) (u : Slice n) :
    penalty n i u ≤ rootMismatch n i u := by
  simpa only [gaugeSlice_one] using penalty_le n i u 1

theorem penalty_eq_sInf (i : Fin 3) (u : Slice n) :
    penalty n i u = sInf ((fun h : SliceGauge n Q => rootMismatch n i (gaugeSlice h u)) ''
      Set.univ) := by
  have hb : BddBelow ((fun h : SliceGauge n Q => rootMismatch n i (gaugeSlice h u)) ''
      Set.univ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨h, _, rfl⟩
    exact rootMismatch_nonneg n i _
  apply le_antisymm
  · apply le_csInf
      (Set.image_nonempty.mpr (Set.univ_nonempty : (Set.univ : Set (SliceGauge n Q)).Nonempty))
    rintro _ ⟨h, _, rfl⟩
    exact penalty_le n i u h
  · exact csInf_le hb ⟨minimizer n i u, Set.mem_univ _, rfl⟩

/-- The minimum value is continuous even though no continuous minimizer is claimed. -/
theorem penalty_continuous (i : Fin 3) : Continuous (penalty n i) := by
  have hc : Continuous (fun z : Slice n × SliceGauge n Q =>
      rootMismatch n i (gaugeSlice z.2 z.1)) := by
    apply (rootMismatch_continuous n i).comp
    unfold gaugeSlice
    fun_prop
  have hh := isCompact_univ.continuous_sInf
    (f := fun u : Slice n => fun h : SliceGauge n Q => rootMismatch n i (gaugeSlice h u)) hc
  simpa only [← penalty_eq_sInf] using hh

theorem penalty_gauge_le (i : Fin 3) (u : Slice n) (h : SliceGauge n Q) :
    penalty n i (gaugeSlice h u) ≤ penalty n i u := by
  have hh := penalty_le n i (gaugeSlice h u) (minimizer n i u * h⁻¹)
  rw [← gaugeSlice_mul, mul_assoc, inv_mul_cancel, mul_one] at hh
  exact hh

theorem penalty_gauge (i : Fin 3) (u : Slice n) (h : SliceGauge n Q) :
    penalty n i (gaugeSlice h u) = penalty n i u := by
  have hh := penalty_gauge_le n i (gaugeSlice h u) h⁻¹
  rw [← gaugeSlice_mul, inv_mul_cancel, gaugeSlice_one] at hh
  exact le_antisymm (penalty_gauge_le n i u h) hh

theorem penalty_twist_le (i : Fin 3) (u : Slice n) :
    penalty n i (twist n i u) ≤ penalty n i u := by
  have hh := penalty_le n i (twist n i u) (minimizer n i u)
  rw [← twist_gauge, rootMismatch_twist] at hh
  exact hh

theorem penalty_twist (i : Fin 3) (u : Slice n) :
    penalty n i (twist n i u) = penalty n i u := by
  have hh := penalty_twist_le n i (twist n i u)
  rw [twist_involution] at hh
  exact le_antisymm (penalty_twist_le n i u) hh

theorem penalty_zero_of_commuting_representative (i : Fin 3) (u : Slice n)
    (h : SliceGauge n Q) (hu : ∀ e, Commute (WilsonSeamRoot.root n) (gaugeSlice h u e)) :
    penalty n i u = 0 := by
  have hh := penalty_le n i u h
  rw [rootMismatch_zero n i _ hu] at hh
  exact le_antisymm hh (penalty_nonneg n i u)

theorem penalty_identity (i : Fin 3) : penalty n i 1 = 0 := by
  apply penalty_zero_of_commuting_representative n i 1 1
  intro e
  simp only [gaugeSlice_one, Pi.one_apply]
  exact Commute.one_right _

theorem small_penalty_open (i : Fin 3) (ε : ℝ) :
    IsOpen {u : Slice n | penalty n i u < ε} :=
  isOpen_lt (penalty_continuous n i) continuous_const

/-- A genuine positive-ground-measure neighborhood exists at each finite cutoff.
No quantitative lower mass, uniform in the cutoff, is asserted. -/
theorem small_penalty_positive (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (hε : 0 < ε) :
    0 < WilsonGroundHeatBath.groundLaw n β hβ {u : Slice n | penalty n i u < ε} := by
  letI := WilsonGroundVarianceBudget.ground_openPos n β hβ
  exact (small_penalty_open n i ε).measure_pos (WilsonGroundHeatBath.groundLaw n β hβ)
    ⟨1, by simpa only [Set.mem_setOf_eq, penalty_identity] using hε⟩

/-- The minimizer evaluates an already invariant transition; it changes no integration measure. -/
theorem physical_likelihood_bounds (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    transition n β hβ (twist n i u) v / transition n β hβ u v ∈
      Set.Icc (Real.exp (-(β * (Real.pi^2 * n + penalty n i u))))
        (Real.exp (β * (Real.pi^2 * n + penalty n i u))) := by
  have hh := WilsonSeamCommutatorComparison.physical_likelihood_bounds n i β hβ
    (gaugeSlice (minimizer n i u) u) v
  rw [twist_gauge, WilsonPhysicalResponse.full_transition_gauge_left,
    WilsonPhysicalResponse.full_transition_gauge_left] at hh
  exact hh

theorem bounded_penalty_likelihood (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n)
    (ε : ℝ) (hu : penalty n i u ≤ ε) :
    transition n β hβ (twist n i u) v / transition n β hβ u v ∈
      Set.Icc (Real.exp (-(β * (Real.pi^2 * n + ε))))
        (Real.exp (β * (Real.pi^2 * n + ε))) := by
  have hh := physical_likelihood_bounds n i β hβ u v
  have hc : β * (Real.pi^2 * n + penalty n i u) ≤ β * (Real.pi^2 * n + ε) :=
    mul_le_mul_of_nonneg_left (by linarith only [hu]) hβ
  exact ⟨(Real.exp_le_exp.mpr (neg_le_neg hc)).trans hh.1,
    hh.2.trans (Real.exp_le_exp.mpr hc)⟩

end
end UnifiedTheory.Clay.YangMills.WilsonSeamGaugePenalty
