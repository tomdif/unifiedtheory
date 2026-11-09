/- The full-clock relative potential response has a finite limit when
the physical limiting vacuum output is nonzero. The local bound depends
on the fixed family. It supplies no constant uniform over families and
does not cover a vanishing limiting output. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPotentialGraphLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredNonzeroResponseLimit
noncomputable section
open Filter
open scoped Topology
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalClockLimit
open KFCausalCorrelatedClusteredPotentialGraphLimit
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)
open KFCausalMatterOrderedDomain (pointField)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)
local notation "V" => limitingOutput f ε h a p hε hh hb ha
local notation "E" => finiteEnergy f ε h a p hε hh hb ha
local notation "R" => finiteResponse f ε h a p hε hh hb ha
local notation "E₀" => limitingEnergy f ε h a p
local notation "R₀" => limitingResponse f ε h a p

theorem limiting_energy_zero_iff : E₀ = 0 ↔ V 0 = 0 := by
  constructor
  · intro he
    rw [limiting_energy_identity f ε h a p hε hh hb ha] at he
    have hn : ‖V 0‖^2 = 0 := by nlinarith [sq_nonneg ‖V 0‖,sq_nonneg ‖V 1‖,sq_nonneg ‖V 2‖]
    exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hn)
  · intro hv
    have h1 := (physicalField pointField).graph_fst_eq_zero_snd (limit_field_graph f ε h a p hε hh hb ha) hv
    have h2 := (fieldSquare pointField).graph_fst_eq_zero_snd (limit_square_graph f ε h a p hε hh hb ha) hv
    rw [limiting_energy_identity f ε h a p hε hh hb ha,hv,h1,h2]
    norm_num

theorem limiting_energy_positive_iff : 0 < E₀ ↔ V 0 ≠ 0 := by
  have hn : 0 ≤ E₀ := by
    rw [limiting_energy_identity f ε h a p hε hh hb ha]
    positivity
  rw [lt_iff_le_and_ne]
  have he := limiting_energy_zero_iff f ε h a p hε hh hb ha
  constructor
  · rintro ⟨_,h⟩ hv
    exact h (he.mpr hv).symm
  · intro hv
    exact ⟨hn,fun h => hv (he.mp h.symm)⟩

theorem energy_eventually_positive (hv : V 0 ≠ 0) : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < E δ :=
  tendsto_const_nhds.eventually_lt (potentialEnergy_tendsto f ε h a p hε hh hb ha)
    ((limiting_energy_positive_iff f ε h a p hε hh hb ha).mpr hv)

theorem relativeResponse_tendsto (hv : V 0 ≠ 0) :
    Tendsto (fun δ => R δ/E δ) (𝓝[>] 0) (𝓝 (R₀/E₀)) :=
  (potentialResponse_tendsto f ε h a p hε hh hb ha).div
    (potentialEnergy_tendsto f ε h a p hε hh hb ha)
    (ne_of_gt ((limiting_energy_positive_iff f ε h a p hε hh hb ha).mpr hv))

theorem local_relative_bound (hv : V 0 ≠ 0) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, |R δ| ≤ (|R₀/E₀|+1)*E δ := by
  have hr := (relativeResponse_tendsto f ε h a p hε hh hb ha hv).abs.eventually_lt
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => |R₀/E₀|+1) (𝓝[>] 0) (𝓝 (|R₀/E₀|+1))) (by linarith)
  filter_upwards [energy_eventually_positive f ε h a p hε hh hb ha hv,hr] with δ hE hR
  rw [abs_div,abs_of_pos hE] at hR
  exact ((div_lt_iff₀ hE).mp hR).le

theorem relative_bound_passes_to_limit (M : ℝ)
    (hM : ∀ δ : ℝ, 0 < δ → |R δ| ≤ M*E δ) :
    |R₀| ≤ M*(‖V 0‖^2+‖V 1‖^2/2+‖V 2‖^2/4) := by
  rw [← limiting_energy_identity f ε h a p hε hh hb ha]
  apply le_of_tendsto_of_tendsto (potentialResponse_tendsto f ε h a p hε hh hb ha).abs
    ((potentialEnergy_tendsto f ε h a p hε hh hb ha).const_mul M)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hM δ hδ

theorem strict_violation_persists (M : ℝ)
    (hM : M*(‖V 0‖^2+‖V 1‖^2/2+‖V 2‖^2/4) < |R₀|) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, M*E δ < |R δ| := by
  rw [← limiting_energy_identity f ε h a p hε hh hb ha] at hM
  exact ((potentialEnergy_tendsto f ε h a p hε hh hb ha).const_mul M).eventually_lt
    (potentialResponse_tendsto f ε h a p hε hh hb ha).abs hM

#print axioms limiting_energy_zero_iff
#print axioms limiting_energy_positive_iff
#print axioms energy_eventually_positive
#print axioms relativeResponse_tendsto
#print axioms local_relative_bound
#print axioms relative_bound_passes_to_limit
#print axioms strict_violation_persists
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredNonzeroResponseLimit
