/- The radial resolvent regularizer and the radial Yosida symbol action commute
with the bounded inverse half-clock, the bounded clock-defect multiplier, and
the complex clock-Gaussian multipliers. Consequently both radial operators
preserve the unbounded half-clock and full-clock domains and commute with both
unbounded clock operators, and the radial resolvent sequence converges strongly
in the half-clock and full-clock graph norms. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventOperator
import UnifiedTheory.Audit.KFCausalClockFloorChargeClockHalf
import UnifiedTheory.Audit.KFCausalClockFloorChargeDefect
import UnifiedTheory.Audit.KFCausalClockFloorClockOperator
import UnifiedTheory.Audit.KFCausalClockFloorPureClockClockResponse
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingTransport

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventClockCommutation
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockChargeMultiplier (clockMultiplier chargeCoordinates_multiplier jointMultiplier_coe)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorDefectOperator (defectOperator)
open KFCausalClockFloorCanonicalDefect (defect)
open KFCausalClockFloorChargeClockHalf (normalizedInverse normalizedInverse_measurable
  normalizedInverse_bound normalizedInverse_operator)
open KFCausalClockFloorChargeDefect (chargeCoordinates_defect jointDefect_coe)
open KFCausalClockFloorClockOperator (clockOperator clock_defect_graph defect_clock)
open KFCausalClockFloorPureClockClockResponse (half_graph)
open KFCausalClockFloorRadialYosidaSymbol (symbol)
open KFCausalClockFloorRadialResolventRegularizer (multiplier action action_coe
  action_norm sequence_tendsto)

private theorem charge_multiplier_commute
    (w₁ w₂ : Joint 2 4 → ℂ) (A B : Hilbert →L[ℂ] Hilbert)
    (hA : ∀ f, chargeCoordinates (A f) =ᵐ[volume]
      fun x => w₁ x * chargeCoordinates f x)
    (hB : ∀ f, chargeCoordinates (B f) =ᵐ[volume]
      fun x => w₂ x * chargeCoordinates f x)
    (f : Hilbert) :
    A (B f) = B (A f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [hA (B f), hB f, hB (A f), hA f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)

local notation "L" => inverseL ε hε
local notation "D" => defectOperator ε hε
local notation "J" => action ε hε h N hN
local notation "M" => KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN

theorem defectOperator_coordinates (f : Hilbert) :
    chargeCoordinates (D f) =ᵐ[volume]
      fun x => (defect ε (x (.inr 0)) : ℂ) * chargeCoordinates f x := by
  rw [chargeCoordinates_defect ε hε f]
  exact jointDefect_coe ε hε (chargeCoordinates f)

theorem normalizedInverse_coordinates (f : Hilbert) :
    chargeCoordinates (clockMultiplier (normalizedInverse ε)
      (normalizedInverse_measurable ε) (normalizedInverse_bound ε hε) f) =ᵐ[volume]
      fun x => normalizedInverse ε (x (.inr 0)) * chargeCoordinates f x := by
  rw [chargeCoordinates_multiplier]
  exact jointMultiplier_coe _ _ _ (chargeCoordinates f)

private theorem commute_inverseL_of_charge_multiplier
    (w : Joint 2 4 → ℂ) (A : Hilbert →L[ℂ] Hilbert)
    (hA : ∀ f, chargeCoordinates (A f) =ᵐ[volume]
      fun x => w x * chargeCoordinates f x)
    (f : Hilbert) :
    A (L f) = L (A f) := by
  have hc : (Real.sqrt ε : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hε).ne'
  have hm := charge_multiplier_commute w
    (fun x => normalizedInverse ε (x (.inr 0))) A
    (clockMultiplier (normalizedInverse ε)
      (normalizedInverse_measurable ε) (normalizedInverse_bound ε hε))
    hA (normalizedInverse_coordinates ε hε) f
  rw [normalizedInverse_operator ε hε f,
    normalizedInverse_operator ε hε (A f), map_smul] at hm
  exact smul_right_injective _ hc hm

theorem clockOperator_graph_iff_defect (f g : Hilbert) :
    (f, g) ∈ (clockOperator ε hε).graph ↔ D g = (ε : ℂ) • f := by
  constructor
  · exact defect_clock ε hε f g
  · intro hd
    have hg := (clockOperator ε hε).graph.smul_mem (ε : ℂ)⁻¹ (clock_defect_graph ε hε g)
    change ((ε : ℂ)⁻¹ • D g, (ε : ℂ)⁻¹ • (ε : ℂ) • g) ∈
      (clockOperator ε hε).graph at hg
    have hc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
    rw [hd, inv_smul_smul₀ hc, inv_smul_smul₀ hc] at hg
    exact hg

theorem resolvent_inverseL_commute (f : Hilbert) :
    J (L f) = L (J f) :=
  commute_inverseL_of_charge_multiplier ε hε
    (fun x => (multiplier ε h N x : ℂ)) J (action_coe ε hε h N hN) f

theorem yosida_inverseL_commute (f : Hilbert) :
    M (L f) = L (M f) :=
  commute_inverseL_of_charge_multiplier ε hε
    (fun x => (symbol ε h N x : ℂ)) M
    (KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN) f

theorem resolvent_defect_commute (f : Hilbert) :
    J (D f) = D (J f) :=
  charge_multiplier_commute
    (fun x => (multiplier ε h N x : ℂ))
    (fun x => (defect ε (x (.inr 0)) : ℂ))
    J D (action_coe ε hε h N hN) (defectOperator_coordinates ε hε) f

theorem yosida_defect_commute (f : Hilbert) :
    M (D f) = D (M f) :=
  charge_multiplier_commute
    (fun x => (symbol ε h N x : ℂ))
    (fun x => (defect ε (x (.inr 0)) : ℂ))
    M D (KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN)
    (defectOperator_coordinates ε hε) f

theorem resolvent_gaussian_commute (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert) :
    J (KFCausalClockFloorGaussianGrowingTransport.action ε a ha y f) =
      KFCausalClockFloorGaussianGrowingTransport.action ε a ha y (J f) :=
  charge_multiplier_commute
    (fun x => (multiplier ε h N x : ℂ))
    (fun x => KFCausalClockFloorGaussianGrowingTransport.line ε a y (x (.inr 0)))
    J (KFCausalClockFloorGaussianGrowingTransport.action ε a ha y)
    (action_coe ε hε h N hN)
    (KFCausalClockFloorGaussianGrowingTransport.action_coordinates ε a ha y) f

theorem yosida_gaussian_commute (a : ℝ) (ha : 0 ≤ a) (y : ℝ) (f : Hilbert) :
    M (KFCausalClockFloorGaussianGrowingTransport.action ε a ha y f) =
      KFCausalClockFloorGaussianGrowingTransport.action ε a ha y (M f) :=
  charge_multiplier_commute
    (fun x => (symbol ε h N x : ℂ))
    (fun x => KFCausalClockFloorGaussianGrowingTransport.line ε a y (x (.inr 0)))
    M (KFCausalClockFloorGaussianGrowingTransport.action ε a ha y)
    (KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN)
    (KFCausalClockFloorGaussianGrowingTransport.action_coordinates ε a ha y) f

theorem resolvent_clockHalf_graph (f g : Hilbert)
    (hfg : (f, g) ∈ (clockHalf ε).graph) :
    (J f, J g) ∈ (clockHalf ε).graph := by
  rw [half_graph ε hε] at hfg ⊢
  rw [hfg, resolvent_inverseL_commute ε hε h N hN g]

theorem resolvent_clockHalf_domain (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    J f ∈ (clockHalf ε).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (resolvent_clockHalf_graph ε hε h N hN f (clockHalf ε ⟨f, hf⟩)
      ((clockHalf ε).mem_graph ⟨f, hf⟩))

theorem resolvent_clockHalf_commute (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    clockHalf ε ⟨J f, resolvent_clockHalf_domain ε hε h N hN f hf⟩ =
      J (clockHalf ε ⟨f, hf⟩) :=
  (clockHalf ε).mem_graph_snd_inj'
    ((clockHalf ε).mem_graph ⟨J f, resolvent_clockHalf_domain ε hε h N hN f hf⟩)
    (resolvent_clockHalf_graph ε hε h N hN f (clockHalf ε ⟨f, hf⟩)
      ((clockHalf ε).mem_graph ⟨f, hf⟩)) rfl

theorem resolvent_clockHalf_norm_le (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    ‖clockHalf ε ⟨J f, resolvent_clockHalf_domain ε hε h N hN f hf⟩‖ ≤
      ‖clockHalf ε ⟨f, hf⟩‖ := by
  rw [resolvent_clockHalf_commute ε hε h N hN f hf]
  exact action_norm ε hε h N hN (clockHalf ε ⟨f, hf⟩)

theorem resolvent_clockHalf_graph_tendsto (f g : Hilbert) :
    Tendsto (fun n : ℕ =>
      (action ε hε h ((n : ℝ) + 1) (by positivity) f,
        action ε hε h ((n : ℝ) + 1) (by positivity) g))
      atTop (𝓝 (f, g)) :=
  (sequence_tendsto ε hε h f).prodMk_nhds (sequence_tendsto ε hε h g)

theorem resolvent_clockHalf_tendsto (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    Tendsto (fun n : ℕ =>
      clockHalf ε ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        resolvent_clockHalf_domain ε hε h ((n : ℝ) + 1) (by positivity) f hf⟩)
      atTop (𝓝 (clockHalf ε ⟨f, hf⟩)) :=
  (sequence_tendsto ε hε h (clockHalf ε ⟨f, hf⟩)).congr'
    (Eventually.of_forall (fun n =>
      (resolvent_clockHalf_commute ε hε h ((n : ℝ) + 1) (by positivity) f hf).symm))

theorem yosida_clockHalf_graph (f g : Hilbert)
    (hfg : (f, g) ∈ (clockHalf ε).graph) :
    (M f, M g) ∈ (clockHalf ε).graph := by
  rw [half_graph ε hε] at hfg ⊢
  rw [hfg, yosida_inverseL_commute ε hε h N hN g]

theorem yosida_clockHalf_domain (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    M f ∈ (clockHalf ε).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (yosida_clockHalf_graph ε hε h N hN f (clockHalf ε ⟨f, hf⟩)
      ((clockHalf ε).mem_graph ⟨f, hf⟩))

theorem yosida_clockHalf_commute (f : Hilbert)
    (hf : f ∈ (clockHalf ε).domain) :
    clockHalf ε ⟨M f, yosida_clockHalf_domain ε hε h N hN f hf⟩ =
      M (clockHalf ε ⟨f, hf⟩) :=
  (clockHalf ε).mem_graph_snd_inj'
    ((clockHalf ε).mem_graph ⟨M f, yosida_clockHalf_domain ε hε h N hN f hf⟩)
    (yosida_clockHalf_graph ε hε h N hN f (clockHalf ε ⟨f, hf⟩)
      ((clockHalf ε).mem_graph ⟨f, hf⟩)) rfl

theorem resolvent_clockOperator_graph (f g : Hilbert)
    (hfg : (f, g) ∈ (clockOperator ε hε).graph) :
    (J f, J g) ∈ (clockOperator ε hε).graph := by
  rw [clockOperator_graph_iff_defect ε hε] at hfg ⊢
  rw [← resolvent_defect_commute ε hε h N hN g, hfg, map_smul]

theorem resolvent_clockOperator_domain (f : Hilbert)
    (hf : f ∈ (clockOperator ε hε).domain) :
    J f ∈ (clockOperator ε hε).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (resolvent_clockOperator_graph ε hε h N hN f (clockOperator ε hε ⟨f, hf⟩)
      ((clockOperator ε hε).mem_graph ⟨f, hf⟩))

theorem resolvent_clockOperator_commute (f : Hilbert)
    (hf : f ∈ (clockOperator ε hε).domain) :
    clockOperator ε hε ⟨J f, resolvent_clockOperator_domain ε hε h N hN f hf⟩ =
      J (clockOperator ε hε ⟨f, hf⟩) :=
  (clockOperator ε hε).mem_graph_snd_inj'
    ((clockOperator ε hε).mem_graph ⟨J f, resolvent_clockOperator_domain ε hε h N hN f hf⟩)
    (resolvent_clockOperator_graph ε hε h N hN f (clockOperator ε hε ⟨f, hf⟩)
      ((clockOperator ε hε).mem_graph ⟨f, hf⟩)) rfl

theorem resolvent_clockOperator_tendsto (f : Hilbert)
    (hf : f ∈ (clockOperator ε hε).domain) :
    Tendsto (fun n : ℕ =>
      clockOperator ε hε ⟨action ε hε h ((n : ℝ) + 1) (by positivity) f,
        resolvent_clockOperator_domain ε hε h ((n : ℝ) + 1) (by positivity) f hf⟩)
      atTop (𝓝 (clockOperator ε hε ⟨f, hf⟩)) :=
  (sequence_tendsto ε hε h (clockOperator ε hε ⟨f, hf⟩)).congr'
    (Eventually.of_forall (fun n =>
      (resolvent_clockOperator_commute ε hε h ((n : ℝ) + 1) (by positivity) f hf).symm))

theorem yosida_clockOperator_graph (f g : Hilbert)
    (hfg : (f, g) ∈ (clockOperator ε hε).graph) :
    (M f, M g) ∈ (clockOperator ε hε).graph := by
  rw [clockOperator_graph_iff_defect ε hε] at hfg ⊢
  rw [← yosida_defect_commute ε hε h N hN g, hfg, map_smul]

theorem yosida_clockOperator_domain (f : Hilbert)
    (hf : f ∈ (clockOperator ε hε).domain) :
    M f ∈ (clockOperator ε hε).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (yosida_clockOperator_graph ε hε h N hN f (clockOperator ε hε ⟨f, hf⟩)
      ((clockOperator ε hε).mem_graph ⟨f, hf⟩))

theorem yosida_clockOperator_commute (f : Hilbert)
    (hf : f ∈ (clockOperator ε hε).domain) :
    clockOperator ε hε ⟨M f, yosida_clockOperator_domain ε hε h N hN f hf⟩ =
      M (clockOperator ε hε ⟨f, hf⟩) :=
  (clockOperator ε hε).mem_graph_snd_inj'
    ((clockOperator ε hε).mem_graph ⟨M f, yosida_clockOperator_domain ε hε h N hN f hf⟩)
    (yosida_clockOperator_graph ε hε h N hN f (clockOperator ε hε ⟨f, hf⟩)
      ((clockOperator ε hε).mem_graph ⟨f, hf⟩)) rfl

#print axioms defectOperator_coordinates
#print axioms normalizedInverse_coordinates
#print axioms clockOperator_graph_iff_defect
#print axioms resolvent_inverseL_commute
#print axioms yosida_inverseL_commute
#print axioms resolvent_defect_commute
#print axioms yosida_defect_commute
#print axioms resolvent_gaussian_commute
#print axioms yosida_gaussian_commute
#print axioms resolvent_clockHalf_graph
#print axioms resolvent_clockHalf_domain
#print axioms resolvent_clockHalf_commute
#print axioms resolvent_clockHalf_norm_le
#print axioms resolvent_clockHalf_graph_tendsto
#print axioms resolvent_clockHalf_tendsto
#print axioms yosida_clockHalf_graph
#print axioms yosida_clockHalf_domain
#print axioms yosida_clockHalf_commute
#print axioms resolvent_clockOperator_graph
#print axioms resolvent_clockOperator_domain
#print axioms resolvent_clockOperator_commute
#print axioms resolvent_clockOperator_tendsto
#print axioms yosida_clockOperator_graph
#print axioms yosida_clockOperator_domain
#print axioms yosida_clockOperator_commute
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventClockCommutation
