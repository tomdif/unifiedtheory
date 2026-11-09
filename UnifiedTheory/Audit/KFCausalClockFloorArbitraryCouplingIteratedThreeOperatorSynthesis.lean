/- Two-Time Iterated Hamiltonian Resolvent and Iterated Yosida Differences,
Telescoping Identities, Unconditional Five-Domain Time-Independent Stability,
Radial and Radial-Root Norm Bounds, Residual-Growing-Potential Second-Resolvent
Representations, and Two-Time Three-Tier Second-Power Graph Convergence across
All Real Couplings m, g, k, s, t ∈ ℝ:
1. Defines twoTimeIteratedHamiltonianResolventDiff, twoTimeIteratedHamiltonianResolventSum,
   twoTimeIteratedHamiltonianYosidaDiff, and twoTimeIteratedHamiltonianYosidaSum for
   arbitrary real times s, t ∈ ℝ, shifts a, b > 0, and real couplings m, g, k ∈ ℝ.
2. Establishes exact telescoping decompositions, cocycle identities, unconditional
   membership in all five time-independent operator and form domains ((T).domain,
   (K).domain, (Tstat).domain, (Kroot).domain, (clockHalf).domain), and Hilbert,
   radial (K), and radial-root (Kroot) norm bounds.
3. Proves two-time residual and potential-growing-residual second-resolvent
   identities, quantitative two-time iteratedYosida approximation bounds, and
   simultaneous two-time 3-tier second-power graph convergence. -/
import UnifiedTheory.Audit.KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryCouplingIteratedCoreApproximation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorArbitraryCouplingIteratedThreeOperatorSynthesis

noncomputable section

open Filter
open scoped Topology InnerProduct
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open KFCausalClockFloorPotentialClockApproximation (cutoff cutoff_pos)
open KFCausalClockFloorSecondPowerOperatorCores
  (secondPowerGraph secondPowerDomain)
open KFCausalClockFloorHamiltonianComponentResolventBounds
  (resolvent_mem_radial_domain resolvent_norm_le)
open KFCausalClockFloorUnconditionalTwoTimeEvolution
  (commonOperatorDomain)
open KFCausalClockFloorIteratedHamiltonianResolventUnconditionalDomination
  (iteratedHamiltonianResolvent squaredHamiltonianResolvent
   iteratedHamiltonianResolvent_eq squaredHamiltonianResolvent_eq
   iteratedHamiltonianResolvent_mem_ten_domains
   iteratedHamiltonianResolvent_first_power_mem_ten_domains
   residual_sub_iteratedHamiltonianResolvent_eq
   potential_sub_iteratedHamiltonianResolvent_via_growing_residual_eq
   iteratedHamiltonianResolvent_five_way_domain_iff)
open KFCausalClockFloorArbitraryCouplingIteratedCoreApproximation
  (iteratedYosida iteratedYosida_eq_sq_smul iteratedYosida_norm_bound
   iteratedYosida_error_on_domain
   hamiltonian_iteratedYosida_sequence_approximation
   hamiltonian_secondPowerGraph_three_tier_convergence)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "K" => KFCausalClockFloorRadialYosidaDomain.operator ε hε h
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k
local notation "Tstat" => KFCausalClockFloorStaticMultiplierForm.rootOperator ε hε h
local notation "Kroot" => KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
local notation "Tpot" => KFCausalClockFloorPotentialOutputClosure.operator ε hε h hh hw m g k

/-- The two-time difference of iterated full-Hamiltonian resolvents
`R_{H(t)}(a)(R_{H(t)}(b) f) - R_{H(s)}(a)(R_{H(s)}(b) f)`. -/
def twoTimeIteratedHamiltonianResolventDiff (s t a b : ℝ) (f : Hilbert) : Hilbert :=
  iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f -
    iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f

/-- The two-time sum of iterated full-Hamiltonian resolvents
`R_{H(t)}(a)(R_{H(t)}(b) f) + R_{H(s)}(a)(R_{H(s)}(b) f)`. -/
def twoTimeIteratedHamiltonianResolventSum (s t a b : ℝ) (f : Hilbert) : Hilbert :=
  iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f +
    iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f

/-- The two-time difference of iterated Hamiltonian Yosida approximants
`iteratedYosida (RH t a) a f - iteratedYosida (RH s a) a f`. -/
def twoTimeIteratedHamiltonianYosidaDiff (s t a : ℝ) (f : Hilbert) : Hilbert :=
  iteratedYosida (RH t a) a f - iteratedYosida (RH s a) a f

/-- The two-time sum of iterated Hamiltonian Yosida approximants
`iteratedYosida (RH t a) a f + iteratedYosida (RH s a) a f`. -/
def twoTimeIteratedHamiltonianYosidaSum (s t a : ℝ) (f : Hilbert) : Hilbert :=
  iteratedYosida (RH t a) a f + iteratedYosida (RH s a) a f

/-! ### 1. Algebraic & Telescoping Identities for Two-Time Iterated Resolvents and Yosida Approximants -/

/-- Definitional unfolding of `twoTimeIteratedHamiltonianResolventDiff`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_eq (s t a b : ℝ) (f : Hilbert) :
    twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f =
      RH t a (RH t b f) - RH s a (RH s b f) :=
  rfl

/-- At equal times `s = t`, `twoTimeIteratedHamiltonianResolventDiff s s a b f = 0`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_self_eq_zero (s a b : ℝ) (f : Hilbert) :
    twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s s a b f = 0 :=
  sub_self _

/-- Antisymmetry under time swap `s ↔ t` for `twoTimeIteratedHamiltonianResolventDiff`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_neg_swap (s t a b : ℝ) (f : Hilbert) :
    twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f =
      - twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k t s a b f := by
  unfold twoTimeIteratedHamiltonianResolventDiff
  abel

/-- Three-time cocycle identity for `twoTimeIteratedHamiltonianResolventDiff`:
`(x_t - x_r) = (x_s - x_r) + (x_t - x_s)`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_cocycle (r s t a b : ℝ) (f : Hilbert) :
    twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k r t a b f =
      twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k r s a b f +
        twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f := by
  unfold twoTimeIteratedHamiltonianResolventDiff
  abel

/-- Forward telescoping decomposition of `twoTimeIteratedHamiltonianResolventDiff s t a b f`:
`RH t a (RH t b f) - RH s a (RH s b f) = (RH t a (RH t b f) - RH s a (RH t b f)) + RH s a (RH t b f - RH s b f)`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_telescope_eq (s t a b : ℝ) (f : Hilbert) :
    twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f =
      (RH t a (RH t b f) - RH s a (RH t b f)) + RH s a (RH t b f - RH s b f) := by
  rw [twoTimeIteratedHamiltonianResolventDiff_eq, map_sub]
  abel

/-- Reverse telescoping decomposition of `twoTimeIteratedHamiltonianResolventDiff s t a b f`:
`RH t a (RH t b f) - RH s a (RH s b f) = RH t a (RH t b f - RH s b f) + (RH t a (RH s b f) - RH s a (RH s b f))`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_reverse_telescope_eq (s t a b : ℝ) (f : Hilbert) :
    twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f =
      RH t a (RH t b f - RH s b f) + (RH t a (RH s b f) - RH s a (RH s b f)) := by
  rw [twoTimeIteratedHamiltonianResolventDiff_eq, map_sub]
  abel

/-- Exact relation between `twoTimeIteratedHamiltonianYosidaDiff` and diagonal
`twoTimeIteratedHamiltonianResolventDiff`:
`twoTimeIteratedHamiltonianYosidaDiff s t a f = ((a ^ 2 : ℝ) : ℂ) • twoTimeIteratedHamiltonianResolventDiff s t a a f`. -/
theorem twoTimeIteratedHamiltonianYosidaDiff_eq_sq_smul (s t a : ℝ) (f : Hilbert) :
    twoTimeIteratedHamiltonianYosidaDiff ε hε h hh hb m g k s t a f =
      ((a ^ 2 : ℝ) : ℂ) •
        twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a a f := by
  unfold twoTimeIteratedHamiltonianYosidaDiff twoTimeIteratedHamiltonianResolventDiff
    iteratedHamiltonianResolvent
  rw [iteratedYosida_eq_sq_smul, iteratedYosida_eq_sq_smul, smul_sub]

/-- At equal times `s = t`, `twoTimeIteratedHamiltonianYosidaDiff s s a f = 0`. -/
theorem twoTimeIteratedHamiltonianYosidaDiff_self_eq_zero (s a : ℝ) (f : Hilbert) :
    twoTimeIteratedHamiltonianYosidaDiff ε hε h hh hb m g k s s a f = 0 :=
  sub_self _

/-- Antisymmetry under time swap `s ↔ t` for `twoTimeIteratedHamiltonianYosidaDiff`. -/
theorem twoTimeIteratedHamiltonianYosidaDiff_neg_swap (s t a : ℝ) (f : Hilbert) :
    twoTimeIteratedHamiltonianYosidaDiff ε hε h hh hb m g k s t a f =
      - twoTimeIteratedHamiltonianYosidaDiff ε hε h hh hb m g k t s a f := by
  unfold twoTimeIteratedHamiltonianYosidaDiff
  abel

/-- Three-time cocycle identity for `twoTimeIteratedHamiltonianYosidaDiff`. -/
theorem twoTimeIteratedHamiltonianYosidaDiff_cocycle (r s t a : ℝ) (f : Hilbert) :
    twoTimeIteratedHamiltonianYosidaDiff ε hε h hh hb m g k r t a f =
      twoTimeIteratedHamiltonianYosidaDiff ε hε h hh hb m g k r s a f +
        twoTimeIteratedHamiltonianYosidaDiff ε hε h hh hb m g k s t a f := by
  unfold twoTimeIteratedHamiltonianYosidaDiff
  abel

/-! ### 2. Unconditional Five-Domain Time-Independent Stability across All Real Couplings -/

/-- Unconditionally for all real `m, g, k, s, t` and `0 < a, 0 < b`,
`twoTimeIteratedHamiltonianResolventDiff s t a b f` belongs to all five time-independent
operator and form domains `(K).domain`, `(Tstat).domain`, `(Kroot).domain`, `(Tpot).domain`,
and `(clockHalf ε).domain`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_mem_common_time_independent_domains
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let d := twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f
    d ∈ (K).domain ∧
      d ∈ (Tstat).domain ∧
      d ∈ (Kroot).domain ∧
      d ∈ (Tpot).domain ∧
      d ∈ (clockHalf ε).domain := by
  intro d
  have ht := iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k t 0 a b ha hb_pos f
  have hs := iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k s 0 a b ha hb_pos f
  exact ⟨(K).domain.sub_mem ht.2.2.1 hs.2.2.1,
    (Tstat).domain.sub_mem ht.2.2.2.2.2.1 hs.2.2.2.2.2.1,
    (Kroot).domain.sub_mem ht.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.1,
    (Tpot).domain.sub_mem ht.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1,
    (clockHalf ε).domain.sub_mem ht.2.2.2.2.2.2.2.2.2.2 hs.2.2.2.2.2.2.2.2.2.2⟩

/-- Unconditionally for all real `m, g, k, s, t` and `0 < a, 0 < b`,
`twoTimeIteratedHamiltonianResolventSum s t a b f` belongs to all five time-independent
operator and form domains `(K).domain`, `(Tstat).domain`, `(Kroot).domain`, `(Tpot).domain`,
and `(clockHalf ε).domain`. -/
theorem twoTimeIteratedHamiltonianResolventSum_mem_common_time_independent_domains
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let w := twoTimeIteratedHamiltonianResolventSum ε hε h hh hb m g k s t a b f
    w ∈ (K).domain ∧
      w ∈ (Tstat).domain ∧
      w ∈ (Kroot).domain ∧
      w ∈ (Tpot).domain ∧
      w ∈ (clockHalf ε).domain := by
  intro w
  have ht := iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k t 0 a b ha hb_pos f
  have hs := iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k s 0 a b ha hb_pos f
  exact ⟨(K).domain.add_mem ht.2.2.1 hs.2.2.1,
    (Tstat).domain.add_mem ht.2.2.2.2.2.1 hs.2.2.2.2.2.1,
    (Kroot).domain.add_mem ht.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.1,
    (Tpot).domain.add_mem ht.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.1,
    (clockHalf ε).domain.add_mem ht.2.2.2.2.2.2.2.2.2.2 hs.2.2.2.2.2.2.2.2.2.2⟩

/-- Unconditionally for all real `m, g, k, s, t` and `0 < a`,
`twoTimeIteratedHamiltonianYosidaDiff s t a f` belongs to all five time-independent
operator and form domains `(K).domain`, `(Tstat).domain`, `(Kroot).domain`, `(Tpot).domain`,
and `(clockHalf ε).domain`. -/
theorem twoTimeIteratedHamiltonianYosidaDiff_mem_common_time_independent_domains
    (s t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    let d := twoTimeIteratedHamiltonianYosidaDiff ε hε h hh hb m g k s t a f
    d ∈ (K).domain ∧
      d ∈ (Tstat).domain ∧
      d ∈ (Kroot).domain ∧
      d ∈ (Tpot).domain ∧
      d ∈ (clockHalf ε).domain := by
  intro d
  have hd : d = ((a ^ 2 : ℝ) : ℂ) •
      twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a a f :=
    twoTimeIteratedHamiltonianYosidaDiff_eq_sq_smul ε hε h hh hb m g k s t a f
  have hmem :=
    twoTimeIteratedHamiltonianResolventDiff_mem_common_time_independent_domains
      ε hε h hh hb m g k s t a a ha ha f
  rw [hd]
  exact ⟨(K).domain.smul_mem _ hmem.1,
    (Tstat).domain.smul_mem _ hmem.2.1,
    (Kroot).domain.smul_mem _ hmem.2.2.1,
    (Tpot).domain.smul_mem _ hmem.2.2.2.1,
    (clockHalf ε).domain.smul_mem _ hmem.2.2.2.2⟩

/-- Unconditionally for all real `m, g, k, s, t` and `0 < a`,
`twoTimeIteratedHamiltonianYosidaSum s t a f` belongs to all five time-independent
operator and form domains `(K).domain`, `(Tstat).domain`, `(Kroot).domain`, `(Tpot).domain`,
and `(clockHalf ε).domain`. -/
theorem twoTimeIteratedHamiltonianYosidaSum_mem_common_time_independent_domains
    (s t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    let w := twoTimeIteratedHamiltonianYosidaSum ε hε h hh hb m g k s t a f
    w ∈ (K).domain ∧
      w ∈ (Tstat).domain ∧
      w ∈ (Kroot).domain ∧
      w ∈ (Tpot).domain ∧
      w ∈ (clockHalf ε).domain := by
  intro w
  have hw_eq : w = ((a ^ 2 : ℝ) : ℂ) •
      twoTimeIteratedHamiltonianResolventSum ε hε h hh hb m g k s t a a f := by
    unfold w twoTimeIteratedHamiltonianYosidaSum twoTimeIteratedHamiltonianResolventSum
      iteratedHamiltonianResolvent
    rw [iteratedYosida_eq_sq_smul, iteratedYosida_eq_sq_smul, smul_add]
  have hmem :=
    twoTimeIteratedHamiltonianResolventSum_mem_common_time_independent_domains
      ε hε h hh hb m g k s t a a ha ha f
  rw [hw_eq]
  exact ⟨(K).domain.smul_mem _ hmem.1,
    (Tstat).domain.smul_mem _ hmem.2.1,
    (Kroot).domain.smul_mem _ hmem.2.2.1,
    (Tpot).domain.smul_mem _ hmem.2.2.2.1,
    (clockHalf ε).domain.smul_mem _ hmem.2.2.2.2⟩

/-- Unconditionally for all real `m, g, k, s, t` and `0 < a, 0 < b`, the difference of the
first-power outputs `y_t - y_s := (RH t b f - a • x_t) - (RH s b f - a • x_s)` belongs to all
five time-independent operator and form domains `(K).domain`, `(Tstat).domain`, `(Kroot).domain`,
`(Tpot).domain`, and `(clockHalf ε).domain`. -/
theorem twoTimeIteratedHamiltonianResolvent_first_power_diff_mem_common_time_independent_domains
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let yt := RH t b f - (a : ℂ) • iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f
    let ys := RH s b f - (a : ℂ) • iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f
    (yt - ys) ∈ (K).domain ∧
      (yt - ys) ∈ (Tstat).domain ∧
      (yt - ys) ∈ (Kroot).domain ∧
      (yt - ys) ∈ (Tpot).domain ∧
      (yt - ys) ∈ (clockHalf ε).domain := by
  intro yt ys
  have ht := iteratedHamiltonianResolvent_first_power_mem_ten_domains ε hε h hh hb m g k t 0 a b ha hb_pos f
  have hs := iteratedHamiltonianResolvent_first_power_mem_ten_domains ε hε h hh hb m g k s 0 a b ha hb_pos f
  exact ⟨(K).domain.sub_mem ht.2.1 hs.2.1,
    (Tstat).domain.sub_mem ht.2.2.2.2.1 hs.2.2.2.2.1,
    (Kroot).domain.sub_mem ht.2.2.2.2.2.1 hs.2.2.2.2.2.1,
    (Tpot).domain.sub_mem ht.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.1,
    (clockHalf ε).domain.sub_mem ht.2.2.2.2.2.2.2.2.2 hs.2.2.2.2.2.2.2.2.2⟩

/-! ### 3. Unconditional Hilbert, Radial, and Radial-Root Norm Bounds -/

/-- Unconditional Hilbert norm bound on `twoTimeIteratedHamiltonianResolventDiff s t a b f`:
`‖twoTimeIteratedHamiltonianResolventDiff s t a b f‖ ≤ 2 * (a⁻¹ * (b⁻¹ * ‖f‖))`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_norm_le
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f‖ ≤
      2 * (a⁻¹ * (b⁻¹ * ‖f‖)) := by
  unfold twoTimeIteratedHamiltonianResolventDiff
  have htri := norm_sub_le
    (iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f)
    (iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f)
  have ht1 := resolvent_norm_le ε hε h hh hb m g k t a ha (RH t b f)
  have ht2 := resolvent_norm_le ε hε h hh hb m g k t b hb_pos f
  have hs1 := resolvent_norm_le ε hε h hh hb m g k s a ha (RH s b f)
  have hs2 := resolvent_norm_le ε hε h hh hb m g k s b hb_pos f
  have ht : ‖iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) :=
    ht1.trans (mul_le_mul_of_nonneg_left ht2 (inv_nonneg.mpr ha.le))
  have hs : ‖iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) :=
    hs1.trans (mul_le_mul_of_nonneg_left hs2 (inv_nonneg.mpr ha.le))
  linarith [htri, ht, hs]

/-- Unconditional Hilbert norm bound on `twoTimeIteratedHamiltonianResolventSum s t a b f`:
`‖twoTimeIteratedHamiltonianResolventSum s t a b f‖ ≤ 2 * (a⁻¹ * (b⁻¹ * ‖f‖))`. -/
theorem twoTimeIteratedHamiltonianResolventSum_norm_le
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    ‖twoTimeIteratedHamiltonianResolventSum ε hε h hh hb m g k s t a b f‖ ≤
      2 * (a⁻¹ * (b⁻¹ * ‖f‖)) := by
  unfold twoTimeIteratedHamiltonianResolventSum
  have htri := norm_add_le
    (iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f)
    (iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f)
  have ht1 := resolvent_norm_le ε hε h hh hb m g k t a ha (RH t b f)
  have ht2 := resolvent_norm_le ε hε h hh hb m g k t b hb_pos f
  have hs1 := resolvent_norm_le ε hε h hh hb m g k s a ha (RH s b f)
  have hs2 := resolvent_norm_le ε hε h hh hb m g k s b hb_pos f
  have ht : ‖iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) :=
    ht1.trans (mul_le_mul_of_nonneg_left ht2 (inv_nonneg.mpr ha.le))
  have hs : ‖iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f‖ ≤ a⁻¹ * (b⁻¹ * ‖f‖) :=
    hs1.trans (mul_le_mul_of_nonneg_left hs2 (inv_nonneg.mpr ha.le))
  linarith [htri, ht, hs]

/-- Unconditional Hilbert norm bound on `twoTimeIteratedHamiltonianYosidaDiff s t a f`:
`‖twoTimeIteratedHamiltonianYosidaDiff s t a f‖ ≤ 2 * ‖f‖`. -/
theorem twoTimeIteratedHamiltonianYosidaDiff_norm_le
    (s t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖twoTimeIteratedHamiltonianYosidaDiff ε hε h hh hb m g k s t a f‖ ≤ 2 * ‖f‖ := by
  unfold twoTimeIteratedHamiltonianYosidaDiff
  have htri := norm_sub_le (iteratedYosida (RH t a) a f) (iteratedYosida (RH s a) a f)
  have ht := iteratedYosida_norm_bound (H t) (RH t a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) f
  have hs := iteratedYosida_norm_bound (H s) (RH s a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k s) f
  linarith

/-- Unconditional Hilbert norm bound on `twoTimeIteratedHamiltonianYosidaSum s t a f`:
`‖twoTimeIteratedHamiltonianYosidaSum s t a f‖ ≤ 2 * ‖f‖`. -/
theorem twoTimeIteratedHamiltonianYosidaSum_norm_le
    (s t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖twoTimeIteratedHamiltonianYosidaSum ε hε h hh hb m g k s t a f‖ ≤ 2 * ‖f‖ := by
  unfold twoTimeIteratedHamiltonianYosidaSum
  have htri := norm_add_le (iteratedYosida (RH t a) a f) (iteratedYosida (RH s a) a f)
  have ht := iteratedYosida_norm_bound (H t) (RH t a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t) f
  have hs := iteratedYosida_norm_bound (H s) (RH s a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k s) f
  linarith

/-- Telescoping norm bound on `twoTimeIteratedHamiltonianResolventDiff s t a b f`:
`‖twoTimeIteratedHamiltonianResolventDiff s t a b f‖ ≤ ‖RH t a (RH t b f) - RH s a (RH t b f)‖ + a⁻¹ * ‖RH t b f - RH s b f‖`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_norm_le_telescope
    (s t a b : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f‖ ≤
      ‖RH t a (RH t b f) - RH s a (RH t b f)‖ + a⁻¹ * ‖RH t b f - RH s b f‖ := by
  rw [twoTimeIteratedHamiltonianResolventDiff_telescope_eq]
  have htri := norm_add_le (RH t a (RH t b f) - RH s a (RH t b f)) (RH s a (RH t b f - RH s b f))
  have hs := resolvent_norm_le ε hε h hh hb m g k s a ha (RH t b f - RH s b f)
  linarith

/-- Exact linearity of `K` on `twoTimeIteratedHamiltonianResolventDiff s t a b f`:
`K (x_t - x_s) = K x_t - K x_s`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_radial_eq_sub
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let d := twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f
    let hd := (twoTimeIteratedHamiltonianResolventDiff_mem_common_time_independent_domains
      ε hε h hh hb m g k s t a b ha hb_pos f).1
    let ht := (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k t 0 a b ha hb_pos f).2.2.1
    let hs := (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k s 0 a b ha hb_pos f).2.2.1
    K ⟨d, hd⟩ =
      K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f, ht⟩ -
        K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f, hs⟩ := by
  intro d hd ht hs
  have hsub : (⟨d, hd⟩ : (K).domain) =
      ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f, ht⟩ -
        ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f, hs⟩ :=
    Subtype.ext rfl
  rw [hsub, (K).map_sub]

/-- Unconditional radial (`K`) norm triangle bound on `twoTimeIteratedHamiltonianResolventDiff s t a b f`:
`‖K (x_t - x_s)‖ ≤ ‖K x_t‖ + ‖K x_s‖`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_radial_norm_le
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let d := twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f
    let hd := (twoTimeIteratedHamiltonianResolventDiff_mem_common_time_independent_domains
      ε hε h hh hb m g k s t a b ha hb_pos f).1
    let ht := (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k t 0 a b ha hb_pos f).2.2.1
    let hs := (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k s 0 a b ha hb_pos f).2.2.1
    ‖K ⟨d, hd⟩‖ ≤
      ‖K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f, ht⟩‖ +
        ‖K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f, hs⟩‖ := by
  intro d hd ht hs
  rw [twoTimeIteratedHamiltonianResolventDiff_radial_eq_sub ε hε h hh hb m g k s t a b ha hb_pos f]
  exact norm_sub_le _ _

/-- Unconditional radial (`K`) norm triangle bound on `twoTimeIteratedHamiltonianResolventSum s t a b f`:
`‖K (x_t + x_s)‖ ≤ ‖K x_t‖ + ‖K x_s‖`. -/
theorem twoTimeIteratedHamiltonianResolventSum_radial_norm_le
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let w := twoTimeIteratedHamiltonianResolventSum ε hε h hh hb m g k s t a b f
    let hw_dom := (twoTimeIteratedHamiltonianResolventSum_mem_common_time_independent_domains
      ε hε h hh hb m g k s t a b ha hb_pos f).1
    let ht := (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k t 0 a b ha hb_pos f).2.2.1
    let hs := (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k s 0 a b ha hb_pos f).2.2.1
    ‖K ⟨w, hw_dom⟩‖ ≤
      ‖K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f, ht⟩‖ +
        ‖K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f, hs⟩‖ := by
  intro w hw_dom ht hs
  have hadd : (⟨w, hw_dom⟩ : (K).domain) =
      ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f, ht⟩ +
        ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f, hs⟩ :=
    Subtype.ext rfl
  rw [hadd, (K).map_add]
  exact norm_add_le _ _

/-- Unconditional radial-root (`Kroot`) norm triangle bound on `twoTimeIteratedHamiltonianResolventDiff s t a b f`:
`‖Kroot (x_t - x_s)‖ ≤ ‖Kroot x_t‖ + ‖Kroot x_s‖`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_radialRoot_norm_le
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert) :
    let d := twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f
    let hd := (twoTimeIteratedHamiltonianResolventDiff_mem_common_time_independent_domains
      ε hε h hh hb m g k s t a b ha hb_pos f).2.2.1
    let ht := (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k t 0 a b ha hb_pos f).2.2.2.2.2.2.1
    let hs := (iteratedHamiltonianResolvent_mem_ten_domains ε hε h hh hb m g k s 0 a b ha hb_pos f).2.2.2.2.2.2.1
    ‖Kroot ⟨d, hd⟩‖ ≤
      ‖Kroot ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f, ht⟩‖ +
        ‖Kroot ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f, hs⟩‖ := by
  intro d hd ht hs
  have hsub : (⟨d, hd⟩ : (Kroot).domain) =
      ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f, ht⟩ -
        ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f, hs⟩ :=
    Subtype.ext rfl
  rw [hsub, (Kroot).map_sub]
  exact norm_sub_le _ _

/-! ### 4. Two-Time Second-Resolvent Identities & Three-Tier Iterated Yosida Convergence -/

/-- Unconditional two-time residual second-resolvent identity for `twoTimeIteratedHamiltonianResolventDiff`:
`twoTimeIteratedHamiltonianResolventDiff s t a b f = (RS t a (RH t b f) - RS s a (RH s b f)) - exp(2t) • RS t a (K x_t) + exp(2s) • RS s a (K x_s)`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_via_residual_eq
    (s t a b : ℝ) (ha : 0 < a) (f : Hilbert) :
    twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f =
      (RS t a (RH t b f) - RS s a (RH s b f)) -
        (Real.exp (2 * t) : ℂ) •
          RS t a (K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f,
            resolvent_mem_radial_domain ε hε h hh hb m g k t a ha (RH t b f)⟩) +
        (Real.exp (2 * s) : ℂ) •
          RS s a (K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f,
            resolvent_mem_radial_domain ε hε h hh hb m g k s a ha (RH s b f)⟩) := by
  have ht := residual_sub_iteratedHamiltonianResolvent_eq ε hε h hh hb m g k t a b ha f
  have hs := residual_sub_iteratedHamiltonianResolvent_eq ε hε h hh hb m g k s a b ha f
  unfold twoTimeIteratedHamiltonianResolventDiff
  have hsub := congrArg₂ (· - ·) ht hs
  dsimp only at hsub
  calc
    iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f -
        iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f =
      (RS t a (RH t b f) - RS s a (RH s b f)) -
        ((RS t a (RH t b f) - iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f) -
          (RS s a (RH s b f) - iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f)) := by
      abel
    _ = _ := by
      rw [hsub]
      abel

/-- Unconditional two-time potential-growing-residual chain identity for
`twoTimeIteratedHamiltonianResolventDiff s t a b f`. -/
theorem twoTimeIteratedHamiltonianResolventDiff_via_potential_growing_residual_eq
    (s t a b : ℝ) (ha : 0 < a) (f : Hilbert) :
    twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f =
      RP a (RH t b f - RH s b f) -
        (RP a (K ⟨RG a (RH t b f),
          KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k a ha (RH t b f)⟩) +
          (RG a (RH t b f) - RS t a (RH t b f)) +
          (Real.exp (2 * t) : ℂ) •
            RS t a (K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f,
              resolvent_mem_radial_domain ε hε h hh hb m g k t a ha (RH t b f)⟩)) +
        (RP a (K ⟨RG a (RH s b f),
          KFCausalClockFloorGrowingComponentResolventBounds.resolvent_mem_radial_domain
            ε hε h hh hb m g k a ha (RH s b f)⟩) +
          (RG a (RH s b f) - RS s a (RH s b f)) +
          (Real.exp (2 * s) : ℂ) •
            RS s a (K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f,
              resolvent_mem_radial_domain ε hε h hh hb m g k s a ha (RH s b f)⟩)) := by
  have ht := potential_sub_iteratedHamiltonianResolvent_via_growing_residual_eq ε hε h hh hb m g k t a b ha f
  have hs := potential_sub_iteratedHamiltonianResolvent_via_growing_residual_eq ε hε h hh hb m g k s a b ha f
  unfold twoTimeIteratedHamiltonianResolventDiff
  have hsub := congrArg₂ (· - ·) ht hs
  dsimp only at hsub
  rw [map_sub]
  calc
    iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f -
        iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f =
      (RP a (RH t b f) - RP a (RH s b f)) -
        ((RP a (RH t b f) - iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f) -
          (RP a (RH s b f) - iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f)) := by
      abel
    _ = _ := by
      rw [hsub]
      abel

/-- Quantitative two-time sum of `iteratedYosida` domain approximation errors:
`‖iteratedYosida (RH t a) a u_t - u_t‖ + ‖iteratedYosida (RH s a) a u_s - u_s‖ ≤ 2 * (a⁻¹ * ‖H t u_t‖) + 2 * (a⁻¹ * ‖H s u_s‖)`. -/
theorem twoTimeIteratedHamiltonianYosida_error_sum_bound
    (s t a : ℝ) (ha : 0 < a) (ut : (H t).domain) (us : (H s).domain) :
    ‖iteratedYosida (RH t a) a (ut : Hilbert) - (ut : Hilbert)‖ +
      ‖iteratedYosida (RH s a) a (us : Hilbert) - (us : Hilbert)‖ ≤
      2 * (a⁻¹ * ‖H t ut‖) + 2 * (a⁻¹ * ‖H s us‖) := by
  have ht := iteratedYosida_error_on_domain (H t) (RH t a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t a ha) ut
  have hs := iteratedYosida_error_on_domain (H s) (RH s a) a ha
    (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k s a ha)
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k s)
    (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k s a ha) us
  linarith

/-- Quantitative two-time difference approximation bound for `iteratedYosida`:
`‖(iteratedYosida (RH t a) a u_t - iteratedYosida (RH s a) a u_s) - (u_t - u_s)‖ ≤ 2 * (a⁻¹ * ‖H t u_t‖) + 2 * (a⁻¹ * ‖H s u_s‖)`. -/
theorem twoTimeIteratedHamiltonianYosida_diff_approx_bound
    (s t a : ℝ) (ha : 0 < a) (ut : (H t).domain) (us : (H s).domain) :
    ‖(iteratedYosida (RH t a) a (ut : Hilbert) - iteratedYosida (RH s a) a (us : Hilbert)) -
        ((ut : Hilbert) - (us : Hilbert))‖ ≤
      2 * (a⁻¹ * ‖H t ut‖) + 2 * (a⁻¹ * ‖H s us‖) := by
  have heq :
      (iteratedYosida (RH t a) a (ut : Hilbert) - iteratedYosida (RH s a) a (us : Hilbert)) -
        ((ut : Hilbert) - (us : Hilbert)) =
      (iteratedYosida (RH t a) a (ut : Hilbert) - (ut : Hilbert)) -
        (iteratedYosida (RH s a) a (us : Hilbert) - (us : Hilbert)) := by
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans
    (twoTimeIteratedHamiltonianYosida_error_sum_bound ε hε h hh hb m g k s t a ha ut us)

/-- Simultaneous two-time strong convergence of `iteratedYosida (RH t (cutoff n)) (cutoff n) u_t`
and `iteratedYosida (RH s (cutoff n)) (cutoff n) u_s` to `(u_t, u_s)` in `Hilbert × Hilbert`. -/
theorem twoTimeIteratedHamiltonianYosida_sequence_strong_limit
    (s t : ℝ) (ut : (H t).domain) (us : (H s).domain) :
    Tendsto
      (fun n : ℕ =>
        (iteratedYosida (RH t (cutoff n)) (cutoff n) (ut : Hilbert),
         iteratedYosida (RH s (cutoff n)) (cutoff n) (us : Hilbert)))
      atTop
      (nhds ((ut : Hilbert), (us : Hilbert))) := by
  have ht : Tendsto (fun n : ℕ => iteratedYosida (RH t (cutoff n)) (cutoff n) (ut : Hilbert))
      atTop (nhds (ut : Hilbert)) :=
    (continuous_fst.tendsto ((ut : Hilbert), H t ut)).comp
      (hamiltonian_iteratedYosida_sequence_approximation ε hε h hh hb m g k t ut).2
  have hs : Tendsto (fun n : ℕ => iteratedYosida (RH s (cutoff n)) (cutoff n) (us : Hilbert))
      atTop (nhds (us : Hilbert)) :=
    (continuous_fst.tendsto ((us : Hilbert), H s us)).comp
      (hamiltonian_iteratedYosida_sequence_approximation ε hε h hh hb m g k s us).2
  exact ht.prodMk_nhds hs

/-- Simultaneous two-time 3-tier `secondPowerGraph` convergence for `H t` and `H s` at
arbitrary real couplings `m, g, k, s, t ∈ ℝ`. -/
theorem twoTimeIteratedHamiltonian_secondPowerGraph_three_tier_convergence
    (s t : ℝ) (ut : (H t).domain) (hHt : H t ut ∈ (H t).domain)
    (us : (H s).domain) (hHs : H s us ∈ (H s).domain) :
    (∀ n : ℕ,
      (((cutoff n : ℂ) • RH t (cutoff n) (ut : Hilbert),
        (cutoff n : ℂ) • RH t (cutoff n) (H t ut)) ∈ secondPowerGraph (H t)) ∧
      (((cutoff n : ℂ) • RH s (cutoff n) (us : Hilbert),
        (cutoff n : ℂ) • RH s (cutoff n) (H s us)) ∈ secondPowerGraph (H s))) ∧
    Tendsto
      (fun n : ℕ =>
        (((cutoff n : ℂ) • RH t (cutoff n) (ut : Hilbert),
          ((cutoff n : ℂ) • RH t (cutoff n) (H t ut),
           (cutoff n : ℂ) • RH t (cutoff n) (H t ⟨H t ut, hHt⟩))),
         ((cutoff n : ℂ) • RH s (cutoff n) (us : Hilbert),
          ((cutoff n : ℂ) • RH s (cutoff n) (H s us),
           (cutoff n : ℂ) • RH s (cutoff n) (H s ⟨H s us, hHs⟩)))))
      atTop
      (nhds (((ut : Hilbert), (H t ut, H t ⟨H t ut, hHt⟩)),
             ((us : Hilbert), (H s us, H s ⟨H s us, hHs⟩)))) := by
  have ht := hamiltonian_secondPowerGraph_three_tier_convergence ε hε h hh hb m g k t ut hHt
  have hs := hamiltonian_secondPowerGraph_three_tier_convergence ε hε h hh hb m g k s us hHs
  exact ⟨fun n => ⟨(ht.1 n).1, (hs.1 n).1⟩, ht.2.prodMk_nhds hs.2⟩

/-- Unconditionally across all real couplings `m, g, k ∈ ℝ`, the pair of iterated Hamiltonian
resolvents at times `t` and `s` both belong to `(P).domain` if and only if both belong to
`commonOperatorDomain`. -/
theorem twoTimeIteratedHamiltonianResolvent_mem_potential_iff_common_pair
    (s t a b : ℝ) (ha : 0 < a) (f : Hilbert) :
    (iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f ∈ (P).domain ∧
      iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f ∈ (P).domain) ↔
    (iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f ∈
        commonOperatorDomain ε hε h hh hb m g k ∧
      iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f ∈
        commonOperatorDomain ε hε h hh hb m g k) := by
  have ht := iteratedHamiltonianResolvent_five_way_domain_iff ε hε h hh hb m g k t a b ha f
  have hs := iteratedHamiltonianResolvent_five_way_domain_iff ε hε h hh hb m g k s a b ha f
  exact and_congr (ht.1.trans (ht.2.1.trans ht.2.2.1)) (hs.1.trans (hs.2.1.trans hs.2.2.1))

/-- Master synthesis theorem for two-time iterated Hamiltonian resolvent and iterated Yosida
differences across all real couplings `m, g, k, s, t ∈ ℝ`:
bundles the telescoping decomposition, unconditional 5-domain time-independent stability,
Hilbert and radial norm bounds, two-time residual second-resolvent identity, and two-time
strong `iteratedYosida` sequence convergence. -/
theorem twoTimeIteratedHamiltonianResolventDiff_three_operator_master_synthesis
    (s t a b : ℝ) (ha : 0 < a) (hb_pos : 0 < b) (f : Hilbert)
    (ut : (H t).domain) (us : (H s).domain) :
    let d := twoTimeIteratedHamiltonianResolventDiff ε hε h hh hb m g k s t a b f
    (d = (RH t a (RH t b f) - RH s a (RH t b f)) + RH s a (RH t b f - RH s b f)) ∧
    (d ∈ (K).domain ∧ d ∈ (Tstat).domain ∧ d ∈ (Kroot).domain ∧
      d ∈ (Tpot).domain ∧ d ∈ (clockHalf ε).domain) ∧
    (‖d‖ ≤ 2 * (a⁻¹ * (b⁻¹ * ‖f‖))) ∧
    (‖twoTimeIteratedHamiltonianYosidaDiff ε hε h hh hb m g k s t a f‖ ≤ 2 * ‖f‖) ∧
    (d =
      (RS t a (RH t b f) - RS s a (RH s b f)) -
        (Real.exp (2 * t) : ℂ) •
          RS t a (K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k t a b f,
            resolvent_mem_radial_domain ε hε h hh hb m g k t a ha (RH t b f)⟩) +
        (Real.exp (2 * s) : ℂ) •
          RS s a (K ⟨iteratedHamiltonianResolvent ε hε h hh hb m g k s a b f,
            resolvent_mem_radial_domain ε hε h hh hb m g k s a ha (RH s b f)⟩)) ∧
    Tendsto
      (fun n : ℕ =>
        (iteratedYosida (RH t (cutoff n)) (cutoff n) (ut : Hilbert),
         iteratedYosida (RH s (cutoff n)) (cutoff n) (us : Hilbert)))
      atTop
      (nhds ((ut : Hilbert), (us : Hilbert))) := by
  intro d
  exact ⟨twoTimeIteratedHamiltonianResolventDiff_telescope_eq ε hε h hh hb m g k s t a b f,
    twoTimeIteratedHamiltonianResolventDiff_mem_common_time_independent_domains
      ε hε h hh hb m g k s t a b ha hb_pos f,
    twoTimeIteratedHamiltonianResolventDiff_norm_le ε hε h hh hb m g k s t a b ha hb_pos f,
    twoTimeIteratedHamiltonianYosidaDiff_norm_le ε hε h hh hb m g k s t a ha f,
    twoTimeIteratedHamiltonianResolventDiff_via_residual_eq ε hε h hh hb m g k s t a b ha f,
    twoTimeIteratedHamiltonianYosida_sequence_strong_limit ε hε h hh hb m g k s t ut us⟩

#print axioms twoTimeIteratedHamiltonianResolventDiff_eq
#print axioms twoTimeIteratedHamiltonianResolventDiff_self_eq_zero
#print axioms twoTimeIteratedHamiltonianResolventDiff_neg_swap
#print axioms twoTimeIteratedHamiltonianResolventDiff_cocycle
#print axioms twoTimeIteratedHamiltonianResolventDiff_telescope_eq
#print axioms twoTimeIteratedHamiltonianResolventDiff_reverse_telescope_eq
#print axioms twoTimeIteratedHamiltonianYosidaDiff_eq_sq_smul
#print axioms twoTimeIteratedHamiltonianYosidaDiff_self_eq_zero
#print axioms twoTimeIteratedHamiltonianYosidaDiff_neg_swap
#print axioms twoTimeIteratedHamiltonianYosidaDiff_cocycle
#print axioms twoTimeIteratedHamiltonianResolventDiff_mem_common_time_independent_domains
#print axioms twoTimeIteratedHamiltonianResolventSum_mem_common_time_independent_domains
#print axioms twoTimeIteratedHamiltonianYosidaDiff_mem_common_time_independent_domains
#print axioms twoTimeIteratedHamiltonianYosidaSum_mem_common_time_independent_domains
#print axioms twoTimeIteratedHamiltonianResolvent_first_power_diff_mem_common_time_independent_domains
#print axioms twoTimeIteratedHamiltonianResolventDiff_norm_le
#print axioms twoTimeIteratedHamiltonianResolventSum_norm_le
#print axioms twoTimeIteratedHamiltonianYosidaDiff_norm_le
#print axioms twoTimeIteratedHamiltonianYosidaSum_norm_le
#print axioms twoTimeIteratedHamiltonianResolventDiff_norm_le_telescope
#print axioms twoTimeIteratedHamiltonianResolventDiff_radial_eq_sub
#print axioms twoTimeIteratedHamiltonianResolventDiff_radial_norm_le
#print axioms twoTimeIteratedHamiltonianResolventSum_radial_norm_le
#print axioms twoTimeIteratedHamiltonianResolventDiff_radialRoot_norm_le
#print axioms twoTimeIteratedHamiltonianResolventDiff_via_residual_eq
#print axioms twoTimeIteratedHamiltonianResolventDiff_via_potential_growing_residual_eq
#print axioms twoTimeIteratedHamiltonianYosida_error_sum_bound
#print axioms twoTimeIteratedHamiltonianYosida_diff_approx_bound
#print axioms twoTimeIteratedHamiltonianYosida_sequence_strong_limit
#print axioms twoTimeIteratedHamiltonian_secondPowerGraph_three_tier_convergence
#print axioms twoTimeIteratedHamiltonianResolvent_mem_potential_iff_common_pair
#print axioms twoTimeIteratedHamiltonianResolventDiff_three_operator_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorArbitraryCouplingIteratedThreeOperatorSynthesis
