/- Resolvent smoothing converges in the actual completed energy-form
norm, not only in physical L2. This uses energy contraction and the
injective embedding; no operator-domain assumption is imposed. -/
import UnifiedTheory.Audit.KFCausalWeakEmbeddingLimit
import UnifiedTheory.Audit.KFCausalClockFloorResolventEnergyControl
import UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorResolventFormLimit
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosida
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaEnergy
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests
open UnifiedTheory.Audit.KFCausalClockFloorResolventEnergyControl
open UnifiedTheory.Audit.KFCausalWeakEmbeddingLimit
open UnifiedTheory.Audit.KFCausalWeakEnergyContinuity

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "A" => regularizerLift ε hε h hne hh m g k
local notation "R" => regularizer ε hε h hne hh m g k
local notation "T" => formTransfer ε hε h hne hh m g k
local notation "L" => referenceEnergyMap ε hε h hne hh m g k
local notation "E" => timeEnergy ε hε h hne hh m g k

theorem transported_regularizer_contraction (a t : ℝ) (ha : 0 < a) (x : V) :
    ‖T 0 t (A a t (J x))‖^2 ≤ ‖T 0 t x‖^2 := by
  have hn := pow_le_pow_left₀ (norm_nonneg _)
    (regularizer_contraction ε hε h hne hh m g k a t ha (J x)) 2
  have hp : ‖J (A a t (J x))‖^2 ≤ ‖J x‖^2 :=
    (congrArg (fun v : Hilbert => ‖v‖^2)
      (regularizerLift_embedding ε hε h hne hh m g k a t (J x))).le.trans hn
  calc
    _ = ‖J (A a t (J x))‖^2+E t (A a t (J x)) :=
      transported_form_norm ε hε h hne hh m g k t (A a t (J x))
    _ ≤ ‖J x‖^2+E t x := add_le_add hp
      (regularizer_energy_contraction ε hε h hne hh m g k a t ha x)
    _ = _ := (transported_form_norm ε hε h hne hh m g k t x).symm

theorem regularizer_form_tendsto (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hlim : Tendsto a atTop atTop) (t : ℝ) (x : V) :
    Tendsto (fun n => A (a n) t (J x)) atTop (𝓝 x) := by
  let u := fun n => T 0 t (A (a n) t (J x))
  let y := T 0 t x
  have hb (n : ℕ) : ‖u n‖^2 ≤ ‖y‖^2 :=
    transported_regularizer_contraction ε hε h hne hh m g k (a n) t (ha n) x
  have hp : Tendsto (fun n => embedding ε hε h hne hh m g k t (u n)) atTop
      (𝓝 (embedding ε hε h hne hh m g k t y)) := by
    simpa only [u,y,transfer_embedding,regularizerLift_embedding,regularizer] using
      (averaged_resolvent_strong_limit ε hε h hne hh m g k t (J x)).comp hlim
  have hw := weak_of_embedding (embedding ε hε h hne hh m g k t)
    (embedding_injective ε hε h hne hh m g k t) u y ‖y‖ (norm_nonneg y)
    (fun n => by nlinarith only [hb n,norm_nonneg (u n),norm_nonneg y]) hp
  have hs := strong_of_weak_sq_bound hw hb (tendsto_const_nhds (x := ‖y‖^2))
  have hf := ((T t 0).continuous.tendsto y).comp hs
  simpa only [u,y,Function.comp_def,transfer_inverse] using hf

theorem boundedEnergy_pairing (a t : ℝ) (ha : 0 < a) (x : V) :
    boundedEnergy ε hε h hne hh m g k a t (J x) = (inner ℂ (L t (A a t (J x))) (L t x)).re := by
  have hv := energy_variational ε hε h hne hh m g k a t ha (J x) x
  have he : averagedYosida ε hε h hne hh m g k a t (J x) = a • (J x-J (A a t (J x))) := by
    have h0 : averagedYosida ε hε h hne hh m g k a t (J x) = a • (J x-R a t (J x)) :=
      yosida_action ε hε h hne hh m g k a t (J x)
    exact h0.trans (congrArg (fun v : Hilbert => a • (J x-v))
      (regularizerLift_embedding ε hε h hne hh m g k a t (J x))).symm
  calc
    _ = (inner ℂ (a • (J x-J (A a t (J x)))) (J x)).re :=
      congrArg (fun v : Hilbert => (inner ℂ v (J x)).re) he
    _ = ((a:ℂ)*inner ℂ (J x-J (A a t (J x))) (J x)).re :=
      congrArg Complex.re (inner_smul_left_eq_smul (𝕜 := ℂ) _ _ a)
    _ = _ := (congrArg Complex.re hv).symm

theorem boundedEnergy_tendsto (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hlim : Tendsto a atTop atTop) (t : ℝ) (x : V) :
    Tendsto (fun n => boundedEnergy ε hε h hne hh m g k (a n) t (J x)) atTop (𝓝 (E t x)) := by
  exact real_pairing_limit (L t) (fun n => A (a n) t (J x)) x
    (fun n => boundedEnergy ε hε h hne hh m g k (a n) t (J x)) (E t x)
    (regularizer_form_tendsto ε hε h hne hh m g k a ha hlim t x)
    (fun n => boundedEnergy_pairing ε hε h hne hh m g k (a n) t (ha n) x)
    (referenceEnergyMap_square ε hε h hne hh m g k t x)

theorem growingLift_tendsto (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hlim : Tendsto a atTop atTop) (t : ℝ) (x : V) :
    Tendsto (fun n => growingLift ε hε h hne hh m g k (a n) t (J x)) atTop
      (𝓝 (Real.exp t • growingMap ε hε h hne hh m g k x)) := by
  have hs := (growingMap ε hε h hne hh m g k).continuous.tendsto x |>.comp
    (regularizer_form_tendsto ε hε h hne hh m g k a ha hlim t x)
  simpa only [growingLift_apply] using hs.const_smul (Real.exp t)

#print axioms transported_regularizer_contraction
#print axioms regularizer_form_tendsto
#print axioms boundedEnergy_pairing
#print axioms boundedEnergy_tendsto
#print axioms growingLift_tendsto
end
end UnifiedTheory.Audit.KFCausalClockFloorResolventFormLimit
