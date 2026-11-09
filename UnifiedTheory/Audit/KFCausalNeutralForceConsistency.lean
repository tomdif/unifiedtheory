/- The actual semiclassical force limits inherit positive interval
addition and the derived uniform mass bound on every finite time window. -/
import UnifiedTheory.Audit.KFCausalForceIntervalAdditivity
import UnifiedTheory.Audit.KFCausalLocalForceConsistency
import UnifiedTheory.Audit.KFCausalNeutralWeakDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralForceConsistency
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralIntegratedForce
open UnifiedTheory.Audit.KFCausalNeutralLocalForceLimit (family)
open UnifiedTheory.Audit.KFCausalCompactifiedForceMeasure (Spectrum compactify)
open UnifiedTheory.Audit.KFCausalLocalForceMeasure (finitePair finitePart)
open UnifiedTheory.Audit.KFCausalLocalForceConsistency

def forceBudget (ε a m g k s T : ℝ) (p : Configuration) : ℝ :=
  2*(1+‖KFCausalNeutralTranslationBounds.weightedLinear
    (KFCausalPhysicalEnergyFactors.energyWeight m g k 0)‖^2)*
    KFCausalClockFloorMovingResolventWindow.windowBudget ε a m g k s T p

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0)) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
  {K : Type*} (b c : K → ℝ) (hbc : ∀ i, b i ≤ c i)
  (ρ : ℕ → ℕ) (hρ : StrictMono ρ) (P N : K → FiniteMeasure Spectrum)

local notation "G" => family ε a hε ha m g k s p h hne hh r hr b c

variable (hP : ∀ i, Tendsto (fun n => compactify
    (family ε a hε ha m g k s p h hne hh r hr b c (ρ n) i).positive) atTop (𝓝 (P i)))
  (hN : ∀ i, Tendsto (fun n => compactify
    (family ε a hε ha m g k s p h hne hh r hr b c (ρ n) i).negative) atTop (𝓝 (N i)))

include ε a hε ha m g k s p h hne hh r hr b c hbc ρ P N hP hN in
theorem compact_family_add (i j l : K) (hl : b i = b l) (hm : c i = b j) (hr' : c j = c l) :
    P l = P i+P j ∧ N l = N i+N j := by
  apply compact_limit_add (fun n => G (ρ n)) P N hP hN i j l
  intro n
  have hcd : c i ≤ c j := by rw [hm]; exact hbc j
  simpa only [family,hl,hm,hr'] using
    KFCausalForceIntervalAdditivity.forceInterval_add ε a (h (ρ n)) hε ha
      (hne (ρ n)) (hh (ρ n)) m g k s p (r (ρ n)) (hr (ρ n))
      (b i) (c i) (c j) (hbc i) hcd

include ε a hε ha m g k s p h hne hh hz r hr b c hbc ρ hρ P N hP hN in
theorem compact_family_mass_bound (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (T : ℝ) (i : K) (hb : |b i-s| ≤ T) (hc : |c i-s| ≤ T) :
    ((P i).mass:ℝ)+((N i).mass:ℝ) ≤ (c i-b i)*forceBudget ε a m g k s T p := by
  apply compact_limit_mass_bound (fun n => G (ρ n) i) (P i) (N i) (hP i) (hN i)
  filter_upwards [hρ.tendsto_atTop.eventually
    (forceInterval_mass_window ε a hε ha m g k s p hm hg hk h hne hh hz T)] with n hn
  exact hn (r (ρ n)) (hr (ρ n)) (b i) (c i) (hbc i) hb hc

include ε a hε ha m g k s p h hne hh hz r hr b c hbc ρ hρ P N hP hN in
theorem local_family_mass_bound (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (T : ℝ) (i : K) (hb : |b i-s| ≤ T) (hc : |c i-s| ≤ T) :
    (finitePair (P i) (N i)).mass ≤ (c i-b i)*forceBudget ε a m g k s T p :=
  (finitePair_mass_bound (P i) (N i)).trans
    (compact_family_mass_bound ε a hε ha m g k s p h hne hh hz r hr b c hbc
      ρ hρ P N hP hN hm hg hk T i hb hc)

#print axioms compact_family_add
#print axioms compact_family_mass_bound
#print axioms local_family_mass_bound
end
end UnifiedTheory.Audit.KFCausalNeutralForceConsistency
