/- The entire domain of the ORIGINAL full Hamiltonian lies in the
maximal radial kinetic domain. The cutoff test is justified on its
original form; a uniform static loss and Fatou remove the cutoff.
This controls Kr, not the full growing operator G. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaHamiltonianPairing

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialDomination
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaSymbol (action)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalClockFloorRadialYosidaDomain (operator domain_of_uniform_bound norm_of_uniform_bound)

private theorem quadratic_bound (u v w e : ℝ) (hv : 0 ≤ v)
    (hw : 0 ≤ w) (he : 0 < e) (hq : e^2*u^2 ≤ v*u+w^2) :
    u ≤ v/e^2+w/e := by
  have hmul : (v/e)*(e*u)=v*u := by rw [← mul_assoc,div_mul_cancel₀ _ he.ne']
  have hs : (e*u)^2 ≤ (v/e)*(e*u)+w^2 := by rw [hmul]; nlinarith only [hq]
  have hn : e*u ≤ v/e+w := by
    have ha : 0 ≤ v/e := div_nonneg hv he.le
    by_contra hbad
    have hb := lt_of_not_ge hbad
    have hc : w < e*u := by linarith
    nlinarith [mul_nonneg ha (show 0 ≤ e*u-w by linarith)]
  have hd : u ≤ (v/e+w)/e := (le_div_iff₀ he).mpr (by simpa only [mul_comm u e] using hn)
  have heq : (v/e+w)/e=v/e^2+w/e := by ring
  exact hd.trans_eq heq

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi*ε/3) (m g k t : ℝ)
local notation "hw" => wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k t

def bound (x : (H).domain) : ℝ :=
  ‖H x‖/Real.exp (2*t)+(|h| /ε*‖(x:Hilbert)‖)/Real.exp t

theorem cutoff_bound (N : ℝ) (hN : 0 < N) (x : (H).domain) :
    ‖action ε hε h N hN (x:Hilbert)‖ ≤ bound ε hε h hh hb m g k t x := by
  have hl := KFCausalClockFloorRadialYosidaHamiltonianPairing.hamiltonian_cutoff_pairing
    ε hε h hh hb m g k N hN t x
  have hc := re_inner_le_norm (𝕜 := ℂ) (H x) (action ε hε h N hN (x:Hilbert))
  change (inner ℂ (H x) (action ε hε h N hN (x:Hilbert))).re ≤ _ at hc
  have he : (Real.exp t)^2=Real.exp (2*t) := by rw [← Real.exp_nat_mul]; norm_num
  have hd : (|h| /ε*‖(x:Hilbert)‖)^2=(h^2/ε^2)*‖(x:Hilbert)‖^2 := by
    rw [mul_pow,div_pow,sq_abs]
  have hq := quadratic_bound ‖action ε hε h N hN (x:Hilbert)‖ ‖H x‖
    (|h| /ε*‖(x:Hilbert)‖) (Real.exp t) (norm_nonneg _)
    (by positivity) (Real.exp_pos t) (by rw [he,hd]; linarith)
  simpa only [he,bound] using hq

theorem radial_domain (x : (H).domain) : (x:Hilbert) ∈ (operator ε hε h).domain :=
  domain_of_uniform_bound ε hε h x (bound ε hε h hh hb m g k t x)
    (fun n => cutoff_bound ε hε h hh hb m g k t ((n:ℝ)+1) (by positivity) x)

theorem radial_norm (x : (H).domain) :
    ‖operator ε hε h ⟨(x:Hilbert),radial_domain ε hε h hh hb m g k t x⟩‖ ≤
      bound ε hε h hh hb m g k t x :=
  norm_of_uniform_bound ε hε h x (bound ε hε h hh hb m g k t x)
    (fun n => cutoff_bound ε hε h hh hb m g k t ((n:ℝ)+1) (by positivity) x)

#print axioms cutoff_bound
#print axioms radial_domain
#print axioms radial_norm
end
end UnifiedTheory.Audit.KFCausalClockFloorHamiltonianRadialDomination
