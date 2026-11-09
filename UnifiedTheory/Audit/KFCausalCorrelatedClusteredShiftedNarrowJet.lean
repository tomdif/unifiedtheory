/- The full clock derivative of the transformed clustered profile has a
polynomial limit and a spacing-independent pointwise envelope. No L2
convergence is inferred from these pointwise facts. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowFourierClockDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredShiftedNarrowJet
noncomputable section
open Filter
open scoped Topology
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalShiftedNarrowFourierGeometry (radius radius_re_nonnegative)
open KFCausalShiftedNarrowFourierClockDerivative (radiusSlope coefficientSlope coefficient_derivative radius_derivative)
open KFCausalCorrelatedClusteredShiftedNarrowProfiles (coefficient transformed limitTransformed)
open KFCausalClusteredWidthChargedJet (jet limitJet)

variable {m : ℕ} (f : Family m) (c cd : Fin m → ℂ) (α β : ℝ) (r rd t td : ℂ) (k : ℕ)
local notation "Z" => radius ((α:ℂ)*r^2)
local notation "Zd" => radiusSlope ((α:ℂ)*r^2) (2*(α:ℂ)*r*rd)
local notation "C" => coefficient f c α β r t k
local notation "Cd" => coefficientSlope f c cd α β r rd t td k

def clockJet (δ : ℝ) (u : Block 2) (v : Block 4) : ℂ :=
  ∑ i, (Cd i v*KFCausalReciprocalWedgeLaplace.laplaceSum (f.degree i+1)
      (KFCausalClusteredWidthProfiles.widths (f.degree i) δ)
      (KFCausalClusteredWidthProfiles.coefficients (f.degree i) δ) (Z u v)+
    C i v*jet (f.degree i) δ (Z u v)*Zd u v)

def limitClockJet (u : Block 2) (v : Block 4) : ℂ :=
  ∑ i, (Cd i v*(Complex.exp (-Z u v)*Z u v^(f.degree i))+
    C i v*limitJet (f.degree i) (Z u v)*Zd u v)

def envelope (u : Block 2) (v : Block 4) : ℝ :=
  ∑ i, (‖Cd i v‖*(Real.exp (-(Z u v).re)*‖Z u v‖^(f.degree i))+
    ‖C i v‖*(Real.exp (-(Z u v).re)*
      ((f.degree i:ℝ)*‖Z u v‖^(f.degree i-1)+‖Z u v‖^(f.degree i)))*‖Zd u v‖)

theorem clockJet_tendsto (u : Block 2) (v : Block 4) :
    Tendsto (fun δ => clockJet f c cd α β r rd t td k δ u v) (𝓝[>] 0)
      (𝓝 (limitClockJet f c cd α β r rd t td k u v)) :=
  tendsto_finset_sum _ (fun i _ =>
    ((KFCausalClusteredWidthProfiles.laplaceSum_tendsto (f.degree i) (Z u v)).const_mul _).add
      (((KFCausalClusteredWidthChargedJet.jet_tendsto (f.degree i) (Z u v)).const_mul _).mul_const _))

theorem envelope_nonnegative (u : Block 2) (v : Block 4) :
    0 ≤ envelope f c cd α β r rd t td k u v := by
  unfold envelope
  positivity

theorem clockJet_bound (hA : 0 ≤ ((α:ℂ)*r^2).re) (δ : ℝ) (hδ : 0 < δ)
    (u : Block 2) (v : Block 4) :
    ‖clockJet f c cd α β r rd t td k δ u v‖ ≤ envelope f c cd α β r rd t td k u v := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  have hz := radius_re_nonnegative ((α:ℂ)*r^2) hA u v
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (KFCausalClusteredWidthProfiles.laplaceSum_norm_le (f.degree i) δ hδ (Z u v) hz) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (KFCausalClusteredWidthChargedJet.jet_norm_le (f.degree i) δ hδ (Z u v) hz) (norm_nonneg _))
      (norm_nonneg _))

omit c cd r rd t td in
theorem transformed_derivative (c : ℝ → Fin m → ℂ) (cd : Fin m → ℂ)
    (r t : ℝ → ℂ) (rd td : ℂ) (s δ : ℝ) (hδ : 0 < δ) (u : Block 2) (v : Block 4)
    (hc : ∀ i, HasDerivAt (fun x => c x i) (cd i) s)
    (hr : HasDerivAt r rd s) (ht : HasDerivAt t td s) (hne : (α:ℂ)*(r s)^2 ≠ 0) :
    HasDerivAt (fun x => transformed f (c x) α β (r x) (t x) k δ u v)
      (clockJet f (c s) cd α β (r s) rd (t s) td k δ u v) s := by
  have hA : HasDerivAt (fun x => (α:ℂ)*(r x)^2) (2*(α:ℂ)*(r s)*rd) s := by
    convert (hr.pow 2).const_mul (α:ℂ) using 1
    simp only [Nat.cast_ofNat,show 2-1=1 from rfl,pow_one]
    ring
  have hZ := radius_derivative _ _ s u v hA hne
  apply HasDerivAt.fun_sum
  intro i _
  convert (coefficient_derivative f c cd α β r t rd td s k i v (hc i) hr ht hne).mul
    (KFCausalClusteredWidthChargedJet.moving_laplaceSum_derivative (f.degree i) δ hδ _ _ s hZ) using 1
  ring

omit c cd r rd t td in
theorem limitTransformed_derivative (c : ℝ → Fin m → ℂ) (cd : Fin m → ℂ)
    (r t : ℝ → ℂ) (rd td : ℂ) (s : ℝ) (u : Block 2) (v : Block 4)
    (hc : ∀ i, HasDerivAt (fun x => c x i) (cd i) s)
    (hr : HasDerivAt r rd s) (ht : HasDerivAt t td s) (hne : (α:ℂ)*(r s)^2 ≠ 0) :
    HasDerivAt (fun x => limitTransformed f (c x) α β (r x) (t x) k u v)
      (limitClockJet f (c s) cd α β (r s) rd (t s) td k u v) s := by
  have hA : HasDerivAt (fun x => (α:ℂ)*(r x)^2) (2*(α:ℂ)*(r s)*rd) s := by
    convert (hr.pow 2).const_mul (α:ℂ) using 1
    simp only [Nat.cast_ofNat,show 2-1=1 from rfl,pow_one]
    ring
  have hZ := radius_derivative _ _ s u v hA hne
  apply HasDerivAt.fun_sum
  intro i _
  convert (coefficient_derivative f c cd α β r t rd td s k i v (hc i) hr ht hne).mul
    ((hZ.neg.cexp).mul (hZ.pow (f.degree i))) using 1
  dsimp [limitJet]
  ring

#print axioms clockJet_tendsto
#print axioms envelope_nonnegative
#print axioms clockJet_bound
#print axioms transformed_derivative
#print axioms limitTransformed_derivative
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredShiftedNarrowJet
