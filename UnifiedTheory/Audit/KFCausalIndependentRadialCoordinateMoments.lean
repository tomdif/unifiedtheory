/- Every charged-coordinate monomial times the actual independent-width
packet is square integrable. A sum of three already constructed radial
moments dominates it; no operator-domain conclusion is assumed. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPacketMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialCoordinateMoments
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalIndependentRadialPacketProfiles (chargeProfile chargeQuadratic_coordinates)
open KFCausalIndependentRadialPacketDerivatives (leftRadius rightRadius momentProfile radii_nonnegative)
open KFCausalIndependentRadialPacketMoments (moment_memLp)

def coordinate (c : ℝ) (x : Joint 2 4) : Fin 4 → ℝ :=
  ![c*x (.inl 0),c*x (.inl 1),x (.inr 1),x (.inr 2)]
def monomial (c : ℝ) (n : Fin 4 → ℕ) (x : Joint 2 4) : ℂ :=
  ∏ j, (coordinate c x j:ℂ)^(n j)
def profile (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (n : Fin 4 → ℕ) (x : Joint 2 4) : ℂ :=
  monomial c n x*chargeProfile α β wL wR c b P g x
def degree (n : Fin 4 → ℕ) : ℕ := ∑ j, n j
def bound (n : Fin 4 → ℕ) : ℝ := ((2:ℝ)^(degree n-1))^2

theorem coordinate_continuous (c : ℝ) (j : Fin 4) : Continuous (fun x => coordinate c x j) := by
  fin_cases j <;> dsimp [coordinate] <;> fun_prop

theorem monomial_continuous (c : ℝ) (n : Fin 4 → ℕ) : Continuous (monomial c n) := by
  unfold monomial
  exact continuous_finset_prod _ (fun j _ => ((Complex.continuous_ofReal.comp
    (coordinate_continuous c j)).pow (n j)))

theorem profile_continuous (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (g : ℝ → ℂ) (hc : Continuous g) (n : Fin 4 → ℕ) :
    Continuous (profile α β wL wR c b P g n) := by
  have hp : Continuous (chargeProfile α β wL wR c b P g) := by
    unfold chargeProfile
    simp only [chargeQuadratic_coordinates,KFCausalNeutralLinePackets.packet,
      KFCausalNeutralLinePackets.entire]
    fun_prop
  exact (monomial_continuous c n).mul hp

private theorem sum_power_bound (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (N : ℕ) :
    (1+X+Y)^N ≤ ((2:ℝ)^(N-1))^2*(1+X^N+Y^N) := by
  let k := (2:ℝ)^(N-1)
  have hk : 1 ≤ k := one_le_pow₀ (by norm_num)
  have h1 := add_pow_le (show 0 ≤ 1+X by positivity) hY N
  have h2 := add_pow_le (show (0:ℝ) ≤ 1 by norm_num) hX N
  simp only [one_pow] at h2
  change (1+X+Y)^N ≤ k^2*(1+X^N+Y^N)
  calc
    _ ≤ k*((1+X)^N+Y^N) := h1
    _ ≤ k*(k*(1+X^N)+Y^N) := by gcongr
    _ ≤ k*(k*(1+X^N)+k*Y^N) := by gcongr; nlinarith [pow_nonneg hY N]
    _ = _ := by ring

theorem monomial_bound (c : ℝ) (n : Fin 4 → ℕ) (x : Joint 2 4) :
    ‖monomial c n x‖ ≤ bound n*
      (1+(leftRadius c x)^(degree n)+(rightRadius c x)^(degree n)) := by
  obtain ⟨hX,hY⟩ := radii_nonnegative c x
  have hs (j : Fin 4) : (coordinate c x j)^2 ≤ leftRadius c x+rightRadius c x := by
    fin_cases j <;> dsimp [coordinate,leftRadius,rightRadius]
    all_goals nlinarith [sq_nonneg (c*x (.inl 0)),sq_nonneg (c*x (.inl 1)),
      sq_nonneg (x (.inr 1)),sq_nonneg (x (.inr 2))]
  have hc (j : Fin 4) : ‖(coordinate c x j:ℂ)‖ ≤ 1+leftRadius c x+rightRadius c x := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    nlinarith [hs j,sq_abs (coordinate c x j),sq_nonneg (|coordinate c x j|-1)]
  calc
    ‖monomial c n x‖ = ∏ j, ‖(coordinate c x j:ℂ)‖^(n j) := by simp only [monomial,norm_prod,norm_pow]
    _ ≤ ∏ j : Fin 4, (1+leftRadius c x+rightRadius c x)^(n j) := by
      apply Finset.prod_le_prod
      · intro j _; positivity
      · intro j _; exact pow_le_pow_left₀ (norm_nonneg _) (hc j) _
    _ = (1+leftRadius c x+rightRadius c x)^(degree n) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := sum_power_bound _ _ hX hY _

theorem monomial_memLp (α β wL wR c : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hL : 0 < wL) (hR : 0 < wR) (hmatch : Real.pi^2/α=α*c^2)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
    (n : Fin 4 → ℕ) : MemLp (profile α β wL wR c b P g n) 2 volume := by
  have hm := moment_memLp α β wL wR c hα hβ hL hR hmatch b P g hc hg
  let majorant := fun x => (bound n:ℂ)*(momentProfile α β wL wR c b P g 0 0 x+
    momentProfile α β wL wR c b P g (degree n) 0 x+
    momentProfile α β wL wR c b P g 0 (degree n) x)
  have hmajor : MemLp majorant 2 volume :=
    (((hm 0 0).add (hm (degree n) 0)).add (hm 0 (degree n))).const_mul (bound n:ℂ)
  apply hmajor.of_le (profile_continuous α β wL wR c b P g hc n).aestronglyMeasurable
  filter_upwards [] with x
  obtain ⟨hX,hY⟩ := radii_nonnegative c x
  have he : majorant x=((bound n*(1+(leftRadius c x)^(degree n)+(rightRadius c x)^(degree n)):ℝ):ℂ)*
      chargeProfile α β wL wR c b P g x := by
    dsimp [majorant,momentProfile]
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by unfold bound; positivity)]
  exact (show ‖profile α β wL wR c b P g n x‖ =
    ‖monomial c n x‖*‖chargeProfile α β wL wR c b P g x‖ by rw [profile,norm_mul]).trans_le
      (mul_le_mul_of_nonneg_right (monomial_bound c n x) (norm_nonneg _))

def state (α β wL wR c : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hL : 0 < wL) (hR : 0 < wR) (hmatch : Real.pi^2/α=α*c^2)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
    (n : Fin 4 → ℕ) : Hilbert := chargeCoordinates.symm
      ((monomial_memLp α β wL wR c hα hβ hL hR hmatch b P g hc hg n).toLp
        (profile α β wL wR c b P g n))

theorem state_charge_coe (α β wL wR c : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hL : 0 < wL) (hR : 0 < wR) (hmatch : Real.pi^2/α=α*c^2)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
    (n : Fin 4 → ℕ) :
    chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b P g hc hg n)=ᵐ[volume]
      profile α β wL wR c b P g n := by
  simp only [state,LinearIsometryEquiv.apply_symm_apply]
  exact (monomial_memLp α β wL wR c hα hβ hL hR hmatch b P g hc hg n).coeFn_toLp

#print axioms coordinate_continuous
#print axioms monomial_continuous
#print axioms profile_continuous
#print axioms monomial_bound
#print axioms monomial_memLp
#print axioms state_charge_coe
end
end UnifiedTheory.Audit.KFCausalIndependentRadialCoordinateMoments
