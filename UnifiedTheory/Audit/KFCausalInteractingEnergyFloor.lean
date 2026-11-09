/- A uniform lower energy bound and sharpened resolvent estimate for the actual
interacting Hamiltonian. This is a bound above the chosen energy origin, not a
vacuum-subtracted excitation gap or a Yang--Mills mass-gap theorem. -/
import UnifiedTheory.Audit.KFCausalInteractingFreeFormSum
import UnifiedTheory.Audit.KFCausalClockFloorHamiltonianClockCore

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalInteractingEnergyFloor
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalClockFloorStaticMultiplierForm

theorem static_symbol_lower (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (x : KFCausalEuclideanProductCoordinates.Joint 5 1) : ε/2 ≤ symbol ε h x := by
  have h0 := KFCausalComplementaryChargeSymbol.complementaryWeight_nonnegative ε hε h 0 x
  have h1 := KFCausalComplementaryChargeSymbol.complementaryWeight_nonnegative ε hε h 1 x
  unfold symbol KFCausalClockFloorFlow.clock
  linarith [Real.exp_pos (x (.inr 0))]

theorem static_root_lower (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f : (rootOperator ε hε h).domain) :
    ε/2*‖(f:Hilbert)‖^2 ≤ ‖rootOperator ε hε h f‖^2 := by
  have he := KFCausalUnitaryRealMultiplier.realPullback_coe dualPhysical
    (rootSymbol ε h) ((symbol_continuous ε hε h).sqrt.measurable) f
  change dualPhysical (rootOperator ε hε h f) =ᵐ[volume]
    (fun x => (rootSymbol ε h x:ℂ)*(dualPhysical (f:Hilbert)) x) at he
  have hi (z : Hilbert) : Integrable (fun x => ‖(dualPhysical z) x‖^2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hn (z : Hilbert) : ‖z‖^2 = ∫ x, ‖(dualPhysical z) x‖^2 :=
    (congrArg (fun r : ℝ => r^2) (dualPhysical.norm_map z)).symm.trans
      (KFCausalAveragedEnergyGraph.l2_norm_square volume (dualPhysical z))
  rw [hn (f:Hilbert),hn (rootOperator ε hε h f),← integral_const_mul]
  apply integral_mono_ae ((hi f).const_mul (ε/2)) (hi _)
  filter_upwards [he] with x hx
  rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    rootSymbol_square ε hε h]
  exact mul_le_mul_of_nonneg_right (static_symbol_lower ε hε h x) (sq_nonneg _)

theorem free_form_lower (ε : ℝ) (hε : 0 < ε) (h t : ℝ)
    (u : KFCausalClockFloorFreeHamiltonianFormSum.FormDomain ε hε h) :
    ε/2*‖u.val‖^2 ≤ (KFCausalClockFloorFreeHamiltonianFormSum.pairing ε hε h t u u).re := by
  have hs := static_root_lower ε hε h ⟨u.val,u.property.2⟩
  have hp : (KFCausalClockFloorFreeHamiltonianFormSum.pairing ε hε h t u u).re =
      ‖rootOperator ε hε h ⟨u.val,u.property.2⟩‖^2 + Real.exp (2*t)*
        ‖KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
          ⟨u.val,u.property.1⟩‖^2 := by
    simp only [KFCausalClockFloorFreeHamiltonianFormSum.pairing,inner_self_eq_norm_sq_to_K]
    change ((‖rootOperator ε hε h ⟨u.val,u.property.2⟩‖:ℂ)^2 +
      (Real.exp (2*t):ℂ)*(‖KFCausalClockFloorGrowingRadialMultiplierForm.rootOperator ε hε h
        ⟨u.val,u.property.1⟩‖:ℂ)^2).re = _
    rw [← Complex.ofReal_pow,← Complex.ofReal_pow,← Complex.ofReal_mul,
      ← Complex.ofReal_add,Complex.ofReal_re]
  rw [hp]
  exact hs.trans (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hpos : 0 < h)
  (hb : |h| ≤ Real.pi*ε/3) (m g k : ℝ) (hk : 0 < k)
local notation "hw" => KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hb
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hpos.ne' hw m g k

include hk in
theorem graph_energy_lower (t : ℝ) (f y : Hilbert) (hy : (f,y) ∈ (H t).graph) :
    ε/2*‖f‖^2 ≤ (inner ℂ y f).re := by
  obtain ⟨u,hu,he⟩ := KFCausalInteractingFreeFormSum.hamiltonian_energy_split
    ε hε h hpos hb m g k hk t f y hy
  rw [he]
  have hf := free_form_lower ε hε h t (KFCausalInteractingFreeFormSum.freeView ε hε h hpos hb m g k u)
  change ε/2*‖u.val‖^2 ≤ _ at hf
  rw [hu] at hf
  exact hf.trans (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))

include hk in
theorem eigenvalue_lower (t lam : ℝ) (f : Hilbert) (hf : f ≠ 0)
    (he : (f,(lam:ℂ) • f) ∈ (H t).graph) : ε/2 ≤ lam := by
  have hb' := graph_energy_lower ε hε h hpos hb m g k hk t f _ he
  have hp : (inner ℂ ((lam:ℂ) • f) f).re = lam*‖f‖^2 := by
    rw [inner_smul_left,Complex.conj_ofReal]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact congrArg (fun r : ℝ => lam*r) (inner_self_eq_norm_sq (𝕜 := ℂ) f)
  rw [hp] at hb'
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (norm_pos_iff.mpr hf))).mp hb'

include hk in
theorem resolvent_norm_le (t a : ℝ) (ha : 0 < a) (f : Hilbert) :
    ‖KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hpos.ne' hw m g k t a f‖ ≤
      ‖f‖/(a+ε/2) := by
  let R := KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hpos.ne' hw m g k t a
  have hr := KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hpos.ne' hw m g k t a ha f
  have hg : (R f,f-a • R f) ∈ (H t).graph :=
    (H t).mem_graph_iff.mpr ⟨⟨R f,hr.1⟩,rfl,hr.2⟩
  have hl := graph_energy_lower ε hε h hpos hb m g k hk t (R f) _ hg
  have he : (inner ℂ (f-a • R f) (R f)).re =
      (inner ℂ f (R f)).re-a*‖R f‖^2 := by
    rw [inner_sub_left,inner_smul_left_eq_smul]
    simp only [Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    exact congrArg (fun r : ℝ => (inner ℂ f (R f)).re-a*r)
      (inner_self_eq_norm_sq (𝕜 := ℂ) (R f))
  rw [he] at hl
  have hi := re_inner_le_norm (𝕜 := ℂ) f (R f)
  change (inner ℂ f (R f)).re ≤ ‖f‖*‖R f‖ at hi
  change ‖R f‖ ≤ _
  by_cases hz : R f = 0
  · rw [hz,norm_zero]
    positivity
  have hn := norm_pos_iff.mpr hz
  apply (le_div_iff₀ (by positivity : 0 < a+ε/2)).mpr
  apply (mul_le_mul_iff_right₀ hn).mp
  nlinarith

#print axioms static_root_lower
#print axioms free_form_lower
#print axioms graph_energy_lower
#print axioms eigenvalue_lower
#print axioms resolvent_norm_le
end
end UnifiedTheory.Audit.KFCausalInteractingEnergyFloor
