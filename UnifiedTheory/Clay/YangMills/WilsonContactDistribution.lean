/- The constructed Wilson diagonal counterterm is an actual continuous linear
functional on the full two-point Schwartz space at every positive cutoff.
Its coefficient bound can diverge with the cutoff; no interacting limit follows. -/
import UnifiedTheory.Clay.YangMills.WilsonCompactContactSubtraction
import UnifiedTheory.Clay.YangMills.SchwartzWeightedTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonContactDistribution
noncomputable section
open MeasureTheory LocalFields RegulatedGauge PeriodicLattice4
open SchwartzDiagonalTaylor WilsonNoiseTubeMass WilsonCompactContactSubtraction

section Taylor
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem jet_add (f g : SchwartzMap E ℂ) (m : ℕ) (x h : E) :
    jet (f + g) m x h = jet f m x h + jet g m x h := by
  unfold jet
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  change (j.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ j (fun y => f y + g y) x (fun _ => h) = _
  rw [iteratedFDeriv_add_apply' (f.smooth j).contDiffAt (g.smooth j).contDiffAt]
  simp only [ContinuousMultilinearMap.add_apply, smul_add]

theorem jet_smul (c : ℂ) (f : SchwartzMap E ℂ) (m : ℕ) (x h : E) :
    jet (c • f) m x h = c • jet f m x h := by
  unfold jet
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (j.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ j (fun y => c • f y) x (fun _ => h) = _
  rw [iteratedFDeriv_const_smul_apply' (f.smooth j).contDiffAt]
  rw [ContinuousMultilinearMap.smul_apply, smul_comm]

/-- A single finite seminorm controls every term of the Taylor jet. -/
theorem jet_bound (f : SchwartzMap E ℂ) (m : ℕ) (x h : E)
    (r : ℝ) (hh : ‖h‖ ≤ r) :
    ‖jet f m x h‖ ≤
      (∑ j ∈ Finset.range (m + 1), (j.factorial : ℝ)⁻¹ * r ^ j) *
        (Finset.Iic (0, m)).sup (schwartzSeminormFamily ℂ E ℂ) f := by
  let p := (Finset.Iic (0, m)).sup (schwartzSeminormFamily ℂ E ℂ) f
  unfold jet
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1),
        ‖(j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j f x (fun _ => h)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (m + 1), (j.factorial : ℝ)⁻¹ * r ^ j * p := by
      apply Finset.sum_le_sum
      intro j hj
      have hjm : j ≤ m := Finset.mem_range_succ_iff.mp hj
      have hd : ‖iteratedFDeriv ℝ j f x‖ ≤ p := by
        simpa only [pow_zero, one_mul, schwartzSeminormFamily] using
          SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
            (m := (0, m)) (k := 0) (by rfl) hjm f x
      have he := (iteratedFDeriv ℝ j f x).le_opNorm (fun _ => h)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at he
      have hjpos : 0 ≤ (j.factorial : ℝ)⁻¹ := by positivity
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hjpos]
      calc
        _ ≤ (j.factorial : ℝ)⁻¹ * (p * r ^ j) := by
          apply mul_le_mul_of_nonneg_left _ hjpos
          exact he.trans (mul_le_mul hd (pow_le_pow_left₀ (norm_nonneg _) hh j)
            (by positivity) (apply_nonneg _ _))
        _ = _ := by ring
    _ = _ := by rw [Finset.sum_mul]

end Taylor

section Kernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E) [μ.HasTemperateGrowth]

/-- Every bounded measurable kernel gives a continuous Schwartz functional. -/
def boundedKernelCLM (w : E → ℂ) (hw : AEStronglyMeasurable w μ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖w x‖ ≤ C) : SchwartzMap E ℂ →L[ℂ] ℂ := by
  have hi (f : SchwartzMap E ℂ) :=
    SchwartzWeightedTail.bounded_mul_integrable μ w hw C hC hbound f
  refine SchwartzMap.mkCLMtoNormedSpace (fun f => ∫ x, w x * f x ∂μ) ?_ ?_ ?_
  · intro f g
    simp only [SchwartzMap.add_apply, mul_add]
    exact integral_add (hi f) (hi g)
  · intro c f
    simp only [SchwartzMap.smul_apply, mul_smul_comm]
    exact integral_smul c _
  · let K := μ.integrablePower
    let D := 2 ^ K * ∫ x, (1 + ‖x‖) ^ (-(K : ℝ)) ∂μ
    have hD : 0 ≤ D := by dsimp [D]; positivity
    refine ⟨Finset.Iic (K, 0), 2 * C * D, by positivity, ?_⟩
    intro f
    let p := (Finset.Iic (K, 0)).sup (schwartzSeminormFamily ℂ E ℂ) f
    have h0 : SchwartzMap.seminorm ℂ 0 0 f ≤ p :=
      Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ E ℂ)
        (s := Finset.Iic (K, 0)) (i := (0, 0)) (x := f)
        (Finset.mem_Iic.mpr ⟨Nat.zero_le K, le_rfl⟩)
    have hK : SchwartzMap.seminorm ℂ K 0 f ≤ p :=
      Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ E ℂ)
        (s := Finset.Iic (K, 0)) (i := (K, 0)) (x := f)
        (Finset.mem_Iic.mpr le_rfl)
    have hm : (∫ x, ‖f x‖ ∂μ) ≤ D *
        (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ K 0 f) := by
      simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul, zero_add] using
        SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ μ f 0 0
    have hn : ‖∫ x, w x * f x ∂μ‖ ≤ ∫ x, C * ‖f x‖ ∂μ :=
      norm_integral_le_of_norm_le (f.integrable.norm.const_mul C)
      (Filter.Eventually.of_forall (fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg (f x))))
    rw [integral_const_mul] at hn
    calc
      _ ≤ C * (∫ x, ‖f x‖ ∂μ) := hn
      _ ≤ C * (D * (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ K 0 f)) := mul_le_mul_of_nonneg_left hm hC
      _ ≤ C * (D * (p + p)) := by gcongr
      _ = _ := by ring

end Kernel

variable (n : ℕ) [NeZero n]

theorem contact4_add (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (f g : SchwartzMap (Spacetime × Spacetime) ℂ) :
    contact4 n β a R S plane plane' (f + g) =
      contact4 n β a R S plane plane' f + contact4 n β a R S plane plane' g := by
  unfold contact4 diagonalJet
  simp_rw [jet_add, mul_add]
  exact integral_add
    (truncated_mul_continuous_integrable n β a R S plane plane'
      (diagonalJet f 4) (diagonalJet_continuous f 4))
    (truncated_mul_continuous_integrable n β a R S plane plane'
      (diagonalJet g 4) (diagonalJet_continuous g 4))

theorem contact4_smul (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (c : ℂ) (f : SchwartzMap (Spacetime × Spacetime) ℂ) :
    contact4 n β a R S plane plane' (c • f) = c • contact4 n β a R S plane plane' f := by
  unfold contact4 diagonalJet
  simp_rw [jet_smul, mul_smul_comm]
  exact integral_smul c _

/-- The finite-cutoff continuity constant is explicit, without an assumed distribution. -/
theorem contact4_bound (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (ha : 0 < a) (f : SchwartzMap (Spacetime × Spacetime) ℂ) :
    ‖contact4 n β a R S plane plane' f‖ ≤
      ((massConstant R / a ^ 4) *
        (∑ j ∈ Finset.range 5, (j.factorial : ℝ)⁻¹ * (4 * a) ^ j)) *
        (Finset.Iic (0, 4)).sup (schwartzSeminormFamily ℂ (Spacetime × Spacetime) ℂ) f := by
  let P := (∑ j ∈ Finset.range 5, (j.factorial : ℝ)⁻¹ * (4 * a) ^ j) *
    (Finset.Iic (0, 4)).sup (schwartzSeminormFamily ℂ (Spacetime × Spacetime) ℂ) f
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hp (z : Spacetime × Spacetime) :
      ‖(truncated n β a R S plane plane' z : ℂ) * diagonalJet f 4 z‖ ≤
        |truncated n β a R S plane plane' z| * P := by
    by_cases hz : truncated n β a R S plane plane' z = 0
    · simp only [hz, Complex.ofReal_zero, zero_mul, norm_zero, abs_zero, le_refl]
    have hd : ‖((0, z.2 - z.1) : Spacetime × Spacetime)‖ ≤ 4 * a := by
      simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using
        (truncated_support n β a R S plane plane' z hz).2
    have hj := jet_bound f 4 (z.1, z.1) (0, z.2 - z.1) (4 * a) hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hj (abs_nonneg _)
  have h := norm_integral_le_of_norm_le
    ((truncated_abs_integrable n β a R S plane plane').mul_const P)
    (Filter.Eventually.of_forall hp)
  rw [integral_mul_const] at h
  apply h.trans
  have hm := mul_le_mul_of_nonneg_right
    (truncated_mass_le n β a R S plane plane' ha) hP
  convert hm using 1
  dsimp [P]
  ring

/-- The actual diagonal counterterm, as a tempered distribution at fixed cutoff. -/
def contactCLM (β a R : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane)
    (ha : 0 < a) : SchwartzMap (Spacetime × Spacetime) ℂ →L[ℂ] ℂ := by
  refine SchwartzMap.mkCLMtoNormedSpace (contact4 n β a R S plane plane')
    (contact4_add n β a R S plane plane') (contact4_smul n β a R S plane plane') ?_
  refine ⟨Finset.Iic (0, 4), (massConstant R / a ^ 4) *
    (∑ j ∈ Finset.range 5, (j.factorial : ℝ)⁻¹ * (4 * a) ^ j), ?_, ?_⟩
  · exact mul_nonneg (div_nonneg (massConstant_nonneg R) (by positivity))
      (Finset.sum_nonneg (fun _ _ => by positivity))
  · exact contact4_bound n β a R S plane plane' ha

theorem contactCLM_apply (β a R : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane)
    (ha : 0 < a) (f : SchwartzMap (Spacetime × Spacetime) ℂ) :
    contactCLM n β a R S plane plane' ha f = contact4 n β a R S plane plane' f := rfl

theorem contactCLM_diagonal_support (β a R : ℝ) (S : Finset (Edge (Vertex n)))
    (plane plane' : Plane) (ha : 0 < a) (f : SchwartzMap (Spacetime × Spacetime) ℂ)
    (hf : ∀ x : Spacetime, (x, x) ∉ tsupport f) :
    contactCLM n β a R S plane plane' ha f = 0 :=
  contact4_eq_zero_of_diagonal_disjoint n β a R S plane plane' f hf

local instance pairVolumeHaar :
    (volume : Measure (Spacetime × Spacetime)).IsAddHaarMeasure := by
  change (volume.prod volume).IsAddHaarMeasure
  infer_instance

/-- The literal periodic sampled removed kernel is a tempered distribution. -/
def pairingCLM (β a : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane) :
    SchwartzMap (Spacetime × Spacetime) ℂ →L[ℂ] ℂ :=
  boundedKernelCLM volume
    (fun z => (WilsonNoisePhysicalSupport.kernel n β a S plane plane' z.1 z.2 : ℂ))
    ((Complex.continuous_ofReal.measurable.comp
      (WilsonNoisePhysicalSupport.kernel_measurable n β a S plane plane')).aestronglyMeasurable)
    (16 / a ^ 8) (by positivity)
    (fun z => by simpa only [Complex.norm_real, Real.norm_eq_abs] using
      WilsonNoisePhysicalSupport.kernel_abs_le n β a S plane plane' z.1 z.2)

theorem pairingCLM_apply (β a : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane)
    (f : SchwartzMap (Spacetime × Spacetime) ℂ) :
    pairingCLM n β a S plane plane' f = pairing n β a S plane plane' f := rfl

/-- Actual subtraction takes place in the continuous dual of the Schwartz space. -/
def remainderCLM (β a R : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane)
    (ha : 0 < a) : SchwartzMap (Spacetime × Spacetime) ℂ →L[ℂ] ℂ :=
  pairingCLM n β a S plane plane' - contactCLM n β a R S plane plane' ha

theorem remainderCLM_apply (β a R : ℝ) (S : Finset (Edge (Vertex n))) (plane plane' : Plane)
    (ha : 0 < a) (f : SchwartzMap (Spacetime × Spacetime) ℂ) :
    remainderCLM n β a R S plane plane' ha f =
      pairing n β a S plane plane' f - contact4 n β a R S plane plane' f := rfl

end
end UnifiedTheory.Clay.YangMills.WilsonContactDistribution
