/- A lower bound on the norm of the twisted transfer operator that is polynomial in the coupling per
link, from Gaussian integrals around the flat slice. No exponential-in-`β` loss occurs because the
twisted slice has an exact zero-action field. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSliceLift
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedNormLower
noncomputable section
open MeasureTheory PeriodicLattice4 TwistedFlat TwistedStability TwistedSeams TwistedSliceLift
open WilsonTimeSlab WilsonSlabOperator TwistedTransfer TwistedLocalization
open WilsonSingleLinkStaples (character)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

/-- The flat slice. -/
def flatSlice : Slice n := fun e => flatLink (Fin.cases (0 : ZMod n) e.1 : Vertex n) e.2.succ

theorem lift_flatSlice : lift n (flatSlice n) = flatLink := by
  funext x μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp [lift_zero, flatLink]
  · rw [lift_succ]
    unfold flatSlice flatLink
    have h1 : (Fin.cases (0 : ZMod n) (sp n x) : Vertex n) 1 = x 1 := rfl
    have h2 : (Fin.cases (0 : ZMod n) (sp n x) : Vertex n) 2 = x 2 := rfl
    simp only [h1, h2]

/-- Squared distance of a slice to the flat slice. -/
def dist (u : Slice n) : ℝ := ∑ e, d (u e) (flatSlice n e) ^ 2

/-- Squared distance of a gauge to the identity. -/
def gaugeDist (h : SliceGauge n Q) : ℝ := ∑ x, d (h x) 1 ^ 2

theorem plane_sum (g : Fin 3 → Fin 3 → ℝ) :
    ∑ p : SpatialPlane, g p.1.1 p.1.2 = g 0 1 + g 0 2 + g 1 2 := by
  have h : ∑ d ∈ Finset.univ.filter (fun d : Fin 3 × Fin 3 => d.1 < d.2), g d.1 d.2 =
      ∑ p : SpatialPlane, g p.1.1 p.1.2 := Finset.sum_subtype _ (by simp) _
  rw [← h, Finset.sum_filter, Fintype.sum_prod_type]
  simp (decide := true) only [Fin.sum_univ_three, if_true, if_false]
  ring

/-- Translation of a sum over spatial vertices. -/
theorem sum_spatialStep (f : SpatialVertex n → ℝ) (i : Fin 3) :
    ∑ x, f (spatialStep n x i) = ∑ x, f x := by
  have := Equiv.sum_comp (Equiv.addRight (Pi.single i (1 : ZMod n) : SpatialVertex n)) f
  simpa [spatialStep] using this

/-- The twisted potential is at most `16` times the squared distance to the flat slice. -/
theorem potential_le (u : Slice n) : twistedPotential n u ≤ 16 * dist n u := by
  have hterm (x : SpatialVertex n) (p : SpatialPlane) :
      2 - spatialSign n x p * (character (spatialHolonomy u x p.1.1 p.1.2)).re ≤
        4 * (d (u (x, p.1.1)) (flatSlice n (x, p.1.1)) ^ 2 +
          d (u (spatialStep n x p.1.1, p.1.2)) (flatSlice n (spatialStep n x p.1.1, p.1.2)) ^ 2 +
          d (u (spatialStep n x p.1.2, p.1.1)) (flatSlice n (spatialStep n x p.1.2, p.1.1)) ^ 2 +
          d (u (x, p.1.2)) (flatSlice n (x, p.1.2)) ^ 2) := by
    set t : Vertex n := Fin.cases 0 x with ht
    have hsp : sp n t = x := rfl
    have h := potential_term_eq n u t p
    rw [hsp] at h
    rw [h]
    rcases p with ⟨⟨i, j⟩, hij⟩
    simp only
    have hneq : (i.succ : Fin 4) < j.succ := Fin.succ_lt_succ_iff.mpr hij
    have hfl := flatLink_flat (N := n) t i.succ j.succ hneq
    unfold TwistedStability.defect
    rw [← hfl]
    have hf := four (lift n u t i.succ) (lift n u (step n t i.succ) j.succ)
      (lift n u (step n t j.succ) i.succ) (lift n u t j.succ)
      (flatLink t i.succ) (flatLink (step n t i.succ) j.succ)
      (flatLink (step n t j.succ) i.succ) (flatLink t j.succ)
    have hflat (y : Vertex n) (k : Fin 3) : flatLink y k.succ = flatSlice n (sp n y, k) := by
      rw [← lift_flatSlice n, lift_succ]
    simp only [hflat, lift_succ, sp_step_succ, hsp] at hf ⊢
    set a := d (u (x, i)) (flatSlice n (x, i))
    set b := d (u (spatialStep n x i, j)) (flatSlice n (spatialStep n x i, j))
    set c := d (u (spatialStep n x j, i)) (flatSlice n (spatialStep n x j, i))
    set e := d (u (x, j)) (flatSlice n (x, j))
    have hsq := pow_le_pow_left₀ (d_nonneg _ _) hf 2
    refine hsq.trans ?_
    nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c),
      sq_nonneg (b - e), sq_nonneg (c - e)]
  let M : Fin 3 → ℝ := fun i => ∑ x, d (u (x, i)) (flatSlice n (x, i)) ^ 2
  have hM (i j : Fin 3) : ∑ x, (d (u (x, i)) (flatSlice n (x, i)) ^ 2 +
      d (u (spatialStep n x i, j)) (flatSlice n (spatialStep n x i, j)) ^ 2 +
      d (u (spatialStep n x j, i)) (flatSlice n (spatialStep n x j, i)) ^ 2 +
      d (u (x, j)) (flatSlice n (x, j)) ^ 2) = 2 * M i + 2 * M j := by
    simp only [Finset.sum_add_distrib]
    rw [sum_spatialStep n (fun y => d (u (y, j)) (flatSlice n (y, j)) ^ 2) i,
      sum_spatialStep n (fun y => d (u (y, i)) (flatSlice n (y, i)) ^ 2) j]
    change M i + M j + M i + M j = _
    ring
  have hdist : dist n u = M 0 + M 1 + M 2 := by
    unfold dist
    rw [Fintype.sum_prod_type, Finset.sum_comm, Fin.sum_univ_three]
  unfold twistedPotential
  calc _ ≤ ∑ x : SpatialVertex n, ∑ p : SpatialPlane,
        4 * (d (u (x, p.1.1)) (flatSlice n (x, p.1.1)) ^ 2 +
          d (u (spatialStep n x p.1.1, p.1.2)) (flatSlice n (spatialStep n x p.1.1, p.1.2)) ^ 2 +
          d (u (spatialStep n x p.1.2, p.1.1)) (flatSlice n (spatialStep n x p.1.2, p.1.1)) ^ 2 +
          d (u (x, p.1.2)) (flatSlice n (x, p.1.2)) ^ 2) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun p _ => hterm x p
    _ = ∑ p : SpatialPlane, 4 * (2 * M p.1.1 + 2 * M p.1.2) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.mul_sum, hM]
    _ = 16 * dist n u := by
        refine (plane_sum (fun i j => 4 * (2 * M i + 2 * M j))).trans ?_
        rw [hdist]
        ring

/-- The temporal action is controlled by the three distances. -/
theorem temporal_le (u v : Slice n) (h : SliceGauge n Q) :
    temporalAction character 2 u v h ≤ 4 * dist n u + 4 * dist n v + 24 * gaugeDist n h := by
  rw [temporalAction_eq _ WilsonSingleLinkStaples.character_classFunction]
  have hk : kineticAction character 2 u (gaugeSlice h v) =
      ∑ e, d (u e) (gaugeSlice h v e) ^ 2 := by
    unfold kineticAction
    exact Finset.sum_congr rfl fun e _ => kinetic_term _ _
  rw [hk]
  have hterm (e : SpatialVertex n × Fin 3) : d (u e) (gaugeSlice h v e) ^ 2 ≤
      4 * (d (u e) (flatSlice n e) ^ 2 + d (v e) (flatSlice n e) ^ 2 +
        d (h e.1) 1 ^ 2 + d (h (spatialStep n e.1 e.2)) 1 ^ 2) := by
    set F := flatSlice n e
    set a := h e.1
    set b := h (spatialStep n e.1 e.2)
    have ht1 := d_triangle (u e) F (a * v e * b⁻¹)
    have ht2 := d_triangle F (a * F * b⁻¹) (a * v e * b⁻¹)
    have ht3 := d_triangle F (a * F) (a * F * b⁻¹)
    have e1 : d F (a * F) = d a 1 := by
      have := d_mul_right F 1 a
      rw [one_mul] at this
      rw [this, d_comm]
    have e2 : d (a * F) (a * F * b⁻¹) = d b 1 := by
      have := d_mul_left (a * F) 1 b⁻¹
      rw [mul_one] at this
      rw [this]
      have h3 := d_mul_right b 1 b⁻¹
      rw [one_mul, inv_mul_cancel] at h3
      rw [← h3, d_comm]
    have e3 : d (a * F * b⁻¹) (a * v e * b⁻¹) = d F (v e) := by
      rw [d_mul_right, d_mul_left]
    have e4 : d F (v e) = d (v e) F := d_comm _ _
    have hsum : d (u e) (a * v e * b⁻¹) ≤ d (u e) F + d (v e) F + d a 1 + d b 1 := by
      linarith only [ht1, ht2, ht3, e1, e2, e3, e4]
    have hsq := pow_le_pow_left₀ (d_nonneg _ _) hsum 2
    change d (u e) (a * v e * b⁻¹) ^ 2 ≤ _
    refine hsq.trans ?_
    nlinarith only [sq_nonneg (d (u e) F - d (v e) F), sq_nonneg (d (u e) F - d a 1),
      sq_nonneg (d (u e) F - d b 1), sq_nonneg (d (v e) F - d a 1), sq_nonneg (d (v e) F - d b 1),
      sq_nonneg (d a 1 - d b 1)]
  refine (Finset.sum_le_sum fun e _ => hterm e).trans ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ e : SpatialVertex n × Fin 3, (d (u e) (flatSlice n e) ^ 2 + d (v e) (flatSlice n e) ^ 2 +
      d (h e.1) 1 ^ 2 + d (h (spatialStep n e.1 e.2)) 1 ^ 2) =
      dist n u + dist n v + 6 * gaugeDist n h := by
    simp only [Finset.sum_add_distrib]
    have h1 : ∑ e : SpatialVertex n × Fin 3, d (h e.1) 1 ^ 2 = 3 * gaugeDist n h := by
      rw [Fintype.sum_prod_type]
      simp [gaugeDist, Finset.mul_sum]
    have h2 : ∑ e : SpatialVertex n × Fin 3, d (h (spatialStep n e.1 e.2)) 1 ^ 2 =
        3 * gaugeDist n h := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [sum_spatialStep n (fun y => d (h y) 1 ^ 2)]
      simp [gaugeDist]
    rw [h1, h2]
    unfold dist
    ring
  rw [hsum]
  linarith only [le_refl (0 : ℝ)]

/-! ### Gaussian integrals -/

/-- Number of slice links. -/
def links : ℕ := Fintype.card (SpatialVertex n × Fin 3)

/-- Number of slice vertices. -/
def sites : ℕ := Fintype.card (SpatialVertex n)

theorem links_eq : links n = 3 * n ^ 3 := by
  simp [links, ZMod.card, mul_comm]

theorem sites_eq : sites n = n ^ 3 := by
  simp [sites, ZMod.card]

theorem gauss_slice (s : ℝ) :
    ∫ u, Real.exp (-s * dist n u) ∂WilsonSlabOperator.measure n =
      SU2GaussianMass.mass s ^ links n := by
  have h := integral_fintype_prod_eq_prod (ι := SpatialVertex n × Fin 3) (E := fun _ => Q)
    (fun e q => Real.exp (-s * d q (flatSlice n e) ^ 2))
    (μ := fun _ => RegulatedGauge.compactHaar Q)
  have hp (u : Slice n) : Real.exp (-s * dist n u) =
      ∏ e, Real.exp (-s * d (u e) (flatSlice n e) ^ 2) := by
    rw [← Real.exp_sum, dist, Finset.mul_sum]
  simp only [hp]
  refine h.trans ?_
  simp only [gaussian_translate, Finset.prod_const, Finset.card_univ, links]

theorem gauss_gauge (s : ℝ) :
    ∫ h, Real.exp (-s * gaugeDist n h) ∂(temporalHaar (n := n) (G := Q)) =
      SU2GaussianMass.mass s ^ sites n := by
  have h := integral_fintype_prod_eq_prod (ι := SpatialVertex n) (E := fun _ => Q)
    (fun _ q => Real.exp (-s * d q 1 ^ 2)) (μ := fun _ => RegulatedGauge.compactHaar Q)
  have hp (k : SliceGauge n Q) : Real.exp (-s * gaugeDist n k) = ∏ x, Real.exp (-s * d (k x) 1 ^ 2) := by
    rw [← Real.exp_sum, gaugeDist, Finset.mul_sum]
  simp only [hp]
  refine h.trans ?_
  simp only [gaussian_translate, Finset.prod_const, Finset.card_univ, sites]

theorem dist_continuous : Continuous (dist n) := by
  unfold dist d
  fun_prop

theorem gaugeDist_continuous : Continuous (gaugeDist n) := by
  unfold gaugeDist d
  fun_prop

theorem temporal_continuous (u v : Slice n) :
    Continuous fun h : SliceGauge n Q => temporalAction character 2 u v h := by
  have hc := WilsonSingleLinkStaples.character_continuous
  unfold temporalAction temporalHolonomy
  fun_prop

/-- Pointwise lower bound on the twisted kernel. -/
theorem kernel_lower (β : ℝ) (hβ : 0 ≤ β) (u v : Slice n) :
    Real.exp (-(12 * β) * dist n u) * Real.exp (-(12 * β) * dist n v) *
        SU2GaussianMass.mass (24 * β) ^ sites n ≤ twistedKernel n β (u, v) := by
  rw [twistedKernel_eq]
  have hpu := potential_le n u
  have hpv := potential_le n v
  have hI : Real.exp (-(4 * β) * dist n u - (4 * β) * dist n v) *
      SU2GaussianMass.mass (24 * β) ^ sites n ≤
      ∫ h, Real.exp (-β * temporalAction character 2 u v h) ∂(temporalHaar (n := n) (G := Q)) := by
    rw [← gauss_gauge, ← integral_const_mul]
    refine integral_mono
      ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul (gaugeDist_continuous n)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      ((Real.continuous_exp.comp (continuous_const.mul
        (temporal_continuous n u v))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) fun h => ?_
    dsimp only
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left (temporal_le n u v h) hβ
    nlinarith only [this]
  have hE1 : Real.exp (-(8 * β) * dist n u) ≤ Real.exp (-(β / 2) * twistedPotential n u) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hpu hβ]
  have hE2 : Real.exp (-(8 * β) * dist n v) ≤ Real.exp (-(β / 2) * twistedPotential n v) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hpv hβ]
  have hmass : 0 ≤ SU2GaussianMass.mass (24 * β) ^ sites n :=
    pow_nonneg (SU2GaussianMass.mass_pos _).le _
  have e : Real.exp (-(12 * β) * dist n u) * Real.exp (-(12 * β) * dist n v) *
      SU2GaussianMass.mass (24 * β) ^ sites n =
      Real.exp (-(8 * β) * dist n u) * (Real.exp (-(4 * β) * dist n u - (4 * β) * dist n v) *
        SU2GaussianMass.mass (24 * β) ^ sites n) * Real.exp (-(8 * β) * dist n v) := by
    have e1 : Real.exp (-(12 * β) * dist n u) =
        Real.exp (-(8 * β) * dist n u) * Real.exp (-(4 * β) * dist n u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-(12 * β) * dist n v) =
        Real.exp (-(8 * β) * dist n v) * Real.exp (-(4 * β) * dist n v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e3 : Real.exp (-(4 * β) * dist n u - (4 * β) * dist n v) =
        Real.exp (-(4 * β) * dist n u) * Real.exp (-(4 * β) * dist n v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e1, e2, e3]
    ring
  rw [e]
  have hq : 0 ≤ Real.exp (-(4 * β) * dist n u - (4 * β) * dist n v) *
      SU2GaussianMass.mass (24 * β) ^ sites n := by positivity
  exact mul_le_mul (mul_le_mul hE1 hI hq (Real.exp_pos _).le) hE2 (Real.exp_pos _).le
    (mul_nonneg (Real.exp_pos _).le ((hq).trans hI))

/-- **Polynomial lower bound on the top eigenvalue.** -/
theorem norm_lower (β : ℝ) (hβ : 0 ≤ β) :
    SU2GaussianMass.mass (12 * β) ^ links n * SU2GaussianMass.mass (12 * β) ^ links n *
        SU2GaussianMass.mass (24 * β) ^ sites n ≤ ‖TwistedTransfer.transfer n β‖ := by
  have hk := kernel_lower n β hβ
  set μ₀ := WilsonSlabOperator.measure n
  have hint : Integrable (fun p : Slice n × Slice n => twistedKernel n β p) (μ₀.prod μ₀) :=
    (twistedKernel n β).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hc1 : Continuous fun u : Slice n => Real.exp (-(12 * β) * dist n u) :=
    Real.continuous_exp.comp (continuous_const.mul (dist_continuous n))
  have hprod : Integrable (fun p : Slice n × Slice n =>
      Real.exp (-(12 * β) * dist n p.1) * Real.exp (-(12 * β) * dist n p.2) *
        SU2GaussianMass.mass (24 * β) ^ sites n) (μ₀.prod μ₀) :=
    (((hc1.comp continuous_fst).mul (hc1.comp continuous_snd)).mul
      continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlow := integral_mono hprod hint fun p => hk p.1 p.2
  have hval : ∫ p : Slice n × Slice n, Real.exp (-(12 * β) * dist n p.1) *
      Real.exp (-(12 * β) * dist n p.2) * SU2GaussianMass.mass (24 * β) ^ sites n ∂(μ₀.prod μ₀) =
      SU2GaussianMass.mass (12 * β) ^ links n * SU2GaussianMass.mass (12 * β) ^ links n *
        SU2GaussianMass.mass (24 * β) ^ sites n := by
    rw [integral_mul_const]
    have hp := integral_prod_mul (μ := μ₀) (ν := μ₀) (fun u : Slice n => Real.exp (-(12 * β) * dist n u))
      (fun v : Slice n => Real.exp (-(12 * β) * dist n v))
    rw [hp, gauss_slice]
  rw [hval] at hlow
  refine hlow.trans ?_
  have hpair := TwistedTransfer.transfer_one_pairing n β
  set one := ContinuousMap.toLp 2 μ₀ ℂ (1 : C(Slice n, ℂ)) with hone
  have hnorm : ‖one‖ = 1 := by
    have h := WilsonPositiveGroundState.embedding_norm_sq μ₀ (1 : C(Slice n, ℂ))
    simp only [ContinuousMap.one_apply, norm_one, one_pow, integral_const, probReal_univ, smul_eq_mul,
      mul_one] at h
    nlinarith only [h, norm_nonneg one, sq_nonneg (‖one‖ - 1)]
  have hle : ‖inner ℂ one (TwistedTransfer.transfer n β one)‖ ≤ ‖TwistedTransfer.transfer n β‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hnorm, one_mul]
    have := (TwistedTransfer.transfer n β).le_opNorm one
    rwa [hnorm, mul_one] at this
  rw [hpair, Complex.norm_real, Real.norm_eq_abs] at hle
  exact (le_abs_self _).trans hle

/-- The cleaner form, with one Gaussian mass. -/
theorem norm_lower' (β : ℝ) (hβ : 0 ≤ β) :
    SU2GaussianMass.mass (24 * β) ^ (2 * links n + sites n) ≤ ‖TwistedTransfer.transfer n β‖ := by
  refine le_trans ?_ (norm_lower n β hβ)
  have hm : SU2GaussianMass.mass (24 * β) ≤ SU2GaussianMass.mass (12 * β) :=
    SU2GaussianMass.mass_antitone (by linarith only [hβ])
  have hm0 := (SU2GaussianMass.mass_pos (24 * β)).le
  rw [pow_add, two_mul, pow_add]
  have h1 := pow_le_pow_left₀ hm0 hm (links n)
  have hs : 0 ≤ SU2GaussianMass.mass (24 * β) ^ sites n := pow_nonneg hm0 _
  have hl : 0 ≤ SU2GaussianMass.mass (24 * β) ^ links n := pow_nonneg hm0 _
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h1 hl (hl.trans h1)) hs

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedNormLower
