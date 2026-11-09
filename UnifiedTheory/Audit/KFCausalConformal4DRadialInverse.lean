import UnifiedTheory.Audit.KFCausalConformal4DRadialJacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/- The actual radial map covers a common target box. Its uniquely determined
inverse there is smooth by the inverse function theorem and actual injectivity.
No inverse or coverage certificate is an input. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalConformal4DRadialInverse
noncomputable section
open Real Set Filter Topology
open scoped ContDiff
open KFCausalConformal4DNormalizedVolume KFCausalConformal4DVolumePositivity
open KFCausalConformal4DRadialScale KFCausalConformal4DRadialJacobian

abbrev Point := ℝ×ℝ
def targetBox : Set Point := {p | |p.1| < 5/2 ∧ |p.2| < 5/2}

theorem targetBox_open : IsOpen targetBox :=
  (isOpen_lt continuous_fst.abs continuous_const).inter
    (isOpen_lt continuous_snd.abs continuous_const)

private theorem box_open : IsOpen box :=
  (isOpen_lt continuous_fst.abs continuous_const).inter
    (isOpen_lt continuous_snd.abs continuous_const)

private theorem box_closed (p : Point) (hp : p∈box) : p∈closedBox :=
  ⟨hp.1.le,hp.2.le⟩

private theorem segment_bound (l x : ℝ) (hl : l∈Icc (0:ℝ) 1) (hx : |x|≤3) :
    |l*x|≤3 := by
  rw [abs_mul,abs_of_nonneg hl.1]
  calc l*|x| ≤ 1*|x| := mul_le_mul_of_nonneg_right hl.2 (abs_nonneg _)
       _ ≤ 3 := by simpa only [one_mul] using hx

theorem target_covered (c : ℝ) (hc : |c|≤1/54) (y : Point) (hy : y∈targetBox) :
    ∃ p∈box, radialMap c p=y := by
  by_cases hy0 : y=0
  · refine ⟨0,by norm_num [box],?_⟩
    simp only [radialMap,smul_zero,hy0]
  have hn : 0<‖y‖ := norm_pos_iff.mpr hy0
  have hn' : ‖y‖<5/2 := by
    rw [Prod.norm_def,max_lt_iff]
    exact hy
  let q : Point := (3/‖y‖) • y
  have hqnorm : ‖q‖=3 := by
    dsimp [q]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos (by norm_num) hn)]
    field_simp [ne_of_gt hn]
  have hq : q∈closedBox := by
    exact ⟨by simpa only [Real.norm_eq_abs,hqnorm] using norm_fst_le q,
      by simpa only [Real.norm_eq_abs,hqnorm] using norm_snd_le q⟩
  have hp (l : ℝ) (hl : l∈Icc (0:ℝ) 1) : 0<normalized c (l*q.1) (l*q.2) :=
    normalized_pos c _ _ hc (segment_bound l q.1 hl hq.1)
      (segment_bound l q.2 hl hq.2)
  have hcont : ContinuousOn (radialRadius c q.1 q.2) (Icc (0:ℝ) 1) := by
    intro l hl
    exact (ray_hasDerivAt c q.1 q.2 l (hp l hl)).continuousAt.continuousWithinAt
  have hstart : radialRadius c q.1 q.2 0=0 := by simp [radialRadius]
  have hend : (5/6:ℝ)≤radialRadius c q.1 q.2 1 := by
    simpa only [radialRadius,one_mul] using (scale_bounds c q.1 q.2 hc hq.1 hq.2).1
  have htarget : ‖y‖/3 ∈ Icc (radialRadius c q.1 q.2 0) (radialRadius c q.1 q.2 1) := by
    rw [hstart]
    constructor
    · positivity
    · linarith
  obtain ⟨l,hl,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hcont htarget
  have hl1 : l<1 := by
    by_contra h
    have heq : l=1 := le_antisymm hl.2 (le_of_not_gt h)
    rw [heq] at he
    linarith
  refine ⟨l • q,?_,?_⟩
  · have hpn : ‖l • q‖<3 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hl.1,hqnorm]
      linarith
    exact ⟨(norm_fst_le _).trans_lt hpn,(norm_snd_le _).trans_lt hpn⟩
  · change scale c (l*q.1) (l*q.2) • (l • q)=y
    rw [smul_smul,mul_comm (scale c (l*q.1) (l*q.2)) l]
    change radialRadius c q.1 q.2 l • q=y
    rw [he]
    dsimp [q]
    rw [smul_smul]
    have hm : ‖y‖/3*(3/‖y‖)=1 := by field_simp [ne_of_gt hn]
    rw [hm,one_smul]

def inverse (c : ℝ) (hc : |c|≤1/54) (y : Point) : Point := by
  classical
  exact if hy : y∈targetBox then Classical.choose (target_covered c hc y hy) else 0

theorem inverse_mem_box (c : ℝ) (hc : |c|≤1/54) (y : Point) (hy : y∈targetBox) :
    inverse c hc y∈box := by
  rw [inverse,dif_pos hy]
  exact (Classical.choose_spec (target_covered c hc y hy)).1

theorem inverse_right (c : ℝ) (hc : |c|≤1/54) (y : Point) (hy : y∈targetBox) :
    radialMap c (inverse c hc y)=y := by
  rw [inverse,dif_pos hy]
  exact (Classical.choose_spec (target_covered c hc y hy)).2

theorem inverse_left (c : ℝ) (hc : |c|≤1/54) (p : Point) (hp : p∈closedBox)
    (hy : radialMap c p∈targetBox) : inverse c hc (radialMap c p)=p :=
  radialMap_injective c hc (box_closed _ (inverse_mem_box c hc _ hy)) hp
    (inverse_right c hc _ hy)

theorem support_image_bound (c : ℝ) (hc : |c|≤1/54) (p : Point)
    (hp : |p.1|≤2 ∧ |p.2|≤2) :
    |(radialMap c p).1|≤7/3 ∧ |(radialMap c p).2|≤7/3 := by
  have hs := scale_bounds c p.1 p.2 hc (by linarith [hp.1]) (by linarith [hp.2])
  have hs0 : 0≤scale c p.1 p.2 := by linarith
  constructor
  · change |scale c p.1 p.2*p.1|≤7/3
    rw [abs_mul,abs_of_nonneg hs0]
    calc _ ≤ (7/6)*2 := mul_le_mul hs.2 hp.1 (abs_nonneg _) (by norm_num)
         _ = _ := by norm_num
  · change |scale c p.1 p.2*p.2|≤7/3
    rw [abs_mul,abs_of_nonneg hs0]
    calc _ ≤ (7/6)*2 := mul_le_mul hs.2 hp.2 (abs_nonneg _) (by norm_num)
         _ = _ := by norm_num

theorem support_image_mem_target (c : ℝ) (hc : |c|≤1/54) (p : Point)
    (hp : |p.1|≤2 ∧ |p.2|≤2) : radialMap c p∈targetBox := by
  have h := support_image_bound c hc p hp
  exact ⟨h.1.trans_lt (by norm_num),h.2.trans_lt (by norm_num)⟩

theorem inverse_smoothAt (c : ℝ) (hc : |c|≤1/54) (y : Point) (hy : y∈targetBox) :
    ContDiffAt ℝ ∞ (inverse c hc) y := by
  let a := inverse c hc y
  have ha : a∈box := inverse_mem_box c hc y hy
  have hac : a∈closedBox := box_closed a ha
  have hPa : 0<normalized c a.1 a.2 := normalized_pos c a.1 a.2 hc hac.1 hac.2
  have hs := radialMap_smoothAt c a hPa
  let eL := (mapDerivative c a).toContinuousLinearEquivOfDetNeZero
    (ne_of_gt (mapDerivative_det_pos c a hc hac))
  have hd : HasFDerivAt (radialMap c) (eL : Point →L[ℝ] Point) a := by
    simpa only [eL,ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
      radialMap_hasFDerivAt c a hPa
  have hn : (∞ : WithTop ℕ∞)≠0 := by simp
  let e := hs.toOpenPartialHomeomorph (f' := eL) (radialMap c) hd hn
  have hae : a∈e.source := hs.mem_toOpenPartialHomeomorph_source (f' := eL) hd hn
  have hmap : radialMap c a=y := inverse_right c hc y hy
  have hye : y∈e.target := by
    rw [← hmap]
    exact hs.image_mem_toOpenPartialHomeomorph_target (f' := eL) hd hn
  have heleft : e.symm y=a := by
    rw [← hmap]
    exact e.left_inv hae
  have hi : ContDiffAt ℝ ∞ e.symm y := by
    have h := hs.to_localInverse (f' := eL) hd hn
    change ContDiffAt ℝ ∞ e.symm (radialMap c a) at h
    simpa only [hmap] using h
  have hstay : ∀ᶠ z in 𝓝 y, e.symm z∈box := by
    apply hi.continuousAt.eventually
    apply box_open.mem_nhds
    simpa only [heleft] using ha
  apply hi.congr_of_eventuallyEq
  filter_upwards [hstay,targetBox_open.mem_nhds hy,e.eventually_right_inverse hye] with z hz hzt hez
  apply radialMap_injective c hc
    (box_closed _ (inverse_mem_box c hc z hzt)) (box_closed _ hz)
  exact (inverse_right c hc z hzt).trans hez.symm

theorem inverse_smoothOn (c : ℝ) (hc : |c|≤1/54) :
    ContDiffOn ℝ ∞ (inverse c hc) targetBox :=
  fun y hy => (inverse_smoothAt c hc y hy).contDiffWithinAt

#print axioms targetBox_open
#print axioms target_covered
#print axioms inverse_mem_box
#print axioms inverse_right
#print axioms inverse_left
#print axioms support_image_bound
#print axioms support_image_mem_target
#print axioms inverse_smoothAt
#print axioms inverse_smoothOn
end
end UnifiedTheory.Audit.KFCausalConformal4DRadialInverse
