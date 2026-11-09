/- The actual radial map is injective on the fixed box and has positive
Frechet determinant. The phase identity uses the original parameter volume;
no inverse chart or integral pushforward is assumed. -/
import UnifiedTheory.Audit.KFCausalConformal4DRadialScale
import UnifiedTheory.Audit.KFCausalConformal4DVolumeSmoothPolynomial
import Mathlib.LinearAlgebra.Determinant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalConformal4DRadialJacobian
noncomputable section
open Real Set
open scoped ContDiff
open KFCausalConformal4DNormalizedVolume KFCausalConformal4DVolumePositivity
open KFCausalConformal4DRadialScale KFCausalConformal4DVolumeSmoothPolynomial

def closedBox : Set (ℝ × ℝ) := {p | |p.1| ≤ 3 ∧ |p.2| ≤ 3}
def box : Set (ℝ × ℝ) := {p | |p.1| < 3 ∧ |p.2| < 3}
def radialMap (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := scale c p.1 p.2 • p

theorem box_open : IsOpen box := by
  exact (isOpen_lt continuous_fst.abs continuous_const).inter
    (isOpen_lt continuous_snd.abs continuous_const)

theorem box_subset_closedBox : box ⊆ closedBox := fun _ hp => ⟨hp.1.le,hp.2.le⟩

theorem radialMap_origin (c : ℝ) : radialMap c 0=0 := by
  simp only [radialMap,smul_zero]

private theorem injective_of_scale_le (c : ℝ) (hc : |c| ≤ 1/54) (p q : ℝ × ℝ)
    (hp : p ∈ closedBox) (hq : q ∈ closedBox) (he : radialMap c p=radialMap c q)
    (hs : scale c q.1 q.2 ≤ scale c p.1 p.2) : p=q := by
  have hsp : 0 < scale c p.1 p.2 := scale_pos _ _ _ (normalized_pos _ _ _ hc hp.1 hp.2)
  have hsq : 0 < scale c q.1 q.2 := scale_pos _ _ _ (normalized_pos _ _ _ hc hq.1 hq.2)
  let l := scale c q.1 q.2/scale c p.1 p.2
  have hl : l ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg hsq.le hsp.le,(div_le_one hsp).mpr hs⟩
  have he1 : scale c p.1 p.2*p.1=scale c q.1 q.2*q.1 := congrArg Prod.fst he
  have he2 : scale c p.1 p.2*p.2=scale c q.1 q.2*q.2 := congrArg Prod.snd he
  have hp1 : p.1=l*q.1 := by
    dsimp [l]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hsp.ne').mpr
    simpa only [mul_comm] using he1
  have hp2 : p.2=l*q.2 := by
    dsimp [l]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hsp.ne').mpr
    simpa only [mul_comm] using he2
  have hr : radialRadius c q.1 q.2 l=radialRadius c q.1 q.2 1 := by
    simp only [radialRadius,one_mul,← hp1,← hp2]
    dsimp [l]
    field_simp
  have hl1 : l=1 := (ray_strictMono c q.1 q.2 hc hq.1 hq.2).injOn hl
    (by constructor <;> norm_num) hr
  apply Prod.ext
  · simpa only [hl1,one_mul] using hp1
  · simpa only [hl1,one_mul] using hp2

theorem radialMap_injective (c : ℝ) (hc : |c| ≤ 1/54) : InjOn (radialMap c) closedBox := by
  intro p hp q hq he
  rcases le_total (scale c q.1 q.2) (scale c p.1 p.2) with h | h
  · exact injective_of_scale_le c hc p q hp hq he h
  · exact (injective_of_scale_le c hc q p hq hp he.symm h).symm

theorem scale_smoothAt (c : ℝ) (p : ℝ × ℝ) (hp : 0 < normalized c p.1 p.2) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => scale c q.1 q.2) p := by
  have hi : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (c,q)) := contDiff_const.prodMk contDiff_id
  have hn : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => normalized c q.1 q.2) p :=
    (normalized_smooth.comp hi).contDiffAt
  exact (hn.sqrt hp.ne').sqrt (ne_of_gt (sqrt_pos.mpr hp))

theorem radialMap_smoothAt (c : ℝ) (p : ℝ × ℝ) (hp : 0 < normalized c p.1 p.2) :
    ContDiffAt ℝ ∞ (radialMap c) p :=
  (scale_smoothAt c p hp).smul contDiffAt_id

def scaleDerivative (c : ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (fun q : ℝ × ℝ => scale c q.1 q.2) p

def mapDerivative (c : ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  scale c p.1 p.2 • ContinuousLinearMap.id ℝ (ℝ × ℝ)+(scaleDerivative c p).smulRight p

theorem radialMap_hasFDerivAt (c : ℝ) (p : ℝ × ℝ) (hp : 0 < normalized c p.1 p.2) :
    HasFDerivAt (radialMap c) (mapDerivative c p) p :=
  ((scale_smoothAt c p hp).differentiableAt (by norm_num)).hasFDerivAt.smul (hasFDerivAt_id p)

private theorem linear_eval (f : (ℝ × ℝ) →L[ℝ] ℝ) (p : ℝ × ℝ) :
    f p=p.1*f (1,0)+p.2*f (0,1) := by
  have he : p=p.1 • ((1:ℝ),0)+p.2 • ((0:ℝ),1) := by ext <;> simp
  calc f p = f (p.1 • ((1:ℝ),0)+p.2 • ((0:ℝ),1)) := congrArg f he
       _ = _ := by simp only [map_add,map_smul,smul_eq_mul]

private theorem radial_linear_det (s : ℝ) (p : ℝ × ℝ) (f : (ℝ × ℝ) →L[ℝ] ℝ) :
    (s • ContinuousLinearMap.id ℝ (ℝ × ℝ)+f.smulRight p).det=s^2+s*f p := by
  have he : s • ContinuousLinearMap.id ℝ (ℝ × ℝ)+f.smulRight p=
      (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
        !![s+p.1*f (1,0),p.1*f (0,1); p.2*f (1,0),s+p.2*f (0,1)]).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    change s • v+f v • p=Matrix.toLin (Module.Basis.finTwoProd ℝ)
      (Module.Basis.finTwoProd ℝ)
        !![s+p.1*f (1,0),p.1*f (0,1); p.2*f (1,0),s+p.2*f (0,1)] v
    rw [Matrix.toLin_finTwoProd_apply]
    rw [linear_eval f v]
    apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring
  rw [he]
  simp only [LinearMap.det_toContinuousLinearMap,LinearMap.det_toLin,Matrix.det_fin_two_of]
  rw [linear_eval f p]
  ring

private theorem radial_differential (c : ℝ) (p : ℝ × ℝ) (hp : 0 < normalized c p.1 p.2) :
    scale c p.1 p.2+scaleDerivative c p p=
      jacobianFactor c p.1 p.2/(scale c p.1 p.2)^3 := by
  have hf : HasFDerivAt (fun q : ℝ × ℝ => scale c q.1 q.2) (scaleDerivative c p) ((1:ℝ) • p) := by
    simpa only [one_smul] using ((scale_smoothAt c p hp).differentiableAt (by norm_num)).hasFDerivAt
  have hd : HasDerivAt (fun l : ℝ => scale c (l*p.1) (l*p.2)) (scaleDerivative c p p) 1 := by
    simpa only [one_smul,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Function.comp_apply] using
      hf.comp_hasDerivAt 1 ((hasDerivAt_id (1:ℝ)).smul_const p)
  have hr : HasDerivAt (radialRadius c p.1 p.2) (scale c p.1 p.2+scaleDerivative c p p) 1 := by
    simpa only [radialRadius,one_mul,id_eq] using (hasDerivAt_id (1:ℝ)).mul hd
  exact hr.unique (by
    simpa only [one_mul] using
      ray_hasDerivAt c p.1 p.2 1 (by simpa only [one_mul] using hp))

theorem mapDerivative_det (c : ℝ) (p : ℝ × ℝ) (hp : 0 < normalized c p.1 p.2) :
    (mapDerivative c p).det=jacobianFactor c p.1 p.2/sqrt (normalized c p.1 p.2) := by
  rw [mapDerivative,radial_linear_det]
  have hn : scale c p.1 p.2 ≠ 0 := (scale_pos c p.1 p.2 hp).ne'
  calc _ = scale c p.1 p.2*(scale c p.1 p.2+scaleDerivative c p p) := by ring
       _ = scale c p.1 p.2*(jacobianFactor c p.1 p.2/(scale c p.1 p.2)^3) := by
         rw [radial_differential c p hp]
       _ = _ := by rw [← scale_sq]; field_simp

theorem mapDerivative_det_pos (c : ℝ) (p : ℝ × ℝ) (hc : |c| ≤ 1/54) (hp : p ∈ closedBox) :
    0 < (mapDerivative c p).det := by
  rw [mapDerivative_det c p (normalized_pos _ _ _ hc hp.1 hp.2)]
  exact div_pos (jacobian_factor_pos _ _ _ hc hp.1 hp.2)
    (sqrt_pos.mpr (normalized_pos _ _ _ hc hp.1 hp.2))

theorem phase_flattening (c : ℝ) (p : ℝ × ℝ) (hp : 0 ≤ normalized c p.1 p.2) :
    KFCausalConformal4DRegularVolume.regularVolume c p.1 p.2=
      (π/24)*((radialMap c p).1^2-(radialMap c p).2^2)^2 := by
  rw [regular_volume_normalized]
  change (π*(p.1^2-p.2^2)^2/24)*normalized c p.1 p.2=
    (π/24)*((scale c p.1 p.2*p.1)^2-(scale c p.1 p.2*p.2)^2)^2
  rw [← scale_fourth c p.1 p.2 hp]
  ring

#print axioms box_open
#print axioms box_subset_closedBox
#print axioms radialMap_origin
#print axioms radialMap_injective
#print axioms scale_smoothAt
#print axioms radialMap_smoothAt
#print axioms radialMap_hasFDerivAt
#print axioms mapDerivative_det
#print axioms mapDerivative_det_pos
#print axioms phase_flattening
end
end UnifiedTheory.Audit.KFCausalConformal4DRadialJacobian
