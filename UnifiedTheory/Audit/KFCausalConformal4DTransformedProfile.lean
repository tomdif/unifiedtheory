/- Actual inverse-radial amplitude and its smooth zero extension. Compact
support stays inside a strict collar of the inverse chart. Null symmetry is
derived from reflection and inverse uniqueness; no limit is a hypothesis. -/
import UnifiedTheory.Audit.KFCausalConformal4DRadialInverse
import UnifiedTheory.Audit.KFCausalConformal4DVolumeReflection
import UnifiedTheory.Audit.KFCausalConformal4DCompactKernelDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalConformal4DTransformedProfile
noncomputable section
open Real Set Filter Topology
open scoped ContDiff
open KFCausalConformal4DNormalizedVolume KFCausalConformal4DVolumePositivity
open KFCausalConformal4DVolumeSmoothPolynomial KFCausalConformal4DVolumeReflection
open KFCausalConformal4DRadialScale KFCausalConformal4DRadialJacobian
open KFCausalConformal4DRadialInverse KFCausalConformal4DTemporalVariation
open KFCausalConformal4DCompactKernelDerivative (cutoff)

def reflect (p : ℝ×ℝ) : ℝ×ℝ := (p.1,-p.2)
def coefficient (c : ℝ) (p : ℝ×ℝ) : ℝ :=
  density c p.1*cutoff p/jacobianFactor c p.1 p.2
def amplitude (c : ℝ) (hc : |c|≤1/54) (y : ℝ×ℝ) : ℝ :=
  @ite ℝ (y∈targetBox) (Classical.propDecidable _) (coefficient c (inverse c hc y)) 0
def nullMap (z : ℝ×ℝ) : ℝ×ℝ := (-(z.1+z.2)/2,(z.2-z.1)/2)
def profile (c : ℝ) (hc : |c|≤1/54) (z : ℝ×ℝ) : ℝ := amplitude c hc (nullMap z)
def supportBox : Set (ℝ×ℝ) := {p | |p.1|≤7/3 ∧ |p.2|≤7/3}

private theorem cutoff_smooth : ContDiff ℝ ∞ cutoff := by
  unfold cutoff
  exact (KFCausalBDG4DCompactProfile.smooth.comp (by fun_prop)).mul
    (KFCausalBDG4DCompactProfile.smooth.comp (by fun_prop))

theorem cutoff_nonzero_bound (p : ℝ×ℝ) (hp : cutoff p≠0) : |p.1|≤2 ∧ |p.2|≤2 := by
  have hx (x : ℝ) (hx : KFCausalBDG4DCompactProfile.profile x≠0) : |x|<2 := by
    by_contra hn
    have hz := KFCausalBDG4DCompactProfile.bump.zero_of_le_dist
      (x := x) (by simpa [KFCausalBDG4DCompactProfile.bump,Real.dist_eq] using le_of_not_gt hn)
    exact hx (by simp [KFCausalBDG4DCompactProfile.profile,hz])
  have h := mul_ne_zero_iff.mp hp
  have h1 := abs_lt.mp (hx _ h.1)
  have h2 := abs_lt.mp (hx _ h.2)
  exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨by linarith,by linarith⟩⟩

private theorem supportBox_compact : IsCompact supportBox := by
  have he : supportBox=Icc (-(7/3:ℝ)) (7/3) ×ˢ Icc (-(7/3:ℝ)) (7/3) := by
    ext p
    simp only [supportBox,mem_setOf_eq,mem_prod,mem_Icc,abs_le]
  rw [he]
  exact isCompact_Icc.prod isCompact_Icc

private theorem supportBox_target : supportBox⊆targetBox := by
  intro y hy
  exact ⟨hy.1.trans_lt (by norm_num),hy.2.trans_lt (by norm_num)⟩

theorem radialMap_reflection (c : ℝ) (p : ℝ×ℝ) :
    radialMap c (reflect p)=reflect (radialMap c p) := by
  ext <;> simp only [radialMap,reflect,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,scale_rneg]
  ring

theorem inverse_reflection (c : ℝ) (hc : |c|≤1/54) (y : ℝ×ℝ) :
    inverse c hc (reflect y)=reflect (inverse c hc y) := by
  have ht : reflect y∈targetBox ↔ y∈targetBox := by simp only [reflect,targetBox,mem_setOf_eq,abs_neg]
  by_cases hy : y∈targetBox
  · have hy' := ht.mpr hy
    have hp := inverse_mem_box c hc y hy
    have hq := inverse_mem_box c hc (reflect y) hy'
    apply radialMap_injective c hc ⟨hq.1.le,hq.2.le⟩
      (show reflect (inverse c hc y)∈closedBox from ⟨hp.1.le,by simpa [reflect] using hp.2.le⟩)
    rw [inverse_right c hc _ hy',radialMap_reflection,inverse_right c hc _ hy]
  · have hy' : reflect y∉targetBox := fun h => hy (ht.mp h)
    have h1 : inverse c hc y=0 := by rw [inverse,dif_neg hy]
    have h2 : inverse c hc (reflect y)=0 := by rw [inverse,dif_neg hy']
    rw [h1,h2]
    simp only [reflect,Prod.fst_zero,Prod.snd_zero,neg_zero,Prod.mk_zero_zero]

theorem coefficient_reflection (c : ℝ) (p : ℝ×ℝ) :
    coefficient c (reflect p)=coefficient c p := by
  unfold coefficient cutoff reflect
  simp only [sub_neg_eq_add,← sub_eq_add_neg,jacobian_rneg]
  ring

theorem amplitude_eq (c : ℝ) (hc : |c|≤1/54) (y : ℝ×ℝ) (hy : y∈targetBox) :
    amplitude c hc y=coefficient c (inverse c hc y) := if_pos hy

theorem amplitude_support (c : ℝ) (hc : |c|≤1/54) :
    Function.support (amplitude c hc)⊆supportBox := by
  intro y hy
  have hyt : y∈targetBox := by
    by_contra h
    exact hy (by simp only [amplitude,if_neg h])
  have hz : cutoff (inverse c hc y)≠0 := by
    intro h
    exact hy (by rw [amplitude_eq c hc y hyt]; simp only [coefficient,h,mul_zero,zero_div])
  have h := support_image_bound c hc _ (cutoff_nonzero_bound _ hz)
  rw [inverse_right c hc y hyt] at h
  exact h

theorem amplitude_compact (c : ℝ) (hc : |c|≤1/54) : HasCompactSupport (amplitude c hc) :=
  HasCompactSupport.intro supportBox_compact (fun _ hy =>
    Function.notMem_support.mp (fun h => hy (amplitude_support c hc h)))

theorem coefficient_smoothAt (c : ℝ) (p : ℝ×ℝ) (hp : jacobianFactor c p.1 p.2≠0) :
    ContDiffAt ℝ ∞ (coefficient c) p := by
  have hd : ContDiff ℝ ∞ (fun p : ℝ×ℝ => density c p.1) := by
    simp_rw [density_polynomial]
    fun_prop
  have hi : ContDiff ℝ ∞ (fun q : ℝ×ℝ => (c,q)) := contDiff_const.prodMk contDiff_id
  have hj := jacobian_factor_smooth.comp hi
  have he : (fun q : ℝ×ℝ => jacobianFactor c q.1 q.2)=
      (fun q : ℝ×(ℝ×ℝ) => jacobianFactor q.1 q.2.1 q.2.2) ∘ (fun q : ℝ×ℝ => (c,q)) := rfl
  rw [← he] at hj
  change ContDiffAt ℝ ∞ (fun q : ℝ×ℝ => density c q.1*cutoff q/jacobianFactor c q.1 q.2) p
  exact (hd.contDiffAt.mul cutoff_smooth.contDiffAt).div hj.contDiffAt hp

theorem amplitude_smooth (c : ℝ) (hc : |c|≤1/54) : ContDiff ℝ ∞ (amplitude c hc) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y∈targetBox
  · have hp := inverse_mem_box c hc y hy
    have hd : jacobianFactor c (inverse c hc y).1 (inverse c hc y).2≠0 :=
      ne_of_gt (jacobian_factor_pos _ _ _ hc hp.1.le hp.2.le)
    apply ((coefficient_smoothAt c _ hd).comp y (inverse_smoothAt c hc y hy)).congr_of_eventuallyEq
    filter_upwards [targetBox_open.mem_nhds hy] with z hz
    exact amplitude_eq c hc z hz
  · have hn : y∈supportBoxᶜ := fun h => hy (supportBox_target h)
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [supportBox_compact.isClosed.isOpen_compl.mem_nhds hn] with z hz
    exact Function.notMem_support.mp (fun h => hz (amplitude_support c hc h))

theorem amplitude_rneg (c : ℝ) (hc : |c|≤1/54) (y : ℝ×ℝ) :
    amplitude c hc (reflect y)=amplitude c hc y := by
  have ht : reflect y∈targetBox ↔ y∈targetBox := by simp only [reflect,targetBox,mem_setOf_eq,abs_neg]
  by_cases hy : y∈targetBox
  · rw [amplitude_eq c hc _ (ht.mpr hy),amplitude_eq c hc y hy,
      inverse_reflection,coefficient_reflection]
  · simp only [amplitude,if_neg hy,if_neg (fun h => hy (ht.mp h))]

theorem profile_smooth (c : ℝ) (hc : |c|≤1/54) : ContDiff ℝ ∞ (profile c hc) :=
  (amplitude_smooth c hc).comp (by unfold nullMap; fun_prop)

theorem profile_support (c : ℝ) (hc : |c|≤1/54) (z : ℝ×ℝ) (hz : profile c hc z≠0) :
    |z.1|≤14/3 ∧ |z.2|≤14/3 := by
  have h := amplitude_support c hc (show nullMap z∈Function.support (amplitude c hc) from hz)
  have h1 := abs_le.mp h.1
  have h2 := abs_le.mp h.2
  change -(7/3:ℝ)≤-(z.1+z.2)/2 ∧ -(z.1+z.2)/2≤7/3 at h1
  change -(7/3:ℝ)≤(z.2-z.1)/2 ∧ (z.2-z.1)/2≤7/3 at h2
  exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨by linarith,by linarith⟩⟩

theorem profile_compact (c : ℝ) (hc : |c|≤1/54) : HasCompactSupport (profile c hc) := by
  apply HasCompactSupport.intro (K := Icc (-(14/3:ℝ)) (14/3) ×ˢ Icc (-(14/3:ℝ)) (14/3))
    (isCompact_Icc.prod isCompact_Icc)
  intro z hz
  by_contra hn
  have h := profile_support c hc z hn
  exact hz ⟨abs_le.mp h.1,abs_le.mp h.2⟩

theorem profile_symmetric (c : ℝ) (hc : |c|≤1/54) (u v : ℝ) :
    profile c hc (u,v)=profile c hc (v,u) := by
  have he : nullMap (v,u)=reflect (nullMap (u,v)) := by ext <;> simp only [nullMap,reflect] <;> ring
  unfold profile
  rw [he,amplitude_rneg]

#print axioms radialMap_reflection
#print axioms cutoff_nonzero_bound
#print axioms inverse_reflection
#print axioms coefficient_reflection
#print axioms amplitude_eq
#print axioms amplitude_support
#print axioms amplitude_compact
#print axioms coefficient_smoothAt
#print axioms amplitude_smooth
#print axioms amplitude_rneg
#print axioms profile_smooth
#print axioms profile_support
#print axioms profile_compact
#print axioms profile_symmetric
end
end UnifiedTheory.Audit.KFCausalConformal4DTransformedProfile
