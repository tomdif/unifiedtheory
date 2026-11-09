/- A canonical uncertainty estimate on the full intersection of the maximal
position and momentum domains. Translation covariance replaces an assumed
domain for either product of the two unbounded operators. -/
import UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalCanonicalUncertainty
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalFourierTranslation
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem position_translation_pairing (l : E →L[ℝ] ℝ) (v : E)
    (f q : Hilbert (E := E))
    (hq : q =ᵐ[volume] fun x => (l x : ℂ)*f x) (t : ℝ) :
    inner ℂ q (translation (t • v) f) =
      inner ℂ (translation (-t • v) f) q -
        (t*l v : ℝ)*inner ℂ f (translation (t • v) f) := by
  have hp : inner ℂ q (translation (t • v) f) =
      inner ℂ f (translation (t • v) q) -
        (t*l v : ℝ)*inner ℂ f (translation (t • v) f) := by
    rw [← inner_smul_right, ← inner_sub_right, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hq, translation_coe (t • v) f, translation_coe (t • v) q,
      (shift_preserves_volume (t • v)).quasiMeasurePreserving.ae hq,
      Lp.coeFn_sub (translation (t • v) q) (((t*l v : ℝ) : ℂ) • translation (t • v) f),
      Lp.coeFn_smul ((t*l v : ℝ) : ℂ) (translation (t • v) f)] with x hqx hf hx hshift hsub hsmul
    change q (x+t • v) = (l (x+t • v) : ℂ)*f (x+t • v) at hshift
    rw [hqx,hsub]
    simp only [Pi.sub_apply]
    rw [hsmul]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hf,hx,hshift,map_add,map_smul]
    simp only [smul_eq_mul,Complex.ofReal_add,Complex.ofReal_mul]
    change inner ℂ ((l x : ℂ) • f x) (f (x+t • v)) = _
    rw [inner_smul_left,Complex.conj_ofReal]
    rw [show ((l x : ℂ)+(t:ℂ)*(l v:ℂ))*f (x+t • v)-(t:ℂ)*(l v:ℂ)*f (x+t • v) =
      (l x : ℂ) • f (x+t • v) by simp only [smul_eq_mul]; ring,inner_smul_right]
  have hu : inner ℂ (translation (-t • v) f) q =
      inner ℂ f (translation (t • v) q) := by
    rw [← (translation (t • v)).inner_map_map,translation_compose,
      show -t • v+t • v = 0 by simp,translation_initial]
  exact hp.trans (by rw [hu])

theorem position_derivative_bound (l : E →L[ℝ] ℝ) (v : E)
    (f q d : Hilbert (E := E))
    (hq : q =ᵐ[volume] fun x => (l x : ℂ)*f x)
    (hd : HasDerivAt (fun t : ℝ => translation (t • v) f) d 0) :
    |l v| *‖f‖^2 ≤ 2*‖q‖*‖d‖ := by
  have hneg : HasDerivAt (fun t : ℝ => translation (-t • v) f) (-d) 0 := by
    have hd' : HasDerivAt (fun t : ℝ => translation (t • v) f) d (-0) := by
      simpa only [neg_zero] using hd
    simpa only [Function.comp_def,neg_smul,one_smul] using hd'.scomp 0 (hasDerivAt_id (0:ℝ)).neg
  have hL := (hasDerivAt_const (0:ℝ) q).inner ℂ hd
  have hR := (hneg.inner ℂ (hasDerivAt_const (0:ℝ) q)).sub
    ((((hasDerivAt_id (0:ℝ)).mul_const (l v)).ofReal_comp).mul
      ((hasDerivAt_const (0:ℝ) f).inner ℂ hd))
  have he : (fun t : ℝ => inner ℂ q (translation (t • v) f)) =
      (fun t : ℝ => inner ℂ (translation (-t • v) f) q -
        (t*l v : ℝ)*inner ℂ f (translation (t • v) f)) :=
    funext (position_translation_pairing l v f q hq)
  have hR' : HasDerivAt (fun t : ℝ => inner ℂ (translation (-t • v) f) q -
      (t*l v : ℝ)*inner ℂ f (translation (t • v) f))
      (-inner ℂ d q-(l v:ℂ)*inner ℂ f f) 0 := by
    simpa only [id_eq,zero_smul,translation_initial,inner_zero_right,zero_add,
      inner_neg_left,zero_mul,Complex.ofReal_zero,one_mul,add_zero] using hR
  rw [← he] at hR'
  have hh := hL.unique hR'
  simp only [inner_zero_left,add_zero] at hh
  have heq : (l v : ℂ)*(‖f‖^2 : ℝ) = -(inner ℂ q d+inner ℂ d q) := by
    have hi : inner ℂ f f = ((‖f‖^2 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f)
    rw [hi] at hh
    linear_combination hh
  calc
    |l v| *‖f‖^2 = ‖(l v : ℂ)*(‖f‖^2 : ℝ)‖ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖f‖)]
    _ = ‖inner ℂ q d+inner ℂ d q‖ := by rw [heq,norm_neg]
    _ ≤ ‖inner ℂ q d‖+‖inner ℂ d q‖ := norm_add_le _ _
    _ ≤ ‖q‖*‖d‖+‖d‖*‖q‖ := add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ = _ := by ring

theorem maximal_uncertainty (h : ℝ) (hne : h ≠ 0) (l : E →L[ℝ] ℝ) (v : E)
    (f q p : Hilbert (E := E))
    (hq : q =ᵐ[volume] fun x => (l x : ℂ)*f x)
    (hp : (f,p) ∈ (spectralMomentum h v).graph) :
    |h| *|l v| *‖f‖^2 ≤ 2*‖q‖*‖p‖ := by
  have hd := (spectralMomentum_graph_derivative h hne v f p).mp hp
  have hu := position_derivative_bound l v f q _ hq hd
  have hn : ‖(Complex.I/(h:ℂ)) • p‖ = ‖p‖/|h| := by
    simp only [norm_smul,norm_div,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs]
    ring
  rw [hn] at hu
  have hm := mul_le_mul_of_nonneg_left hu (abs_nonneg h)
  have hc : |h| ≠ 0 := abs_ne_zero.mpr hne
  calc
    _ = |h| *(|l v| *‖f‖^2) := by ring
    _ ≤ |h| *(2*‖q‖*(‖p‖/|h|)) := hm
    _ = _ := by field_simp

#print axioms position_translation_pairing
#print axioms position_derivative_bound
#print axioms maximal_uncertainty
end
end UnifiedTheory.Audit.KFCausalCanonicalUncertainty
