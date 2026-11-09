/- The complete finite quadratic-polynomial charged Gram matrix equals
an absolutely integrable squared packet norm. Its entries include every
cross degree and coherent pair of widths. Positivity here concerns the
energy Gram matrix; no sign of its clock derivative is asserted. -/
import UnifiedTheory.Audit.KFCausalChargedFourierGaussianMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedFourierPolynomialGram
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure density kernel)
open KFCausalShiftedComplexGaussianMoments (normalized)

abbrev Index (n : ℕ) := Fin n × Fin 3
def width (p : ℂ) (w v : ℝ) : ℂ := conj p*(w:ℂ)+p*(v:ℂ)
def atom (p : ℂ) (w c : ℝ) (m : ℕ) (u v Y : ℝ) : ℂ :=
  (v:ℂ)^m*Complex.exp (-(w:ℂ)*p*((u:ℂ)^2+(v:ℂ)^2)-
    (w:ℂ)*conj p*(Y:ℂ)+(c:ℂ)/2*(v:ℂ))
def family (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (u v Y : ℝ) : ℂ :=
  ∑ I : Index n, a I.1 I.2*atom p (w I.1) c I.2.val u v Y
def entry (p : ℂ) (w v c : ℝ) (m n : ℕ) : ℂ :=
  kernel (width p w v) (conj (width p w v)) (c:ℂ)*normalized (width p w v) (c:ℂ) (m+n)
def gram (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ) (a : Fin n → Fin 3 → ℂ) : ℂ :=
  ∑ I : Index n, ∑ J : Index n,
    (conj (a I.1 I.2)*a J.1 J.2)*entry p (w I.1) (w J.1) c I.2.val J.2.val

theorem width_positive (p : ℂ) (w v : ℝ) (hp : 0 < p.re) (hw : 0 < w) (hv : 0 < v) :
    0 < (width p w v).re := by
  simp only [width,Complex.add_re,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  positivity

theorem atom_cross (p : ℂ) (w q c : ℝ) (m n : ℕ) (u v Y : ℝ) :
    conj (atom p w c m u v Y)*atom p q c n u v Y =
      density (width p w q) (conj (width p w q)) (c:ℂ) (m+n) u v Y := by
  rw [KFCausalChargedFourierGaussianMoments.density_expansion]
  unfold atom width
  simp only [map_mul,map_pow,map_add,map_sub,map_neg,map_div₀,Complex.conj_ofReal,
    Complex.conj_ofNat,starRingEnd_self_apply,← Complex.exp_conj]
  rw [show (v:ℂ)^m*Complex.exp (-(w:ℂ)*conj p*((u:ℂ)^2+(v:ℂ)^2)-
      (w:ℂ)*p*(Y:ℂ)+(c:ℂ)/2*(v:ℂ))*
      ((v:ℂ)^n*Complex.exp (-(q:ℂ)*p*((u:ℂ)^2+(v:ℂ)^2)-
        (q:ℂ)*conj p*(Y:ℂ)+(c:ℂ)/2*(v:ℂ))) =
      (v:ℂ)^m*(v:ℂ)^n*(Complex.exp (-(w:ℂ)*conj p*((u:ℂ)^2+(v:ℂ)^2)-
        (w:ℂ)*p*(Y:ℂ)+(c:ℂ)/2*(v:ℂ))*
      Complex.exp (-(q:ℂ)*p*((u:ℂ)^2+(v:ℂ)^2)-
        (q:ℂ)*conj p*(Y:ℂ)+(c:ℂ)/2*(v:ℂ))) by ring,
    ← pow_add,← Complex.exp_add]
  congr 2
  ring

theorem family_square (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (u v Y : ℝ) :
    (‖family n p w c a u v Y‖^2:ℝ) =
      (∑ I : Index n, ∑ J : Index n, (conj (a I.1 I.2)*a J.1 J.2)*
        density (width p (w I.1) (w J.1)) (conj (width p (w I.1) (w J.1)))
          (c:ℂ) (I.2.val+J.2.val) u v Y).re := by
  have he : ((‖family n p w c a u v Y‖^2:ℝ):ℂ) =
      ∑ I : Index n, ∑ J : Index n, (conj (a I.1 I.2)*a J.1 J.2)*
        density (width p (w I.1) (w J.1)) (conj (width p (w I.1) (w J.1)))
          (c:ℂ) (I.2.val+J.2.val) u v Y := by
    rw [Complex.ofReal_pow,← Complex.conj_mul']
    unfold family
    simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro J _
    rw [← atom_cross]
    ring
  exact congrArg Complex.re he

theorem family_square_complex (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (u v Y : ℝ) :
    ((‖family n p w c a u v Y‖^2:ℝ):ℂ) =
      ∑ I : Index n, ∑ J : Index n, (conj (a I.1 I.2)*a J.1 J.2)*
        density (width p (w I.1) (w J.1)) (conj (width p (w I.1) (w J.1)))
          (c:ℂ) (I.2.val+J.2.val) u v Y := by
  rw [Complex.ofReal_pow,← Complex.conj_mul']
  unfold family
  simp only [map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  rw [← atom_cross]
  ring

private theorem cross_integrable (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (I J : Index n) :
    Integrable (fun x : Charged => (conj (a I.1 I.2)*a J.1 J.2)*
      density (width p (w I.1) (w J.1)) (conj (width p (w I.1) (w J.1)))
        (c:ℂ) (I.2.val+J.2.val) x.1.1 x.1.2 x.2) chargedMeasure := by
  have hS := width_positive p (w I.1) (w J.1) hp (hw _) (hw _)
  exact (KFCausalChargedFourierGaussianMoments.density_integrable _ _ _ hS
    (by simpa only [Complex.conj_re] using hS) _).const_mul _

theorem family_square_integrable (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    Integrable (fun x : Charged => ((‖family n p w c a x.1.1 x.1.2 x.2‖^2:ℝ):ℂ)) chargedMeasure := by
  have hi := integrable_finset_sum Finset.univ (fun I _ =>
    integrable_finset_sum Finset.univ (fun J _ => cross_integrable n p w c a hp hw I J))
  exact hi.congr (Filter.Eventually.of_forall (fun x => (family_square_complex n p w c a _ _ _).symm))

theorem product_integral_order (f : Charged → ℂ) (hf : Integrable f chargedMeasure) :
    (∫ x, f x ∂chargedMeasure) = ∫ Y in Set.Ioi 0, ∫ u, ∫ v, f ((u,v),Y) := by
  unfold chargedMeasure at hf ⊢
  rw [integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with Y hY
  exact integral_prod _ hY

theorem gram_integral (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    (∫ x : Charged, ((‖family n p w c a x.1.1 x.1.2 x.2‖^2:ℝ):ℂ) ∂chargedMeasure) =
      gram n p w c a := by
  simp_rw [family_square_complex]
  rw [integral_finset_sum Finset.univ (fun I _ =>
    integrable_finset_sum Finset.univ (fun J _ => cross_integrable n p w c a hp hw I J))]
  unfold gram
  apply Finset.sum_congr rfl
  intro I _
  rw [integral_finset_sum Finset.univ (fun J _ => cross_integrable n p w c a hp hw I J)]
  apply Finset.sum_congr rfl
  intro J _
  rw [integral_const_mul]
  have hS := width_positive p (w I.1) (w J.1) hp (hw _) (hw _)
  rw [product_integral_order _ (KFCausalChargedFourierGaussianMoments.density_integrable _ _ _ hS
    (by simpa only [Complex.conj_re] using hS) _)]
  change _*KFCausalChargedFourierGaussianMoments.integral _ _ _ _ = _
  rw [KFCausalChargedFourierGaussianMoments.integral_moment _ _ _ hS
    (by simpa only [Complex.conj_re] using hS)]
  rfl

theorem ordered_gram_integral (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    (∫ Y in Set.Ioi 0, ∫ u, ∫ v, ((‖family n p w c a u v Y‖^2:ℝ):ℂ)) = gram n p w c a := by
  rw [← product_integral_order _ (family_square_integrable n p w c a hp hw)]
  exact gram_integral n p w c a hp hw

theorem gram_nonnegative (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    0 ≤ (gram n p w c a).re := by
  rw [← gram_integral n p w c a hp hw]
  change 0 ≤ RCLike.re (∫ x : Charged,
    ((‖family n p w c a x.1.1 x.1.2 x.2‖^2:ℝ):ℂ) ∂chargedMeasure)
  rw [← integral_re (family_square_integrable n p w c a hp hw)]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem gram_real (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : ℝ)
    (a : Fin n → Fin 3 → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) :
    (gram n p w c a).im = 0 := by
  rw [← gram_integral n p w c a hp hw]
  change RCLike.im (∫ x : Charged,
    ((‖family n p w c a x.1.1 x.1.2 x.2‖^2:ℝ):ℂ) ∂chargedMeasure) = 0
  rw [← integral_im (family_square_integrable n p w c a hp hw)]
  change (∫ _ : Charged, (0:ℝ) ∂chargedMeasure) = 0
  exact integral_zero _ _

#print axioms width_positive
#print axioms atom_cross
#print axioms family_square
#print axioms family_square_complex
#print axioms family_square_integrable
#print axioms product_integral_order
#print axioms gram_integral
#print axioms ordered_gram_integral
#print axioms gram_nonnegative
#print axioms gram_real
end
end UnifiedTheory.Audit.KFCausalChargedFourierPolynomialGram
