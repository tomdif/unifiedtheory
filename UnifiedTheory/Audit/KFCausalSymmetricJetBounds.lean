/- Joint Gaussian bounds for both full numerator derivatives. The source,
two polynomial factors, linear Gaussian derivative, and curvature term
are absorbed together, before discarding any Gaussian decay. -/
import UnifiedTheory.Audit.KFCausalTwoPolynomialSourceAbsorption
import UnifiedTheory.Audit.KFCausalSymmetricNumeratorJets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSymmetricJetBounds
noncomputable section
open KFCausalTwoPolynomialSourceAbsorption (cap cap_nonnegative weighted_source_bound)

def firstCore (Q P : Polynomial ℂ) (x z a d g : ℂ) : ℂ :=
  a*Q.derivative.eval x*P.eval z+d*Q.eval x*P.derivative.eval z+g*Q.eval x*P.eval z

def secondCore (Q P : Polynomial ℂ) (x z a d g c : ℂ) : ℂ :=
  a^2*Q.derivative.derivative.eval x*P.eval z+
    2*a*d*Q.derivative.eval x*P.derivative.eval z+
    d^2*Q.eval x*P.derivative.derivative.eval z+
    2*g*(a*Q.derivative.eval x*P.eval z+d*Q.eval x*P.derivative.eval z)+
    (g^2+c)*Q.eval x*P.eval z

def firstCap (Q P : Polynomial ℂ) (b : ℂ) (A K G da dz δ : ℝ) : ℝ :=
  da*cap Q.derivative P b A K δ 0+dz*cap Q P.derivative b A K δ 0+
    G*cap Q P b A K δ 1

def secondCap (Q P : Polynomial ℂ) (b : ℂ) (A K G da dz dc δ : ℝ) : ℝ :=
  da^2*cap Q.derivative.derivative P b A K δ 0+
    (2*da*dz)*cap Q.derivative P.derivative b A K δ 0+
    dz^2*cap Q P.derivative.derivative b A K δ 0+
    (2*da)*G*cap Q.derivative P b A K δ 1+
    (2*dz)*G*cap Q P.derivative b A K δ 1+
    G^2*cap Q P b A K δ 2+dc*cap Q P b A K δ 0

theorem sum_bound {n : ℕ} (Q P : Fin n → Polynomial ℂ) (N : Fin n → ℕ)
    (c : Fin n → ℂ) (M : Fin n → ℝ) (b x z g : ℂ) (A K G R δ : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hG : 0 ≤ G) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hx : ‖x‖ ≤ A*R) (hz : ‖z‖ ≤ K*R) (hg : ‖g‖ ≤ G*(1+R))
    (hc : ∀ i, ‖c i‖ ≤ M i) :
    ‖∑ i, c i*g^(N i)*((Q i).eval x*(P i).eval z*Complex.exp (b*z))‖*
      Real.exp (-δ*R^2) ≤ ∑ i, M i*G^(N i)*cap (Q i) (P i) b A K δ (N i) := by
  apply (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ = ‖c i‖*(‖g^(N i)*((Q i).eval x*(P i).eval z*Complex.exp (b*z))‖*
        Real.exp (-δ*R^2)) := by simp only [norm_mul]; ring
    _ ≤ M i*(G^(N i)*cap (Q i) (P i) b A K δ (N i)) :=
      mul_le_mul (hc i)
        (weighted_source_bound (Q i) (P i) b x z g A K G R δ (N i) hA hK hG hR hδ hx hz hg)
        (by positivity) ((norm_nonneg _).trans (hc i))
    _ = _ := by ring

theorem first_bound (Q P : Polynomial ℂ) (b x z a d g : ℂ) (A K G da dz R δ : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hG : 0 ≤ G) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hx : ‖x‖ ≤ A*R) (hz : ‖z‖ ≤ K*R) (hg : ‖g‖ ≤ G*(1+R))
    (ha : ‖a‖ ≤ da) (hd : ‖d‖ ≤ dz) :
    ‖firstCore Q P x z a d g*Complex.exp (b*z)‖*Real.exp (-δ*R^2) ≤
      firstCap Q P b A K G da dz δ := by
  have he := sum_bound ![Q.derivative,Q,Q] ![P,P.derivative,P] ![0,0,1]
    ![a,d,1] ![da,dz,1] b x z g A K G R δ hA hK hG hR hδ hx hz hg
    (by intro i; fin_cases i <;> simp [ha,hd])
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    pow_zero,pow_one,one_mul,add_zero] at he
  convert he using 1
  · congr 1
    congr 1
    unfold firstCore
    ring
  · unfold firstCap
    ring

theorem second_bound (Q P : Polynomial ℂ) (b x z a d g c : ℂ)
    (A K G da dz dc R δ : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hG : 0 ≤ G) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hx : ‖x‖ ≤ A*R) (hz : ‖z‖ ≤ K*R) (hg : ‖g‖ ≤ G*(1+R))
    (ha : ‖a‖ ≤ da) (hd : ‖d‖ ≤ dz) (hc : ‖c‖ ≤ dc) :
    ‖secondCore Q P x z a d g c*Complex.exp (b*z)‖*Real.exp (-δ*R^2) ≤
      secondCap Q P b A K G da dz dc δ := by
  have hda : 0 ≤ da := (norm_nonneg _).trans ha
  have hdz : 0 ≤ dz := (norm_nonneg _).trans hd
  have hcoeff : ∀ i : Fin 7, ‖(![a^2,2*a*d,d^2,2*a,2*d,1,c] : Fin 7 → ℂ) i‖ ≤
      (![da^2,2*da*dz,dz^2,2*da,2*dz,1,dc] : Fin 7 → ℝ) i := by
    intro i
    fin_cases i
    · change ‖a^2‖ ≤ da^2
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ha 2
    · change ‖2*a*d‖ ≤ 2*da*dz
      simp only [norm_mul]
      norm_num only [Complex.norm_ofNat]
      exact mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) hd (norm_nonneg _) (by positivity)
    · change ‖d^2‖ ≤ dz^2
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hd 2
    · change ‖2*a‖ ≤ 2*da
      simp only [norm_mul]
      norm_num only [Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left ha (by norm_num)
    · change ‖2*d‖ ≤ 2*dz
      simp only [norm_mul]
      norm_num only [Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hd (by norm_num)
    · change ‖(1:ℂ)‖ ≤ (1:ℝ)
      norm_num
    · exact hc
  have he := sum_bound
    ![Q.derivative.derivative,Q.derivative,Q,Q.derivative,Q,Q,Q]
    ![P,P.derivative,P.derivative.derivative,P,P.derivative,P,P]
    ![0,0,0,1,1,2,0] ![a^2,2*a*d,d^2,2*a,2*d,1,c]
    ![da^2,2*da*dz,dz^2,2*da,2*dz,1,dc] b x z g A K G R δ
    hA hK hG hR hδ hx hz hg hcoeff
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    pow_zero,pow_one,one_mul,add_zero] at he
  convert he using 1
  · congr 1
    congr 1
    unfold secondCore
    ring
  · unfold secondCap
    ring

#print axioms sum_bound
#print axioms first_bound
#print axioms second_bound
end
end UnifiedTheory.Audit.KFCausalSymmetricJetBounds
