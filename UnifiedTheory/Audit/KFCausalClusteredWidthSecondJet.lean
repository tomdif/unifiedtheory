/- Second charged derivatives of clustered profiles. An explicit local
spacing-independent polynomial envelope and the exact width-cube sum. -/
import UnifiedTheory.Audit.KFCausalClusteredChargedJetIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalClusteredWidthSecondJet
noncomputable section
open Filter
open scoped Topology
open KFCausalClusteredWidthProfiles (quotient widths coefficients quotient_tendsto quotient_norm_le)
open KFCausalClusteredWidthChargedJet (jet quotient_derivative exponential_norm_le_one)
open KFCausalClusteredChargedJetIdentity (widthSquareSum widthSquareSum_eq)

def secondJet (n : ℕ) (δ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-z)*((n:ℂ)*(n-1:ℕ)*quotient δ z^(n-2)*Complex.exp (-(δ:ℂ)*z)^2-
    (n:ℂ)*((δ:ℂ)+2)*quotient δ z^(n-1)*Complex.exp (-(δ:ℂ)*z)+quotient δ z^n)
def limitSecondJet (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-z)*((n:ℂ)*(n-1:ℕ)*z^(n-2)-2*(n:ℂ)*z^(n-1)+z^n)

theorem jet_derivative (n : ℕ) (δ : ℝ) (hδ : δ ≠ 0) (z : ℂ) :
    HasDerivAt (jet n δ) (secondJet n δ z) z := by
  have hq := quotient_derivative δ hδ z
  have he := ((hasDerivAt_id z).const_mul (-(δ:ℂ))).cexp
  have hd := ((hasDerivAt_id z).neg.cexp).mul ((((hq.pow (n-1)).const_mul (n:ℂ)).mul he).sub (hq.pow n))
  convert hd using 1
  simp only [secondJet,Pi.neg_apply,Pi.mul_apply,Pi.sub_apply,Pi.pow_apply,id_eq,Nat.sub_sub,show (1:ℕ)+1=2 from rfl]
  ring

theorem secondJet_tendsto (n : ℕ) (z : ℂ) :
    Tendsto (fun δ : ℝ => secondJet n δ z) (𝓝[>] 0) (𝓝 (limitSecondJet n z)) := by
  have he : Tendsto (fun δ : ℝ => Complex.exp (-(δ:ℂ)*z)) (𝓝[>] 0) (𝓝 (1:ℂ)) := by
    have hc : ContinuousAt (fun δ : ℝ => Complex.exp (-(δ:ℂ)*z)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun δ : ℝ => (δ:ℂ)+2) (𝓝[>] 0) (𝓝 (2:ℂ)) := by
    have hc : ContinuousAt (fun δ : ℝ => (δ:ℂ)+2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hq := quotient_tendsto z
  convert (((((hq.pow (n-2)).const_mul ((n:ℂ)*(n-1:ℕ))).mul (he.pow 2)).sub
    (((hd.const_mul (n:ℂ)).mul (hq.pow (n-1))).mul he)).add (hq.pow n)).const_mul (Complex.exp (-z)) using 1
  simp only [limitSecondJet,one_pow,mul_one]
  ring

theorem secondJet_norm_le (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (z : ℂ) (hz : 0 ≤ z.re) :
    ‖secondJet n δ z‖ ≤ Real.exp (-z.re)*
      ((n:ℝ)*(n-1:ℕ)*‖z‖^(n-2)+3*(n:ℝ)*‖z‖^(n-1)+‖z‖^n) := by
  have hq := quotient_norm_le δ z hδ hz
  have he := exponential_norm_le_one δ z hδ.le hz
  have hA : ‖(n:ℂ)*(n-1:ℕ)*quotient δ z^(n-2)*Complex.exp (-(δ:ℂ)*z)^2‖ ≤
      (n:ℝ)*(n-1:ℕ)*‖z‖^(n-2) := by
    simp only [norm_mul,norm_pow,Complex.norm_natCast]
    calc
      _ ≤ (n:ℝ)*(n-1:ℕ)*‖z‖^(n-2)*1^2 := by gcongr
      _ = _ := by ring
  have hB : ‖(n:ℂ)*((δ:ℂ)+2)*quotient δ z^(n-1)*Complex.exp (-(δ:ℂ)*z)‖ ≤
      3*(n:ℝ)*‖z‖^(n-1) := by
    have hd : ‖(δ:ℂ)+2‖ ≤ 3 := by
      rw [← Complex.ofReal_ofNat 2,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ δ+2)]
      linarith
    simp only [norm_mul,norm_pow,Complex.norm_natCast]
    calc
      _ ≤ (n:ℝ)*3*‖z‖^(n-1)*1 := by gcongr
      _ = _ := by ring
  have hC : ‖quotient δ z^n‖ ≤ ‖z‖^n := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hq n
  unfold secondJet
  rw [norm_mul,Complex.norm_exp,Complex.neg_re]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  let A := (n:ℂ)*(n-1:ℕ)*quotient δ z^(n-2)*Complex.exp (-(δ:ℂ)*z)^2
  let B := (n:ℂ)*((δ:ℂ)+2)*quotient δ z^(n-1)*Complex.exp (-(δ:ℂ)*z)
  let D := quotient δ z^n
  change ‖A-B+D‖ ≤ _
  calc
    _ ≤ ‖A-B‖+‖D‖ := norm_add_le _ _
    _ ≤ (‖A‖+‖B‖)+‖D‖ := add_le_add (norm_sub_le A B) le_rfl
    _ ≤ _ := add_le_add (add_le_add hA hB) hC

def widthCubeSum (n : ℕ) (δ : ℝ) (z : ℂ) : ℂ :=
  ∑ i, coefficients n δ i*(widths n δ i:ℂ)^3*Complex.exp (-(widths n δ i:ℂ)*z)

theorem widthCubeSum_eq (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    widthCubeSum n δ z = secondJet n δ z := by
  have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (n+1))))
    (fun i _ => (((hasDerivAt_id z).const_mul (-(widths n δ i:ℂ))).cexp).const_mul
      (coefficients n δ i*(widths n δ i:ℂ)^2))
  have hj := (jet_derivative n δ hδ.ne' z).neg
  have he : (fun x => -jet n δ x) = widthSquareSum n δ :=
    funext (fun x => (widthSquareSum_eq n δ hδ x).symm)
  change HasDerivAt (fun x => -jet n δ x) (-secondJet n δ z) z at hj
  rw [he] at hj
  have hu := hj.unique hd
  simp only [id_eq] at hu
  calc
    widthCubeSum n δ z = -(∑ i, (coefficients n δ i*(widths n δ i:ℂ)^2)*
      (Complex.exp (-(widths n δ i:ℂ)*z)*(-(widths n δ i:ℂ)*1))) := by
        rw [← Finset.sum_neg_distrib]
        unfold widthCubeSum
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = secondJet n δ z := by rw [← hu,neg_neg]

#print axioms jet_derivative
#print axioms secondJet_tendsto
#print axioms secondJet_norm_le
#print axioms widthCubeSum_eq
end
end UnifiedTheory.Audit.KFCausalClusteredWidthSecondJet
