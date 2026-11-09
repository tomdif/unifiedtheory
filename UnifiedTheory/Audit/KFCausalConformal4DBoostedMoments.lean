import UnifiedTheory.Audit.KFCausalConformal4DCurvatureExpansion

/-!
Exact moments of an explicitly parameterized, spherically reduced rest diamond.
The boost preserves the Lorentz quadratic form and has determinant one.  This
file does not identify the parameter integral with a manifold volume measure
or prove a chronological-diamond change of variables.
-/

namespace UnifiedTheory.Audit.KFCausalConformal4DBoostedMoments

noncomputable section
open MeasureTheory Real
open KFCausalConformal4DDiamondBenchmark

def boostMatrix (A B : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![A, B, 0, 0; B, A, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def boost (A B : ℝ) (p : Point) : Point :=
  ![A*p 0+B*p 1, B*p 0+A*p 1, p 2, p 3]

def lorentzSquare (p : Point) : ℝ := -p 0^2+p 1^2+p 2^2+p 3^2

theorem boost_lorentz (A B : ℝ) (h : A^2-B^2=1) (p : Point) :
    lorentzSquare (boost A B p) = lorentzSquare p := by
  change -(A*p 0+B*p 1)^2+(B*p 0+A*p 1)^2+p 2^2+p 3^2 =
    -p 0^2+p 1^2+p 2^2+p 3^2
  nlinarith [congrArg (fun x : ℝ => x*p 0^2) h,
    congrArg (fun x : ℝ => x*p 1^2) h]

theorem boost_determinant (A B : ℝ) (h : A^2-B^2=1) :
    Matrix.det (boostMatrix A B) = 1 := by
  have hd (x : ℝ) : Matrix.det (!![x,0,0; 0,1,0; 0,0,1] : Matrix (Fin 3) (Fin 3) ℝ) = x := by
    rw [Matrix.det_fin_three]
    change x*1*1-x*0*0-0*0*1+0*0*0+0*0*0-0*1*0=x
    ring
  have h0 : (boostMatrix A B).submatrix Fin.succ (0 : Fin 4).succAbove =
      (!![A,0,0; 0,1,0; 0,0,1] : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h1 : (boostMatrix A B).submatrix Fin.succ (1 : Fin 4).succAbove =
      (!![B,0,0; 0,1,0; 0,0,1] : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [show boostMatrix A B 0 2=0 by rfl,
    show boostMatrix A B 0 3=0 by rfl, mul_zero, zero_mul, add_zero, h0, h1, hd]
  norm_num [boostMatrix]
  nlinarith

def boostLinear (A B : ℝ) : Point →L[ℝ] Point :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin (boostMatrix A B))

theorem boost_linear_action (A B : ℝ) (p : Point) : boostLinear A B p = boost A B p := by
  change (boostMatrix A B).mulVec p = boost A B p
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, boostMatrix, boost]

theorem boost_derivative (A B : ℝ) (p : Point) :
    HasFDerivAt (boost A B) (boostLinear A B) p := by
  have he : boost A B = boostLinear A B := by
    funext x
    exact (boost_linear_action A B x).symm
  rw [he]
  exact (boostLinear A B).hasFDerivAt

/-- The two time branches after scaling the compact rest-diamond parameters. -/
def time (T m A B u v mu : ℝ) : ℝ := m+A*T*u+B*T*(1-u)*v*mu

def pair (T m A B : ℝ) (f : ℝ → ℝ) (u v mu : ℝ) : ℝ :=
  (1-u)^3*v^2*(f (time T m A B u v mu)+f (time T m (-A) B u v mu))

/-- Literal compact coordinate integral; its Jacobian is explicit. -/
def coordinateIntegral (T m A B : ℝ) (f : ℝ → ℝ) : ℝ :=
  2*π*T^4 * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
    ∫ mu in (-1 : ℝ)..1, pair T m A B f u v mu

private theorem inner_continuous (T m A B : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => ∫ mu in (-1 : ℝ)..1, pair T m A B f p.1 p.2 mu) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold pair time
  fun_prop

private theorem middle_continuous (T m A B : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun u : ℝ => ∫ v in (0 : ℝ)..1,
      ∫ mu in (-1 : ℝ)..1, pair T m A B f u v mu) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (inner_continuous T m A B hf) 0 1

theorem coordinate_integrable (T m A B : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    (∀ u v, IntervalIntegrable (pair T m A B f u v) volume (-1) 1) ∧
    (∀ u, IntervalIntegrable (fun v => ∫ mu in (-1 : ℝ)..1,
      pair T m A B f u v mu) volume 0 1) ∧
    IntervalIntegrable (fun u => ∫ v in (0 : ℝ)..1,
      ∫ mu in (-1 : ℝ)..1, pair T m A B f u v mu) volume 0 1 := by
  refine ⟨?_, ?_, (middle_continuous T m A B hf).intervalIntegrable _ _⟩
  · intro u v
    apply Continuous.intervalIntegrable
    unfold pair time
    fun_prop
  · intro u
    exact ((inner_continuous T m A B hf).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

theorem coordinate_add (T m A B : ℝ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    coordinateIntegral T m A B (fun x => f x+g x) =
      coordinateIntegral T m A B f + coordinateIntegral T m A B g := by
  obtain ⟨hfi, hfm, hfo⟩ := coordinate_integrable T m A B hf
  obtain ⟨hgi, hgm, hgo⟩ := coordinate_integrable T m A B hg
  have hp : ∀ u v mu, pair T m A B (fun x => f x+g x) u v mu =
      pair T m A B f u v mu+pair T m A B g u v mu := by
    intros; unfold pair; ring
  unfold coordinateIntegral
  simp_rw [hp, intervalIntegral.integral_add (hfi _ _) (hgi _ _),
    intervalIntegral.integral_add (hfm _) (hgm _),
    intervalIntegral.integral_add hfo hgo]
  ring

theorem coordinate_smul (T m A B c : ℝ) (f : ℝ → ℝ) :
    coordinateIntegral T m A B (fun x => c*f x) = c*coordinateIntegral T m A B f := by
  have hp : ∀ u v mu, pair T m A B (fun x => c*f x) u v mu =
      c*pair T m A B f u v mu := by
    intros; unfold pair; ring
  unfold coordinateIntegral
  simp_rw [hp, intervalIntegral.integral_const_mul]
  ring

theorem coordinate_mass (T m A B : ℝ) :
    coordinateIntegral T m A B (fun _ => 1) = 2*π*T^4/3 := by
  unfold coordinateIntegral pair
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  norm_num only [show (1 : ℝ)+1=2 by norm_num, show (1 : ℝ)-(-1)=2 by norm_num]
  have hv : ∀ u : ℝ, (∫ v in (0 : ℝ)..1, 2*((1-u)^3*v^2*2)) =
      (4/3 : ℝ)*(1-u)^3 := by
    intro u
    calc _ = (4*(1-u)^3) * ∫ v in (0 : ℝ)..1, v^2 := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro v hv
          ring
      _ = _ := by norm_num [integral_pow]; ring
  change 2*π*T^4*(∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
    2*((1-u)^3*v^2*2)) = _
  simp_rw [hv, intervalIntegral.integral_const_mul, KFCausalCSpecRSSConformal.J3]
  ring

private theorem angular_second (m a b : ℝ) :
    (∫ mu in (-1 : ℝ)..1, (m+a+b*mu)^2+(m-a+b*mu)^2) =
      4*m^2+4*a^2+4/3*b^2 := by
  have he : ∀ mu : ℝ, (m+a+b*mu)^2+(m-a+b*mu)^2 =
      (2*m^2+2*a^2)+4*m*b*mu+2*b^2*mu^2 := by intro mu; ring
  simp_rw [he]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num [intervalIntegral.integral_const_mul, integral_pow]
  ring

theorem coordinate_second (T m A B : ℝ) :
    coordinateIntegral T m A B (fun x => x^2) =
      2*π*T^4*m^2/3+2*π*T^6*A^2/45+4*π*T^6*B^2/45 := by
  have hi (u v : ℝ) : (∫ mu in (-1 : ℝ)..1, pair T m A B (fun x => x^2) u v mu) =
      (1-u)^3*v^2*(4*m^2+4*(A*T*u)^2+4/3*(B*T*(1-u)*v)^2) := by
    unfold pair time
    rw [intervalIntegral.integral_const_mul]
    congr 1
    convert angular_second m (A*T*u) (B*T*(1-u)*v) using 1
    congr 1
    funext mu; ring
  have hm (u : ℝ) : (∫ v in (0 : ℝ)..1,
      (1-u)^3*v^2*(4*m^2+4*(A*T*u)^2+4/3*(B*T*(1-u)*v)^2)) =
      (4/3*m^2)*(1-u)^3+(4/3*A^2*T^2)*(u^2*(1-u)^3)+
        (4/15*B^2*T^2)*(1-u)^5 := by
    have he : ∀ v : ℝ, (1-u)^3*v^2*(4*m^2+4*(A*T*u)^2+4/3*(B*T*(1-u)*v)^2) =
        (4*m^2*(1-u)^3+4*A^2*T^2*u^2*(1-u)^3)*v^2+
          (4/3*B^2*T^2*(1-u)^5)*v^4 := by intro v; ring
    simp_rw [he]
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    norm_num [intervalIntegral.integral_const_mul, integral_pow]
    ring
  unfold coordinateIntegral
  simp_rw [hi, hm]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  simp_rw [intervalIntegral.integral_const_mul, KFCausalCSpecRSSConformal.J3,
    KFCausalCSpecRSSConformal.J23, KFCausalCSpecRSSConformal.J5]
  ring

theorem boosted_second (T A B : ℝ) (h : A^2-B^2=1) :
    coordinateIntegral T (A*T) A B (fun x => x^2) =
      coordinateIntegral T (A*T) A B (fun _ => 1) *
        (3/10*(2*A*T)^2-(4*T^2)/30) := by
  rw [coordinate_second, coordinate_mass]
  have he : B^2 = A^2-1 := by linarith
  rw [he]
  ring

#print axioms boost_lorentz
#print axioms boost_determinant
#print axioms boost_linear_action
#print axioms boost_derivative
#print axioms coordinate_integrable
#print axioms coordinate_add
#print axioms coordinate_smul
#print axioms coordinate_mass
#print axioms coordinate_second
#print axioms boosted_second

end
end UnifiedTheory.Audit.KFCausalConformal4DBoostedMoments
