import UnifiedTheory.Audit.KFCausalBDG4DCompactTensorFactors
import UnifiedTheory.Audit.KFCausalBDG4DNonzeroCompactKernel

/- Smooth compact symmetric finite tensors supply the actual BDG profile
theorem. All derivative, support, uniform and cone bounds are constructed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalBDG4DCompactSymmetricTensor
noncomputable section
open MeasureTheory Real Set Filter Topology
open scoped BigOperators
open KFCausalBDG4DCompactTensorFactors KFCausalCSpecBridgeDefectObservable
open KFCausalMinkowski4DMoments (f4D)

structure Term where
  coefficient : ℝ
  left : Factor
  right : Factor

def jet (f : Factor) (k : Fin 3) : ℝ → ℝ := ![f.value,f.first,f.second] k

private theorem jet_continuous (f : Factor) (k : Fin 3) : Continuous (jet f k) := by
  fin_cases k
  · exact f.smooth.continuous
  · exact f.first_smooth.continuous
  · exact f.second_smooth.continuous

private theorem jet_derivative (f : Factor) (k : Fin 2) (x : ℝ) :
    HasDerivAt (jet f k.castSucc) (jet f k.succ x) x := by
  fin_cases k
  · exact f.value_derivative x
  · exact f.first_derivative x

private theorem jet_bound (f : Factor) (k : Fin 3) (x : ℝ) : |jet f k x| ≤ f.bound := by
  fin_cases k
  · exact f.uniform_bound.2.1 x
  · exact f.uniform_bound.2.2.1 x
  · exact f.uniform_bound.2.2.2 x

private theorem jet_outside (f : Factor) (k : Fin 3) (x : ℝ) (hx : 3 ≤ |x|) : jet f k x=0 := by
  fin_cases k
  · exact (f.outside_support x hx).1
  · exact (f.outside_support x hx).2.1
  · exact (f.outside_support x hx).2.2

def component {n : ℕ} (terms : Fin n → Term) (k l : Fin 3) (u v : ℝ) : ℝ :=
  ∑ i, (terms i).coefficient *
    (jet (terms i).left k u*jet (terms i).right l v+
      jet (terms i).right k u*jet (terms i).left l v)

def bound {n : ℕ} (terms : Fin n → Term) : ℝ :=
  ∑ i, 2*|(terms i).coefficient| *(terms i).left.bound*(terms i).right.bound

theorem bound_nonneg {n : ℕ} (terms : Fin n → Term) : 0 ≤ bound terms := by
  apply Finset.sum_nonneg
  intro i hi
  have hl := (terms i).left.uniform_bound.1
  have hr := (terms i).right.uniform_bound.1
  positivity

theorem component_continuous {n : ℕ} (terms : Fin n → Term) (k l : Fin 3) :
    Continuous (Function.uncurry (component terms k l)) := by
  unfold Function.uncurry component
  apply continuous_finset_sum
  intro i hi
  exact continuous_const.mul
    ((((jet_continuous (terms i).left k).comp continuous_fst).mul
      ((jet_continuous (terms i).right l).comp continuous_snd)).add
      (((jet_continuous (terms i).right k).comp continuous_fst).mul
        ((jet_continuous (terms i).left l).comp continuous_snd)))

theorem component_derivative_u {n : ℕ} (terms : Fin n → Term)
    (k : Fin 2) (l : Fin 3) (u v : ℝ) :
    HasDerivAt (fun x => component terms k.castSucc l x v)
      (component terms k.succ l u v) u := by
  apply HasDerivAt.fun_sum
  intro i hi
  exact (((jet_derivative (terms i).left k u).mul_const (jet (terms i).right l v)).add
    ((jet_derivative (terms i).right k u).mul_const (jet (terms i).left l v))).const_mul _

theorem component_derivative_v {n : ℕ} (terms : Fin n → Term)
    (k : Fin 3) (l : Fin 2) (u v : ℝ) :
    HasDerivAt (fun x => component terms k l.castSucc u x)
      (component terms k l.succ u v) v := by
  apply HasDerivAt.fun_sum
  intro i hi
  exact (((jet_derivative (terms i).right l v).const_mul (jet (terms i).left k u)).add
    ((jet_derivative (terms i).left l v).const_mul (jet (terms i).right k u))).const_mul _

theorem component_swap {n : ℕ} (terms : Fin n → Term) (k l : Fin 3) (u v : ℝ) :
    component terms k l u v=component terms l k v u := by
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem component_outside {n : ℕ} (terms : Fin n → Term) (k l : Fin 3) (u v : ℝ)
    (h : 3 ≤ |u| ∨ 3 ≤ |v|) : component terms k l u v=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rcases h with hu | hv
  · rw [jet_outside (terms i).left k u hu,jet_outside (terms i).right k u hu]
    ring
  · rw [jet_outside (terms i).left l v hv,jet_outside (terms i).right l v hv]
    ring

theorem component_bound {n : ℕ} (terms : Fin n → Term) (k l : Fin 3) (u v : ℝ) :
    |component terms k l u v| ≤ bound terms := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro i hi
  have hl := (terms i).left.uniform_bound.1
  have hr := (terms i).right.uniform_bound.1
  have h1 : |jet (terms i).left k u*jet (terms i).right l v| ≤
      (terms i).left.bound*(terms i).right.bound := by
    rw [abs_mul]
    exact mul_le_mul (jet_bound _ _ _) (jet_bound _ _ _) (abs_nonneg _) hl
  have h2 : |jet (terms i).right k u*jet (terms i).left l v| ≤
      (terms i).left.bound*(terms i).right.bound := by
    rw [abs_mul,mul_comm]
    exact mul_le_mul (jet_bound _ _ _) (jet_bound _ _ _) (abs_nonneg _) hl
  rw [abs_mul]
  calc _ ≤ |(terms i).coefficient| *(2*(terms i).left.bound*(terms i).right.bound) :=
      mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _)
    _ = _ := by ring

def functions {n : ℕ} (terms : Fin n → Term) : BDG4DOperatorProfileFunctions where
  mbar t r := component terms 0 0 (-t-r) (-t+r)
  profile := component terms 0 0
  profileU := component terms 1 0
  profileUV := component terms 1 1
  profileUVU := component terms 2 1
  profileUVV := component terms 1 2
  profileUU v := component terms 2 0 0 v
  profileVV u := component terms 0 2 u 0
  profile_def := by
    intro u v
    congr 1 <;> ring
  even_mbar := by
    intro t r
    simp only [sub_neg_eq_add,← sub_eq_add_neg]
    exact component_swap terms 0 0 _ _

def scales {n : ℕ} (terms : Fin n → Term) : BDG4DOperatorProfileScales where
  uSupport := 3
  vSupport := 3
  profileBound := bound terms
  profileDerivBound := bound terms
  mixedBound := bound terms
  mixedUDerivBound := bound terms
  mixedVDerivBound := bound terms
  coneBound := 324*bound terms
  huSupport_pos := by norm_num
  hvSupport_pos := by norm_num

def regularity {n : ℕ} (terms : Fin n → Term) : BDG4DOperatorProfileRegularity (functions terms) where
  profile_cont := component_continuous terms 0 0
  profileU_cont := component_continuous terms 1 0
  profileUV_cont := component_continuous terms 1 1
  profile_deriv_u := fun v u => component_derivative_u terms 0 0 u v
  profileU_deriv_v := fun u v => component_derivative_v terms 1 0 u v
  profileUV_deriv_u := fun v u => component_derivative_u terms 1 1 u v
  profileUV_deriv_v := fun u v => component_derivative_v terms 1 1 u v
  profileVV_deriv := fun u => component_derivative_u terms 0 2 u 0
  profileUU_deriv := fun v => component_derivative_v terms 2 0 0 v
  profileUVV_axis_cont := (component_continuous terms 1 2).comp (continuous_id.prodMk continuous_const)
  profileUVU_axis_cont := (component_continuous terms 2 1).comp (continuous_const.prodMk continuous_id)

def uniformBounds {n : ℕ} (terms : Fin n → Term) :
    BDG4DOperatorProfileUniformBounds (scales terms) (functions terms) where
  profile_bound := component_bound terms 0 0
  profileU_bound := component_bound terms 1 0
  profileUV_bound := component_bound terms 1 1
  profileUVU_bound := component_bound terms 2 1
  profileUVV_bound := component_bound terms 1 2

def support {n : ℕ} (terms : Fin n → Term) :
    BDG4DOperatorProfileSupport (scales terms) (functions terms) where
  profile_support_u := fun u v h => component_outside terms 0 0 u v (Or.inl (h.trans (le_abs_self u)))
  profile_support_v := fun u v h => component_outside terms 0 0 u v (Or.inr (h.trans (le_abs_self v)))
  profileU_support_u := fun u v h => component_outside terms 1 0 u v (Or.inl (h.trans (le_abs_self u)))
  profileU_support_v := fun u v h => component_outside terms 1 0 u v (Or.inr (h.trans (le_abs_self v)))
  profileUV_support_u := fun u v h => component_outside terms 1 1 u v (Or.inl (h.trans (le_abs_self u)))
  profileUV_support_v := fun u v h => component_outside terms 1 1 u v (Or.inr (h.trans (le_abs_self v)))
  profileVV_support := fun u h => component_outside terms 0 2 u 0 (Or.inl (h.trans (le_abs_self u)))
  profileUU_support := fun v h => component_outside terms 2 0 0 v (Or.inr (h.trans (le_abs_self v)))

theorem cone_bound {n : ℕ} (terms : Fin n → Term) (a : ℝ) (ha : 0<a) (u v : ℝ) :
    |a*(v-u)^2*f4D (a*u^2*v^2)*component terms 0 0 u v| ≤ 324*bound terms*a := by
  have hC := bound_nonneg terms
  by_cases hu : 3 ≤ |u|
  · rw [component_outside terms 0 0 u v (Or.inl hu),mul_zero,abs_zero]
    positivity
  by_cases hv : 3 ≤ |v|
  · rw [component_outside terms 0 0 u v (Or.inr hv),mul_zero,abs_zero]
    positivity
  have hab : |v-u| ≤ 6 := (abs_sub v u).trans (by linarith [lt_of_not_ge hu,lt_of_not_ge hv])
  have hsq : (v-u)^2 ≤ 36 := by nlinarith [sq_abs (v-u),abs_nonneg (v-u)]
  have hk := KFCausalMinkowski4DRealModes.f4D_abs_le (a*u^2*v^2) (by positivity)
  rw [abs_mul,abs_mul,abs_mul,abs_of_pos ha,abs_sq]
  calc
    _ ≤ (a*36)*9*bound terms := by
      apply mul_le_mul _ (component_bound terms 0 0 u v) (abs_nonneg _) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsq ha.le) hk (abs_nonneg _) (by positivity)
    _ = _ := by ring

def data {n : ℕ} (terms : Fin n → Term) : BDG4DOperatorProfileSplitData where
  scales := scales terms
  functions := functions terms
  regularity := regularity terms
  uniformBounds := uniformBounds terms
  support := support terms
  coneBound := ⟨cone_bound terms⟩

theorem quadrant_tendsto {n : ℕ} (terms : Fin n → Term) :
    Tendsto (fun a : ℝ => sqrt a*((∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ),
      a*(v-u)^2*f4D (a*u^2*v^2)*component terms 0 0 u v)-component terms 0 0 0 0/6))
      atTop (𝓝 (sqrt π/24*(component terms 2 0 0 0+component terms 0 2 0 0)-
        sqrt π/6*component terms 1 1 0 0)) := by
  let D := (data terms).toProfileData
  have h := KFCausalMinkowski4DProfileTheorem.bdg_4d_profile
    D.uSupport D.vSupport D.profileBound D.profileDerivBound D.mixedBound
    D.mixedUDerivBound D.mixedVDerivBound D.coneBound D.huSupport_pos D.hvSupport_pos
    D.profile D.profileU D.profileUV D.profileUVU D.profileUVV D.profileUU D.profileVV
    D.profile_cont D.profileU_cont D.profileUV_cont D.profile_deriv_u D.profileU_deriv_v
    D.profileUV_deriv_u D.profileUV_deriv_v D.profile_bound D.profileU_bound D.profileUV_bound
    D.profileUVU_bound D.profileUVV_bound D.hCcone D.profile_support_u D.profile_support_v
    D.profileU_support_u D.profileU_support_v D.profileUV_support_u D.profileUV_support_v
    D.profileVV_deriv D.profileUU_deriv D.profileUVV_axis_cont D.profileUVU_axis_cont
    D.profileVV_support D.profileUU_support
  simpa only [D,data,BDG4DOperatorProfileSplitData.toProfileData,functions,
    one_div,mul_comm (6 : ℝ)⁻¹,← div_eq_mul_inv] using h

#print axioms bound_nonneg
#print axioms component_continuous
#print axioms component_derivative_u
#print axioms component_derivative_v
#print axioms component_swap
#print axioms component_outside
#print axioms component_bound
#print axioms cone_bound
#print axioms quadrant_tendsto
end
end UnifiedTheory.Audit.KFCausalBDG4DCompactSymmetricTensor
