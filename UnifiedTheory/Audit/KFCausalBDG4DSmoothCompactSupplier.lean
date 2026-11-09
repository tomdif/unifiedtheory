import UnifiedTheory.Audit.KFCausalBDG4DSmoothCompactPartials

/- Every smooth compact symmetric two-variable profile supplies the permissive
BDG profile theorem. Neither derivative certificates nor a limit are inputs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalBDG4DSmoothCompactSupplier
noncomputable section
open MeasureTheory Real Set Filter Topology
open scoped ContDiff
open KFCausalBDG4DSmoothCompactPartials KFCausalCSpecBridgeDefectObservable
open KFCausalMinkowski4DMoments (f4D)

structure Profile where
  value : Point → ℝ
  smooth : ContDiff ℝ ∞ value
  compact : HasCompactSupport value
  symmetric : ∀ u v, value (u,v)=value (v,u)

def uJet (F : Point → ℝ) : ℕ → Point → ℝ
  | 0 => F
  | k+1 => du (uJet F k)

def jet (F : Point → ℝ) (k : ℕ) : ℕ → Point → ℝ
  | 0 => uJet F k
  | l+1 => dv (jet F k l)

private theorem uJet_smooth (F : Point → ℝ) (hF : ContDiff ℝ ∞ F) (k : ℕ) :
    ContDiff ℝ ∞ (uJet F k) := by
  induction k with
  | zero => exact hF
  | succ k ih => exact directional_smooth _ ih _

theorem jet_smooth (F : Point → ℝ) (hF : ContDiff ℝ ∞ F) (k l : ℕ) :
    ContDiff ℝ ∞ (jet F k l) := by
  induction l with
  | zero => exact uJet_smooth F hF k
  | succ l ih => exact directional_smooth _ ih _

private theorem uJet_support (F : Point → ℝ) (k : ℕ) :
    tsupport (uJet F k) ⊆ tsupport F := by
  induction k with
  | zero => exact Subset.rfl
  | succ k ih => exact (directional_support _ _).trans ih

theorem jet_support (F : Point → ℝ) (k l : ℕ) :
    tsupport (jet F k l) ⊆ tsupport F := by
  induction l with
  | zero => exact uJet_support F k
  | succ l ih => exact (directional_support _ _).trans ih

theorem jet_compact (F : Point → ℝ) (hF : HasCompactSupport F) (k l : ℕ) :
    HasCompactSupport (jet F k l) :=
  hF.of_isClosed_subset (isClosed_tsupport _) (jet_support F k l)

private theorem du_jet (F : Point → ℝ) (hF : ContDiff ℝ ∞ F) (k l : ℕ) :
    du (jet F k l)=jet F (k+1) l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    change du (dv (jet F k l))=dv (jet F (k+1) l)
    rw [du_dv _ (jet_smooth F hF k l),ih]

theorem jet_derivative_u (F : Point → ℝ) (hF : ContDiff ℝ ∞ F)
    (k l : ℕ) (u v : ℝ) :
    HasDerivAt (fun x => jet F k l (x,v)) (jet F (k+1) l (u,v)) u := by
  simpa only [du_jet F hF k l] using derivative_u _ (jet_smooth F hF k l) u v

theorem jet_derivative_v (F : Point → ℝ) (hF : ContDiff ℝ ∞ F)
    (k l : ℕ) (u v : ℝ) :
    HasDerivAt (fun x => jet F k l (u,x)) (jet F k (l+1) (u,v)) v :=
  derivative_v _ (jet_smooth F hF k l) u v

def radius (F : Profile) : ℝ := Classical.choose (compact_radius F.value F.compact)

theorem radius_spec (F : Profile) : 0<radius F ∧
    ∀ p ∈ tsupport F.value, |p.1| < radius F ∧ |p.2| < radius F :=
  Classical.choose_spec (compact_radius F.value F.compact)

def bound (F : Profile) (k l : ℕ) : ℝ := Classical.choose
  (compact_bound (jet F.value k l) (jet_compact F.value F.compact k l)
    (jet_smooth F.value F.smooth k l).continuous)

theorem bound_spec (F : Profile) (k l : ℕ) :
    0≤bound F k l ∧ ∀ p, |jet F.value k l p|≤bound F k l :=
  Classical.choose_spec (compact_bound (jet F.value k l) (jet_compact F.value F.compact k l)
    (jet_smooth F.value F.smooth k l).continuous)

theorem jet_outside (F : Profile) (k l : ℕ) (u v : ℝ)
    (h : radius F ≤ |u| ∨ radius F ≤ |v|) : jet F.value k l (u,v)=0 :=
  outside_radius F.value (jet F.value k l) (radius F) (radius_spec F).2
    (jet_support F.value k l) u v h

def functions (F : Profile) : BDG4DOperatorProfileFunctions where
  mbar t r := F.value (-t-r,-t+r)
  profile u v := F.value (u,v)
  profileU u v := jet F.value 1 0 (u,v)
  profileUV u v := jet F.value 1 1 (u,v)
  profileUVU u v := jet F.value 2 1 (u,v)
  profileUVV u v := jet F.value 1 2 (u,v)
  profileUU v := jet F.value 2 0 (0,v)
  profileVV u := jet F.value 0 2 (u,0)
  profile_def := by
    intro u v
    congr 1
    ext <;> dsimp <;> ring
  even_mbar := by
    intro t r
    simpa only [sub_neg_eq_add,← sub_eq_add_neg] using F.symmetric (-t+r) (-t-r)

def scales (F : Profile) : BDG4DOperatorProfileScales where
  uSupport := radius F
  vSupport := radius F
  profileBound := bound F 0 0
  profileDerivBound := bound F 1 0
  mixedBound := bound F 1 1
  mixedUDerivBound := bound F 2 1
  mixedVDerivBound := bound F 1 2
  coneBound := 36*(radius F)^2*bound F 0 0
  huSupport_pos := (radius_spec F).1
  hvSupport_pos := (radius_spec F).1

def regularity (F : Profile) : BDG4DOperatorProfileRegularity (functions F) where
  profile_cont := F.smooth.continuous
  profileU_cont := (jet_smooth F.value F.smooth 1 0).continuous
  profileUV_cont := (jet_smooth F.value F.smooth 1 1).continuous
  profile_deriv_u := fun v u => jet_derivative_u F.value F.smooth 0 0 u v
  profileU_deriv_v := fun u v => jet_derivative_v F.value F.smooth 1 0 u v
  profileUV_deriv_u := fun v u => jet_derivative_u F.value F.smooth 1 1 u v
  profileUV_deriv_v := fun u v => jet_derivative_v F.value F.smooth 1 1 u v
  profileVV_deriv := fun u => jet_derivative_u F.value F.smooth 0 2 u 0
  profileUU_deriv := fun v => jet_derivative_v F.value F.smooth 2 0 0 v
  profileUVV_axis_cont := (jet_smooth F.value F.smooth 1 2).continuous.comp
    (continuous_id.prodMk continuous_const)
  profileUVU_axis_cont := (jet_smooth F.value F.smooth 2 1).continuous.comp
    (continuous_const.prodMk continuous_id)

def uniformBounds (F : Profile) :
    BDG4DOperatorProfileUniformBounds (scales F) (functions F) where
  profile_bound := fun u v => (bound_spec F 0 0).2 (u,v)
  profileU_bound := fun u v => (bound_spec F 1 0).2 (u,v)
  profileUV_bound := fun u v => (bound_spec F 1 1).2 (u,v)
  profileUVU_bound := fun u v => (bound_spec F 2 1).2 (u,v)
  profileUVV_bound := fun u v => (bound_spec F 1 2).2 (u,v)

def support (F : Profile) : BDG4DOperatorProfileSupport (scales F) (functions F) where
  profile_support_u := fun u v h => jet_outside F 0 0 u v (Or.inl (h.trans (le_abs_self u)))
  profile_support_v := fun u v h => jet_outside F 0 0 u v (Or.inr (h.trans (le_abs_self v)))
  profileU_support_u := fun u v h => jet_outside F 1 0 u v (Or.inl (h.trans (le_abs_self u)))
  profileU_support_v := fun u v h => jet_outside F 1 0 u v (Or.inr (h.trans (le_abs_self v)))
  profileUV_support_u := fun u v h => jet_outside F 1 1 u v (Or.inl (h.trans (le_abs_self u)))
  profileUV_support_v := fun u v h => jet_outside F 1 1 u v (Or.inr (h.trans (le_abs_self v)))
  profileVV_support := fun u h => jet_outside F 0 2 u 0 (Or.inl (h.trans (le_abs_self u)))
  profileUU_support := fun v h => jet_outside F 2 0 0 v (Or.inr (h.trans (le_abs_self v)))

theorem cone_bound (F : Profile) (a : ℝ) (ha : 0<a) (u v : ℝ) :
    |a*(v-u)^2*f4D (a*u^2*v^2)*F.value (u,v)| ≤ 36*(radius F)^2*bound F 0 0*a := by
  have hC := (bound_spec F 0 0).1
  have hR := (radius_spec F).1
  by_cases hu : radius F ≤ |u|
  · have hz := jet_outside F 0 0 u v (Or.inl hu)
    change F.value (u,v)=0 at hz
    rw [hz,mul_zero,abs_zero]
    positivity
  by_cases hv : radius F ≤ |v|
  · have hz := jet_outside F 0 0 u v (Or.inr hv)
    change F.value (u,v)=0 at hz
    rw [hz,mul_zero,abs_zero]
    positivity
  have hab : |v-u| ≤ 2*radius F := (abs_sub v u).trans
    (by linarith [lt_of_not_ge hu,lt_of_not_ge hv])
  have hsq : (v-u)^2 ≤ 4*(radius F)^2 := by
    nlinarith [sq_abs (v-u),abs_nonneg (v-u)]
  have hk := KFCausalMinkowski4DRealModes.f4D_abs_le (a*u^2*v^2) (by positivity)
  rw [abs_mul,abs_mul,abs_mul,abs_of_pos ha,abs_sq]
  calc
    _ ≤ (a*(4*(radius F)^2))*9*bound F 0 0 := by
      apply mul_le_mul _ ((bound_spec F 0 0).2 (u,v)) (abs_nonneg _) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsq ha.le) hk (abs_nonneg _) (by positivity)
    _ = _ := by ring

def data (F : Profile) : BDG4DOperatorProfileSplitData where
  scales := scales F
  functions := functions F
  regularity := regularity F
  uniformBounds := uniformBounds F
  support := support F
  coneBound := ⟨cone_bound F⟩

theorem quadrant_tendsto (F : Profile) :
    Tendsto (fun a : ℝ => sqrt a*((∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ),
      a*(v-u)^2*f4D (a*u^2*v^2)*F.value (u,v))-F.value (0,0)/6))
      atTop (𝓝 (sqrt π/24*(jet F.value 2 0 (0,0)+jet F.value 0 2 (0,0))-
        sqrt π/6*jet F.value 1 1 (0,0))) := by
  let D := (data F).toProfileData
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

theorem smooth_compact_quadrant_tendsto (F : Point → ℝ) (hF : ContDiff ℝ ∞ F)
    (hcompact : HasCompactSupport F) (hsym : ∀ u v, F (u,v)=F (v,u)) :
    Tendsto (fun a : ℝ => sqrt a*((∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ),
      a*(v-u)^2*f4D (a*u^2*v^2)*F (u,v))-F (0,0)/6))
      atTop (𝓝 (sqrt π/24*(du (du F) (0,0)+dv (dv F) (0,0))-
        sqrt π/6*dv (du F) (0,0))) :=
  quadrant_tendsto ⟨F,hF,hcompact,hsym⟩

#print axioms jet_smooth
#print axioms jet_support
#print axioms jet_compact
#print axioms jet_derivative_u
#print axioms jet_derivative_v
#print axioms radius_spec
#print axioms bound_spec
#print axioms jet_outside
#print axioms cone_bound
#print axioms quadrant_tendsto
#print axioms smooth_compact_quadrant_tendsto
end
end UnifiedTheory.Audit.KFCausalBDG4DSmoothCompactSupplier
