/- Strong approximation to the identity by F(F+bI)^(-1), derived from
contractivity of I-F and density of the range of F. -/
import UnifiedTheory.Audit.KFCausalContractiveResidualResolvent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalResidualResolventApproximation
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalInvariantRangeCore (residual)
open UnifiedTheory.Audit.KFCausalContractiveResidualResolvent
variable {V W E ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

def smoothing (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖) (b : ℝ) (hb : 0 < b) :
    V →L[ℂ] V := ContinuousLinearMap.id ℂ V-(b:ℂ) • resolvent F hF b hb

theorem scaled_resolvent_norm (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (b : ℝ) (hb : 0 < b) (x : V) : ‖(b:ℂ) • resolvent F hF b hb x‖ ≤ ‖x‖ := by
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb]
  simpa only [equation] using lower_bound F hF b hb (resolvent F hF b hb x)

theorem smoothing_norm (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (b : ℝ) (hb : 0 < b) (x : V) : ‖smoothing F hF b hb x‖ ≤ 2*‖x‖ := by
  change ‖x-(b:ℂ) • resolvent F hF b hb x‖ ≤ _
  exact (norm_sub_le _ _).trans (by linarith [scaled_resolvent_norm F hF b hb x])

theorem smoothing_factor (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (b : ℝ) (hb : 0 < b) (x : V) : F (resolvent F hF b hb x) = smoothing F hF b hb x :=
  eq_sub_of_add_eq (equation F hF b hb x)

theorem smoothing_reverse (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (b : ℝ) (hb : 0 < b) (x : V) : resolvent F hF b hb (F x) = smoothing F hF b hb x := by
  have he := reverse_equation F hF b hb x
  rw [map_add,map_smul] at he
  exact eq_sub_of_add_eq he

theorem smoothing_intertwine (J : V →L[ℂ] W) (F : V →L[ℂ] V) (D : W →L[ℂ] W)
    (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖) (hD : ∀ x, ‖residual D x‖ ≤ ‖x‖)
    (hJ : ∀ x, J (F x) = D (J x)) (b : ℝ) (hb : 0 < b) (x : V) :
    J (smoothing F hF b hb x) = smoothing D hD b hb (J x) := by
  change J (x-(b:ℂ) • resolvent F hF b hb x) = J x-(b:ℂ) • resolvent D hD b hb (J x)
  rw [map_sub,map_smul,intertwine J F D hF hD hJ]

omit [CompleteSpace V] in
theorem dense_contraction_limit (J : E → V) (hJ : DenseRange J) (T : ι → V →L[ℂ] V)
    (hT : ∀ i x, ‖T i x‖ ≤ ‖x‖) (l : Filter ι)
    (hc : ∀ w, Tendsto (fun i => T i (J w)) l (𝓝 0)) (x : V) :
    Tendsto (fun i => T i x) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨w,hw⟩ := hJ.exists_dist_lt x (show 0 < δ/2 from by positivity)
  have hl := Metric.tendsto_nhds.mp (hc w) (δ/2) (by positivity)
  filter_upwards [hl] with i hi
  have hd : dist (T i x) (T i (J w)) ≤ dist x (J w) := by
    simpa only [dist_eq_norm,map_sub] using hT i (x-J w)
  have ht := dist_triangle (T i x) (T i (J w)) 0
  linarith

theorem scaled_resolvent_tendsto_zero (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (hdense : DenseRange F) (b : ι → ℝ) (hb : ∀ i, 0 < b i) (l : Filter ι)
    (hzero : Tendsto b l (𝓝 0)) (x : V) :
    Tendsto (fun i => (b i:ℂ) • resolvent F hF (b i) (hb i) x) l (𝓝 0) := by
  apply dense_contraction_limit F hdense (fun i => (b i:ℂ) • resolvent F hF (b i) (hb i))
    (fun i y => scaled_resolvent_norm F hF (b i) (hb i) y) l _ x
  intro w
  apply squeeze_zero_norm (a := fun i => b i*(2*‖w‖))
  · intro i
    rw [ContinuousLinearMap.smul_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (hb i),smoothing_reverse]
    exact mul_le_mul_of_nonneg_left (smoothing_norm F hF (b i) (hb i) w) (hb i).le
  · simpa only [zero_mul] using hzero.mul_const (2*‖w‖)

theorem smoothing_tendsto (F : V →L[ℂ] V) (hF : ∀ x, ‖residual F x‖ ≤ ‖x‖)
    (hdense : DenseRange F) (b : ι → ℝ) (hb : ∀ i, 0 < b i) (l : Filter ι)
    (hzero : Tendsto b l (𝓝 0)) (x : V) :
    Tendsto (fun i => smoothing F hF (b i) (hb i) x) l (𝓝 x) := by
  simpa only [sub_zero] using tendsto_const_nhds.sub (scaled_resolvent_tendsto_zero F hF hdense b hb l hzero x)

#print axioms scaled_resolvent_norm
#print axioms smoothing_norm
#print axioms smoothing_factor
#print axioms smoothing_reverse
#print axioms smoothing_intertwine
#print axioms dense_contraction_limit
#print axioms scaled_resolvent_tendsto_zero
#print axioms smoothing_tendsto
end
end UnifiedTheory.Audit.KFCausalResidualResolventApproximation
