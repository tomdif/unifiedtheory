/- Joint continuity of genuine external Schwartz products and reflected
configuration tensors. The proof uses the established weighted derivative
product estimates, not a separate-continuity shortcut. -/
import UnifiedTheory.Clay.YangMills.WilsonReflectedTensor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SchwartzTensorContinuity
noncomputable section
open Filter SchwartzProductTensor
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem control_continuous (k n : ℕ) : Continuous (control (E := E) k n) := by
  apply Seminorm.continuous_of_le (p := control k n)
    (q := ∑ i ∈ Finset.Iic (k,n), schwartzSeminormFamily ℂ E ℂ i) _
    (Seminorm.finset_sup_le_sum _ _)
  change Continuous (fun f => Seminorm.coeFnAddMonoidHom ℂ (SchwartzMap E ℂ)
    (∑ i ∈ Finset.Iic (k,n), schwartzSeminormFamily ℂ E ℂ i) f)
  simp_rw [map_sum, Finset.sum_apply]
  exact continuous_finset_sum _ (fun i _ =>
    (schwartz_withSeminorms ℂ E ℂ).continuous_seminorm i)

theorem product_seminorm_bound (f : SchwartzMap E ℂ) (g : SchwartzMap F ℂ) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (tensor f g) ≤
      (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)) *
        (2^k * control k n f) * (2^k * control k n g) :=
  SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity)
    (weighted_derivative_bound f g k n)

/-- Both factors may vary, in an arbitrary filter. -/
theorem product_tendsto {ι : Type*} {l : Filter ι}
    (u : ι → SchwartzMap E ℂ) (v : ι → SchwartzMap F ℂ)
    (f : SchwartzMap E ℂ) (g : SchwartzMap F ℂ)
    (hu : Tendsto u l (𝓝 f)) (hv : Tendsto v l (𝓝 g)) :
    Tendsto (fun r => tensor (u r) (v r)) l (𝓝 (tensor f g)) := by
  apply ((schwartz_withSeminorms ℂ (E × F) ℂ).tendsto_nhds _ (tensor f g)).mpr
  rintro ⟨k,n⟩ eps heps
  let C : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)
  have hud : Tendsto (fun r => control k n (u r-f)) l (𝓝 0) := by
    simpa only [map_zero] using (control_continuous k n).continuousAt.tendsto.comp
      (show Tendsto (fun r => u r-f) l (𝓝 0) by simpa using hu.sub_const f)
  have hvd : Tendsto (fun r => control k n (v r-g)) l (𝓝 0) := by
    simpa only [map_zero] using (control_continuous k n).continuousAt.tendsto.comp
      (show Tendsto (fun r => v r-g) l (𝓝 0) by simpa using hv.sub_const g)
  have hvc := (control_continuous k n).continuousAt.tendsto.comp hv
  have ht : Tendsto (fun r =>
      C * (2^k * control k n (u r-f)) * (2^k * control k n (v r)) +
      C * (2^k * control k n f) * (2^k * control k n (v r-g))) l (𝓝 0) := by
    simpa only [mul_zero, zero_mul, add_zero] using
      ((hud.const_mul (2^k)).const_mul C |>.mul (hvc.const_mul (2^k))).add
        ((hvd.const_mul (2^k)).const_mul (C * (2^k * control k n f)))
  filter_upwards [ht.eventually (gt_mem_nhds heps)] with r hr
  have hd : tensor (u r) (v r) - tensor f g =
      tensor (u r-f) (v r) + tensor f (v r-g) := by
    ext x
    simp only [SchwartzMap.sub_apply, SchwartzMap.add_apply, tensor_apply]
    ring
  apply lt_of_le_of_lt _ hr
  rw [hd]
  exact (map_add_le_add (SchwartzMap.seminorm ℂ k n) _ _).trans
    (add_le_add (product_seminorm_bound (u r-f) (v r) k n)
      (product_seminorm_bound f (v r-g) k n))

open ContinuumControl PeriodicLattice4

theorem configuration_tensor_tendsto {ι : Type*} {l : Filter ι} (m n : ℕ)
    (u : ι → CorrelationTest m) (v : ι → CorrelationTest n)
    (f : CorrelationTest m) (g : CorrelationTest n)
    (hu : Tendsto u l (𝓝 f)) (hv : Tendsto v l (𝓝 g)) :
    Tendsto (fun r => SchwartzConfigurationTensor.tensor m n (u r) (v r)) l
      (𝓝 (SchwartzConfigurationTensor.tensor m n f g)) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (SchwartzConfigurationTensor.split m n)).continuous
    |>.continuousAt.tendsto.comp (product_tendsto u v f g hu hv)

theorem reflected_tensor_tendsto {ι : Type*} {l : Filter ι} (m n : ℕ)
    (a : ℝ) (plane : Plane) (u : ι → CorrelationTest m) (v : ι → CorrelationTest n)
    (f : CorrelationTest m) (g : CorrelationTest n)
    (hu : Tendsto u l (𝓝 f)) (hv : Tendsto v l (𝓝 g)) :
    Tendsto (fun r => WilsonReflectedTensor.reflectedTensor m n a plane (u r) (v r)) l
      (𝓝 (WilsonReflectedTensor.reflectedTensor m n a plane f g)) := by
  apply configuration_tensor_tendsto
  · exact (SchwartzConfigurationConjugation.conjugation_continuous m).continuousAt.tendsto.comp
      ((AffineCellReflection.reflectionPullback m a plane).continuous.continuousAt.tendsto.comp hu)
  · exact hv

end
end UnifiedTheory.Clay.YangMills.SchwartzTensorContinuity
