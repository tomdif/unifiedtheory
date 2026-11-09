/- The exact dual trial Gaussian lies in the full static multiplier
domain. All transverse polynomial moments and the full clock moment
are derived; inverse clock multiplication is bounded by the positive
clock floor. No operator-domain or graph-core premise is used. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticOperator
import UnifiedTheory.Audit.KFCausalClockFloorDualGaussian
import UnifiedTheory.Audit.KFCausalGaussianClockSquare

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticOperatorGaussianWeight
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalClockFloorDualGaussian (widths widths_positive fourierTransverse weight)
open KFCausalGaussianSliceDomain (gaussian gaussian_continuous gaussian_memLp_iff)
open KFCausalChargeGaussianProducts (block_product_memLp)
open KFCausalClockFloorInvariantTrial (clockFunction clockFunction_continuous clockFunction_memLp)
open KFCausalClockFloorStaticMultiplierForm (symbol symbol_coordinates)

theorem transverse_coordinate_memLp (h : ℝ) (hh : h ≠ 0) (i : Fin 5) (n : ℕ) :
    MemLp (fun x : Block 5 => (x i:ℂ)^n*fourierTransverse h x) 2 := by
  let g : Fin 5 → ℝ → ℂ := fun j t =>
    (Real.sqrt (Real.pi/widths h j):ℂ)*gaussian (Real.pi^2/widths h j:ℝ) t
  let f : Fin 5 → ℝ → ℂ := fun j t => (if j=i then (t:ℂ)^n else 1)*g j t
  have hb (j : Fin 5) : 0 < Real.pi^2/widths h j := div_pos (sq_pos_of_pos Real.pi_pos) (widths_positive h hh j)
  have hc (j : Fin 5) : Continuous (f j) := by
    by_cases hj : j=i
    · simp only [f,hj,if_true,g]
      exact (Complex.continuous_ofReal.pow n).mul (continuous_const.mul (gaussian_continuous _))
    · simpa only [f,hj,if_false,one_mul,g] using (continuous_const.mul (gaussian_continuous
        ((Real.pi^2/widths h j:ℝ):ℂ)) : Continuous (fun t => (Real.sqrt (Real.pi/widths h j):ℂ)*gaussian ((Real.pi^2/widths h j:ℝ):ℂ) t))
  have hm (j : Fin 5) : MemLp (f j) 2 := by
    by_cases hj : j=i
    · have ht := (KFCausalGaussianQuadraticFourier.moment_memLp _ (hb j) n).const_mul
        (Real.sqrt (Real.pi/widths h j):ℂ)
      simpa only [f,hj,if_true,g,KFCausalGaussianQuadraticFourier.moment,mul_left_comm,mul_assoc] using ht
    · simpa only [f,hj,if_false,one_mul,g] using
        ((gaussian_memLp_iff ((Real.pi^2/widths h j:ℝ):ℂ)).mpr (hb j)).const_mul
          (Real.sqrt (Real.pi/widths h j):ℂ)
  have he : (fun x : Block 5 => (x i:ℂ)^n*fourierTransverse h x) =
      fun x => ∏ j, f j (x j) := by
    funext x
    simp only [f,Finset.prod_mul_distrib,fourierTransverse,g]
    simp
  rw [he]
  exact block_product_memLp 5 f hc hm

private theorem transverse_memLp (h : ℝ) (hh : h ≠ 0) : MemLp (fourierTransverse h) 2 := by
  simpa only [pow_zero,one_mul] using transverse_coordinate_memLp h hh 0 0

private theorem clock_block_memLp (h : ℝ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2) :
    MemLp (fun x : Block 1 => ((Real.pi/KFCausalChargeGaussianGeometry.groundWidth h:ℝ):ℂ)*g (x 0)) 2 := by
  have hm := block_product_memLp 1 (fun _ => g) (fun _ => hc) (fun _ => hg)
  simpa only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one] using
    hm.const_mul ((Real.pi/KFCausalChargeGaussianGeometry.groundWidth h:ℝ):ℂ)

private theorem clock_memLp (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    MemLp (KFCausalClockFloorDualGaussian.clock ε a h) 2 :=
  clock_block_memLp h (clockFunction ε a) (clockFunction_continuous ε a)
    (clockFunction_memLp ε a hε ha)

private theorem joint_product_memLp (f : Block 5 → ℂ) (g : Block 1 → ℂ)
    (hf : MemLp f 2) (hg : MemLp g 2) :
    MemLp (fun x : Joint 5 1 => f (split 5 1 x).1*g (split 5 1 x).2) 2 :=
  (KFCausalL2TensorEmbedding.product_memLp volume volume f g hf hg).comp_measurePreserving
    (split_preserves_volume 5 1)

theorem coordinate_weight_memLp (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (i : Fin 5) (n : ℕ) :
    MemLp (fun x : Joint 5 1 => (x (.inl i):ℂ)^n*weight ε a h x) 2 := by
  have hm := joint_product_memLp _ _ (transverse_coordinate_memLp h hh i n) (clock_memLp ε a h hε ha)
  simpa only [weight,split_fst,mul_assoc] using hm

theorem clock_weight_memLp (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) :
    MemLp (fun x : Joint 5 1 => (KFCausalClockFloorFlow.clock ε (x (.inr 0)):ℂ)*weight ε a h x) 2 := by
  have hc : Continuous (KFCausalGaussianClockSquare.fullClockFunction ε a) := by
    unfold KFCausalGaussianClockSquare.fullClockFunction
    exact (by fun_prop : Continuous (fun s : ℝ => ((Real.exp s+ε:ℝ):ℂ))).mul (clockFunction_continuous ε a)
  have hm := joint_product_memLp _ _ (transverse_memLp h hh)
    (clock_block_memLp h _ hc (KFCausalGaussianClockSquare.fullClockFunction_memLp ε a hε ha))
  convert hm using 1
  funext x
  simp only [weight,KFCausalClockFloorDualGaussian.clock,
    KFCausalGaussianClockSquare.fullClockFunction,KFCausalClockFloorFlow.clock,split_snd]
  push_cast
  ring

private theorem inverse_clock_memLp (ε : ℝ) (hε : 0 < ε) (f : Joint 5 1 → ℂ) (hf : MemLp f 2) :
    MemLp (fun x => ((KFCausalClockFloorFlow.clock ε (x (.inr 0)))⁻¹:ℝ)*f x) 2 := by
  have hp (x : Joint 5 1) : 0 < KFCausalClockFloorFlow.clock ε (x (.inr 0)) := by
    unfold KFCausalClockFloorFlow.clock; positivity
  have hc : Continuous (fun x : Joint 5 1 => ((KFCausalClockFloorFlow.clock ε (x (.inr 0)))⁻¹:ℝ)) := by
    apply Continuous.inv₀ (by unfold KFCausalClockFloorFlow.clock; fun_prop)
    intro x; exact (hp x).ne'
  apply (hf.const_mul ((ε⁻¹:ℝ):ℂ)).of_le ((Complex.continuous_ofReal.comp hc).aestronglyMeasurable.mul hf.1)
  filter_upwards [] with x
  change ‖(((KFCausalClockFloorFlow.clock ε (x (.inr 0)))⁻¹:ℝ):ℂ)*f x‖ ≤ ‖((ε⁻¹:ℝ):ℂ)*f x‖
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (hp x)),abs_of_pos (inv_pos.mpr hε)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact inv_le_inv₀ (hp x) hε |>.mpr (by unfold KFCausalClockFloorFlow.clock; linarith [Real.exp_pos (x (.inr 0))])

theorem symbol_weight_memLp (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) :
    MemLp (fun x => (symbol ε h x:ℂ)*weight ε a h x) 2 := by
  let c := KFCausalNormalizedChargeFlow.momentumScale h
  let q : Joint 5 1 → ℂ := fun x =>
    ((c^2*(x (.inl 2)^2+x (.inl 3)^2+x (.inl 4)^2)+x (.inl 0)^2+x (.inl 1)^2:ℝ):ℂ)*weight ε a h x
  have hm (i : Fin 5) := coordinate_weight_memLp ε a h hε ha hh i 2
  have hq : MemLp q 2 := by
    convert (((((hm 2).add (hm 3)).add (hm 4)).const_mul ((c^2:ℝ):ℂ)).add (hm 0)).add (hm 1) using 1
    funext x
    dsimp only [q,Pi.add_apply]
    push_cast
    ring
  have hz := (clock_weight_memLp ε a h hε ha hh).add (inverse_clock_memLp ε hε q hq)
  convert hz.const_mul ((1/2:ℝ):ℂ) using 1
  funext x
  rw [symbol_coordinates]
  dsimp only [q,c,Pi.add_apply]
  push_cast
  ring

#print axioms transverse_coordinate_memLp
#print axioms coordinate_weight_memLp
#print axioms clock_weight_memLp
#print axioms symbol_weight_memLp
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticOperatorGaussianWeight
