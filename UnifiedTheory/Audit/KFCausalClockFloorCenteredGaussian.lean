/- Completion of the physical Gaussian square before taking absolute
values. The displacement amplitude and the real source cancel exactly.
This keeps the estimates centred at the translated packet. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorCenteredGaussian
noncomputable section

def weight (α β : ℝ) : Fin 5 → ℝ := ![α,α,α,α,β]
def quadratic (α β : ℝ) (v : Fin 5 → ℂ) : ℂ := ∑ i, (weight α β i:ℂ)*(v i)^2
def realQuadratic (α β : ℝ) (x : Fin 5 → ℝ) : ℝ := ∑ i, weight α β i*(x i)^2
def linear (R : Fin 5 → ℝ) (v : Fin 5 → ℂ) : ℂ := ∑ i, (R i:ℂ)*v i
def source (α β : ℝ) (Q R : Fin 5 → ℝ) (i : Fin 5) : ℂ :=
  2*(weight α β i:ℂ)*(Q i:ℂ)+Complex.I*(R i:ℂ)
def amplitude (α β : ℝ) (Q : Fin 5 → ℝ) : ℂ := Complex.exp (-(realQuadratic α β Q:ℂ))
def packet (α β : ℝ) (Q R : Fin 5 → ℝ) (v : Fin 5 → ℂ) : ℂ :=
  Complex.exp (-quadratic α β (fun i => v i-(Q i:ℂ))+Complex.I*linear R v)

theorem weight_nonnegative (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (i : Fin 5) :
    0 ≤ weight α β i := by fin_cases i <;> simp [weight] <;> assumption

theorem source_identity (α β : ℝ) (Q R : Fin 5 → ℝ) (v : Fin 5 → ℂ) :
    amplitude α β Q * Complex.exp (∑ i, source α β Q R i*v i) * Complex.exp (-quadratic α β v) =
      packet α β Q R v := by
  unfold amplitude packet
  rw [← Complex.exp_add,← Complex.exp_add]
  congr 1
  simp only [realQuadratic,quadratic,linear,source,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  push_cast
  ring

theorem packet_norm (α β : ℝ) (Q R : Fin 5 → ℝ) (v : Fin 5 → ℂ) :
    ‖packet α β Q R v‖ = Real.exp
      ((∑ i, weight α β i*((v i).im^2-((v i).re-Q i)^2)) - ∑ i, R i*(v i).im) := by
  rw [packet,Complex.norm_exp]
  congr 1
  simp [quadratic,linear,Fin.sum_univ_succ,pow_two,Complex.mul_re,Complex.mul_im]
  ring

theorem packet_recenter_norm (α β : ℝ) (Q R ξ δ : Fin 5 → ℝ) :
    ‖packet α β Q R (fun i => ((Q i+ξ i:ℝ):ℂ)+Complex.I*(δ i:ℂ))‖ =
      Real.exp (-realQuadratic α β ξ+realQuadratic α β δ-∑ i, R i*δ i) := by
  rw [packet_norm]
  congr 1
  simp [realQuadratic,Fin.sum_univ_succ,Complex.mul_re,Complex.mul_im]
  ring

theorem packet_real_recenter (α β σ : ℝ) (Q R x : Fin 5 → ℝ) :
    ‖packet α β Q R (fun i => ((Q i+σ*x i:ℝ):ℂ))‖ =
      Real.exp (-σ^2*realQuadratic α β x) := by
  rw [packet_norm]
  congr 1
  simp [realQuadratic,Fin.sum_univ_succ]
  ring

theorem packet_error_bound (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (Q R ξ : Fin 5 → ℝ) (e : Fin 5 → ℂ) :
    ‖packet α β Q R (fun i => ((Q i+ξ i:ℝ):ℂ)+e i)‖ ≤
      Real.exp ((∑ i, weight α β i*‖e i‖^2)+∑ i, |R i| * |(e i).im|) *
        Real.exp (-realQuadratic α β ξ/2) := by
  rw [packet_norm,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hb (i : Fin 5) :
      weight α β i*((e i).im^2-(ξ i+(e i).re)^2)-R i*(e i).im ≤
        weight α β i*‖e i‖^2+|R i| * |(e i).im|-weight α β i*(ξ i)^2/2 := by
    have hw := weight_nonnegative α β hα hβ i
    have hn : ‖e i‖^2 = (e i).re^2+(e i).im^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      ring
    have he := mul_nonneg hw (sq_nonneg (ξ i+2*(e i).re))
    have hp : -(R i*(e i).im) ≤ |R i| * |(e i).im| := by
      simpa only [abs_mul] using neg_le_abs (R i*(e i).im)
    rw [hn]
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hb i)
  simp only [Complex.add_im,Complex.ofReal_im,zero_add,Complex.add_re,Complex.ofReal_re]
  simp_rw [show ∀ i, Q i+ξ i+(e i).re-Q i = ξ i+(e i).re by intro i; ring]
  simpa only [realQuadratic,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_div,
    neg_div,sub_eq_add_neg,Finset.sum_neg_distrib] using hs

#print axioms weight_nonnegative
#print axioms source_identity
#print axioms packet_norm
#print axioms packet_recenter_norm
#print axioms packet_real_recenter
#print axioms packet_error_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorCenteredGaussian
