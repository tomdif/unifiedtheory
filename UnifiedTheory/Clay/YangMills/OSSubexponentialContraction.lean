/- Exponential damping removes the uniform bounded-orbit assumption from
the OS doubling argument. Subexponential growth is enough for contraction;
the actual Schwartz-kernel application supplies that growth separately. -/
import UnifiedTheory.Clay.YangMills.OSBoundedOrbitContraction
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Instances.NNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSSubexponentialContraction
noncomputable section
open Filter
open scoped Topology NNReal

/-- Damping a nonnegative doubling function and then letting the damping
vanish proves the undamped bound. No contraction is supplied as a premise. -/
theorem subexponential_doubling (f : ℝ≥0 → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hf : ∀ t, 0 ≤ f t) (hd : ∀ t, f t ^ 2 ≤ r * f (t + t))
    (hg : ∀ eps : ℝ, 0 < eps →
      Tendsto (fun t : ℝ≥0 => Real.exp (-eps*(t:ℝ)) * f t) atTop (𝓝 0)) :
    ∀ t, f t ≤ r := by
  intro t
  by_cases ht : t = 0
  · subst t
    have h := hd 0
    simp only [add_zero] at h
    nlinarith [hf 0]
  have htpos : 0 < t := pos_iff_ne_zero.mpr ht
  have htimes : Tendsto (fun n : ℕ => (n : ℝ≥0)*t) atTop atTop := by
    apply NNReal.tendsto_coe_atTop.mp
    simp only [NNReal.coe_mul, NNReal.coe_natCast]
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).atTop_mul_const
      (by exact_mod_cast htpos)
  have heps (eps : ℝ) (heps : 0 < eps) : Real.exp (-eps*(t:ℝ)) * f t ≤ r := by
    let g : ℕ → ℝ := fun n => Real.exp (-eps*((n:ℝ≥0)*t:ℝ)) * f ((n:ℝ≥0)*t)
    have hb : BddAbove (Set.range g) := ((hg eps heps).comp htimes).bddAbove_range
    have hn (n : ℕ) : 0 ≤ g n := mul_nonneg (Real.exp_pos _).le (hf _)
    have hh (n : ℕ) : g n ^ 2 ≤ r * g (2*n) := by
      have htime : ((2*n : ℕ) : ℝ≥0)*t = (n:ℝ≥0)*t + (n:ℝ≥0)*t := by
        push_cast
        ring
      have he : Real.exp (-eps*↑((n:ℝ≥0)*t))^2 =
          Real.exp (-eps*↑((n:ℝ≥0)*t+(n:ℝ≥0)*t)) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        push_cast
        ring
      change (Real.exp (-eps*↑((n:ℝ≥0)*t)) * f ((n:ℝ≥0)*t))^2 ≤
        r * (Real.exp (-eps*↑(((2*n:ℕ):ℝ≥0)*t)) * f (((2*n:ℕ):ℝ≥0)*t))
      rw [mul_pow, he, htime]
      calc
        _ ≤ Real.exp (-eps*↑((n:ℝ≥0)*t+(n:ℝ≥0)*t)) *
            (r*f ((n:ℝ≥0)*t+(n:ℝ≥0)*t)) :=
          mul_le_mul_of_nonneg_left (hd _) (Real.exp_pos _).le
        _ = _ := by ring
    simpa [g] using
      OSBoundedOrbitContraction.bounded_doubling g (fun n => 2*n) r hr hn hb hh 1
  have hc : Tendsto (fun eps : ℝ => Real.exp (-eps*(t:ℝ))*f t)
      (𝓝[>] 0) (𝓝 (f t)) := by
    have hh : Continuous (fun eps : ℝ => Real.exp (-eps*(t:ℝ))*f t) :=
      (Real.continuous_exp.comp (continuous_neg.mul continuous_const)).mul continuous_const
    simpa using (hh.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hc
  filter_upwards [self_mem_nhdsWithin] with eps he
  exact heps eps he

end
end UnifiedTheory.Clay.YangMills.OSSubexponentialContraction
