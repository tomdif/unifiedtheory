/- Quantitative finite-energy mass criteria for a nonzero Euclidean-time
limit. These are theorems about actual finite measures on nonnegative physical
energies; no Wilson spectral measure or uniform window mass is postulated as
already constructed. -/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Sequences

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ContinuumSpectralWindow
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

variable (μ : Measure ℝ≥0) [IsFiniteMeasure μ]

def laplace (t : ℝ) : ℝ := ∫ s : ℝ≥0, Real.exp (-t*(s : ℝ)) ∂μ

theorem laplace_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun s : ℝ≥0 => Real.exp (-t*(s : ℝ))) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).aestronglyMeasurable
  apply Eventually.of_forall
  intro s
  change ‖Real.exp (-t*(s : ℝ))‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) s.coe_nonneg)

theorem laplace_nonneg (t : ℝ) : 0 ≤ laplace μ t :=
  integral_nonneg (fun _ => (Real.exp_pos _).le)

/-- Low physical-energy mass survives at every fixed nonnegative time. -/
theorem window_lower (t : ℝ) (ht : 0 ≤ t) (R : ℝ≥0) :
    μ.real (Set.Iic R)*Real.exp (-t*(R : ℝ)) ≤ laplace μ t := by
  have hi := laplace_integrable μ t ht
  calc
    _ = ∫ _s in Set.Iic R, Real.exp (-t*(R : ℝ)) ∂μ := by simp
    _ ≤ ∫ s in Set.Iic R, Real.exp (-t*(s : ℝ)) ∂μ := by
      apply setIntegral_mono_on (integrableOn_const) hi.integrableOn measurableSet_Iic
      intro s hs
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (by exact_mod_cast hs : (s : ℝ) ≤ R) (by linarith)
    _ ≤ laplace μ t := setIntegral_le_integral hi (Eventually.of_forall (fun _ => (Real.exp_pos _).le))

/-- The high-energy contribution is exponentially suppressed. This upper
bound exposes how all the norm can escape to infinite physical energy. -/
theorem window_upper (t : ℝ) (ht : 0 ≤ t) (R : ℝ≥0) :
    laplace μ t ≤ μ.real (Set.Iic R)+μ.real Set.univ*Real.exp (-t*(R : ℝ)) := by
  let indicator := (Set.Iic R).indicator (fun _ : ℝ≥0 => (1 : ℝ))
  have hi : Integrable indicator μ := (integrable_const _).indicator measurableSet_Iic
  have hc : Integrable (fun _ : ℝ≥0 => Real.exp (-t*(R : ℝ))) μ := integrable_const _
  have hb (s : ℝ≥0) : Real.exp (-t*(s : ℝ)) ≤ indicator s+Real.exp (-t*(R : ℝ)) := by
    by_cases hs : s ≤ R
    · have he : Real.exp (-t*(s : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) s.coe_nonneg)
      simp only [indicator, Set.indicator_of_mem (show s ∈ Set.Iic R from hs)]
      linarith [Real.exp_pos (-t*(R : ℝ))]
    · have hsr : (R : ℝ) ≤ s := by exact_mod_cast (le_of_lt (lt_of_not_ge hs))
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsr (by linarith : -t ≤ 0))
      simpa only [indicator, Set.indicator_of_notMem (show s ∉ Set.Iic R from hs), zero_add] using he
  calc
    _ ≤ ∫ s, indicator s+Real.exp (-t*(R : ℝ)) ∂μ :=
      integral_mono (laplace_integrable μ t ht) (hi.add hc) hb
    _ = _ := by rw [integral_add hi hc]; simp [indicator, integral_indicator, measurableSet_Iic]

theorem positive_signal_forces_window (t : ℝ) (ht : 0 ≤ t) (R : ℝ≥0)
    (c M : ℝ) (hmass : μ.real Set.univ ≤ M) (hsignal : c ≤ laplace μ t)
    (htail : M*Real.exp (-t*(R : ℝ)) ≤ c/2) : c/2 ≤ μ.real (Set.Iic R) := by
  have hu := window_upper μ t ht R
  have hm := mul_le_mul_of_nonneg_right hmass (Real.exp_pos (-t*(R : ℝ))).le
  linarith

/-- An actual positive uniform window yields a positive scalar subsequential
limit. No positive limit is supplied as a hypothesis. -/
theorem window_limit_positive {ι : Type*} {l : Filter ι} [NeBot l]
    (ν : ι → Measure ℝ≥0) [∀ k, IsFiniteMeasure (ν k)]
    (t : ℝ) (ht : 0 ≤ t) (R : ℝ≥0) (c : ℝ) (hc : 0 < c)
    (hwindow : ∀ᶠ k in l, c ≤ (ν k).real (Set.Iic R))
    (q : ℝ) (hq : Tendsto (fun k => laplace (ν k) t) l (𝓝 q)) :
    0 < q ∧ c*Real.exp (-t*(R : ℝ)) ≤ q := by
  have hf : ∀ᶠ k in l, c*Real.exp (-t*(R : ℝ)) ≤ laplace (ν k) t := by
    filter_upwards [hwindow] with k hk
    exact (mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le).trans (window_lower (ν k) t ht R)
  have hh := ge_of_tendsto hq hf
  exact ⟨(mul_pos hc (Real.exp_pos _)).trans_le hh,hh⟩

/-- A fixed-rate transfer model can have unit norm and strictly positive
correlations at every cutoff while all fixed positive-time limits vanish. -/
def escapingMeasure (n : ℕ) : Measure ℝ≥0 := Measure.dirac (n+1 : ℝ≥0)

instance escaping_probability (n : ℕ) : IsProbabilityMeasure (escapingMeasure n) := by
  unfold escapingMeasure
  infer_instance

theorem escaping_laplace (n : ℕ) (t : ℝ) :
    laplace (escapingMeasure n) t = Real.exp (-t*((n : ℝ)+1)) := by
  simp [laplace, escapingMeasure]

theorem escaping_zero_time (n : ℕ) : laplace (escapingMeasure n) 0 = 1 := by
  simp [escaping_laplace]

theorem escaping_positive (n : ℕ) (t : ℝ) : 0 < laplace (escapingMeasure n) t := by
  rw [escaping_laplace]
  exact Real.exp_pos _

theorem escaping_tendsto_zero (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n => laplace (escapingMeasure n) t) atTop (𝓝 0) := by
  simp_rw [escaping_laplace]
  apply Real.tendsto_exp_atBot.comp
  have hp : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.const_mul_atTop_of_neg (by linarith : -t < 0) hp


theorem laplace_le_mass (t : ℝ) (ht : 0 ≤ t) : laplace μ t ≤ μ.real Set.univ := by
  calc
    _ ≤ ∫ _s : ℝ≥0, (1 : ℝ) ∂μ := by
      apply integral_mono (laplace_integrable μ t ht) (integrable_const _)
      intro s
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) s.coe_nonneg)
    _ = _ := by simp

/-- Constructs a nonzero scalar subsequential limit from bounded total mass
and a uniform finite-energy window. Convergence is a conclusion here. -/
theorem exists_positive_subsequence (ν : ℕ → Measure ℝ≥0)
    [∀ k, IsFiniteMeasure (ν k)] (t : ℝ) (ht : 0 ≤ t) (R : ℝ≥0)
    (c M : ℝ) (hc : 0 < c) (hmass : ∀ k, (ν k).real Set.univ ≤ M)
    (hwindow : ∀ k, c ≤ (ν k).real (Set.Iic R)) :
    ∃ q : ℝ, 0 < q ∧ c*Real.exp (-t*(R : ℝ)) ≤ q ∧ q ≤ M ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        Tendsto (fun k => laplace (ν (phi k)) t) atTop (𝓝 q) := by
  have hb (k : ℕ) : laplace (ν k) t ∈ Set.Icc (c*Real.exp (-t*(R : ℝ))) M := by
    exact ⟨(mul_le_mul_of_nonneg_right (hwindow k) (Real.exp_pos _).le).trans
      (window_lower (ν k) t ht R), (laplace_le_mass (ν k) t ht).trans (hmass k)⟩
  obtain ⟨q,hq,phi,hphi,hl⟩ := isCompact_Icc.tendsto_subseq hb
  exact ⟨q,(mul_pos hc (Real.exp_pos _)).trans_le hq.1,hq.1,hq.2,phi,hphi,hl⟩

/-- Positive fixed-time limits with bounded total mass necessarily retain
mass in one bounded physical-energy window. Strict positivity at each cutoff
alone is insufficient. -/
theorem positive_limit_forces_window {ι : Type*} {l : Filter ι}
    (ν : ι → Measure ℝ≥0) [∀ k, IsFiniteMeasure (ν k)]
    (t M q : ℝ) (ht : 0 < t) (hq : 0 < q)
    (hmass : ∀ k, (ν k).real Set.univ ≤ M)
    (hlimit : Tendsto (fun k => laplace (ν k) t) l (𝓝 q)) :
    ∃ R : ℝ≥0, ∀ᶠ k in l, q/4 ≤ (ν k).real (Set.Iic R) := by
  have hexp : Tendsto (fun n : ℕ => M*Real.exp (-t*((n : ℝ)+1))) atTop (𝓝 0) := by
    simpa only [escaping_laplace, mul_zero] using (escaping_tendsto_zero t ht).const_mul M
  obtain ⟨n,hn⟩ := (hexp.eventually (gt_mem_nhds (by positivity : 0 < q/4))).exists
  refine ⟨(n+1 : ℝ≥0), ?_⟩
  filter_upwards [hlimit.eventually (lt_mem_nhds (by linarith : q/2 < q))] with k hk
  have hh := positive_signal_forces_window (ν k) t ht.le (n+1 : ℝ≥0) (q/2) M
    (hmass k) hk.le (by
      simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
      linarith)
  linarith

/-- Escape of all bounded physical-energy windows forces collapse at every
positive physical time, even though total norm may stay bounded away from zero. -/
theorem escape_forces_zero {ι : Type*} {l : Filter ι}
    (ν : ι → Measure ℝ≥0) [∀ k, IsFiniteMeasure (ν k)]
    (t M : ℝ) (ht : 0 < t) (hmass : ∀ k, (ν k).real Set.univ ≤ M)
    (hescape : ∀ R : ℝ≥0, Tendsto (fun k => (ν k).real (Set.Iic R)) l (𝓝 0)) :
    Tendsto (fun k => laplace (ν k) t) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun k => hb.trans_le (laplace_nonneg (ν k) t))
  · intro b hb
    have hexp : Tendsto (fun n : ℕ => M*Real.exp (-t*((n : ℝ)+1))) atTop (𝓝 0) := by
      simpa only [escaping_laplace, mul_zero] using (escaping_tendsto_zero t ht).const_mul M
    obtain ⟨n,hn⟩ := (hexp.eventually (gt_mem_nhds (half_pos hb))).exists
    let R : ℝ≥0 := n+1
    have htail : M*Real.exp (-t*(R : ℝ)) < b/2 := by
      simpa only [R, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using hn
    filter_upwards [(hescape R).eventually (gt_mem_nhds (half_pos hb))] with k hk
    have hu := window_upper (ν k) t ht.le R
    have hm := mul_le_mul_of_nonneg_right (hmass k) (Real.exp_pos (-t*(R : ℝ))).le
    linarith

/-- A gap in the whole spectral support gives exponential decay. A lower
window mass alone, which may include zero energy, does not give this premise. -/
theorem gapped_upper (t : ℝ) (ht : 0 ≤ t) (m : ℝ≥0)
    (hgap : ∀ᵐ s ∂μ, m ≤ s) :
    laplace μ t ≤ μ.real Set.univ*Real.exp (-t*(m : ℝ)) := by
  calc
    _ ≤ ∫ _s : ℝ≥0, Real.exp (-t*(m : ℝ)) ∂μ := by
      apply integral_mono_ae (laplace_integrable μ t ht) (integrable_const _)
      filter_upwards [hgap] with s hs
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (by exact_mod_cast hs : (m : ℝ) ≤ s) (neg_nonpos.mpr ht)
    _ = _ := by simp

end
end UnifiedTheory.Clay.YangMills.ContinuumSpectralWindow
