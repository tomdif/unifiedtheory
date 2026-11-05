/- Actual even-step physical-time mesh and its vanishing-spacing limit.
Combined with TransferEnergySurvival this converts an O(a) Dirichlet bound
into a positive limiting signal. The Wilson-specific energy bound remains open. -/
import UnifiedTheory.Clay.YangMills.TransferEnergySurvival
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.MetricSpace.Sequences

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PhysicalTimeMesh
noncomputable section
open Filter TransferEnergySurvival
open scoped Topology

def steps (a tau : ℝ) : ℕ := ⌊tau/(2*a)⌋₊
def time (a tau : ℝ) : ℝ := 2*(steps a tau : ℝ)*a

theorem time_le (a tau : ℝ) (ha : 0 < a) (htau : 0 ≤ tau) : time a tau ≤ tau := by
  have h := (le_div_iff₀ (by positivity : 0 < 2*a)).mp
    (Nat.floor_le (show 0 ≤ tau/(2*a) by positivity))
  unfold time steps
  nlinarith

theorem time_lower (a tau : ℝ) (ha : 0 < a) : tau-2*a < time a tau := by
  have h := (div_lt_iff₀ (by positivity : 0 < 2*a)).mp (Nat.lt_floor_add_one (tau/(2*a)))
  unfold time steps
  nlinarith

theorem time_tendsto {ι : Type*} {l : Filter ι} (a : ι → ℝ)
    (ha : ∀ᶠ k in l, 0 < a k) (ha0 : Tendsto a l (𝓝 0)) (tau : ℝ) (htau : 0 ≤ tau) :
    Tendsto (fun k => time (a k) tau) l (𝓝 tau) := by
  have hlo : Tendsto (fun k => tau-2*a k) l (𝓝 tau) := by
    simpa using tendsto_const_nhds.sub (ha0.const_mul 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    (ha.mono (fun k hk => (time_lower (a k) tau hk).le))
    (ha.mono (fun k hk => time_le (a k) tau hk htau))

theorem steps_tendsto {ι : Type*} {l : Filter ι} (a : ι → ℝ)
    (ha : ∀ᶠ k in l, 0 < a k) (ha0 : Tendsto a l (𝓝 0)) (tau : ℝ) (htau : 0 < tau) :
    Tendsto (fun k => steps (a k) tau) l atTop := by
  apply tendsto_atTop.2
  intro b
  have hc : 0 < tau/(2*((b : ℝ)+1)) := by positivity
  filter_upwards [ha,ha0.eventually (gt_mem_nhds hc)] with k hk hsmall
  apply Nat.le_floor
  have hb : (b : ℝ) < tau/(2*a k) := by
    apply (lt_div_iff₀ (by positivity : 0 < 2*a k)).mpr
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*((b : ℝ)+1))).mp hsmall
    nlinarith
  exact hb.le

/-- The Hilbert spaces and transfer operators may depend on the cutoff.
Their physical identity and the energy estimate are explicit hypotheses. -/
theorem positive_limit {ι : Type*} {l : Filter ι} [NeBot l]
    (E : ι → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℂ (E k)]
    (T : (k : ι) → E k →L[ℂ] E k) (w : (k : ι) → E k)
    (hs : ∀ k x y, inner ℂ (T k x) y = inner ℂ x (T k y))
    (a : ι → ℝ) (ha : ∀ᶠ k in l, 0 < a k)
    (C tau c : ℝ) (hC : 0 ≤ C) (htau : 0 < tau) (hc : 0 < c) (hsmall : C*tau ≤ 1/2)
    (henergy : ∀ᶠ k in l, dirichlet (T k) (w k) ≤ C*a k*‖w k‖^2)
    (hnorm : ∀ᶠ k in l, c ≤ ‖w k‖^2) (q : ℝ)
    (hq : Tendsto (fun k => (inner ℂ (w k) (iterate (T k) (2*steps (a k) tau) (w k))).re)
      l (𝓝 q)) : 0 < q ∧ c/2 ≤ q := by
  have hf : ∀ᶠ k in l, c/2 ≤
      (inner ℂ (w k) (iterate (T k) (2*steps (a k) tau) (w k))).re := by
    filter_upwards [ha,henergy,hnorm] with k hk he hn
    exact half_norm_survives (T k) (hs k) (w k) (a k) C tau c hC (steps (a k) tau)
      (time_le (a k) tau hk htau.le) hsmall he hn
  have hb := ge_of_tendsto hq hf
  exact ⟨(half_pos hc).trans_le hb,hb⟩

/-- Construct a positive scalar continuum subsequence at a fixed positive
physical time. Neither a positive limit nor its convergence is an input. -/
theorem exists_surviving_subsequence
    (E : ℕ → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℂ (E k)]
    (T : (k : ℕ) → E k →L[ℂ] E k) (w : (k : ℕ) → E k)
    (hs : ∀ k x y, inner ℂ (T k x) y = inner ℂ x (T k y))
    (hcontract : ∀ k x, ‖T k x‖ ≤ ‖x‖)
    (a : ℕ → ℝ) (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (C tau c M : ℝ) (hC : 0 ≤ C) (htau : 0 < tau) (hc : 0 < c)
    (hsmall : C*tau ≤ 1/2)
    (henergy : ∀ k, dirichlet (T k) (w k) ≤ C*a k*‖w k‖^2)
    (hnorm : ∀ k, c ≤ ‖w k‖^2) (hupper : ∀ k, ‖w k‖^2 ≤ M) :
    ∃ q : ℝ, 0 < q ∧ c/2 ≤ q ∧ q ≤ M ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧
        Tendsto (fun k => (inner ℂ (w (phi k))
          (iterate (T (phi k)) (2*steps (a (phi k)) tau) (w (phi k)))).re) atTop (𝓝 q) ∧
        Tendsto (fun k => time (a (phi k)) tau) atTop (𝓝 tau) ∧
        Tendsto (fun k => steps (a (phi k)) tau) atTop atTop := by
  let signal := fun k => (inner ℂ (w k) (iterate (T k) (2*steps (a k) tau) (w k))).re
  have hb (k : ℕ) : signal k ∈ Set.Icc (c/2) M := by
    refine ⟨half_norm_survives (T k) (hs k) (w k) (a k) C tau c hC _
      (time_le (a k) tau (ha k) htau.le) hsmall (henergy k) (hnorm k), ?_⟩
    dsimp only [signal]
    rw [even_pairing (T k) (hs k)]
    exact (pow_le_pow_left₀ (norm_nonneg _) (iterate_contraction (T k) (hcontract k) _ (w k)) 2).trans
      (hupper k)
  obtain ⟨q,hq,phi,hphi,hlim⟩ := isCompact_Icc.tendsto_subseq hb
  refine ⟨q,(half_pos hc).trans_le hq.1,hq.1,hq.2,phi,hphi,hlim,?_,?_⟩
  · exact (time_tendsto a (Eventually.of_forall ha) ha0 tau htau.le).comp hphi.tendsto_atTop
  · exact (steps_tendsto a (Eventually.of_forall ha) ha0 tau htau).comp hphi.tendsto_atTop

end
end UnifiedTheory.Clay.YangMills.PhysicalTimeMesh
