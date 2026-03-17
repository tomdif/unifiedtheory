/-
  LayerB/RiemannAction.lean — Riemann-derived action functional

  Derives a dressing functional from the Riemann tensor, eliminating D
  as a free parameter. The Kretschner-like action S(md) = Σ R²
  provides a geometrically motivated, non-negative, quadratic action
  on the metric derivative space.

  Key results:
    (1) S is non-negative (sum of squares)
    (2) S is nonzero on some MetricDerivs (explicit witness)
    (3) S scales quadratically: S(φ · md) = φ² · S(md)
    (4) riemannDressing: a geometrically derived dressing functional
    (5) Path-dependence: different histories with same net perturbation
        can have different accumulated actions, making path ordering matter
-/
import UnifiedTheory.LayerA.MetricToRiemann
import UnifiedTheory.LayerB.HistoryAmplitudes

namespace UnifiedTheory.LayerB.RiemannAction

open UnifiedTheory.LayerA.MetricConstruction

variable {n : ℕ}

/-! ## The Kretschner-like action -/

/-- The **Kretschner-like action**: S(md) = Σ_{a,b,c,d} R_metric(md, a, b, c, d)².
    This is a sum of squares of all Riemann tensor components. -/
noncomputable def kretschnerAction (md : MetricDerivs n) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
    (R_metric md a b c d) ^ 2

/-! ## S is non-negative -/

/-- **S is non-negative**: the Kretschner action is a sum of squares. -/
theorem kretschnerAction_nonneg (md : MetricDerivs n) :
    0 ≤ kretschnerAction md := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro c _
  apply Finset.sum_nonneg
  intro d _
  exact sq_nonneg _

/-! ## S is nonzero for some MetricDerivs -/

/-- Symmetrized Kronecker witness: h(e,f,a,b) = δ(e,a)·δ(f,b) + δ(e,b)·δ(f,a).
    Satisfies h_metric (swap a,b: commutative by ring) and
    h_comm (swap e,f: commutative by ring). -/
noncomputable def witnessH (e f a b : Fin 2) : ℝ :=
  (if e = a then (1 : ℝ) else 0) * (if f = b then 1 else 0) +
  (if e = b then (1 : ℝ) else 0) * (if f = a then 1 else 0)

private theorem witnessH_metric (e f a b : Fin 2) :
    witnessH e f a b = witnessH e f b a := by
  unfold witnessH; ring

private theorem witnessH_comm (e f a b : Fin 2) :
    witnessH e f a b = witnessH f e a b := by
  unfold witnessH; ring

/-- Witness MetricDerivs on Fin 2 with symmetrized Kronecker h. -/
noncomputable def witnessMD : MetricDerivs 2 where
  h := witnessH
  h_metric := witnessH_metric
  h_comm := witnessH_comm
  k := fun _ _ _ _ _ => 0
  k_metric := fun _ _ _ _ _ => rfl
  k_sym12 := fun _ _ _ _ _ => rfl
  k_sym23 := fun _ _ _ _ _ => rfl

/-- R_metric of witnessMD at (0,1,0,1) is nonzero.
    We compute using the direct formula for h. -/
private theorem witness_R_nonzero :
    R_metric witnessMD 0 1 0 1 ≠ 0 := by
  suffices h : witnessH 0 1 0 1 - witnessH 0 0 1 1 -
    witnessH 1 1 0 0 + witnessH 1 0 1 0 ≠ 0 by
    simp only [R_metric]
    intro heq
    apply h
    -- witnessMD.h = witnessH, so the terms are definitionally equal
    have : witnessMD.h = witnessH := rfl
    rw [this] at heq
    linarith
  simp only [witnessH]
  norm_num [show (0 : Fin 2) = 0 from rfl, show (1 : Fin 2) = 1 from rfl,
            show (0 : Fin 2) ≠ 1 from by decide, show (1 : Fin 2) ≠ 0 from by decide]

/-- R_metric of witnessMD at (0,1,0,1) squared is positive. -/
private theorem witness_R_sq_pos :
    0 < (R_metric witnessMD 0 1 0 1) ^ 2 := by
  apply sq_pos_of_ne_zero
  exact witness_R_nonzero

set_option maxHeartbeats 800000 in
-- Fin 2 enumeration in Finset.single_le_sum requires extra heartbeats
/-- The witness has positive Kretschner action. -/
private theorem witnessMD_action_pos : 0 < kretschnerAction witnessMD := by
  apply lt_of_lt_of_le witness_R_sq_pos
  apply le_trans (Finset.single_le_sum (fun d _ => sq_nonneg _) (Finset.mem_univ (1 : Fin 2)))
  apply le_trans (Finset.single_le_sum
    (fun c _ => Finset.sum_nonneg (fun d _ => sq_nonneg _)) (Finset.mem_univ (0 : Fin 2)))
  apply le_trans (Finset.single_le_sum
    (fun b _ => Finset.sum_nonneg (fun c _ => Finset.sum_nonneg (fun d _ => sq_nonneg _)))
    (Finset.mem_univ (1 : Fin 2)))
  exact Finset.single_le_sum
    (fun a _ => Finset.sum_nonneg (fun b _ => Finset.sum_nonneg
      (fun c _ => Finset.sum_nonneg (fun d _ => sq_nonneg _))))
    (Finset.mem_univ (0 : Fin 2))

/-- **S is nonzero** for the witness MetricDerivs: there exists a MetricDerivs
    with positive Kretschner action. -/
theorem kretschnerAction_nonzero_exists :
    ∃ md : MetricDerivs 2, 0 < kretschnerAction md :=
  ⟨witnessMD, witnessMD_action_pos⟩

/-! ## Scaling of MetricDerivs -/

/-- Scale a MetricDerivs by a scalar φ: multiply all h and k entries by φ. -/
noncomputable def scaleMetricDerivs (φ : ℝ) (md : MetricDerivs n) : MetricDerivs n where
  h := fun e f a b => φ * md.h e f a b
  h_metric := fun e f a b => by simp [md.h_metric]
  h_comm := fun e f a b => by simp [md.h_comm]
  k := fun e f g a b => φ * md.k e f g a b
  k_metric := fun e f g a b => by simp [md.k_metric]
  k_sym12 := fun e f g a b => by simp [md.k_sym12]
  k_sym23 := fun e f g a b => by simp [md.k_sym23]

/-- R_metric scales linearly with the metric derivative scaling. -/
theorem R_metric_scale (φ : ℝ) (md : MetricDerivs n) (a b c d : Fin n) :
    R_metric (scaleMetricDerivs φ md) a b c d = φ * R_metric md a b c d := by
  simp only [R_metric, scaleMetricDerivs]
  ring

/-- **S scales quadratically**: S(φ · md) = φ² · S(md). -/
theorem kretschnerAction_scale (φ : ℝ) (md : MetricDerivs n) :
    kretschnerAction (scaleMetricDerivs φ md) = φ ^ 2 * kretschnerAction md := by
  simp only [kretschnerAction, R_metric_scale]
  rw [Finset.mul_sum]
  congr 1; funext a
  rw [Finset.mul_sum]
  congr 1; funext b
  rw [Finset.mul_sum]
  congr 1; funext c
  rw [Finset.mul_sum]
  congr 1; funext d
  ring

/-! ## Addition of MetricDerivs -/

/-- Add two MetricDerivs pointwise. -/
noncomputable def addMetricDerivs (md₁ md₂ : MetricDerivs n) : MetricDerivs n where
  h := fun e f a b => md₁.h e f a b + md₂.h e f a b
  h_metric := fun e f a b => by simp [md₁.h_metric, md₂.h_metric]
  h_comm := fun e f a b => by simp [md₁.h_comm, md₂.h_comm]
  k := fun e f g a b => md₁.k e f g a b + md₂.k e f g a b
  k_metric := fun e f g a b => by simp [md₁.k_metric, md₂.k_metric]
  k_sym12 := fun e f g a b => by simp [md₁.k_sym12, md₂.k_sym12]
  k_sym23 := fun e f g a b => by simp [md₁.k_sym23, md₂.k_sym23]

/-- R_metric is additive in the MetricDerivs. -/
theorem R_metric_add (md₁ md₂ : MetricDerivs n) (a b c d : Fin n) :
    R_metric (addMetricDerivs md₁ md₂) a b c d =
    R_metric md₁ a b c d + R_metric md₂ a b c d := by
  simp only [R_metric, addMetricDerivs]
  ring

/-! ## Riemann dressing functional -/

/-- The **Riemann dressing functional**: assigns to each MetricDerivs
    the square root of its Kretschner action. This is a geometrically
    motivated dressing that makes history amplitudes carry genuine
    curvature content.

    When used as the imaginary component of an amplitude:
    z = Q(perturbation) + i · riemannDressing(metricDerivs)
    the amplitude encodes both source strength and curvature information. -/
noncomputable def riemannDressing (md : MetricDerivs n) : ℝ :=
  Real.sqrt (kretschnerAction md)

/-- The Riemann dressing is non-negative. -/
theorem riemannDressing_nonneg (md : MetricDerivs n) :
    0 ≤ riemannDressing md :=
  Real.sqrt_nonneg _

/-- The Riemann dressing is nonzero for the witness MetricDerivs. -/
theorem riemannDressing_nonzero_exists :
    ∃ md : MetricDerivs 2, 0 < riemannDressing md := by
  obtain ⟨md, hmd⟩ := kretschnerAction_nonzero_exists
  exact ⟨md, Real.sqrt_pos_of_pos hmd⟩

/-! ## Accumulated action and path-dependence -/

/-- The **accumulated action** over a history of metric perturbation steps.
    Each step contributes its own Kretschner action to the total.
    This is the sum of per-step actions: Σ S(step). -/
noncomputable def accumulatedAction (history : List (MetricDerivs n)) : ℝ :=
  (history.map kretschnerAction).sum

/-- Kretschner action of the sum doubles: S(md + md) = 4 * S(md),
    because R is linear so R(md+md) = 2*R(md), and squaring gives 4. -/
private theorem kretschnerAction_double (md : MetricDerivs n) :
    kretschnerAction (addMetricDerivs md md) = 4 * kretschnerAction md := by
  have hR : ∀ a b c d : Fin n,
      R_metric (addMetricDerivs md md) a b c d =
      2 * R_metric md a b c d := by
    intro a b c d
    rw [R_metric_add]; ring
  simp only [kretschnerAction]
  rw [Finset.mul_sum]
  congr 1; funext a
  rw [Finset.mul_sum]
  congr 1; funext b
  rw [Finset.mul_sum]
  congr 1; funext c
  rw [Finset.mul_sum]
  congr 1; funext d
  rw [hR]; ring

/-- **PATH-DEPENDENCE OF ACCUMULATED ACTION.**

    Two histories with the SAME net perturbation can have DIFFERENT
    accumulated actions. Specifically:
    - History A: two steps [md, md] with accumulated action S(md) + S(md) = 2*S(md)
    - History B: one step [md + md] with accumulated action S(md+md) = 4*S(md)

    Both produce the same total perturbation (md + md), but
    2*S(md) ≠ 4*S(md) when S(md) > 0. This is because S is quadratic:
    S(h₁) + S(h₂) ≠ S(h₁ + h₂) in general.

    This is the crucial result: path ordering MATTERS for the action,
    even though it doesn't matter for the net perturbation. This makes
    the sum-over-histories non-trivial. -/
theorem path_dependence_exists :
    ∃ (md₁ md₂ : MetricDerivs 2),
      accumulatedAction [md₁, md₂] ≠ accumulatedAction [addMetricDerivs md₁ md₂] := by
  use witnessMD, witnessMD
  simp only [accumulatedAction, List.map, List.sum_cons, List.sum_nil, add_zero]
  rw [kretschnerAction_double]
  linarith [witnessMD_action_pos]

/-- **RIEMANN ACTION CAPSTONE.**

    The Kretschner-like action S(md) = Σ R² provides:
    (1) Non-negativity: S(md) ≥ 0
    (2) Non-degeneracy: ∃ md, S(md) > 0
    (3) Quadratic scaling: S(φ·md) = φ² · S(md)
    (4) Path-dependence: different decompositions of the same net perturbation
        yield different accumulated actions

    This eliminates D as a free parameter: the dressing functional is
    determined by the Riemann curvature of each perturbation step. -/
theorem riemann_action_capstone :
    -- (1) Non-negativity
    (∀ md : MetricDerivs 2, 0 ≤ kretschnerAction md)
    -- (2) Non-degeneracy
    ∧ (∃ md : MetricDerivs 2, 0 < kretschnerAction md)
    -- (3) Quadratic scaling
    ∧ (∀ (φ : ℝ) (md : MetricDerivs 2),
        kretschnerAction (scaleMetricDerivs φ md) = φ ^ 2 * kretschnerAction md)
    -- (4) Path-dependence
    ∧ (∃ (md₁ md₂ : MetricDerivs 2),
        accumulatedAction [md₁, md₂] ≠ accumulatedAction [addMetricDerivs md₁ md₂]) :=
  ⟨kretschnerAction_nonneg, kretschnerAction_nonzero_exists,
   kretschnerAction_scale, path_dependence_exists⟩

end UnifiedTheory.LayerB.RiemannAction
