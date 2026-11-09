/- A normalized one-link energy tail for the actual U(d) Wilson conditional
law. The excess partition has an explicit polynomial-in-coupling lower bound,
uniform in the exterior links and lattice volume. This is not a multiscale
large-field estimate or a bound on a vacuum-subtracted source insertion. -/
import UnifiedTheory.Clay.YangMills.WilsonConditionalPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonConditionalEnergyTail
noncomputable section
open MeasureTheory Filter CompactGibbsContinuity RegulatedGauge
open UnitaryHaarNeighborhood UnitaryHaarCaps WilsonConditionalPolynomial WilsonUniformVariance
open PeriodicLattice4

section General
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def excessPartition (S : X → ℝ) (b : ℝ) : ℝ := ∫ x, Real.exp (-(S x-b)) ∂μ

def tiltedTail (S : X → ℝ) (b δ T : ℝ) : ℝ :=
  ∫ x, ({x | T ≤ S x-b} : Set X).indicator (fun x => Real.exp (δ*(S x-b))) x ∂law μ S

def markedTail (S : X → ℝ) (b : ℝ) (Q : X → ℝ) (T : ℝ) : ℝ :=
  ∫ x, ({x | T ≤ S x-b} : Set X).indicator Q x ∂law μ S

/-- Recentring the action cancels exactly between numerator and partition.
The expectation remains under the original Gibbs law. -/
theorem shifted_expectation (S : X → ℝ) (hS : Continuous S) (b : ℝ) (Q : X → ℝ) :
    (∫ x, Q x ∂law μ S) =
      (∫ x, Real.exp (-(S x-b))*Q x ∂μ) / excessPartition μ S b := by
  have he (x : X) : Real.exp (-S x) = Real.exp (-b)*Real.exp (-(S x-b)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [law, LocalGibbsComparison.weighted_integral μ (fun x => Real.exp (-S x))
    (Real.continuous_exp.comp hS.neg).measurable (fun _ => (Real.exp_pos _).le)
    (partition_positive μ S hS) Q]
  simp_rw [he, mul_assoc]
  rw [integral_const_mul, integral_const_mul, mul_div_mul_left _ _ (Real.exp_pos (-b)).ne']
  rfl

/-- A lower bound on the recentered partition gives a normalized tilted tail.
Only delta<=1 is needed; delta<1 gives exponential decay in T. -/
theorem tiltedTail_bound (S : X → ℝ) (hS : Continuous S) (b δ T : ℝ) (hδ : δ ≤ 1)
    (z : ℝ) (hz : 0 < z) (hpart : z ≤ excessPartition μ S b) :
    tiltedTail μ S b δ T ≤ Real.exp (-(1-δ)*T)/z := by
  let A : Set X := {x | T ≤ S x-b}
  have hA : MeasurableSet A := (isClosed_le continuous_const (hS.sub continuous_const)).measurableSet
  let q : X → ℝ := fun x => Real.exp (-(1-δ)*(S x-b))
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hi : Integrable (A.indicator q) μ :=
    (hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).indicator hA
  have hn : (∫ x, A.indicator q x ∂μ) ≤ Real.exp (-(1-δ)*T) := by
    calc
      _ ≤ ∫ _x : X, Real.exp (-(1-δ)*T) ∂μ := by
        apply integral_mono hi (integrable_const _)
        intro x
        by_cases hx : x ∈ A
        · rw [Set.indicator_of_mem hx]
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left hx (by linarith)
        · rw [Set.indicator_of_notMem hx]
          exact (Real.exp_pos _).le
      _ = _ := by simp
  have hid (x : X) : Real.exp (-(S x-b)) *
      A.indicator (fun x => Real.exp (δ*(S x-b))) x = A.indicator q x := by
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      rw [← Real.exp_add]
      congr 1
      dsimp [q]
      ring
    · simp only [Set.indicator_of_notMem hx, mul_zero]
  rw [tiltedTail, shifted_expectation μ S hS b]
  change (∫ x, Real.exp (-(S x-b))*A.indicator (fun x => Real.exp (δ*(S x-b))) x ∂μ) /
    excessPartition μ S b ≤ _
  simp_rw [hid]
  exact (div_le_div_of_nonneg_right hn (hz.le.trans hpart)).trans
    (div_le_div_of_nonneg_left (Real.exp_pos _).le hz hpart)

/-- A bounded mark costs only its uniform bound on the energy-tail event.
No pointwise domination of the mark by the excess energy is assumed. -/
theorem markedTail_le (S : X → ℝ) (hS : Continuous S) (b : ℝ)
    (Q : X → ℝ) (hQ : Continuous Q) (M T : ℝ) (hbound : ∀ x, Q x ≤ M) :
    markedTail μ S b Q T ≤ M*tiltedTail μ S b 0 T := by
  let A : Set X := {x | T ≤ S x-b}
  have hA : MeasurableSet A := (isClosed_le continuous_const (hS.sub continuous_const)).measurableSet
  letI : IsProbabilityMeasure (law μ S) := law_probability μ S hS
  have hi : Integrable (A.indicator Q) (law μ S) :=
    (hQ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).indicator hA
  have hj : Integrable (A.indicator (fun _ => (1 : ℝ))) (law μ S) :=
    (integrable_const 1).indicator hA
  change (∫ x, A.indicator Q x ∂law μ S) ≤ _
  calc
    _ ≤ ∫ x, M*A.indicator (fun _ => (1 : ℝ)) x ∂law μ S := by
      apply integral_mono hi (hj.const_mul M)
      intro x
      by_cases hx : x ∈ A
      · simpa only [Set.indicator_of_mem hx, mul_one] using hbound x
      · simp only [Set.indicator_of_notMem hx, mul_zero, le_refl]
    _ = M*tiltedTail μ S b 0 T := by
      rw [integral_const_mul]
      simp only [tiltedTail, zero_mul, Real.exp_zero, A]

end General

section Unitary
variable (d : Type*) [Fintype d] [DecidableEq d]

/-- A cap radius small enough that the action increases by at most one. -/
theorem cap_energy_le_one (S : Matrix.unitaryGroup d ℂ → ℝ)
    (L : ℝ)
    (hLip : ∀ A B : Matrix.unitaryGroup d ℂ, ∀ r : ℝ, 0 ≤ r →
      (∀ i j, ‖A i j-B i j‖ ≤ r) → |S A-S B| ≤ L*r)
    (K : ℕ) (hK : 0 < K) (hscale : 2*(Fintype.card d : ℝ)^2*L ≤ K)
    (A U : Matrix.unitaryGroup d ℂ) (hU : U ∈ cap d A K) : S U-S A ≤ 1 := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hh := (le_abs_self (S U-S A)).trans
    (hLip U A ((Fintype.card d : ℝ)*entryRadius d K) (by unfold entryRadius; positivity)
      (cap_entry_bound d A U K hU))
  have hr : L*((Fintype.card d : ℝ)*entryRadius d K) = 2*(Fintype.card d : ℝ)^2*L/(K : ℝ) := by
    unfold entryRadius
    ring
  rw [hr] at hh
  exact hh.trans ((div_le_one hk).mpr hscale)

/-- A polynomial lower bound on the actual recentered partition; no global
oscillation estimate or supplied neighborhood probability is used. -/
theorem unitary_partition_lower (S : Matrix.unitaryGroup d ℂ → ℝ) (hS : Continuous S)
    (L : ℝ)
    (hLip : ∀ A B : Matrix.unitaryGroup d ℂ, ∀ r : ℝ, 0 ≤ r →
      (∀ i j, ‖A i j-B i j‖ ≤ r) → |S A-S B| ≤ L*r)
    (K : ℕ) (hK : 0 < K) (hscale : 2*(Fintype.card d : ℝ)^2*L ≤ K)
    (A : Matrix.unitaryGroup d ℂ) :
    massLower d K * Real.exp (-1) ≤
      excessPartition (compactHaar (Matrix.unitaryGroup d ℂ)) S (S A) := by
  let μ := compactHaar (Matrix.unitaryGroup d ℂ)
  have hi : Integrable (fun U => Real.exp (-(S U-S A))) μ :=
    (Real.continuous_exp.comp (hS.sub continuous_const).neg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ μ.real (cap d A K)*Real.exp (-1) :=
      mul_le_mul_of_nonneg_right (cap_mass_lower d A K hK) (Real.exp_pos _).le
    _ = ∫ _U in cap d A K, Real.exp (-1) ∂μ := by simp
    _ ≤ ∫ U in cap d A K, Real.exp (-(S U-S A)) ∂μ := by
      apply setIntegral_mono_on integrableOn_const hi.integrableOn (cap_measurable d A K)
      intro U hU
      exact Real.exp_le_exp.mpr (neg_le_neg (cap_energy_le_one d S L hLip K hK hscale A U hU))
    _ ≤ excessPartition μ S (S A) :=
      setIntegral_le_integral hi (Eventually.of_forall (fun U => (Real.exp_pos _).le))

def grid (β : ℝ) : ℕ := ⌈48*(Fintype.card d : ℝ)^5*|β|⌉₊+1

omit [DecidableEq d] in
theorem grid_pos (β : ℝ) : 0 < grid d β := by unfold grid; omega

omit [DecidableEq d] in
theorem grid_scale (β : ℝ) :
    2*(Fintype.card d : ℝ)^2*(24*(Fintype.card d : ℝ)^3*|β|) ≤ grid d β := by
  have hh := (Nat.le_ceil (48*(Fintype.card d : ℝ)^5*|β|)).trans
    (Nat.cast_le.mpr (Nat.le_succ _))
  unfold grid
  convert hh using 1
  ring

/-- Explicit normalized tail factor. Its coupling growth is polynomial. -/
def tailBound (β δ T : ℝ) : ℝ :=
  Real.exp (1-(1-δ)*T) * ((2*grid d β+1 : ℕ) : ℝ)^(2*(Fintype.card d)^2)

omit [DecidableEq d] in
theorem tailBound_eq (β δ T : ℝ) :
    Real.exp (-(1-δ)*T)/(massLower d (grid d β)*Real.exp (-1)) = tailBound d β δ T := by
  unfold massLower tailBound
  rw [Real.exp_neg, show 1-(1-δ)*T = -(1-δ)*T+1 by ring, Real.exp_add]
  field_simp

variable (n : ℕ) [NeZero n]

/-- Applies to the exact fixed-exterior one-link Wilson action. -/
theorem actual_partition_lower (β c : ℝ) (x : Vertex n) (μ : Fin 4)
    (r : Exterior n (Matrix.unitaryGroup d ℂ) x μ) (A : Matrix.unitaryGroup d ℂ) :
    massLower d (grid d β) * Real.exp (-1) ≤
      excessPartition (compactHaar (Matrix.unitaryGroup d ℂ))
        (action n d β c x μ r) (action n d β c x μ r A) := by
  apply unitary_partition_lower d (action n d β c x μ r) (action_continuous n d β c x μ r)
    (24*(Fintype.card d : ℝ)^3*|β|)
    (action_lipschitz n d β c x μ r) (grid d β) (grid_pos d β) (grid_scale d β) A

/-- The tail is normalized under the ACTUAL conditional Wilson law, and its
bound has no volume, exterior or plaquette-offset dependence. The reference
can be any A; a minimizing A makes the excess energy everywhere nonnegative. -/
theorem actual_tilted_tail (β c : ℝ) (x : Vertex n) (μ : Fin 4)
    (r : Exterior n (Matrix.unitaryGroup d ℂ) x μ) (A : Matrix.unitaryGroup d ℂ)
    (δ T : ℝ) (hδ : δ ≤ 1) :
    tiltedTail (compactHaar (Matrix.unitaryGroup d ℂ)) (action n d β c x μ r)
      (action n d β c x μ r A) δ T ≤ tailBound d β δ T := by
  rw [← tailBound_eq]
  exact tiltedTail_bound _ (action n d β c x μ r) (action_continuous n d β c x μ r)
    (action n d β c x μ r A) δ T hδ (massLower d (grid d β)*Real.exp (-1))
    (mul_pos (massLower_pos d _) (Real.exp_pos _)) (actual_partition_lower d n β c x μ r A)

/-- Bounded local observables on a conditional energy-tail event have a
normalized bound uniform in all exterior links and in the volume. -/
theorem actual_marked_tail (β c : ℝ) (x : Vertex n) (μ : Fin 4)
    (r : Exterior n (Matrix.unitaryGroup d ℂ) x μ) (A : Matrix.unitaryGroup d ℂ)
    (Q : Matrix.unitaryGroup d ℂ → ℝ) (hQ : Continuous Q)
    (M T : ℝ) (hM : 0 ≤ M) (hbound : ∀ U, Q U ≤ M) :
    markedTail (compactHaar (Matrix.unitaryGroup d ℂ)) (action n d β c x μ r)
      (action n d β c x μ r A) Q T ≤
        M*Real.exp (1-T)*((2*grid d β+1 : ℕ) : ℝ)^(2*(Fintype.card d)^2) := by
  have h := (markedTail_le _ (action n d β c x μ r) (action_continuous n d β c x μ r)
    (action n d β c x μ r A) Q hQ M T hbound).trans
      (mul_le_mul_of_nonneg_left (actual_tilted_tail d n β c x μ r A 0 T (by norm_num)) hM)
  simpa only [tailBound, sub_zero, one_mul, mul_assoc] using h

/-- In particular, a squared centered local trace costs at most 4d^2 on the
energy-tail event. R can be the fixed residual holonomy of a plaquette.
This uses only boundedness of the trace, not trace domination by energy. -/
theorem actual_centered_trace_tail (β c : ℝ) (x : Vertex n) (μ : Fin 4)
    (r : Exterior n (Matrix.unitaryGroup d ℂ) x μ) (A R : Matrix.unitaryGroup d ℂ)
    (z : ℂ) (hz : ‖z‖ ≤ (Fintype.card d : ℝ)) (T : ℝ) :
    markedTail (compactHaar (Matrix.unitaryGroup d ℂ)) (action n d β c x μ r)
      (action n d β c x μ r A) (fun U => ‖realTrace d (U*R)-z‖^2) T ≤
        (4*(Fintype.card d : ℝ)^2)*Real.exp (1-T)*
          ((2*grid d β+1 : ℕ) : ℝ)^(2*(Fintype.card d)^2) := by
  apply actual_marked_tail d n β c x μ r A _
    ((((realTrace_continuous d).comp (continuous_id.mul continuous_const)).sub
      continuous_const).norm.pow 2) _ T (by positivity)
  intro U
  change ‖realTrace d (U*R)-z‖^2 ≤ 4*(Fintype.card d : ℝ)^2
  have ht : ‖realTrace d (U*R)‖ ≤ (Fintype.card d : ℝ) := by
    rw [realTrace, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans
      (UnitaryCharacterObservables.unitary_trace_bound (U*R))
  have hnorm := (norm_sub_le (realTrace d (U*R)) z).trans (add_le_add ht hz)
  nlinarith [norm_nonneg (realTrace d (U*R)-z), Nat.cast_nonneg (α := ℝ) (Fintype.card d)]

/-- A minimizing reference is constructed by compactness. This supplies an
actual nonnegative energy reserve, not an assumed tail distribution. -/
theorem exists_minimum_with_tail (β c : ℝ) (x : Vertex n) (μ : Fin 4)
    (r : Exterior n (Matrix.unitaryGroup d ℂ) x μ) :
    ∃ A : Matrix.unitaryGroup d ℂ,
      (∀ U, 0 ≤ action n d β c x μ r U-action n d β c x μ r A) ∧
      ∀ δ T : ℝ, δ ≤ 1 →
        tiltedTail (compactHaar (Matrix.unitaryGroup d ℂ)) (action n d β c x μ r)
          (action n d β c x μ r A) δ T ≤ tailBound d β δ T := by
  obtain ⟨A,_,hA⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (Matrix.unitaryGroup d ℂ)).Nonempty)
    (action_continuous n d β c x μ r).continuousOn
  exact ⟨A, fun U => sub_nonneg.mpr (hA (Set.mem_univ U)),
    fun δ T hδ => actual_tilted_tail d n β c x μ r A δ T hδ⟩

end Unitary
end
end UnifiedTheory.Clay.YangMills.WilsonConditionalEnergyTail
