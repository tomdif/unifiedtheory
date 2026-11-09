/-
  First cohomological descent for the Abelian overlap anomaly.
  The periodic prefix construction and finite matrix identities below are
  formal. Full cubical contraction is additionally checked by an executable;
  the spectral/locality estimates and physical continuum are not formalized.
  The field-strength and winding remainders are NOT set to zero.
-/
import UnifiedTheory.Audit.KFCausalRadialMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalLocalCohomology
noncomputable section
open Matrix
open scoped BigOperators

section PeriodicPrimitive
variable {R : Type*} [AddCommGroup R]

/-- Source with its total moved to a chosen anchor r. -/
def centeredSource (a : ℕ → R) (N r i : ℕ) : R :=
  a i - if i = r then ∑ j ∈ Finset.range (N + 1), a j else 0

/-- Minus the strict prefix: the edge convention is h(i)-h(i+1). -/
def cutPrimitive (z : ℕ → R) (i : ℕ) : R := -∑ j ∈ Finset.range i, z j

theorem centeredSource_zero_sum (a : ℕ → R) (N r : ℕ) (hr : r ≤ N) :
    ∑ i ∈ Finset.range (N + 1), centeredSource a N r i = 0 := by
  have hr' : r ∈ Finset.range (N + 1) := by simp; omega
  simp [centeredSource, Finset.sum_sub_distrib, hr']

theorem cutPrimitive_bulk (z : ℕ → R) (i : ℕ) :
    cutPrimitive z i - cutPrimitive z (i + 1) = z i := by
  simp [cutPrimitive, Finset.sum_range_succ]

theorem cutPrimitive_periodic_last (z : ℕ → R) (N : ℕ)
    (hz : ∑ j ∈ Finset.range (N + 1), z j = 0) :
    cutPrimitive z N - cutPrimitive z 0 = z N := by
  have h := cutPrimitive_bulk z N
  simpa [cutPrimitive, hz] using h

/-- The primitive vanishes beyond any interval containing a zero-total source. -/
theorem cutPrimitive_support (z : ℕ → R) (b i : ℕ) (hbi : b ≤ i)
    (hz : ∑ j ∈ Finset.range b, z j = 0) (ht : ∀ j, b ≤ j → z j = 0) :
    cutPrimitive z i = 0 := by
  have hs : ∀ k, ∑ j ∈ Finset.range (b + k), z j = 0 := by
    intro k
    induction k with
    | zero => simpa using hz
    | succ k ih =>
      rw [Nat.add_succ, Finset.sum_range_succ, ih, ht (b + k) (by omega), add_zero]
  have hi : b + (i - b) = i := by omega
  have h := hs (i - b)
  rw [hi] at h
  simp [cutPrimitive, h]

/-- A one-cycle carries an explicit constant harmonic part through the cut. -/
theorem cutPrimitive_boundary (c : ℕ → R) (i : ℕ) :
    cutPrimitive (fun j => c j - c (j + 1)) i = c i - c 0 := by
  induction i with
  | zero => simp [cutPrimitive]
  | succ i ih =>
    have h := cutPrimitive_bulk (fun j => c j - c (j + 1)) i
    rw [ih] at h
    calc
      _ = (c i - c 0) - (c i - c 0 -
          cutPrimitive (fun j => c j - c (j + 1)) (i + 1)) := by abel
      _ = (c i - c 0) - (c i - c (i + 1)) := by rw [h]
      _ = _ := by abel

end PeriodicPrimitive

section ChainAlgebra
variable {R : Type*} [Ring R]

/-- Any supplied chain contraction commutes with the boundary projection. -/
theorem contraction_projection_chain_map (d h p : R)
    (hd : d * d = 0) (hc : d * h + h * d = 1 - p) : d * p = p * d := by
  have hp : p = 1 - (d * h + h * d) := by rw [hc]; noncomm_ring
  rw [hp]
  have hdd : d * (d * h) = 0 := by rw [← mul_assoc, hd, zero_mul]
  noncomm_ring [hd, hdd]

/-- Closed chains split into an actual boundary and a retained harmonic piece. -/
theorem contraction_cycle (d h p f : R)
    (hc : d * h + h * d = 1 - p) (hf : d * f = 0) :
    d * (h * f) = f - p * f := by
  have hh := congrArg (fun z : R => z * f) hc
  simpa [add_mul, sub_mul, mul_assoc, hf] using hh

end ChainAlgebra

section GaugeDerivative
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Differentiating an Abelian invariant density preserves gauge invariance,
including along the moving radial path t(A+g). No gauge-frame derivative
appears in this scalar kernel, unlike the pair-flux construction. -/
theorem radial_link_derivative_gauge (f : W → ℝ) (A g e : W)
    (hg : ∀ (X : W) (u : ℝ), f (X + u • g) = f X) (t : ℝ) :
    deriv (fun s : ℝ => f (t • (A + g) + s • e)) 0 =
      deriv (fun s : ℝ => f (t • A + s • e)) 0 := by
  have he : (fun s : ℝ => f (t • (A + g) + s • e)) =
      (fun s : ℝ => f (t • A + s • e)) := by
    funext s
    have hx : t • (A + g) + s • e = (t • A + s • e) + t • g := by
      rw [smul_add]
      abel
    rw [hx, hg]
  rw [he]

end GaugeDerivative

section HarmonicBound
/-- The retained flux is a transverse sum at the distant cut. A supplied
pointwise tail estimate controls it with an explicit cardinality factor. -/
theorem cut_flux_bound {I : Type*} (s : Finset I) (f : I → ℝ) (ε : ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ ε) : |∑ i ∈ s, f i| ≤ s.card * ε := by
  calc
    _ ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs f s
    _ ≤ ∑ _i ∈ s, ε := Finset.sum_le_sum hf
    _ = _ := by simp

end HarmonicBound

section Anchoring
variable {V F : Type*} [Fintype V]

/-- The column sum is placed at that face's own anchor, not a global root. -/
def anchored (anchor : F → V) (theta : Matrix V F ℝ) : Matrix V F ℝ :=
  by
    classical
    exact fun x f => if x = anchor f then ∑ z, theta z f else 0

theorem anchored_column_sum (anchor : F → V) (theta : Matrix V F ℝ) (f : F) :
    ∑ x, anchored anchor theta x f = ∑ x, theta x f := by
  classical
  simp [anchored]

theorem centered_column_sum (anchor : F → V) (theta : Matrix V F ℝ) (f : F) :
    ∑ x, (theta - anchored anchor theta) x f = 0 := by
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib, anchored_column_sum, sub_self]

end Anchoring

section Descent
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

omit [Fintype V] in
/-- Exact first descent. Both remainders remain on the right-hand side. -/
theorem first_descent (j : Matrix V E ℝ) (theta : Matrix V F ℝ)
    (C : Matrix F E ℝ) (r : Matrix V E ℝ) (B : Matrix E V ℝ)
    (tau : Matrix E F ℝ) (phi : Matrix V F ℝ) (A : Matrix E Unit ℝ)
    (hj : j = theta * C + r) (ht : theta = Bᵀ * tau + phi) :
    j * A = Bᵀ * (tau * (C * A)) + phi * (C * A) + r * A := by
  rw [hj, ht]
  simp only [Matrix.add_mul, Matrix.mul_assoc]

omit [Fintype E] in
/-- The periodic harmonic term modifies the next co-closedness equation. -/
theorem summed_descent_constraint (theta : Matrix V F ℝ) (C : Matrix F E ℝ)
    (r j : Matrix V E ℝ) (total : Matrix Unit V ℝ)
    (hj : j = theta * C + r) (ht : total * j = 0) :
    (total * theta) * C = -(total * r) := by
  rw [hj, Matrix.mul_add, ← Matrix.mul_assoc] at ht
  exact eq_neg_of_add_eq_zero_left ht

/-- An invariant kernel times an invariant curvature yields an invariant current. -/
theorem descent_current_gauge (tau tau' : Matrix E F ℝ) (C : Matrix F E ℝ)
    (B : Matrix E V ℝ) (A : Matrix E Unit ℝ) (omega : Matrix V Unit ℝ)
    (ht : tau' = tau) (hCB : C * B = 0) :
    tau' * (C * (A + B * omega)) = tau * (C * A) := by
  rw [ht, Matrix.mul_add, ← Matrix.mul_assoc C B, hCB, Matrix.zero_mul, add_zero]

/-- The explicit winding contribution is invariant when it is a cycle. -/
theorem winding_gauge (r : Matrix V E ℝ) (B : Matrix E V ℝ)
    (A : Matrix E Unit ℝ) (omega : Matrix V Unit ℝ) (hr : r * B = 0) :
    r * (A + B * omega) = r * A := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc r B, hr, Matrix.zero_mul, add_zero]

/-- Scalar phase transformation for a supplied gauge-invariant weighted current. -/
theorem phase_gauge_change (A h h' : Matrix E Unit ℝ) (B : Matrix E V ℝ)
    (omega : Matrix V Unit ℝ) (hh : h' = h) :
    -(A + B * omega)ᵀ * h' - (-Aᵀ * h) = -omegaᵀ * (Bᵀ * h) := by
  rw [hh, Matrix.transpose_add, Matrix.transpose_mul]
  simp only [Matrix.neg_mul, Matrix.add_mul, Matrix.mul_assoc]
  abel

omit [Fintype V] in
/-- Removing the constructed divergence leaves exactly the displayed remainder. -/
theorem corrected_ward_remainder (radial a h rem : Matrix V Unit ℝ)
    (hward : radial + a = h + rem) : radial + a - h = rem := by
  rw [hward]
  abel

end Descent

#print axioms centeredSource_zero_sum
#print axioms cutPrimitive_bulk
#print axioms cutPrimitive_periodic_last
#print axioms cutPrimitive_support
#print axioms cutPrimitive_boundary
#print axioms contraction_projection_chain_map
#print axioms contraction_cycle
#print axioms radial_link_derivative_gauge
#print axioms cut_flux_bound
#print axioms anchored_column_sum
#print axioms centered_column_sum
#print axioms first_descent
#print axioms summed_descent_constraint
#print axioms descent_current_gauge
#print axioms winding_gauge
#print axioms phase_gauge_change
#print axioms corrected_ward_remainder

end
end UnifiedTheory.Audit.KFCausalLocalCohomology
