/-
  Classical areal-clock reduction of the diagonal one-coordinate target.
  x=T+Q, z=T-Q, y=L; choose T=tau and P_L=-c, c>0.
  k=(b/a)*exp(2*tau)>0 is spatially constant. The remaining wave has
  positive Hamiltonian and sources the longitudinal metric. Exact local
  reconstruction identities are proved; global gauge existence, periodic
  reconstruction, the continuum PDE and microscopic realization are not
  silently assumed to follow from these algebraic theorems.
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalArealTensorDynamics
noncomputable section

theorem areal_one_form (pT pQ pL dT dQ dL : ℝ) :
    (pT+pQ)/2*(dT+dQ)+pL*dL+(pT-pQ)/2*(dT-dQ) =
      pT*dT+pQ*dQ+pL*dL := by ring

theorem areal_kinetic (pT pQ pL : ℝ) :
    ((pT+pQ)/2)^2+pL^2+((pT-pQ)/2)^2-
      (((pT+pQ)/2)+pL+((pT-pQ)/2))^2/2 =
        pQ^2/2+pL^2/2-pT*pL := by ring

theorem areal_curvature (dT dQ dL ddT : ℝ) :
    2*ddT+((dT+dQ)^2+(dT-dQ)^2+(dT+dQ)*(dT-dQ)-2*dL*dT)/2 =
      2*ddT+3*dT^2/2+dQ^2/2-dL*dT := by ring

/-- Scalar constraint divided by its positive metric/kinetic prefactor,
    after imposing T'=T''=0 and P_L=-c. -/
def gaugedConstraint (c k pT p qx : ℝ) : ℝ :=
  p^2/2+c^2/2+c*pT+k*qx^2/2

def radiationEnergy (c k p qx : ℝ) : ℝ := (p^2+k*qx^2)/(2*c)
def physicalDensity (c k p qx : ℝ) : ℝ := c/2+radiationEnergy c k p qx

theorem scalar_constraint_solved (c k pT p qx : ℝ) (hc : c ≠ 0) :
    gaugedConstraint c k pT p qx = 0 ↔ pT = -physicalDensity c k p qx := by
  have hid : gaugedConstraint c k pT p qx = c*(pT+physicalDensity c k p qx) := by
    dsimp [gaugedConstraint, physicalDensity, radiationEnergy]
    field_simp
    ring
  rw [hid, mul_eq_zero]
  simp only [hc, false_or]
  constructor <;> intro h <;> linarith

theorem radiationEnergy_nonneg (c k p qx : ℝ) (hc : 0 < c) (hk : 0 ≤ k) :
    0 ≤ radiationEnergy c k p qx := by
  unfold radiationEnergy
  positivity

theorem physicalDensity_positive (c k p qx : ℝ) (hc : 0 < c) (hk : 0 ≤ k) :
    0 < physicalDensity c k p qx := by
  have he := radiationEnergy_nonneg c k p qx hc hk
  dsimp [physicalDensity]
  linarith

/-- With prefactor=a*exp(-T-L/2)>0 the lapse is positive and T-dot=1. -/
theorem areal_clock_lapse (prefactor c : ℝ) (he : 0 < prefactor) (hc : 0 < c) :
    0 < 1/(prefactor*c) ∧ (1/(prefactor*c))*(-prefactor*(-c)) = 1 := by
  constructor
  · positivity
  · field_simp

theorem physicalDensity_deriv_p (c k p qx : ℝ) :
    HasDerivAt (fun u => physicalDensity c k u qx) (p/c) p := by
  have hd := ((((hasDerivAt_id p).pow 2).add_const (k*qx^2)).div_const (2*c)).const_add (c/2)
  convert hd using 1
  dsimp
  ring

theorem physicalDensity_deriv_gradient (c k p qx : ℝ) :
    HasDerivAt (fun u => physicalDensity c k p u) (k*qx/c) qx := by
  have hd := (((((hasDerivAt_id qx).pow 2).const_mul k).const_add (p^2)).div_const (2*c)).const_add (c/2)
  convert hd using 1
  dsimp
  ring

/-- In areal gauge the remaining spatial constraint determines L'. -/
theorem spatial_constraint_solved (c p qx lx : ℝ) (hc : c ≠ 0) :
    p*qx-c*lx = 0 ↔ lx = p*qx/c := by
  constructor <;> intro h
  · apply (eq_div_iff hc).2
    nlinarith
  · rw [h]
    field_simp
    ring

def metricTimeRate (c k p qx : ℝ) : ℝ := -1/2+(p^2+k*qx^2)/(2*c^2)

/-- Original Hamiltonian L-dot agrees with the reduced reconstruction. -/
theorem metric_time_from_original (c k p qx : ℝ) (hc : c ≠ 0) :
    ((-c)-(-physicalDensity c k p qx))/c = metricTimeRate c k p qx := by
  dsimp [physicalDensity, radiationEnergy, metricTimeRate]
  field_simp
  ring

/-- L'_tau=(L_tau)' when Q_tau=p/c and p_tau=k Q''/c. This is the
    compatibility condition needed to reconstruct the metric locally. -/
theorem metric_reconstruction_compatible (c k p qx px qxx : ℝ) :
    ((k*qxx/c)*qx+p*(px/c))/c = (p*px+k*qx*qxx)/c^2 := by
  ring

/-- The residual global momentum condition has a local divergence law. -/
theorem momentum_balance (c k p qx px qxx : ℝ) :
    (k*qxx/c)*qx+p*(px/c) = (p*px+k*qx*qxx)/c := by ring

/-- Explicit time dependence k_tau=2k supplies energy; no false energy
    conservation claim is made. The flux is k*p*Q'/c^2. -/
theorem local_energy_balance (c k p qx px qxx : ℝ) :
    p*(k*qxx/c)/c+k*qx*(px/c)/c+k*qx^2/c =
      k*(px*qx+p*qxx)/c^2+k*qx^2/c := by ring

theorem energy_source_bound (c k p qx : ℝ) (hc : 0 < c) (hk : 0 ≤ k) :
    0 ≤ k*qx^2/c ∧ k*qx^2/c ≤ 2*radiationEnergy c k p qx := by
  constructor
  · positivity
  · dsimp [radiationEnergy]
    have hid : 2*((p^2+k*qx^2)/(2*c))-k*qx^2/c = p^2/c := by ring
    have hn := div_nonneg (sq_nonneg p) (le_of_lt hc)
    nlinarith

/-- The eliminated pT equation is consistent with the wave and spatial
    constraint, not merely with the algebraic scalar-constraint solve. -/
theorem eliminated_momentum_equation (c k p qx px qxx : ℝ) :
    -(p*(k*qxx/c)/c+k*qx*(px/c)/c+k*qx^2/c) =
      -k/c*(qx^2+(px*qx+p*qxx)/c) := by ring

/-- Converting log-area tau to area t gives the polarized wave equation. -/
theorem area_time_wave_equation (t c r qt qtt qxx : ℝ) (ht : t ≠ 0)
    (hlog : t^2*qtt+t*qt = r*t^2*qxx/c^2) :
    qtt+qt/t = r*qxx/c^2 := by
  have h := congrArg (fun u : ℝ => u/t^2) hlog
  field_simp at h ⊢
  nlinarith

/-- With the normal-bracket normalization a*b=1, the wave coefficient equals
    the null-cone coefficient of the reconstructed lapse and spatial metric. -/
theorem wave_metric_cone (a b c : ℝ) (ha : a ≠ 0) (hab : a*b = 1) :
    (b/a)/c^2 = 1/(a^2*c^2) := by
  have hb : b = 1/a := (eq_div_iff ha).2 (by nlinarith [hab])
  rw [hb]
  ring

/-- Each spatial Fourier mode obeys q'=p/c, p'=-k*q/c, k'=2k.
    Its exact energy derivative supplies a cutoff-independent estimate. -/
theorem mode_energy_derivative (c : ℝ) (q p k : ℝ → ℝ) (t : ℝ)
    (hq : HasDerivAt q (p t/c) t) (hp : HasDerivAt p (-k t*q t/c) t)
    (hk : HasDerivAt k (2*k t) t) :
    HasDerivAt (fun s => radiationEnergy c (k s) (p s) (q s))
      (k t*(q t)^2/c) t := by
  have hd := ((hp.pow 2).add (hk.mul (hq.pow 2))).div_const (2*c)
  convert hd using 1
  dsimp
  ring

/-- Actual finite-time stability for any differentiable mode solution.
    No uniform bound on its frequency is required. -/
theorem mode_energy_bound (c a b : ℝ) (hc : 0 < c) (hab : a ≤ b)
    (q p k : ℝ → ℝ)
    (hkpos : ∀ t ∈ Set.Icc a b, 0 ≤ k t)
    (hq : ∀ t ∈ Set.Icc a b, HasDerivAt q (p t/c) t)
    (hp : ∀ t ∈ Set.Icc a b, HasDerivAt p (-k t*q t/c) t)
    (hk : ∀ t ∈ Set.Icc a b, HasDerivAt k (2*k t) t) :
    radiationEnergy c (k b) (p b) (q b) ≤
      radiationEnergy c (k a) (p a) (q a) * Real.exp (2*(b-a)) := by
  let E := fun t => radiationEnergy c (k t) (p t) (q t)
  have hE : ∀ t ∈ Set.Icc a b, HasDerivAt E (k t*(q t)^2/c) t := by
    intro t ht
    exact mode_energy_derivative c q p k t (hq t ht) (hp t ht) (hk t ht)
  have hpos : ∀ t ∈ Set.Icc a b, 0 ≤ E t := by
    intro t ht
    exact radiationEnergy_nonneg c (k t) (p t) (q t) hc (hkpos t ht)
  have hcont : ContinuousOn E (Set.Icc a b) :=
    fun t ht => (hE t ht).continuousAt.continuousWithinAt
  have hright : ∀ t ∈ Set.Ico a b,
      HasDerivWithinAt E (k t*(q t)^2/c) (Set.Ici t) t := by
    intro t ht
    exact (hE t ⟨ht.1, le_of_lt ht.2⟩).hasDerivWithinAt
  have hinitial : ‖E a‖ ≤ E a := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos a ⟨le_refl a, hab⟩)]
  have hbound : ∀ t ∈ Set.Ico a b, ‖k t*(q t)^2/c‖ ≤ 2*‖E t‖+0 := by
    intro t ht
    have hclosed : t ∈ Set.Icc a b := ⟨ht.1, le_of_lt ht.2⟩
    have hs := energy_source_bound c (k t) (p t) (q t) hc (hkpos t hclosed)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hs.1,
      abs_of_nonneg (hpos t hclosed), add_zero] using hs.2
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hcont hright hinitial hbound
    b ⟨hab, le_refl b⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos b ⟨hab, le_refl b⟩),
    gronwallBound_ε0] using h

/-- The same growth factor controls every finite mode cutoff. This proves
    stability of supplied solutions, not their existence or a spin limit. -/
theorem finite_mode_energy_bound {ι : Type*} [Fintype ι]
    (c a b : ℝ) (hc : 0 < c) (hab : a ≤ b) (q p k : ι → ℝ → ℝ)
    (hkpos : ∀ i t, t ∈ Set.Icc a b → 0 ≤ k i t)
    (hq : ∀ i t, t ∈ Set.Icc a b → HasDerivAt (q i) (p i t/c) t)
    (hp : ∀ i t, t ∈ Set.Icc a b → HasDerivAt (p i) (-k i t*q i t/c) t)
    (hk : ∀ i t, t ∈ Set.Icc a b → HasDerivAt (k i) (2*k i t) t) :
    (∑ i, radiationEnergy c (k i b) (p i b) (q i b)) ≤
      (∑ i, radiationEnergy c (k i a) (p i a) (q i a))*Real.exp (2*(b-a)) := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ =>
    mode_energy_bound c a b hc hab (q i) (p i) (k i) (hkpos i) (hq i) (hp i) (hk i)

#print axioms areal_one_form
#print axioms scalar_constraint_solved
#print axioms physicalDensity_positive
#print axioms areal_clock_lapse
#print axioms physicalDensity_deriv_p
#print axioms physicalDensity_deriv_gradient
#print axioms spatial_constraint_solved
#print axioms metric_reconstruction_compatible
#print axioms energy_source_bound
#print axioms eliminated_momentum_equation
#print axioms area_time_wave_equation
#print axioms wave_metric_cone
#print axioms mode_energy_derivative
#print axioms mode_energy_bound
#print axioms finite_mode_energy_bound

end
end UnifiedTheory.Audit.KFCausalArealTensorDynamics
