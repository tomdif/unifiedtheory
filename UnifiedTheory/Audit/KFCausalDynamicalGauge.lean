/-
  Finite-group quantum matter/link dynamics with exact Gauss constraints.
  Matter is a regular group rotor at every vertex, not a Weyl fermion.
  The graph, group, interaction, and electric update remain specified inputs.
  This does not construct continuous Yang-Mills theory, GR, or a TOE.
-/
import UnifiedTheory.Audit.KFCausalGaugeWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalDynamicalGauge
noncomputable section
open scoped BigOperators

section Configurations
variable {V E G : Type*} [Group G]

abbrev Config (V E G : Type*) := (V → G) × (E → G)

def gauge (s t : E → V) (h : V → G) (c : Config V E G) : Config V E G :=
  (fun v => h v * c.1 v, fun e => h (s e) * c.2 e * (h (t e))⁻¹)

def relative (s t : E → V) (c : Config V E G) (e : E) : G :=
  (c.1 (s e))⁻¹ * c.2 e * c.1 (t e)

def canonical (r : E → G) : Config V E G := (fun _ => 1, r)

theorem gauge_one (s t : E → V) (c : Config V E G) :
    gauge s t (fun _ => 1) c = c := by
  ext <;> simp [gauge]

theorem gauge_comp (s t : E → V) (h k : V → G) (c : Config V E G) :
    gauge s t h (gauge s t k c) = gauge s t (fun v => h v * k v) c := by
  ext <;> simp [gauge, mul_assoc]

theorem relative_gauge (s t : E → V) (h : V → G) (c : Config V E G) :
    relative s t (gauge s t h c) = relative s t c := by
  funext e
  simp [relative, gauge, mul_assoc]

theorem gauge_to_canonical (s t : E → V) (c : Config V E G) :
    gauge s t (fun v => (c.1 v)⁻¹) c = canonical (relative s t c) := by
  ext <;> simp [gauge, canonical, relative]

theorem gauge_from_canonical (s t : E → V) (c : Config V E G) :
    gauge s t c.1 (canonical (relative s t c)) = c := by
  ext <;> simp [gauge, canonical, relative, mul_assoc]

/-- Regular matter at every vertex makes the gauge action free and gives
complete orbit coordinates. This is not the pure-gauge orbit formula. -/
theorem orbit_iff_relative (s t : E → V) (c d : Config V E G) :
    (∃ h, gauge s t h c = d) ↔ relative s t c = relative s t d := by
  constructor
  · rintro ⟨h, rfl⟩
    exact (relative_gauge s t h c).symm
  · intro hr
    refine ⟨fun v => d.1 v * (c.1 v)⁻¹, ?_⟩
    rw [← gauge_comp, gauge_to_canonical, hr, gauge_from_canonical]

def Physical (s t : E → V) (psi : Config V E G → ℂ) : Prop :=
  ∀ h c, psi (gauge s t h c) = psi c

theorem physical_iff_relative (s t : E → V) (psi : Config V E G → ℂ) :
    Physical s t psi ↔ ∃ f : (E → G) → ℂ, ∀ c, psi c = f (relative s t c) := by
  constructor
  · intro hp
    refine ⟨fun r => psi (canonical r), ?_⟩
    intro c
    have h := hp (fun v => (c.1 v)⁻¹) c
    rw [gauge_to_canonical] at h
    exact h.symm
  · rintro ⟨f, hf⟩ h c
    rw [hf, hf, relative_gauge]

def phase (s t : E → V) (w : (E → G) → ℂ)
    (psi : Config V E G → ℂ) (c : Config V E G) : ℂ :=
  w (relative s t c) * psi c

theorem phase_physical (s t : E → V) (w : (E → G) → ℂ)
    (psi : Config V E G → ℂ) (hp : Physical s t psi) :
    Physical s t (phase s t w psi) := by
  intro h c
  simp only [phase, relative_gauge, hp h c]

variable [DecidableEq E]

def replaceLink (c : Config V E G) (e : E) (u : G) : Config V E G :=
  (c.1, Function.update c.2 e u)

theorem gauge_replaceLink (s t : E → V) (h : V → G)
    (c : Config V E G) (e : E) (u : G) :
    gauge s t h (replaceLink c e u) =
      replaceLink (gauge s t h c) e (h (s e) * u * (h (t e))⁻¹) := by
  ext j
  · rfl
  · by_cases hj : j = e
    · subst j
      simp [gauge, replaceLink]
    · simp [gauge, replaceLink, hj]

variable [Fintype G]

def linkMean (e : E) (psi : Config V E G → ℂ) (c : Config V E G) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ u : G, psi (replaceLink c e u)

theorem linkMean_physical (s t : E → V) (e : E)
    (psi : Config V E G → ℂ) (hp : Physical s t psi) :
    Physical s t (linkMean e psi) := by
  intro h c
  unfold linkMean
  congr 1
  let p : G ≃ G := (Equiv.mulLeft (h (s e))).trans (Equiv.mulRight ((h (t e))⁻¹))
  calc
    _ = ∑ u : G, psi (replaceLink (gauge s t h c) e (p u)) :=
      (Equiv.sum_comp p _).symm
    _ = ∑ u : G, psi (replaceLink c e u) := by
      apply Finset.sum_congr rfl
      intro u _
      change psi (replaceLink (gauge s t h c) e
        (h (s e) * u * (h (t e))⁻¹)) = _
      rw [← gauge_replaceLink, hp h]

theorem linkMean_idempotent (e : E) (psi : Config V E G → ℂ) :
    linkMean e (linkMean e psi) = linkMean e psi := by
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  funext c
  simp [linkMean, replaceLink, Function.update_idem, hn]

/-- Convolution by a conjugation-invariant kernel permits electric dynamics
that distinguish irreducible sectors of a non-Abelian group. -/
def linkConvolution (e : E) (k : G → ℂ) (psi : Config V E G → ℂ)
    (c : Config V E G) : ℂ :=
  ∑ u : G, k u * psi (replaceLink c e (u * c.2 e))

theorem linkConvolution_physical (s t : E → V) (e : E) (k : G → ℂ)
    (hk : ∀ a u, k (a * u * a⁻¹) = k u)
    (psi : Config V E G → ℂ) (hp : Physical s t psi) :
    Physical s t (linkConvolution e k psi) := by
  intro h c
  unfold linkConvolution
  let p : G ≃ G := (Equiv.mulLeft (h (s e))).trans (Equiv.mulRight ((h (s e))⁻¹))
  calc
    _ = ∑ u : G, k (p u) * psi (replaceLink (gauge s t h c) e
        (p u * (gauge s t h c).2 e)) := (Equiv.sum_comp p _).symm
    _ = ∑ u : G, k u * psi (replaceLink c e (u * c.2 e)) := by
      apply Finset.sum_congr rfl
      intro u _
      change k (h (s e) * u * (h (s e))⁻¹) * psi
        (replaceLink (gauge s t h c) e
          ((h (s e) * u * (h (s e))⁻¹) * (h (s e) * c.2 e * (h (t e))⁻¹))) = _
      rw [hk]
      have hv : (h (s e) * u * (h (s e))⁻¹) *
          (h (s e) * c.2 e * (h (t e))⁻¹) =
          h (s e) * (u * c.2 e) * (h (t e))⁻¹ := by group
      rw [hv, ← gauge_replaceLink, hp h]

def classElectric (e : E) (k : G → ℂ) (psi : Config V E G → ℂ)
    (c : Config V E G) : ℂ :=
  psi c - linkConvolution e k (linkConvolution e k psi) c -
    Complex.I * linkConvolution e k psi c

theorem classElectric_physical (s t : E → V) (e : E) (k : G → ℂ)
    (hk : ∀ a u, k (a * u * a⁻¹) = k u)
    (psi : Config V E G → ℂ) (hp : Physical s t psi) :
    Physical s t (classElectric e k psi) := by
  have hc := linkConvolution_physical s t e k hk psi hp
  have hcc := linkConvolution_physical s t e k hk _ hc
  intro h c
  simp only [classElectric, hp h c, hc h c, hcc h c]

def classStep (s t : E → V) (e : E) (k : G → ℂ) (w : (E → G) → ℂ)
    (psi : Config V E G → ℂ) : Config V E G → ℂ :=
  classElectric e k (phase s t w psi)

theorem classStep_physical (s t : E → V) (e : E) (k : G → ℂ)
    (hk : ∀ a u, k (a * u * a⁻¹) = k u) (w : (E → G) → ℂ)
    (psi : Config V E G → ℂ) (hp : Physical s t psi) :
    Physical s t (classStep s t e k w psi) :=
  classElectric_physical s t e k hk _ (phase_physical s t w psi hp)

theorem classIterate_physical (s t : E → V) (e : E) (k : G → ℂ)
    (hk : ∀ a u, k (a * u * a⁻¹) = k u) (w : (E → G) → ℂ)
    (psi : Config V E G → ℂ) (hp : Physical s t psi) (n : ℕ) :
    Physical s t ((classStep s t e k w)^[n] psi) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact classStep_physical s t e k hk w _ ih

def electric (e : E) (psi : Config V E G → ℂ) (c : Config V E G) : ℂ :=
  psi c - 2 * linkMean e psi c

theorem electric_physical (s t : E → V) (e : E)
    (psi : Config V E G → ℂ) (hp : Physical s t psi) :
    Physical s t (electric e psi) := by
  intro h c
  simp only [electric, hp h c, linkMean_physical s t e psi hp h c]

/-- A concrete joint matter/link update preserves all Gauss constraints. -/
def step (s t : E → V) (e : E) (w : (E → G) → ℂ)
    (psi : Config V E G → ℂ) : Config V E G → ℂ :=
  electric e (phase s t w psi)

theorem step_physical (s t : E → V) (e : E) (w : (E → G) → ℂ)
    (psi : Config V E G → ℂ) (hp : Physical s t psi) :
    Physical s t (step s t e w psi) :=
  electric_physical s t e _ (phase_physical s t w psi hp)

theorem iterate_physical (s t : E → V) (e : E) (w : (E → G) → ℂ)
    (psi : Config V E G → ℂ) (hp : Physical s t psi) (n : ℕ) :
    Physical s t ((step s t e w)^[n] psi) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact step_physical s t e w _ ih
end Configurations

section Gates
variable {R : Type*} [Ring R] [StarRing R]

def reflection (P : R) : R := 1 - (P + P)

omit [StarRing R] in
theorem reflection_square (P : R) (hPP : P * P = P) :
    reflection P * reflection P = 1 := by
  unfold reflection
  noncomm_ring [hPP]

theorem reflection_selfadjoint (P : R) (hP : star P = P) :
    star (reflection P) = reflection P := by
  simp [reflection, hP]

theorem reflection_unitary (P : R) (hP : star P = P) (hPP : P * P = P) :
    star (reflection P) * reflection P = 1 := by
  rw [reflection_selfadjoint P hP, reflection_square P hPP]
end Gates

open Matrix
section UniformProjection
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def uniformProjector : Matrix ι ι ℂ := fun _ _ => (Fintype.card ι : ℂ)⁻¹

omit [Nonempty ι] in
theorem uniformProjector_selfadjoint :
    (uniformProjector (ι := ι))ᴴ = uniformProjector := by
  ext i j
  simp [uniformProjector, Matrix.conjTranspose_apply]

theorem uniformProjector_square :
    uniformProjector (ι := ι) * uniformProjector = uniformProjector := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext i j
  simp [uniformProjector, Matrix.mul_apply, hn]

variable [DecidableEq ι]

theorem uniform_reflection_unitary :
    (reflection (uniformProjector (ι := ι)))ᴴ * reflection uniformProjector = 1 :=
  reflection_unitary _ uniformProjector_selfadjoint uniformProjector_square
end UniformProjection

section CubicGate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cubicRotation (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  1 - A * A - Complex.I • A

/-- For a self-adjoint A with spectrum in {-1,0,1}, this is exp(-i pi A/2).
The polynomial proof itself requires no spectral theorem or exponential. -/
theorem cubicRotation_unitary (A : Matrix ι ι ℂ)
    (hA : Aᴴ = A) (h3 : A * A * A = A) :
    (cubicRotation A)ᴴ * cubicRotation A = 1 := by
  simp only [cubicRotation, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hA, Complex.star_def,
    Complex.conj_I]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc, h3]
  match_scalars <;> simp
end CubicGate

section Histories
variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
open UnifiedTheory.Audit.KFCausalGaugeWalk (propagator)

theorem intertwined_history (W : Matrix a b ℂ)
    (F : ℕ → Matrix a a ℂ) (f : ℕ → Matrix b b ℂ)
    (hF : ∀ n, F n * W = W * f n) (n : ℕ) :
    propagator F n * W = W * propagator f n := by
  induction n with
  | zero => simp [propagator]
  | succ n ih =>
    simp only [propagator]
    rw [Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hF n, Matrix.mul_assoc]

omit [DecidableEq a] in
theorem isometry_branch_weight (W : Matrix a b ℂ) (hW : Wᴴ * W = 1)
    (rho : Matrix b b ℂ) : (W * rho * Wᴴ).trace = rho.trace := by
  rw [Matrix.trace_mul_cycle, hW, Matrix.one_mul]
end Histories

#print axioms gauge_comp
#print axioms relative_gauge
#print axioms gauge_to_canonical
#print axioms orbit_iff_relative
#print axioms physical_iff_relative
#print axioms phase_physical
#print axioms gauge_replaceLink
#print axioms linkMean_physical
#print axioms linkMean_idempotent
#print axioms linkConvolution_physical
#print axioms classElectric_physical
#print axioms classStep_physical
#print axioms classIterate_physical
#print axioms electric_physical
#print axioms step_physical
#print axioms iterate_physical
#print axioms reflection_unitary
#print axioms uniformProjector_selfadjoint
#print axioms uniformProjector_square
#print axioms uniform_reflection_unitary
#print axioms cubicRotation_unitary
#print axioms intertwined_history
#print axioms isometry_branch_weight

end
end UnifiedTheory.Audit.KFCausalDynamicalGauge
