/-
  Audit/KFCausalAharonovBohm.lean
  — THE AHARONOV–BOHM EFFECT ON ORDERS, GRAPHS AND HISTORY PAIRS

  Three pieces, each tied to structures this repository already has.

  Part I — order cocycles.  A `G`-valued cochain `U(x,y)` on the relations
  `x ≤ y` of a preorder with `U(x,z) = U(x,y)·U(y,z)` (flatness on every
  2-chain).
  * `coboundary_of_directed`: on an upward-directed preorder EVERY such
    cocycle is a coboundary, `U(x,y) = g(x)·g(y)⁻¹`, for any group `G`
    (non-Abelian included).  Generalizes CAG's `cone_kills_H1` (which needs
    a global top) to common upper bounds.  Consequence: a cocycle imposed on
    all relations of a directed causal order carries no AB phase.
  * `crown_cocycle_not_coboundary`: the finite caveat is real.  The crown
    (two minimal below two maximal elements, the circle poset P₄(S¹)) carries
    a ℤˣ-valued cocycle with holonomy −1 around its 4-cycle, so it is not a
    coboundary.  Finite causal sets are not directed, and whether they carry
    global cocycle holonomy is a question about the H¹ of their order complex.

  Part II — the decoherence functional with flux.  Path amplitudes are
  dressed by the U(1) holonomy of a `DiscreteConnection` (DiscreteBundles /
  DiscreteAmbroseSinger):
  * `wilson_gauge_covariant` / `wilson_gauge_invariant`: for two paths with
    common endpoints, `hol(γ₁)·hol(γ₂)⁻¹` is gauge-conjugated (invariant for
    Abelian `G`).
  * `dressedD_diagonal`: the diagonal of `D` is flux-independent.
  * `dressedD_offdiag`: off-diagonal entries pick up the Wilson factor of the
    closed curve γ₁∘γ₂⁻¹, and it is gauge invariant (`dressedD_gauge_invariant`).
  * `dressed_strong_positivity`: strong positivity survives the dressing.
  * `two_history_flux` / `unitarity_quantizes_with_flux`: in the
    Born-from-growth functional of KFCausalQuantumMeasure, a flux Φ through
    the two-history diamond enters ONLY the interference term, and the
    normalization condition μ(Ω)=1 becomes cos(θ₁ − θ₂ + Φ) = 0: the
    "unitarity quantizes the action gap" condition is flux-shifted.
    `two_history_flux_periodic`: Byers–Yang periodicity Φ ↦ Φ + 2π.

  Part III — the ring with time-dependent flux (the exactly solvable model
  of ring_time_dependent_flux.py).  `ring_rigid_rotation`: for ANY flux
  history, the evolved wavefunction is exactly a global phase times the
  static-initial-flux evolution rigidly rotated by ∫(α − αᵢ)dt.  The three
  published answers (time-averaged flux / initial flux / cancellation) are
  readouts of this one identity against different references;
  `ring_lab_fringe_shift` is the lab-frame bookkeeping at the meeting time.

  Zero sorry.  Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.LayerA.DiscreteAmbroseSinger
import UnifiedTheory.Audit.KFCausalQuantumMeasure

set_option autoImplicit false

open Complex

namespace UnifiedTheory.Audit.KFCausalAharonovBohm

/-! ## Part I: cocycles on the relations of a preorder -/

/-- A `G`-valued 1-cochain on the relations of a preorder that is flat on
every 2-chain `x ≤ y ≤ z`. -/
structure OrderCocycle (α : Type*) [Preorder α] (G : Type*) [Group G] where
  U : α → α → G
  comp : ∀ x y z, x ≤ y → y ≤ z → U x z = U x y * U y z

namespace OrderCocycle

variable {α : Type*} [Preorder α] {G : Type*} [Group G] (c : OrderCocycle α G)

theorem refl_eq_one (x : α) : c.U x x = 1 :=
  mul_left_cancel ((c.comp x x x le_rfl le_rfl).symm.trans (mul_one _).symm)

/-- Climbing to any higher common upper bound does not change
`U(x,w)·U(o,w)⁻¹`. -/
theorem climb (x o v w : α) (hx : x ≤ v) (ho : o ≤ v) (hv : v ≤ w) :
    c.U x v * (c.U o v)⁻¹ = c.U x w * (c.U o w)⁻¹ := by
  rw [c.comp x v w hx hv, c.comp o v w ho hv]
  group

/-- `U(x,w)·U(o,w)⁻¹` is the same for every common upper bound `w` of `x`
and `o`. -/
theorem upperBound_indep [IsDirected α (· ≤ ·)] (x o w₁ w₂ : α)
    (h₁x : x ≤ w₁) (h₁o : o ≤ w₁) (h₂x : x ≤ w₂) (h₂o : o ≤ w₂) :
    c.U x w₁ * (c.U o w₁)⁻¹ = c.U x w₂ * (c.U o w₂)⁻¹ := by
  obtain ⟨w, hw₁, hw₂⟩ := directed_of (· ≤ ·) w₁ w₂
  rw [c.climb x o w₁ w h₁x h₁o hw₁, c.climb x o w₂ w h₂x h₂o hw₂]

/-- **Every cocycle on a directed order is a coboundary**, for any group. -/
theorem coboundary_of_directed [IsDirected α (· ≤ ·)] (o : α) :
    ∃ g : α → G, ∀ x y, x ≤ y → c.U x y = g x * (g y)⁻¹ := by
  choose u hux huo using fun x : α => directed_of (· ≤ ·) x o
  refine ⟨fun x => c.U x (u x) * (c.U o (u x))⁻¹, fun x y hxy => ?_⟩
  have hx := c.upperBound_indep x o (u y) (u x)
    (hxy.trans (hux y)) (huo y) (hux x) (huo x)
  show c.U x y = c.U x (u x) * (c.U o (u x))⁻¹ * (c.U y (u y) * (c.U o (u y))⁻¹)⁻¹
  rw [← hx, c.comp x y (u y) hxy (hux y)]
  group

/-- A global top makes the order directed: the CAG `cone_kills_H1` case. -/
theorem coboundary_of_top (top o : α) (htop : ∀ x, x ≤ top) :
    ∃ g : α → G, ∀ x y, x ≤ y → c.U x y = g x * (g y)⁻¹ := by
  haveI : IsDirected α (· ≤ ·) := ⟨fun a b => ⟨top, htop a, htop b⟩⟩
  exact c.coboundary_of_directed o

end OrderCocycle

/-- Holonomy around the 4-cycle `a < c > b < d > a` of two minimal and two
maximal elements: the elementary AB loop of an order (a pair of two-chain
diamonds sharing their endpoints' antichains). -/
def crownHol {α G : Type*} [Group G] (U : α → α → G) (a b c d : α) : G :=
  U a c * (U b c)⁻¹ * U b d * (U a d)⁻¹

/-- Coboundaries have trivial crown holonomy. -/
theorem crownHol_coboundary {α G : Type*} [Group G] (g : α → G) (a b c d : α) :
    crownHol (fun x y => g x * (g y)⁻¹) a b c d = 1 := by
  unfold crownHol
  group

/-- On a directed order the crown holonomy of every cocycle is trivial. -/
theorem crownHol_directed {α : Type*} [Preorder α] [IsDirected α (· ≤ ·)]
    {G : Type*} [Group G] (c : OrderCocycle α G) (a b x y : α)
    (hax : a ≤ x) (hbx : b ≤ x) (hby : b ≤ y) (hay : a ≤ y) :
    crownHol c.U a b x y = 1 := by
  obtain ⟨g, hg⟩ := c.coboundary_of_directed a
  unfold crownHol
  rw [hg a x hax, hg b x hbx, hg b y hby, hg a y hay]
  group

/-! ### The crown: a finite order with a non-trivial cocycle -/

/-- The crown poset P₄(S¹): `a, b` minimal, `c, d` maximal, every minimal
below every maximal. -/
inductive Crown | a | b | c | d
  deriving DecidableEq, Fintype

namespace Crown

def leB : Crown → Crown → Bool
  | a, a | b, b | c, c | d, d => true
  | a, c | a, d | b, c | b, d => true
  | _, _ => false

instance : PartialOrder Crown where
  le x y := leB x y = true
  le_refl x := by cases x <;> rfl
  le_trans x y z :=
    (by decide : ∀ x y z : Crown, leB x y = true → leB y z = true →
      leB x z = true) x y z
  le_antisymm x y :=
    (by decide : ∀ x y : Crown, leB x y = true → leB y x = true → x = y) x y

instance : DecidableRel (α := Crown) (· ≤ ·) :=
  fun x y => inferInstanceAs (Decidable (leB x y = true))

/-- A ℤˣ-valued cochain: `−1` on the relation `b < d`, `1` elsewhere. -/
def twist (x y : Crown) : ℤˣ := if x = b ∧ y = d then -1 else 1

/-- It is a cocycle: the crown has no 2-chains with three distinct elements. -/
def twistCocycle : OrderCocycle Crown ℤˣ where
  U := twist
  comp x y z :=
    (by decide : ∀ x y z : Crown, leB x y = true → leB y z = true →
      twist x z = twist x y * twist y z) x y z

theorem twist_hol : crownHol twist a b c d = -1 := by decide

/-- **The finite caveat**: a finite (non-directed) order can carry a flat
cocycle with non-trivial holonomy, so the directed-order triviality lemma
does not transfer to finite causal sets without further structure. -/
theorem crown_cocycle_not_coboundary :
    ¬ ∃ g : Crown → ℤˣ, ∀ x y, x ≤ y → twistCocycle.U x y = g x * (g y)⁻¹ := by
  rintro ⟨g, hg⟩
  have h : crownHol twist a b c d = 1 := by
    unfold crownHol
    rw [show twist a c = g a * (g c)⁻¹ from hg a c (by decide),
      show twist b c = g b * (g c)⁻¹ from hg b c (by decide),
      show twist b d = g b * (g d)⁻¹ from hg b d (by decide),
      show twist a d = g a * (g d)⁻¹ from hg a d (by decide)]
    group
  rw [twist_hol] at h
  exact absurd h (by decide)

/-- Hence the crown is not directed. -/
theorem not_directed : ¬ IsDirected Crown (· ≤ ·) := by
  intro h
  exact crown_cocycle_not_coboundary (twistCocycle.coboundary_of_directed a)

end Crown

/-! ## Part II: two-path Wilson factor and the dressed decoherence functional -/

section Wilson

open UnifiedTheory.LayerA.DiscreteBundles UnifiedTheory.LayerA.DiscreteAmbroseSinger

variable {Γ : DirectedGraph} {G : Type*} [Group G]

/-- The Wilson factor of two paths with common endpoints: the holonomy of
the closed curve `γ₁ ∘ γ₂⁻¹` (the two-chain diamond of a causal set). -/
def wilson (conn : DiscreteConnection Γ G) (p₁ p₂ : GraphPath Γ) : G :=
  hol conn p₁.edges * (hol conn p₂.edges)⁻¹

/-- Gauge covariance: the Wilson factor of two co-terminal paths is
conjugated by the gauge element at the common source. -/
theorem wilson_gauge_covariant (conn : DiscreteConnection Γ G)
    (g : GaugeTransformation Γ G) (p₁ p₂ : GraphPath Γ)
    (h₁ : 0 < p₁.edges.length) (h₂ : 0 < p₂.edges.length)
    (hs : Γ.src (p₁.edges[0]'h₁) = Γ.src (p₂.edges[0]'h₂))
    (ht : Γ.tgt (p₁.edges[p₁.edges.length - 1]'(by omega))
        = Γ.tgt (p₂.edges[p₂.edges.length - 1]'(by omega))) :
    wilson (gaugeTransform conn g) p₁ p₂
      = (g (Γ.src (p₁.edges[0]'h₁)))⁻¹ * wilson conn p₁ p₂
        * g (Γ.src (p₁.edges[0]'h₁)) := by
  unfold wilson
  rw [hol_gaugeTransform_telescope conn g p₁.edges h₁ p₁.composable,
    hol_gaugeTransform_telescope conn g p₂.edges h₂ p₂.composable, ht, hs]
  group

/-- Abelian case: the Wilson factor of co-terminal paths is gauge invariant. -/
theorem wilson_gauge_invariant {A : Type*} [CommGroup A]
    (conn : DiscreteConnection Γ A) (g : GaugeTransformation Γ A)
    (p₁ p₂ : GraphPath Γ)
    (h₁ : 0 < p₁.edges.length) (h₂ : 0 < p₂.edges.length)
    (hs : Γ.src (p₁.edges[0]'h₁) = Γ.src (p₂.edges[0]'h₂))
    (ht : Γ.tgt (p₁.edges[p₁.edges.length - 1]'(by omega))
        = Γ.tgt (p₂.edges[p₂.edges.length - 1]'(by omega))) :
    wilson (gaugeTransform conn g) p₁ p₂ = wilson conn p₁ p₂ := by
  rw [wilson_gauge_covariant conn g p₁ p₂ h₁ h₂ hs ht, mul_comm, ← mul_assoc,
    mul_inv_cancel, one_mul]

end Wilson

section Dressed

variable {H : Type*}

/-- Amplitude dressed by a phase `w γ` (the U(1) holonomy of history `γ`). -/
def dressedAmp (A : H → ℂ) (w : H → Circle) (γ : H) : ℂ := A γ * (w γ : ℂ)

/-- The dressed decoherence functional. -/
def dressedD (A : H → ℂ) (w : H → Circle) (γ γ' : H) : ℂ :=
  dressedAmp A w γ * (starRingEnd ℂ) (dressedAmp A w γ')

/-- Off-diagonal entries pick up exactly the Wilson factor `w γ · w γ'⁻¹`. -/
theorem dressedD_offdiag (A : H → ℂ) (w : H → Circle) (γ γ' : H) :
    dressedD A w γ γ'
      = A γ * (starRingEnd ℂ) (A γ') * ((w γ * (w γ')⁻¹ : Circle) : ℂ) := by
  unfold dressedD dressedAmp
  rw [Circle.coe_mul, Circle.coe_inv_eq_conj, map_mul]
  ring

/-- **The diagonal is flux-independent**: the gauge field is invisible to
the probabilities of fine-grained histories. -/
theorem dressedD_diagonal (A : H → ℂ) (w : H → Circle) (γ : H) :
    dressedD A w γ γ = A γ * (starRingEnd ℂ) (A γ) := by
  rw [dressedD_offdiag, mul_inv_cancel, Circle.coe_one, mul_one]

/-- Two phase assignments with the same Wilson factor on a pair of histories
give the same decoherence functional entry: gauge transformations that fix
the Wilson factor of co-terminal histories (`wilson_gauge_invariant`) leave
`D` unchanged. -/
theorem dressedD_gauge_invariant (A : H → ℂ) (w w' : H → Circle) (γ γ' : H)
    (h : w' γ * (w' γ')⁻¹ = w γ * (w γ')⁻¹) :
    dressedD A w' γ γ' = dressedD A w γ γ' := by
  rw [dressedD_offdiag, dressedD_offdiag, h]

/-- **Strong positivity survives the dressing**: every quadratic form of the
dressed functional is a squared norm. -/
theorem dressed_strong_positivity [Fintype H] (A : H → ℂ) (w : H → Circle) (c : H → ℂ) :
    (∑ γ, ∑ γ', c γ * (starRingEnd ℂ) (c γ') * dressedD A w γ γ')
      = (Complex.normSq (∑ γ, c γ * dressedAmp A w γ) : ℂ) := by
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun γ' _ => ?_
  rw [map_mul]
  unfold dressedD
  ring

/-- Two-slit measure: the flux enters only the interference term. -/
theorem two_slit_flux (a₁ a₂ : ℂ) (w₁ w₂ : Circle) :
    Complex.normSq (a₁ * w₁ + a₂ * w₂)
      = Complex.normSq a₁ + Complex.normSq a₂
        + 2 * (a₁ * (starRingEnd ℂ) a₂ * ((w₁ * w₂⁻¹ : Circle) : ℂ)).re := by
  rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul,
    Circle.normSq_coe, Circle.normSq_coe, mul_one, mul_one,
    Circle.coe_mul, Circle.coe_inv_eq_conj, map_mul]
  ring_nf

end Dressed

/-! ### Flux in the Born-from-growth two-history stage -/

open UnifiedTheory.Audit.KFCausalQuantumMeasure in
/-- A flux `Φ` (holonomy `e^{iΦ}` of the closed two-history curve) shifts
the interference term of the repository's two-history stage and nothing
else. -/
theorem two_history_flux (t θ₁ θ₂ Φ : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Complex.normSq ((Real.sqrt t : ℂ) * Complex.exp (θ₁ * Complex.I)
        * Complex.exp (Φ * Complex.I)
      + (Real.sqrt (1-t) : ℂ) * Complex.exp (θ₂ * Complex.I))
      = 1 + 2 * Real.sqrt (t*(1-t)) * Real.cos (θ₁ - θ₂ + Φ) := by
  have h : (Real.sqrt t : ℂ) * Complex.exp (θ₁ * Complex.I)
      * Complex.exp (Φ * Complex.I)
      = (Real.sqrt t : ℂ) * Complex.exp (((θ₁ + Φ : ℝ) : ℂ) * Complex.I) := by
    rw [mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [h, two_history_interference t (θ₁ + Φ) θ₂ ht0 ht1]
  ring_nf

open UnifiedTheory.Audit.KFCausalQuantumMeasure in
/-- **Unitarity quantizes the flux-shifted gap**: with a flux through the
two-history diamond, `μ(Ω) = 1` forces `cos(θ₁ − θ₂ + Φ) = 0`, so the
repository's "unitarity quantizes the action gap" condition is not gauge-
flux-neutral: a change of enclosed flux must be compensated in the action. -/
theorem unitarity_quantizes_with_flux (t θ₁ θ₂ Φ : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hnorm : Complex.normSq ((Real.sqrt t : ℂ) * Complex.exp (θ₁ * Complex.I)
        * Complex.exp (Φ * Complex.I)
      + (Real.sqrt (1-t) : ℂ) * Complex.exp (θ₂ * Complex.I)) = 1) :
    Real.cos (θ₁ - θ₂ + Φ) = 0 := by
  rw [two_history_flux t θ₁ θ₂ Φ ht0.le ht1.le] at hnorm
  have hsq : 0 < Real.sqrt (t*(1-t)) := Real.sqrt_pos.mpr (by nlinarith)
  have h2 : 2 * Real.sqrt (t*(1-t)) * Real.cos (θ₁ - θ₂ + Φ) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h | h
  · linarith
  · exact h

/-- Byers–Yang periodicity of the two-history measure. -/
theorem two_history_flux_periodic (t θ₁ θ₂ Φ : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Complex.normSq ((Real.sqrt t : ℂ) * Complex.exp (θ₁ * Complex.I)
        * Complex.exp (((Φ + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
      + (Real.sqrt (1-t) : ℂ) * Complex.exp (θ₂ * Complex.I))
    = Complex.normSq ((Real.sqrt t : ℂ) * Complex.exp (θ₁ * Complex.I)
        * Complex.exp (Φ * Complex.I)
      + (Real.sqrt (1-t) : ℂ) * Complex.exp (θ₂ * Complex.I)) := by
  rw [two_history_flux t θ₁ θ₂ _ ht0 ht1, two_history_flux t θ₁ θ₂ Φ ht0 ht1]
  rw [show θ₁ - θ₂ + (Φ + 2 * Real.pi) = (θ₁ - θ₂ + Φ) + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

/-! ## Part III: the ring with a time-dependent flux -/

/-- Wavefunction on the ring from finitely many Fourier coefficients. -/
noncomputable def ringPsi (S : Finset ℤ) (c : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ S, c n * Complex.exp ((n : ℂ) * θ * Complex.I)

/-- Exact evolution for `H(t) = ½(n − α(t))²` (ℏ = m = r = 1) over `[0,T]`,
written through `I₁ = ∫α dt` and `I₂ = ∫α² dt`: `H` is diagonal in `n` at
every instant, so this is the exact propagator for any flux history. -/
noncomputable def ringEvolve (T I₁ I₂ : ℝ) (c : ℤ → ℂ) (n : ℤ) : ℂ :=
  c n * Complex.exp (-(1/2 : ℂ) * ((n : ℂ)^2 * T - 2 * n * I₁ + I₂) * Complex.I)

/-- **Rigid-rotation theorem.**  For any flux history with integrals
`I₁, I₂`, the evolved wavefunction equals a global phase times the evolution
under the static initial flux `αᵢ`, rigidly rotated by
`δ = I₁ − αᵢT = ∫(α − αᵢ)dt`.  Every fringe readout of the time-dependent
problem is a readout of this identity. -/
theorem ring_rigid_rotation (S : Finset ℤ) (c : ℤ → ℂ) (T I₁ I₂ αi θ : ℝ) :
    ringPsi S (ringEvolve T I₁ I₂ c) θ
      = Complex.exp (-(1/2 : ℂ) * (I₂ - αi^2 * T) * Complex.I)
        * ringPsi S (ringEvolve T (αi * T) (αi^2 * T) c) (θ + (I₁ - αi * T)) := by
  unfold ringPsi ringEvolve
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, mul_assoc, ← Complex.exp_add,
    mul_assoc (c n), ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Lab-frame bookkeeping at the meeting time `T = π/k₀`: a rigid rotation by
`δ = T(⟨α⟩ − αᵢ)` shifts fringes of wavenumber `2k₀` by `2π(⟨α⟩ − αᵢ)`, so
the lab fringe phase reads the time-averaged flux while the envelope-relative
phase keeps the initial flux. -/
theorem ring_lab_fringe_shift (k₀ T mean αi : ℝ) (hk : k₀ ≠ 0) (hT : T = Real.pi / k₀) :
    2 * k₀ * (T * mean - αi * T) = 2 * Real.pi * (mean - αi) := by
  subst hT
  field_simp

end UnifiedTheory.Audit.KFCausalAharonovBohm
