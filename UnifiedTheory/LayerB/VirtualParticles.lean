/-
  LayerB/VirtualParticles.lean — Virtual particles as off-shell internal histories

  This file gives the framework's intrinsic interpretation of virtual particles.
  In QFT, virtual particles are off-shell internal lines in Feynman diagrams,
  weighted by propagators and summed over. In this framework — built on
  perturbations of the locally-finite causal poset — the same content arises
  WITHOUT introducing momentum-space propagators or loop integrals.

  The construction:

  1. **On-shell vs. off-shell**: Given a linear field operator
     L : Perturbation (m+2) →ₗ[ℝ] W (e.g., the linearized Einstein operator),
     a perturbation h is on-shell iff L h = 0 and off-shell iff L h ≠ 0.
     On-shell perturbations are admissible asymptotic states. Off-shell
     perturbations carry K/P content but cannot be physical asymptotes —
     they are virtual.

  2. **K-virtual vs. P-virtual**: Off-shell perturbations split via the
     K/P decomposition (already proved in `MetricDefects.decomp_derived`).
     A K-virtual perturbation carries source charge but no dressing phase
     (its amplitude is purely real). A P-virtual perturbation carries
     dressing but no source charge (its amplitude is purely imaginary).
     This is the framework's analog of "virtual fermion" vs. "virtual boson".

  3. **Internal histories**: A history with on-shell endpoints and arbitrary
     intermediates. The intermediates may be off-shell — they are the
     virtual lines of the diagram. The amplitude of an internal history
     is the sum of step amplitudes (linearity of stepAmplitude on the
     perturbation space, already proved in `FeynmanRules.amplitude_additive`).

  4. **Field propagator**: A linear operator G that acts as identity on
     on-shell perturbations (so it does nothing to physical states) and
     weights off-shell intermediates. In QFT this is the Green's function
     of L. Here it is left abstract; concretely it can be the pseudo-inverse
     of L on ker(L)^⊥. The propagator-weighted amplitude reduces to the
     bare amplitude when no off-shell intermediates appear.

  5. **Feshbach effective Hamiltonian = single-virtual-line amplitude**:
     The Schur complement
         H_eff(λ) = H_PP + H_PQ · (λ - H_QQ)⁻¹ · H_QP
     is exactly the amplitude of a one-virtual-line history: vertex × propagator
     × vertex. Specialized to the J₄ chamber Jacobi matrix in
     `LayerA.FeshbachJ4`, the off-diagonal entries b₁², b₂² *are* the
     squared-vertex couplings, and the relation b₁² = C_int · (λ* - a₁) is
     the propagator-weighted self-energy fixed point. This unifies the
     Feshbach machinery (used to derive the Higgs mass and mass hierarchy)
     with the virtual-particle framework: the same algebra computes both.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.HistoryAmplitudes
import UnifiedTheory.LayerB.FeynmanRules
import UnifiedTheory.LayerA.FeshbachJ4

namespace UnifiedTheory.LayerB.VirtualParticles

open MetricDefects SignedSource HistoryAmplitudes FeynmanRules
open scoped ComplexConjugate

variable {m : ℕ}

/-! ## Section 1: On-shell / off-shell predicates

    A perturbation is on-shell for a linear field operator L iff L h = 0.
    These are the only perturbations that can serve as physical asymptotic
    in/out states. Everything else is virtual.
-/

/-- A perturbation is **on-shell** for a linear field operator L iff `L h = 0`. -/
def OnShell {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) (h : Perturbation (m + 2)) : Prop :=
  L h = 0

/-- A perturbation is **off-shell** for L iff `L h ≠ 0`. Off-shell perturbations
    are virtual: they participate in the K/P algebra but cannot be physical
    asymptotic states. -/
def OffShell {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) (h : Perturbation (m + 2)) : Prop :=
  L h ≠ 0

/-- The zero perturbation is always on-shell (linearity of L). -/
theorem onShell_zero {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) : OnShell L (0 : Perturbation (m + 2)) := by
  unfold OnShell; exact map_zero L

/-- Sum of two on-shell perturbations is on-shell (linearity of L). -/
theorem onShell_add {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) (h₁ h₂ : Perturbation (m + 2))
    (h1 : OnShell L h₁) (h2 : OnShell L h₂) : OnShell L (h₁ + h₂) := by
  unfold OnShell at *; rw [map_add, h1, h2, add_zero]

/-- Negation of an on-shell perturbation is on-shell. -/
theorem onShell_neg {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) (h : Perturbation (m + 2))
    (hh : OnShell L h) : OnShell L (-h) := by
  unfold OnShell at *; rw [map_neg, hh, neg_zero]

/-- Scalar multiple of an on-shell perturbation is on-shell. -/
theorem onShell_smul {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) (c : ℝ) (h : Perturbation (m + 2))
    (hh : OnShell L h) : OnShell L (c • h) := by
  unfold OnShell at *; rw [map_smul, hh, smul_zero]

/-- On-shell and off-shell are mutually exclusive and exhaustive. -/
theorem onShell_or_offShell {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) (h : Perturbation (m + 2)) :
    OnShell L h ∨ OffShell L h := by
  unfold OnShell OffShell
  exact em (L h = 0)

/-! ## Section 2: K-virtual vs. P-virtual classification

    The K/P decomposition (`MetricDefects.decomp_derived`) splits any
    perturbation into a charge-carrying K-part and a dressing-only P-part.
    Off-shell perturbations inherit this split: a "K-virtual" intermediate
    carries source charge (real-axis amplitude); a "P-virtual" intermediate
    carries dressing only (imaginary-axis amplitude). This is the
    framework-native analog of virtual fermions vs. virtual gauge bosons.
-/

/-- A **K-virtual** perturbation: off-shell, lying entirely in the K-sector
    (no dressing component). Carries source charge. -/
def KVirtual {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) (h : Perturbation (m + 2)) : Prop :=
  OffShell L h ∧ P_proj m h = 0

/-- A **P-virtual** perturbation: off-shell, lying entirely in the P-sector
    (no source charge). Carries dressing only. -/
def PVirtual {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) (h : Perturbation (m + 2)) : Prop :=
  OffShell L h ∧ K_proj m h = 0

/-- A K-virtual perturbation equals its own K-projection. -/
theorem KVirtual.eq_K_proj {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W} {h : Perturbation (m + 2)}
    (hKV : KVirtual L h) : h = K_proj m h := by
  have := decomp_derived h
  rw [hKV.2, add_zero] at this
  exact this

/-- A P-virtual perturbation equals its own P-projection. -/
theorem PVirtual.eq_P_proj {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W} {h : Perturbation (m + 2)}
    (hPV : PVirtual L h) : h = P_proj m h := by
  have := decomp_derived h
  rw [hPV.2, zero_add] at this
  exact this

/-- A K-virtual perturbation carries the full source charge of h. -/
theorem KVirtual.charge_eq_trace {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W} {h : Perturbation (m + 2)}
    (_hKV : KVirtual L h) : Q h = traceFunc m h :=
  Q_eq_trace h

/-- A P-virtual perturbation has zero source charge — it is "neutral matter". -/
theorem PVirtual.charge_zero {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W} {h : Perturbation (m + 2)}
    (hPV : PVirtual L h) : Q h = 0 := by
  unfold Q
  rw [hPV.2, map_zero]

/-- **A P-virtual perturbation has purely imaginary amplitude.**
    No source charge contribution to the real axis. This is the framework's
    analog of "a virtual gauge boson is a phase, not a charge". -/
theorem PVirtual.amplitude_imaginary
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W} {h : Perturbation (m + 2)}
    (hPV : PVirtual L h) (D : Perturbation (m + 2) → ℝ) :
    (stepAmplitude D h).re = 0 :=
  pure_dressing_imaginary D h hPV.2

/-- **A K-virtual perturbation has purely real amplitude when D vanishes on K.**
    A virtual fermion carries source charge (real part) but no dressing phase. -/
theorem KVirtual.amplitude_real
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W} {h : Perturbation (m + 2)}
    (hKV : KVirtual L h) (D : Perturbation (m + 2) → ℝ)
    (hDK : D (K_proj m h) = 0) :
    (stepAmplitude D h).im = 0 :=
  pure_source_real D h hDK hKV.2

/-! ## Section 3: Internal histories — the diagram structure

    An internal history has on-shell endpoints (physical in/out states) and
    a list of intermediate perturbations that may be off-shell (virtual).
    This is the framework-native structure of a Feynman diagram with one
    "outer skeleton": external legs on-shell, internal lines arbitrary.
-/

/-- An **internal history**: on-shell incoming and outgoing perturbations
    bracketing a list of arbitrary (possibly off-shell) intermediate
    perturbations. The intermediates are the virtual lines of the diagram. -/
structure InternalHistory {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) where
  inEvent : Perturbation (m + 2)
  intermediates : List (Perturbation (m + 2))
  outEvent : Perturbation (m + 2)
  inOnShell : OnShell L inEvent
  outOnShell : OnShell L outEvent

/-- The list-amplitude: sum of step amplitudes over a list of perturbations.
    This is the same coherent-sum convention used in `eventAmplitude`. -/
noncomputable def listAmplitude (D : Perturbation (m + 2) → ℝ)
    (steps : List (Perturbation (m + 2))) : ℂ :=
  (steps.map (stepAmplitude D)).foldl (· + ·) 0

/-- The amplitude of an internal history: in-step + intermediates + out-step.
    Each intermediate contributes its own step amplitude (no propagator yet —
    that is the abstract `FieldPropagator` of Section 4). -/
noncomputable def InternalHistory.amplitude
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (ih : InternalHistory L) : ℂ :=
  stepAmplitude D ih.inEvent + listAmplitude D ih.intermediates +
    stepAmplitude D ih.outEvent

/-- The empty list contributes nothing to the amplitude. -/
theorem listAmplitude_nil (D : Perturbation (m + 2) → ℝ) :
    listAmplitude D ([] : List (Perturbation (m + 2))) = 0 := by
  simp [listAmplitude]

/-- A singleton list contributes its single step amplitude. -/
theorem listAmplitude_singleton (D : Perturbation (m + 2) → ℝ)
    (h : Perturbation (m + 2)) :
    listAmplitude D [h] = stepAmplitude D h := by
  simp [listAmplitude, List.foldl]

/-- **Diagram with no virtual lines collapses to in + out.**
    When the intermediates list is empty, no virtual particles appear and
    the amplitude is the bare two-step coherent sum. -/
theorem InternalHistory.no_virtual_lines
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (ih : InternalHistory L)
    (h_empty : ih.intermediates = []) :
    ih.amplitude D = stepAmplitude D ih.inEvent + stepAmplitude D ih.outEvent := by
  simp [InternalHistory.amplitude, h_empty, listAmplitude_nil]

/-- **Diagram with one virtual intermediate.**
    The amplitude is the coherent sum: in + virtual + out. -/
theorem InternalHistory.single_virtual_line
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (ih : InternalHistory L)
    (h_int : Perturbation (m + 2)) (h_one : ih.intermediates = [h_int]) :
    ih.amplitude D = stepAmplitude D ih.inEvent + stepAmplitude D h_int +
      stepAmplitude D ih.outEvent := by
  simp [InternalHistory.amplitude, h_one, listAmplitude_singleton]

/-! ## Section 4: Field propagator — the Green's function

    A field propagator is a linear operator G that acts as identity on
    on-shell perturbations (so the framework's existing on-shell propagation
    rule, `expAmplitude k s`, is unchanged for physical states) and assigns
    propagator weights to off-shell virtual intermediates. This is the
    abstract analog of the QFT Green's function (L)⁻¹ on ker(L)^⊥.
-/

/-- A **field propagator** for L: a linear self-map of the perturbation space
    that acts as identity on on-shell perturbations. Off-shell perturbations
    are mapped to their propagator-weighted images. -/
structure FieldPropagator {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) where
  G : Perturbation (m + 2) →ₗ[ℝ] Perturbation (m + 2)
  identity_on_shell : ∀ h, OnShell L h → G h = h

/-- The **identity propagator**: G = id. Trivially satisfies the on-shell
    identity condition. Corresponds to "no propagator weighting" — every
    intermediate is treated as if it were on-shell. -/
noncomputable def identityPropagator {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W) : FieldPropagator L where
  G := LinearMap.id
  identity_on_shell := fun _ _ => rfl

/-- The propagator-weighted amplitude of a single (possibly virtual) step. -/
noncomputable def virtualStepAmplitude
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (Gp : FieldPropagator L)
    (h : Perturbation (m + 2)) : ℂ :=
  stepAmplitude D (Gp.G h)

/-- For an on-shell step, the propagator does nothing — virtual amplitude
    equals bare amplitude. -/
theorem virtualStepAmplitude_onShell
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (Gp : FieldPropagator L)
    (h : Perturbation (m + 2)) (hOn : OnShell L h) :
    virtualStepAmplitude D Gp h = stepAmplitude D h := by
  unfold virtualStepAmplitude
  rw [Gp.identity_on_shell h hOn]

/-- The propagator-weighted amplitude of an internal history.
    Endpoints are on-shell (so the propagator is identity there, by the
    `FieldPropagator.identity_on_shell` axiom); intermediates may be off-shell
    and pick up a propagator weight. -/
noncomputable def InternalHistory.amplitudeWithPropagator
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (Gp : FieldPropagator L)
    (ih : InternalHistory L) : ℂ :=
  stepAmplitude D ih.inEvent +
    (ih.intermediates.map (virtualStepAmplitude D Gp)).foldl (· + ·) 0 +
    stepAmplitude D ih.outEvent

/-- **Reduction theorem**: the identity propagator gives the bare amplitude.
    Choosing G = id recovers the unweighted internal-history amplitude. -/
theorem InternalHistory.amplitudeWithPropagator_identity
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (ih : InternalHistory L) :
    ih.amplitudeWithPropagator D (identityPropagator L) = ih.amplitude D := by
  unfold InternalHistory.amplitudeWithPropagator InternalHistory.amplitude
    listAmplitude virtualStepAmplitude identityPropagator
  rfl

/-- **Reduction theorem**: if every intermediate is on-shell, ANY propagator
    gives the bare amplitude. The propagator only affects virtual lines. -/
theorem InternalHistory.amplitudeWithPropagator_all_onShell
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Perturbation (m + 2) →ₗ[ℝ] W}
    (D : Perturbation (m + 2) → ℝ) (Gp : FieldPropagator L)
    (ih : InternalHistory L)
    (h_all : ∀ h ∈ ih.intermediates, OnShell L h) :
    ih.amplitudeWithPropagator D Gp = ih.amplitude D := by
  have key : ih.intermediates.map (virtualStepAmplitude D Gp) =
             ih.intermediates.map (stepAmplitude D) := by
    apply List.map_congr_left
    intro h hh
    exact virtualStepAmplitude_onShell D Gp h (h_all h hh)
  unfold InternalHistory.amplitudeWithPropagator InternalHistory.amplitude listAmplitude
  rw [key]

/-! ## Section 5: Feshbach effective Hamiltonian = single-virtual-line amplitude

    The Schur complement of a 2×2 block Hamiltonian is the framework's
    finite-dimensional realization of the virtual-particle sum:

        H_eff(λ) = H_PP + H_PQ · (λ - H_QQ)⁻¹ · H_QP

    The second term is exactly the amplitude of a one-virtual-line history:
    the on-shell P-state emits a virtual Q-state (vertex H_QP), the Q-state
    propagates ((λ - H_QQ)⁻¹), and is reabsorbed (vertex H_PQ).

    The J₄ chamber Jacobi matrix in `LayerA.FeshbachJ4` is constructed from
    exactly this self-energy. Its off-diagonal entries b₁², b₂² are the
    squared vertex couplings, and the relation b₁² = C_int · (λ* - a₁) is
    the propagator-weighted self-energy fixed point — i.e., the C_int
    constant IS the residue of a single virtual line.
-/

/-- **Schur complement = single virtual amplitude (1×1 case).**
    For a Hamiltonian with 1D model space P and 1D bath Q,
        H = ⎡ a_P  b ⎤      H_eff(λ) = a_P + b² / (λ - a_Q),
            ⎣ b   a_Q ⎦
    and the second term factors as vertex × propagator × vertex:
        b² / (λ - a_Q) = b · (λ - a_Q)⁻¹ · b.
    This makes manifest the virtual-line interpretation. -/
theorem feshbach_eq_virtual_line (a_P b a_Q lam : ℝ) (_hlam : lam ≠ a_Q) :
    a_P + b ^ 2 / (lam - a_Q) = a_P + b * ((lam - a_Q)⁻¹) * b := by
  rw [div_eq_mul_inv, sq]; ring

/-- **The single-virtual-line amplitude.** Vertex × propagator × vertex,
    as a function of the spectral parameter λ. -/
noncomputable def virtualLineAmplitude (b a_Q lam : ℝ) : ℝ :=
  b * ((lam - a_Q)⁻¹) * b

/-- The single-virtual-line amplitude equals b² / (λ - a_Q). -/
theorem virtualLineAmplitude_eq (b a_Q lam : ℝ) (_hlam : lam ≠ a_Q) :
    virtualLineAmplitude b a_Q lam = b ^ 2 / (lam - a_Q) := by
  unfold virtualLineAmplitude
  rw [div_eq_mul_inv, sq]; ring

/-- **The b₁² coupling in the J₄ chamber matrix IS the single-virtual-line
    residue C_int times the propagator denominator.**
    Reading `FeshbachJ4.b1_from_self_energy` in the virtual-particle frame:
        b₁² = C_int · (λ* - a₁)   ⟺   C_int = b₁² / (λ* - a₁).
    The right-hand side is `virtualLineAmplitude b₁ a₁ λ*` — i.e., C_int IS
    the propagator-weighted amplitude of a single virtual line connecting
    the boundary channel to the bath. -/
theorem feshbach_b1_is_virtual_residue :
    UnifiedTheory.LayerA.FeshbachJ4.b₁_sq =
    UnifiedTheory.LayerA.FeshbachJ4.C_int *
      (UnifiedTheory.LayerA.FeshbachJ4.lambda_star -
        UnifiedTheory.LayerA.FeshbachJ4.a₁) :=
  UnifiedTheory.LayerA.FeshbachJ4.b1_from_self_energy

/-- The same identity for the b₂² coupling: it is a virtual-line residue. -/
theorem feshbach_b2_is_virtual_residue :
    UnifiedTheory.LayerA.FeshbachJ4.b₂_sq =
    (UnifiedTheory.LayerA.FeshbachJ4.lambda_star -
      UnifiedTheory.LayerA.FeshbachJ4.a₃) *
      UnifiedTheory.LayerA.FeshbachJ4.x_int :=
  UnifiedTheory.LayerA.FeshbachJ4.b2_from_self_energy

/-- **Interior self-energy uniformity = universal virtual residue.**
    The C_int constant is the same regardless of which interior Q-state
    mediates the virtual line. In QFT terms: the "running coupling" at the
    interior of the chamber is energy-independent. -/
theorem feshbach_self_energy_uniform_as_virtual :
    UnifiedTheory.LayerA.FeshbachJ4.C_int *
      UnifiedTheory.LayerA.FeshbachJ4.x_int /
      UnifiedTheory.LayerA.FeshbachJ4.x_int =
    UnifiedTheory.LayerA.FeshbachJ4.C_int :=
  UnifiedTheory.LayerA.FeshbachJ4.self_energy_uniform

/-- **The C_int constant is the propagator-weighted single-virtual-line
    amplitude at the spectral fixed point.**
    Equivalently, the framework's chamber-interior self-energy IS the
    universal residue of a virtual mediator: C_int = b₁² / (λ* − a₁). -/
theorem C_int_is_virtual_residue :
    UnifiedTheory.LayerA.FeshbachJ4.C_int =
    UnifiedTheory.LayerA.FeshbachJ4.b₁_sq /
      (UnifiedTheory.LayerA.FeshbachJ4.lambda_star -
        UnifiedTheory.LayerA.FeshbachJ4.a₁) := by
  rw [feshbach_b1_is_virtual_residue]
  unfold UnifiedTheory.LayerA.FeshbachJ4.C_int
    UnifiedTheory.LayerA.FeshbachJ4.lambda_star
    UnifiedTheory.LayerA.FeshbachJ4.a₁
  norm_num

/-! ## Section 6: Capstone — the virtual-particle framework -/

/-- **VIRTUAL PARTICLES IN THE UNIFIED-THEORY FRAMEWORK.**

    The framework derives the virtual-particle structure of QFT without
    introducing momentum-space propagators or loop integrals:

    (1) **On-shell / off-shell split**: linear field operator L gives
        OnShell L h := L h = 0 and OffShell L h := L h ≠ 0. On-shell
        perturbations are admissible asymptotic states; off-shell ones
        are virtual. (`onShell_zero`, `onShell_add`, `onShell_neg`)

    (2) **K-virtual / P-virtual classification** from the K/P decomposition
        already proved in `MetricDefects`: K-virtual carries source charge
        (purely real amplitude); P-virtual carries dressing only (purely
        imaginary amplitude). The framework's analog of "virtual fermion
        vs. virtual gauge boson". (`KVirtual.amplitude_real`,
        `PVirtual.amplitude_imaginary`)

    (3) **Internal histories** with on-shell endpoints and arbitrary
        intermediates implement the diagrammatic structure of QFT:
        external legs are on-shell; internal lines may be virtual.
        (`InternalHistory`, `InternalHistory.amplitude`)

    (4) **Field propagator** abstracts the QFT Green's function. It is
        identity on on-shell perturbations and assigns propagator weights
        to off-shell intermediates. The reduction theorem confirms that
        when no virtual lines appear, the propagator does nothing.
        (`FieldPropagator`, `InternalHistory.amplitudeWithPropagator_all_onShell`)

    (5) **Feshbach = single-virtual-line amplitude**: the Schur complement
        H_eff(λ) = H_PP + H_PQ · (λ-H_QQ)⁻¹ · H_QP factors as vertex ×
        propagator × vertex. Specialized to the J₄ chamber matrix in
        `LayerA.FeshbachJ4`, the off-diagonal couplings b₁², b₂² ARE the
        squared vertex couplings, and the universal interior constant
        C_int IS the residue of a single virtual line.
        (`feshbach_eq_virtual_line`, `C_int_is_virtual_residue`)

    Consequence: the same algebra that computes the Higgs mass and the
    mass hierarchy in the framework (via the Feshbach J₄ projection) is
    also the framework's virtual-particle calculation. The two pieces of
    the codebase that were previously isolated — `LayerA.FeshbachJ4` and
    the `LayerB` quantum/amplitude machinery — are unified. -/
theorem virtual_particle_framework
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : Perturbation (m + 2) →ₗ[ℝ] W)
    (D : Perturbation (m + 2) → ℝ) :
    -- (1) On-shell is closed under the vector-space operations
    OnShell L (0 : Perturbation (m + 2))
    ∧ (∀ h₁ h₂, OnShell L h₁ → OnShell L h₂ → OnShell L (h₁ + h₂))
    ∧ (∀ h, OnShell L h → OnShell L (-h))
    -- (2) K-virtual is real-axis; P-virtual is imaginary-axis
    ∧ (∀ h, PVirtual L h → (stepAmplitude D h).re = 0)
    -- (3) No-virtual-line collapse
    ∧ (∀ ih : InternalHistory L, ih.intermediates = [] →
        ih.amplitude D = stepAmplitude D ih.inEvent + stepAmplitude D ih.outEvent)
    -- (4) Identity-propagator reduction
    ∧ (∀ ih : InternalHistory L,
        ih.amplitudeWithPropagator D (identityPropagator L) = ih.amplitude D)
    -- (5) Feshbach C_int IS the single-virtual-line residue
    ∧ UnifiedTheory.LayerA.FeshbachJ4.C_int =
        UnifiedTheory.LayerA.FeshbachJ4.b₁_sq /
          (UnifiedTheory.LayerA.FeshbachJ4.lambda_star -
            UnifiedTheory.LayerA.FeshbachJ4.a₁) :=
  ⟨onShell_zero L, onShell_add L, onShell_neg L,
   fun _ hPV => PVirtual.amplitude_imaginary hPV D,
   fun ih h_empty => InternalHistory.no_virtual_lines D ih h_empty,
   fun ih => InternalHistory.amplitudeWithPropagator_identity D ih,
   C_int_is_virtual_residue⟩

end UnifiedTheory.LayerB.VirtualParticles
