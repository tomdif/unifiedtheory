/- Exact boundary messages and matrix elements for the actual finite open
Wilson cylinder. Full spatial endpoints use the explicit boundary exp(-beta V/2),
not the vacuum profile. Temporal length and spatial period are independent. -/
import UnifiedTheory.Clay.YangMills.WilsonFiniteCylinder
import UnifiedTheory.Clay.YangMills.WilsonOpenSlab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonBoundaryTransfer
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonFiniteCylinder
open WilsonPositiveGroundState TransferEnergySurvival

variable (n : ℕ) [NeZero n]

local instance cylinderBorel (L : ℕ) :
    BorelSpace (Slices n Q L × TemporalLinks n Q L) :=
  WilsonFiniteCylinder.cylinderBorel (n := n) (G := Q) L

/-- Propagation of an actual continuous boundary function through the full interacting kernel. -/
def message (β : ℝ) (B : C(Slice n, ℝ)) : ℕ → C(Slice n, ℝ)
  | 0 => B
  | L + 1 => realSmoothing (measure n) (kernelMap n β) (message β B L)

theorem message_succ (β : ℝ) (B : C(Slice n, ℝ)) (L : ℕ) (u : Slice n) :
    message n β B (L + 1) u =
      ∫ v, kernelMap n β (u, v) * message n β B L v ∂measure n :=
  realSmoothing_integral (measure n) (kernelMap n β) (message n β B L) u

/-- Boundary propagation agrees with actual L² operator powers. -/
theorem message_embedding (β : ℝ) (B : C(Slice n, ℝ)) (L : ℕ) :
    ContinuousMap.toLp 2 (measure n) ℂ (complexify (message n β B L)) =
      iterate (transfer n β) L (ContinuousMap.toLp 2 (measure n) ℂ (complexify B)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change ContinuousMap.toLp 2 (measure n) ℂ
      (complexify (realSmoothing (measure n) (kernelMap n β) (message n β B L))) = _
    rw [complexify_realSmoothing]
    change transfer n β (ContinuousMap.toLp 2 (measure n) ℂ
      (complexify (message n β B L))) = _
    rw [ih, iterate_succ]

/-- The full endpoint convention has this explicit, strictly positive spatial boundary. -/
def spatialBoundary (β : ℝ) : C(Slice n, ℝ) :=
  ⟨spatialWeight WilsonSingleLinkStaples.character β 2,
    spatialWeight_continuous WilsonSingleLinkStaples.character
      WilsonSingleLinkStaples.character_continuous β 2⟩

theorem spatialBoundary_pos (β : ℝ) (u : Slice n) : 0 < spatialBoundary n β u :=
  Real.exp_pos _

/-- The actual product of slab kernels splits at its first temporal bond. -/
theorem transferProduct_cons (β : ℝ) (L : ℕ) (u : Slice n)
    (U : Slices n Q L) :
    transferProduct WilsonSingleLinkStaples.character β 2 (L + 1) (Fin.cons u U) =
      kernelMap n β (u, U 0) * transferProduct WilsonSingleLinkStaples.character β 2 L U := by
  unfold transferProduct
  rw [Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_succ]
  rfl

/-- Two endpoint insertions in the literal finite chain of full slab kernels. -/
def endpointIntegral (β : ℝ) (L : ℕ) (F G : C(Slice n, ℝ)) : ℝ :=
  ∫ U : Slices n Q L, F (U 0) * transferProduct WilsonSingleLinkStaples.character β 2 L U *
    G (U (Fin.last L)) ∂slicesHaar (n := n) (G := Q) L

theorem endpointIntegrand_continuous (β : ℝ) (L : ℕ) (F G : C(Slice n, ℝ)) :
    Continuous (fun U : Slices n Q L => F (U 0) *
      transferProduct WilsonSingleLinkStaples.character β 2 L U * G (U (Fin.last L))) :=
  ((F.continuous.comp (continuous_apply 0)).mul
    (transferProduct_continuous WilsonSingleLinkStaples.character
      WilsonSingleLinkStaples.character_continuous β 2 L)).mul
    (G.continuous.comp (continuous_apply (Fin.last L)))

/-- Finite-chain integration derives the boundary-message pairing by Fubini. -/
theorem endpointIntegral_message (β : ℝ) (L : ℕ) (F G : C(Slice n, ℝ)) :
    endpointIntegral n β L F G = ∫ u, F u * message n β G L u ∂measure n := by
  induction L generalizing F with
  | zero =>
    unfold endpointIntegral
    rw [WilsonOpenSlab.path_integral_succ n 0 _ (endpointIntegrand_continuous n β 0 F G)]
    simp only [transferProduct, Fin.prod_univ_zero, Fin.last_zero, Fin.cons_zero, mul_one]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rfl
  | succ L ih =>
    unfold endpointIntegral
    rw [WilsonOpenSlab.path_integral_succ n (L + 1) _
      (endpointIntegrand_continuous n β (L + 1) F G)]
    apply integral_congr_ae
    filter_upwards [] with u
    have hlast : Fin.last (L + 1) = (Fin.last L).succ := rfl
    simp only [Fin.cons_zero, transferProduct_cons, hlast, Fin.cons_succ]
    have he (U : Slices n Q L) :
        F u * (kernelMap n β (u, U 0) * transferProduct WilsonSingleLinkStaples.character β 2 L U) *
          G (U (Fin.last L)) =
        F u * (kernelMap n β (u, U 0) * transferProduct WilsonSingleLinkStaples.character β 2 L U *
          G (U (Fin.last L))) := by ring
    simp_rw [he]
    rw [integral_const_mul]
    let R : C(Slice n, ℝ) :=
      ⟨fun v => kernelMap n β (u, v),
        (kernelMap n β).continuous.comp (continuous_const.prodMk continuous_id)⟩
    have hr := ih R
    change (∫ U : Slices n Q L,
      kernelMap n β (u, U 0) * transferProduct WilsonSingleLinkStaples.character β 2 L U *
        G (U (Fin.last L)) ∂slicesHaar (n := n) (G := Q) L) =
      ∫ v, kernelMap n β (u, v) * message n β G L v ∂measure n at hr
    rw [hr, ← message_succ]

/-- The endpoint pairing is the real part of a genuine complex Hilbert-space matrix element. -/
theorem endpointIntegral_matrix (β : ℝ) (L : ℕ) (F G : C(Slice n, ℝ)) :
    endpointIntegral n β L F G =
      (inner ℂ (ContinuousMap.toLp 2 (measure n) ℂ (complexify F))
        (iterate (transfer n β) L
          (ContinuousMap.toLp 2 (measure n) ℂ (complexify G)))).re := by
  rw [← message_embedding, MeasureTheory.ContinuousMap.inner_toLp, endpointIntegral_message]
  simp only [complexify, ContinuousMap.coe_mk, Complex.conj_ofReal, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_re]
  congr 1
  ext u
  ring

/-- The two actual slice observables at the endpoints of the finite cylinder. -/
def endpointObservable (L : ℕ) (F G : C(Slice n, ℝ)) : C(Slices n Q L, ℝ) :=
  ⟨fun U => F (U 0) * G (U (Fin.last L)),
    (F.continuous.comp (continuous_apply 0)).mul
      (G.continuous.comp (continuous_apply (Fin.last L)))⟩

/-- Full-action temporal integration gives explicit boundary-weighted endpoint insertions. -/
theorem weighted_endpoint_integral (β : ℝ) (L : ℕ) (F G : C(Slice n, ℝ)) :
    (∫ U : Slices n Q L,
      (spatialWeight WilsonSingleLinkStaples.character β 2 (U 0) *
        transferProduct WilsonSingleLinkStaples.character β 2 L U *
          spatialWeight WilsonSingleLinkStaples.character β 2 (U (Fin.last L))) *
            endpointObservable n L F G U ∂slicesHaar (n := n) (G := Q) L) =
      endpointIntegral n β L (spatialBoundary n β * F) (spatialBoundary n β * G) := by
  unfold endpointIntegral
  apply integral_congr_ae
  filter_upwards [] with U
  simp only [endpointObservable, ContinuousMap.coe_mk, ContinuousMap.mul_apply,
    spatialBoundary]
  ring

/-- Exact finite-cylinder two-time expectation, including its true partition normalization. -/
theorem cylinder_endpoint_expectation (β : ℝ) (L : ℕ) (F G : C(Slice n, ℝ)) :
    (∫ z : Slices n Q L × TemporalLinks n Q L, F (z.1 0) * G (z.1 (Fin.last L))
      ∂WilsonFiniteCylinder.law WilsonSingleLinkStaples.character β 2 L) =
      endpointIntegral n β L (spatialBoundary n β * F) (spatialBoundary n β * G) /
        endpointIntegral n β L (spatialBoundary n β) (spatialBoundary n β) := by
  change (∫ z, endpointObservable n L F G z.1
    ∂WilsonFiniteCylinder.law WilsonSingleLinkStaples.character β 2 L) = _
  rw [WilsonFiniteCylinder.law_integral _ WilsonSingleLinkStaples.character_continuous,
    weighted_endpoint_integral]
  congr 1

/-- The raw cylinder expectation is a transfer matrix-element ratio with boundary b. -/
theorem cylinder_endpoint_matrix (β : ℝ) (L : ℕ) (F G : C(Slice n, ℝ)) :
    (∫ z : Slices n Q L × TemporalLinks n Q L, F (z.1 0) * G (z.1 (Fin.last L))
      ∂WilsonFiniteCylinder.law WilsonSingleLinkStaples.character β 2 L) =
      (inner ℂ (ContinuousMap.toLp 2 (measure n) ℂ (complexify (spatialBoundary n β * F)))
        (iterate (transfer n β) L (ContinuousMap.toLp 2 (measure n) ℂ
          (complexify (spatialBoundary n β * G))))).re /
      (inner ℂ (ContinuousMap.toLp 2 (measure n) ℂ (complexify (spatialBoundary n β)))
        (iterate (transfer n β) L (ContinuousMap.toLp 2 (measure n) ℂ
          (complexify (spatialBoundary n β))))).re := by
  rw [cylinder_endpoint_expectation, endpointIntegral_matrix, endpointIntegral_matrix]

/-- The matrix denominator is strictly positive for every finite cylinder, including length zero. -/
theorem cylinder_partition_pos (β : ℝ) (L : ℕ) :
    0 < endpointIntegral n β L (spatialBoundary n β) (spatialBoundary n β) := by
  have hp := CompactGibbsContinuity.partition_positive
    (cylinderHaar (n := n) (G := Q) L)
    (fun z => fullAction WilsonSingleLinkStaples.character β 2 L z.1 z.2)
    (fullAction_continuous _ WilsonSingleLinkStaples.character_continuous β 2 L)
  have he := full_integral WilsonSingleLinkStaples.character
    WilsonSingleLinkStaples.character_continuous β 2 L (1 : C(Slices n Q L, ℝ))
  simp only [ContinuousMap.one_apply, mul_one] at he
  rw [he] at hp
  exact hp

end
end UnifiedTheory.Clay.YangMills.WilsonBoundaryTransfer
