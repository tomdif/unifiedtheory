/- Interior slice insertions in the actual open Wilson cylinder. -/
import UnifiedTheory.Clay.YangMills.WilsonBoundaryTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCylinderGluing
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonFiniteCylinder
open WilsonPositiveGroundState WilsonBoundaryTransfer

variable (n : ℕ) [NeZero n]

local instance cylinderBorel (L : ℕ) :
    BorelSpace (Slices n Q L × TemporalLinks n Q L) :=
  WilsonFiniteCylinder.cylinderBorel (n := n) (G := Q) L

/-- Exact propagation of a boundary through two successive time intervals. -/
theorem message_add (β : ℝ) (B : C(Slice n, ℝ)) (k l : ℕ) :
    message n β (message n β B k) l = message n β B (k + l) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    change realSmoothing (measure n) (kernelMap n β) (message n β (message n β B k) l) =
      realSmoothing (measure n) (kernelMap n β) (message n β B (k + l))
    rw [ih]

/-- Integrating the first slice transports the true boundary, with arbitrary remaining insertion. -/
theorem eliminate_first (β : ℝ) (L : ℕ) (B : C(Slice n, ℝ))
    (H : C(Slices n Q L, ℝ)) :
    (∫ U : Slices n Q (L + 1), B (U 0) *
      transferProduct WilsonSingleLinkStaples.character β 2 (L + 1) U *
      H (fun i => U i.succ) ∂slicesHaar (n := n) (G := Q) (L + 1)) =
    ∫ V : Slices n Q L, message n β B 1 (V 0) *
      transferProduct WilsonSingleLinkStaples.character β 2 L V * H V
      ∂slicesHaar (n := n) (G := Q) L := by
  have hc : Continuous (fun U : Slices n Q (L + 1) => B (U 0) *
      transferProduct WilsonSingleLinkStaples.character β 2 (L + 1) U *
      H (fun i => U i.succ)) :=
    ((B.continuous.comp (continuous_apply 0)).mul
      (transferProduct_continuous _ WilsonSingleLinkStaples.character_continuous β 2 (L + 1))).mul
      (H.continuous.comp (continuous_pi (fun i => continuous_apply i.succ)))
  rw [WilsonOpenSlab.path_integral_succ n (L + 1) _ hc]
  simp only [Fin.cons_zero, transferProduct_cons, Fin.cons_succ]
  let J : Slice n × Slices n Q L → ℝ := fun z =>
    B z.1 * (kernelMap n β (z.1, z.2 0) *
      transferProduct WilsonSingleLinkStaples.character β 2 L z.2) * H z.2
  have hJ : Continuous J := by
    exact ((B.continuous.comp continuous_fst).mul
      (((kernelMap n β).continuous.comp
        (f := fun z : Slice n × Slices n Q L => (z.1, z.2 0))
        (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))).mul
        ((transferProduct_continuous _ WilsonSingleLinkStaples.character_continuous β 2 L).comp
          continuous_snd))).mul (H.continuous.comp continuous_snd)
  have hi := hJ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := (WilsonSlabOperator.measure n).prod (slicesHaar (n := n) (G := Q) L))
  have hs := integral_integral_swap (f := fun u V => J (u, V)) hi
  change (∫ u, ∫ V, J (u, V) ∂slicesHaar (n := n) (G := Q) L ∂measure n) = _
  rw [hs]
  apply integral_congr_ae
  filter_upwards [] with V
  have he (u : Slice n) : J (u, V) =
      (kernelMap n β (V 0, u) * B u) *
        (transferProduct WilsonSingleLinkStaples.character β 2 L V * H V) := by
    dsimp [J]
    rw [kernelMap_symm n β u (V 0)]
    ring
  simp_rw [he]
  rw [integral_mul_const]
  rw [message_succ]
  simp only [message]
  ring

/-- A time index with a prescribed number of subsequent bonds. -/
def mark (r k : ℕ) : Fin (r + k + 1) := ⟨k, by omega⟩

@[simp] theorem mark_zero (r : ℕ) : mark r 0 = 0 := rfl
@[simp] theorem mark_succ (r k : ℕ) : mark r (k + 1) = (mark r k).succ := rfl

/-- One marked slice in the literal finite product of interacting kernels. -/
def markedIntegral (β : ℝ) (r k : ℕ) (B F C : C(Slice n, ℝ)) : ℝ :=
  ∫ U : Slices n Q (r + k), B (U 0) *
    transferProduct WilsonSingleLinkStaples.character β 2 (r + k) U *
    F (U (mark r k)) * C (U (Fin.last (r + k)))
    ∂slicesHaar (n := n) (G := Q) (r + k)

theorem markedIntegrand_continuous (β : ℝ) (r k : ℕ) (B F C : C(Slice n, ℝ)) :
    Continuous (fun U : Slices n Q (r + k) => B (U 0) *
      transferProduct WilsonSingleLinkStaples.character β 2 (r + k) U *
      F (U (mark r k)) * C (U (Fin.last (r + k)))) :=
  (((B.continuous.comp (continuous_apply 0)).mul
    (transferProduct_continuous _ WilsonSingleLinkStaples.character_continuous β 2 (r + k))).mul
    (F.continuous.comp (continuous_apply (mark r k)))).mul
    (C.continuous.comp (continuous_apply (Fin.last (r + k))))

/-- The marked finite chain equals an explicitly propagated insertion. -/
theorem markedIntegral_message (β : ℝ) (r k : ℕ) (B F C : C(Slice n, ℝ)) :
    markedIntegral n β r k B F C =
      ∫ u, B u * message n β (F * message n β C r) k u ∂measure n := by
  induction k generalizing B with
  | zero =>
    have he : markedIntegral n β r 0 B F C = endpointIntegral n β r (B * F) C := by
      unfold markedIntegral endpointIntegral
      apply integral_congr_ae
      filter_upwards [] with U
      simp only [mark_zero, ContinuousMap.mul_apply, Nat.add_zero]
      ring
    rw [he, endpointIntegral_message]
    apply integral_congr_ae
    filter_upwards [] with u
    change B u * F u * message n β C r u = B u * (F u * message n β C r u)
    ring
  | succ k ih =>
    unfold markedIntegral
    change (∫ U : WilsonOpenSlab.Path n (r + k + 1 + 1), B (U 0) *
      transferProduct WilsonSingleLinkStaples.character β 2 (r + k + 1) U *
      F (U (mark r (k + 1))) * C (U (Fin.last (r + k + 1)))
      ∂WilsonOpenSlab.pathHaar n (r + k + 1 + 1)) = _
    erw [WilsonOpenSlab.path_integral_succ n (r + k + 1) _
      (markedIntegrand_continuous n β r (k + 1) B F C)]
    apply integral_congr_ae
    filter_upwards [] with u
    have hlast : Fin.last (r + (k + 1)) = (Fin.last (r + k)).succ := rfl
    simp only [Fin.cons_zero, mark_succ, hlast, Fin.cons_succ]
    change (∫ U : Slices n Q (r + k), B u *
      transferProduct WilsonSingleLinkStaples.character β 2 (r + k + 1) (Fin.cons u U) *
      F (U (mark r k)) * C (U (Fin.last (r + k)))
      ∂slicesHaar (n := n) (G := Q) (r + k)) = _
    simp only [transferProduct_cons]
    have he (U : Slices n Q (r + k)) :
      B u * (kernelMap n β (u, U 0) *
          transferProduct WilsonSingleLinkStaples.character β 2 (r + k) U) *
          F (U (mark r k)) * C (U (Fin.last (r + k))) =
        B u * (kernelMap n β (u, U 0) *
          transferProduct WilsonSingleLinkStaples.character β 2 (r + k) U *
          F (U (mark r k)) * C (U (Fin.last (r + k)))) := by ring
    simp_rw [he]
    rw [integral_const_mul]
    let R : C(Slice n, ℝ) := ⟨fun v => kernelMap n β (u, v),
      (kernelMap n β).continuous.comp (continuous_const.prodMk continuous_id)⟩
    have hr := ih R
    change (∫ U : Slices n Q (r + k), kernelMap n β (u, U 0) *
      transferProduct WilsonSingleLinkStaples.character β 2 (r + k) U *
      F (U (mark r k)) * C (U (Fin.last (r + k)))
      ∂slicesHaar (n := n) (G := Q) (r + k)) =
        ∫ v, kernelMap n β (u, v) * message n β (F * message n β C r) k v ∂measure n at hr
    rw [hr, ← message_succ]


/-- A later marked time, separated by k bonds from the first mark at l. -/
def secondMark (r k l : ℕ) : Fin (r + k + l + 1) := ⟨k + l, by omega⟩

@[simp] theorem secondMark_zero (r k : ℕ) : secondMark r k 0 = mark r k := rfl
@[simp] theorem secondMark_succ (r k l : ℕ) :
    secondMark r k (l + 1) = (secondMark r k l).succ := rfl

/-- Two interior insertions in the literal finite temporal product. -/
def twoMarkedIntegral (β : ℝ) (r k l : ℕ) (B F G C : C(Slice n, ℝ)) : ℝ :=
  ∫ U : Slices n Q (r + k + l), B (U 0) *
    transferProduct WilsonSingleLinkStaples.character β 2 (r + k + l) U *
    F (U (mark (r + k) l)) * G (U (secondMark r k l)) *
    C (U (Fin.last (r + k + l))) ∂slicesHaar (n := n) (G := Q) (r + k + l)

/-- Removing the genuine left boundary gives the exact three-segment cylinder gluing identity. -/
theorem twoMarkedIntegral_message (β : ℝ) (r k l : ℕ) (B F G C : C(Slice n, ℝ)) :
    twoMarkedIntegral n β r k l B F G C =
      ∫ u, (message n β B l u * F u) *
        message n β (G * message n β C r) k u ∂measure n := by
  induction l generalizing B with
  | zero =>
    have he : twoMarkedIntegral n β r k 0 B F G C =
        markedIntegral n β r k (B * F) G C := by
      unfold twoMarkedIntegral markedIntegral
      apply integral_congr_ae
      filter_upwards [] with U
      simp only [mark_zero, secondMark_zero, ContinuousMap.mul_apply, Nat.add_zero]
      ring
    rw [he, markedIntegral_message]
    rfl
  | succ l ih =>
    let H : C(Slices n Q (r + k + l), ℝ) :=
      ⟨fun U => F (U (mark (r + k) l)) * G (U (secondMark r k l)) *
          C (U (Fin.last (r + k + l))),
        ((F.continuous.comp (continuous_apply (mark (r + k) l))).mul
          (G.continuous.comp (continuous_apply (secondMark r k l)))).mul
          (C.continuous.comp (continuous_apply (Fin.last (r + k + l))))⟩
    have he : twoMarkedIntegral n β r k (l + 1) B F G C =
        twoMarkedIntegral n β r k l (message n β B 1) F G C := by
      have h := eliminate_first n β (r + k + l) B H
      convert h using 1
      · unfold twoMarkedIntegral
        apply integral_congr_ae
        filter_upwards [] with U
        simp only [mark_succ, secondMark_succ, H, ContinuousMap.coe_mk, Nat.add_succ]
        ring_nf
        rfl
      · unfold twoMarkedIntegral
        apply integral_congr_ae
        filter_upwards [] with U
        simp only [H, ContinuousMap.coe_mk]
        ring
    rw [he, ih, message_add]
    rw [Nat.add_comm 1 l]

/-- Interior gluing expressed as the central segment's exact transfer matrix element. -/
theorem twoMarkedIntegral_endpoint (β : ℝ) (r k l : ℕ) (B F G C : C(Slice n, ℝ)) :
    twoMarkedIntegral n β r k l B F G C =
      endpointIntegral n β k (message n β B l * F) (G * message n β C r) := by
  rw [twoMarkedIntegral_message, endpointIntegral_message]
  rfl

/-- The denominator glues with the same propagated true boundaries as the numerator. -/
theorem partition_gluing (β : ℝ) (r k l : ℕ) (B C : C(Slice n, ℝ)) :
    endpointIntegral n β (r + k + l) B C =
      endpointIntegral n β k (message n β B l) (message n β C r) := by
  have h := twoMarkedIntegral_endpoint n β r k l B 1 1 C
  simpa only [twoMarkedIntegral, endpointIntegral, ContinuousMap.one_apply, mul_one,
    one_mul] using h

/-- The actual two observed slices, with independently chosen left and right padding. -/
def interiorObservable (r k l : ℕ) (F G : C(Slice n, ℝ)) :
    C(Slices n Q (r + k + l), ℝ) :=
  ⟨fun U => F (U (mark (r + k) l)) * G (U (secondMark r k l)),
    (F.continuous.comp (continuous_apply (mark (r + k) l))).mul
      (G.continuous.comp (continuous_apply (secondMark r k l)))⟩

/-- Exact interior correlation under the full Wilson cylinder law, before any vacuum limit. -/
theorem cylinder_interior_expectation (β : ℝ) (r k l : ℕ) (F G : C(Slice n, ℝ)) :
    (∫ z : Slices n Q (r + k + l) × TemporalLinks n Q (r + k + l),
      F (z.1 (mark (r + k) l)) * G (z.1 (secondMark r k l))
      ∂WilsonFiniteCylinder.law WilsonSingleLinkStaples.character β 2 (r + k + l)) =
      endpointIntegral n β k (message n β (spatialBoundary n β) l * F)
        (G * message n β (spatialBoundary n β) r) /
      endpointIntegral n β k (message n β (spatialBoundary n β) l)
        (message n β (spatialBoundary n β) r) := by
  change (∫ z, interiorObservable n r k l F G z.1
    ∂WilsonFiniteCylinder.law WilsonSingleLinkStaples.character β 2 (r + k + l)) = _
  rw [WilsonFiniteCylinder.law_integral _ WilsonSingleLinkStaples.character_continuous]
  have hn : (∫ U : Slices n Q (r + k + l),
      (spatialWeight WilsonSingleLinkStaples.character β 2 (U 0) *
        transferProduct WilsonSingleLinkStaples.character β 2 (r + k + l) U *
        spatialWeight WilsonSingleLinkStaples.character β 2 (U (Fin.last (r + k + l)))) *
        interiorObservable n r k l F G U ∂slicesHaar (n := n) (G := Q) (r + k + l)) =
      twoMarkedIntegral n β r k l (spatialBoundary n β) F G (spatialBoundary n β) := by
    unfold twoMarkedIntegral
    apply integral_congr_ae
    filter_upwards [] with U
    simp only [interiorObservable, ContinuousMap.coe_mk, spatialBoundary]
    ring
  rw [hn, twoMarkedIntegral_endpoint]
  congr 1
  exact partition_gluing n β r k l (spatialBoundary n β) (spatialBoundary n β)

/-- Actual interior correlations are ratios of matrix elements of the full interacting transfer. -/
theorem cylinder_interior_matrix (β : ℝ) (r k l : ℕ) (F G : C(Slice n, ℝ)) :
    (∫ z : Slices n Q (r + k + l) × TemporalLinks n Q (r + k + l),
      F (z.1 (mark (r + k) l)) * G (z.1 (secondMark r k l))
      ∂WilsonFiniteCylinder.law WilsonSingleLinkStaples.character β 2 (r + k + l)) =
    (inner ℂ (ContinuousMap.toLp 2 (measure n) ℂ
        (complexify (message n β (spatialBoundary n β) l * F)))
      (TransferEnergySurvival.iterate (transfer n β) k
        (ContinuousMap.toLp 2 (measure n) ℂ
          (complexify (G * message n β (spatialBoundary n β) r))))).re /
    (inner ℂ (ContinuousMap.toLp 2 (measure n) ℂ
        (complexify (message n β (spatialBoundary n β) l)))
      (TransferEnergySurvival.iterate (transfer n β) k
        (ContinuousMap.toLp 2 (measure n) ℂ
          (complexify (message n β (spatialBoundary n β) r))))).re := by
  rw [cylinder_interior_expectation, endpointIntegral_matrix, endpointIntegral_matrix]

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderGluing
