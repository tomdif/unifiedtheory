/- Finite open chains of the actual full Wilson slab kernel. Boundary
messages are constructed by integration, their L² embeddings are actual
operator powers, and gluing two chains gives the exact midpoint law. -/
import UnifiedTheory.Clay.YangMills.WilsonPositiveGroundState
import UnifiedTheory.Clay.YangMills.WilsonGroundLocalComparison
import UnifiedTheory.Clay.YangMills.TransferEnergySurvival
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonOpenSlab
noncomputable section
open MeasureTheory WilsonSlabOperator WilsonTimeSlab WilsonPositiveGroundState
open LocalGibbsComparison TransferEnergySurvival
open scoped ENNReal

variable (n : ℕ) [NeZero n]

/-- Free-boundary messages for the original, unnormalized Wilson transfer kernel. -/
def message (β : ℝ) : ℕ → C(Slice n, ℝ)
  | 0 => 1
  | k + 1 => realSmoothing (measure n) (kernelMap n β) (message β k)

@[simp] theorem message_zero (β : ℝ) : message n β 0 = 1 := rfl

theorem message_succ (β : ℝ) (k : ℕ) (u : Slice n) :
    message n β (k + 1) u =
      ∫ v, kernel WilsonSingleLinkStaples.character β 2 u v * message n β k v ∂measure n :=
  realSmoothing_integral (measure n) (kernelMap n β) (message n β k) u

theorem message_positive (β : ℝ) (k : ℕ) (u : Slice n) : 0 < message n β k u := by
  induction k generalizing u with
  | zero => simp [message]
  | succ k ih =>
    rw [message_succ]
    have hc : Continuous (fun v => kernel WilsonSingleLinkStaples.character β 2 u v *
        message n β k v) :=
      ((kernelMap n β).continuous.comp (continuous_const.prodMk continuous_id)).mul
        (message n β k).continuous
    have hp (v : Slice n) : 0 < kernel WilsonSingleLinkStaples.character β 2 u v *
        message n β k v :=
      mul_pos (kernel_positive WilsonSingleLinkStaples.character
        WilsonSingleLinkStaples.character_continuous β 2 u v) (ih v)
    apply (integral_pos_iff_support_of_nonneg (fun v => (hp v).le)
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mpr
    have hs : Function.support (fun v => kernel WilsonSingleLinkStaples.character β 2 u v *
        message n β k v) = Set.univ := by
      ext v
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (hp v).ne'
    simp [hs]

/-- The constructed message is the genuine L² transfer iterate of the constant boundary state. -/
theorem message_embedding (β : ℝ) (k : ℕ) :
    ContinuousMap.toLp 2 (measure n) ℂ (complexify (message n β k)) =
      iterate (transfer n β) k (ContinuousMap.toLp 2 (measure n) ℂ (1 : C(Slice n, ℂ))) := by
  induction k with
  | zero =>
    simp only [message_zero, iterate_zero]
    congr 1
  | succ k ih =>
    change ContinuousMap.toLp 2 (measure n) ℂ
      (complexify (realSmoothing (measure n) (kernelMap n β) (message n β k))) = _
    rw [complexify_realSmoothing]
    change transfer n β (ContinuousMap.toLp 2 (measure n) ℂ
      (complexify (message n β k))) = _
    rw [ih, iterate_succ]

/-- Every finite boundary message is gauge invariant for the actual full kernel. -/
theorem message_gauge (β : ℝ) (k : ℕ) (h : SliceGauge n Q) (u : Slice n) :
    message n β k (gaugeSlice h u) = message n β k u := by
  cases k with
  | zero => rfl
  | succ k =>
    change (representative n β
      (ContinuousMap.toLp 2 (measure n) ℂ (complexify (message n β k))) (gaugeSlice h u)).re =
      (representative n β
        (ContinuousMap.toLp 2 (measure n) ℂ (complexify (message n β k))) u).re
    rw [representative_gauge]

/-- The k non-central slices of an open half-chain. -/
abbrev Path (k : ℕ) := Fin k → Slice n
abbrev pathHaar (k : ℕ) : Measure (Path n k) := Measure.pi (fun _ : Fin k => measure n)

local instance pathPairBorel (k : ℕ) : BorelSpace (Path n k × Path n k) := Prod.borelSpace

/-- Literal product of consecutive original full-kernel factors, with a fixed central endpoint. -/
def chainWeight (β : ℝ) : (k : ℕ) → Slice n → Path n k → ℝ
  | 0, _, _ => 1
  | k + 1, u, v => kernel WilsonSingleLinkStaples.character β 2 u (v 0) *
      chainWeight β k (v 0) (fun i => v i.succ)

@[simp] theorem chainWeight_zero (β : ℝ) (u : Slice n) (v : Path n 0) :
    chainWeight n β 0 u v = 1 := rfl

theorem chainWeight_succ (β : ℝ) (k : ℕ) (u v : Slice n) (p : Path n k) :
    chainWeight n β (k + 1) u (Fin.cons v p) =
      kernel WilsonSingleLinkStaples.character β 2 u v * chainWeight n β k v p := by
  simp only [chainWeight, Fin.cons_zero, Fin.cons_succ]

theorem chainWeight_continuous (β : ℝ) (k : ℕ) :
    Continuous (fun z : Slice n × Path n k => chainWeight n β k z.1 z.2) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    have hhead : Continuous (fun z : Slice n × Path n (k + 1) => z.2 0) :=
      (continuous_apply 0).comp continuous_snd
    have htail : Continuous (fun z : Slice n × Path n (k + 1) => fun i : Fin k => z.2 i.succ) :=
      continuous_pi (fun i => (continuous_apply i.succ).comp continuous_snd)
    exact ((kernelMap n β).continuous.comp (continuous_fst.prodMk hhead)).mul
      (ih.comp (hhead.prodMk htail))

theorem chainWeight_positive (β : ℝ) (k : ℕ) (u : Slice n) (v : Path n k) :
    0 < chainWeight n β k u v := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    exact mul_pos (kernel_positive WilsonSingleLinkStaples.character
      WilsonSingleLinkStaples.character_continuous β 2 u (v 0)) (ih _ _)

/-- Head/tail integration is the actual finite-product Haar coordinate decomposition. -/
theorem path_integral_succ (k : ℕ) (F : Path n (k + 1) → ℝ) (hF : Continuous F) :
    (∫ v, F v ∂pathHaar n (k + 1)) =
      ∫ u, ∫ v, F (Fin.cons u v) ∂pathHaar n k ∂measure n := by
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => measure n) 0).symm
  have he := hp.integral_comp' F
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] at he
  rw [← he]
  have hc : Continuous (fun z : Slice n × Path n k => F (Fin.cons z.1 z.2)) := by
    apply hF.comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using
        (continuous_fst : Continuous (fun z : Slice n × Path n k => z.1))
    · simpa only [Fin.cons_succ] using
        ((continuous_apply j).comp continuous_snd :
          Continuous (fun z : Slice n × Path n k => z.2 j))
  exact integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

/-- Boundary messages are derived from the full finite chain product, not postulated as a law. -/
theorem chain_integral (β : ℝ) (k : ℕ) (u : Slice n) :
    (∫ v, chainWeight n β k u v ∂pathHaar n k) = message n β k u := by
  induction k generalizing u with
  | zero => simp [message]
  | succ k ih =>
    have he : Continuous (fun v : Path n (k + 1) => (u, v)) :=
      continuous_const.prodMk continuous_id
    have hc := (chainWeight_continuous n β (k + 1)).comp he
    rw [path_integral_succ n k (fun v => chainWeight n β (k + 1) u v) hc]
    simp only [chainWeight_succ, integral_const_mul, ih]
    exact (message_succ n β k u).symm

/-- Center slice with two free k-edge half-chains: a genuine open 2k-edge chain. -/
abbrev OpenChain (k : ℕ) := Slice n × (Path n k × Path n k)
abbrev openHaar (k : ℕ) : Measure (OpenChain n k) :=
  (WilsonSlabOperator.measure n).prod ((pathHaar n k).prod (pathHaar n k))

def openWeight (β : ℝ) (k : ℕ) (z : OpenChain n k) : ℝ :=
  chainWeight n β k z.1 z.2.1 * chainWeight n β k z.1 z.2.2

theorem openWeight_continuous (β : ℝ) (k : ℕ) : Continuous (openWeight n β k) :=
  ((chainWeight_continuous n β k).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).mul
    ((chainWeight_continuous n β k).comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

theorem openWeight_positive (β : ℝ) (k : ℕ) (z : OpenChain n k) : 0 < openWeight n β k z :=
  mul_pos (chainWeight_positive n β k _ _) (chainWeight_positive n β k _ _)

/-- Exact gluing factorization at the center slice. -/
theorem openWeight_fiber_integral (β : ℝ) (k : ℕ) (u : Slice n) :
    (∫ z, openWeight n β k (u, z) ∂(pathHaar n k).prod (pathHaar n k)) =
      (message n β k u) ^ 2 := by
  change (∫ z, chainWeight n β k u z.1 * chainWeight n β k u z.2
    ∂(pathHaar n k).prod (pathHaar n k)) = _
  rw [integral_prod_mul, chain_integral]
  ring


/-- The half-chain can equivalently be oriented toward the midpoint, by actual kernel symmetry. -/
theorem chainWeight_succ_reverse (β : ℝ) (k : ℕ) (u v : Slice n) (p : Path n k) :
    chainWeight n β (k + 1) u (Fin.cons v p) =
      kernel WilsonSingleLinkStaples.character β 2 v u * chainWeight n β k v p := by
  rw [chainWeight_succ]
  congr 1
  exact kernelMap_symm n β u v

def squareMass (β : ℝ) (k : ℕ) : ℝ := ∫ u, (message n β k u) ^ 2 ∂measure n

theorem squareMass_positive (β : ℝ) (k : ℕ) : 0 < squareMass n β k := by
  have hc := (message n β k).continuous.pow 2
  apply (integral_pos_iff_support_of_nonneg (fun u => sq_nonneg (message n β k u))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mpr
  have hs : Function.support (fun u => (message n β k u) ^ 2) = Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (sq_pos_of_pos (message_positive n β k u)).ne'
  simp [hs]

/-- The open-chain partition is the actual squared norm of the transfer iterate. -/
theorem squareMass_eq_norm_sq (β : ℝ) (k : ℕ) :
    squareMass n β k =
      ‖iterate (transfer n β) k (ContinuousMap.toLp 2 (measure n) ℂ
        (1 : C(Slice n, ℂ)))‖ ^ 2 := by
  rw [← message_embedding, real_embedding_norm_sq]
  rfl

theorem open_partition (β : ℝ) (k : ℕ) :
    (∫ z, openWeight n β k z ∂openHaar n k) = squareMass n β k := by
  rw [integral_prod _ ((openWeight_continuous n β k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  simp only [openWeight_fiber_integral]
  rfl

def openLaw (β : ℝ) (k : ℕ) : Measure (OpenChain n k) :=
  weightedLaw (openHaar n k) (openWeight n β k)

def midpointLaw (β : ℝ) (k : ℕ) : Measure (Slice n) :=
  weightedLaw (measure n) (fun u => (message n β k u) ^ 2)

theorem openLaw_probability (β : ℝ) (k : ℕ) : IsProbabilityMeasure (openLaw n β k) :=
  weightedLaw_probability _ _ (openWeight_continuous n β k).measurable
    ((openWeight_continuous n β k).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun z => (openWeight_positive n β k z).le)
    (by rw [open_partition]; exact squareMass_positive n β k)

theorem midpointLaw_probability (β : ℝ) (k : ℕ) : IsProbabilityMeasure (midpointLaw n β k) :=
  weightedLaw_probability _ _ ((message n β k).continuous.pow 2).measurable
    (((message n β k).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun u => sq_nonneg (message n β k u)) (squareMass_positive n β k)

/-- The exact midpoint expectation of the original finite open chain. -/
theorem midpoint_integral (β : ℝ) (k : ℕ) (F : Slice n → ℝ) (hF : Continuous F) :
    (∫ z, F z.1 ∂openLaw n β k) = ∫ u, F u ∂midpointLaw n β k := by
  have hnum : (∫ z, openWeight n β k z * F z.1 ∂openHaar n k) =
      ∫ u, (message n β k u) ^ 2 * F u ∂measure n := by
    have hc : Continuous (fun z : OpenChain n k => openWeight n β k z * F z.1) :=
      (openWeight_continuous n β k).mul (hF.comp continuous_fst)
    rw [integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro u
    dsimp only
    rw [integral_mul_const, openWeight_fiber_integral]
  rw [openLaw, weighted_integral _ _ (openWeight_continuous n β k).measurable
    (fun z => (openWeight_positive n β k z).le)
    (by rw [open_partition]; exact squareMass_positive n β k), open_partition, hnum]
  exact (weighted_integral (measure n) (fun u => (message n β k u) ^ 2)
    ((message n β k).continuous.pow 2).measurable (fun u => sq_nonneg (message n β k u))
    (squareMass_positive n β k) F).symm

/-- The midpoint measure is literally the pushforward of the constructed chain law. -/
theorem midpoint_map (β : ℝ) (k : ℕ) :
    (openLaw n β k).map Prod.fst = midpointLaw n β k := by
  letI := openLaw_probability n β k
  letI := midpointLaw_probability n β k
  letI := Measure.isProbabilityMeasure_map (μ := openLaw n β k) measurable_fst.aemeasurable
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro F
  rw [integral_map (f := fun u => F u) measurable_fst.aemeasurable
    F.continuous.aestronglyMeasurable]
  exact midpoint_integral n β k F F.continuous

end
end UnifiedTheory.Clay.YangMills.WilsonOpenSlab
