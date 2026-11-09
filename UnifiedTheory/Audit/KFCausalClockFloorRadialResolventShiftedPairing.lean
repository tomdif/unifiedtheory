/- Conjugation symmetry of the complex clock inverse and the shifted
radial Yosida and radial resolvent multipliers. Moving a shifted radial
multiplier or resolvent across the physical Hilbert inner product negates
the imaginary clock shift. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventShifted
import UnifiedTheory.Audit.KFCausalClockFloorRadialResolventRegularizer

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialResolventShiftedPairing
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (Space FrequencyHilbert)
open KFCausalEuclideanClockSplit (TailSpace tail)
open KFCausalComplexClockChart (complexChart closedStrip openStrip targetStrip)
open KFCausalComplexClockInverse
  (complexInverse complexInverse_left complexInverse_right complexInverse_mem)
open KFCausalClockFloorRadialYosidaStrip
  (base cutoff radialComplex multiplier sixth_strip_subset)
open KFCausalClockFloorRadialYosidaOrderedTransport
  (family family_line_continuous family_bound mixedTail shifted_zero)
open KFCausalClockFloorRadialResolventShifted
  (coordinates line shifted shifted_coe)

theorem zero_shift_bound (ε : ℝ) (hε : 0 < ε) :
    |(0:ℝ)| ≤ Real.pi*ε/6 := by
  rw [abs_zero]
  positivity

theorem neg_shift_bound (ε y : ℝ) (hy : |y| ≤ Real.pi*ε/6) :
    |-y| ≤ Real.pi*ε/6 := by
  simpa only [abs_neg] using hy

theorem half_shift_bound (ε h : ℝ) (hb : |h| ≤ Real.pi*ε/3) :
    |h/2| ≤ Real.pi*ε/6 := by
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  linarith

theorem complexChart_conj (ε : ℝ) (z : ℂ) :
    complexChart ε (starRingEnd ℂ z) = starRingEnd ℂ (complexChart ε z) := by
  unfold complexChart
  rw [map_add,map_mul,Complex.exp_conj,Complex.conj_ofReal]

theorem closedStrip_conj {z : ℂ} (hz : z ∈ closedStrip) :
    starRingEnd ℂ z ∈ closedStrip := by
  change |(starRingEnd ℂ z).im| ≤ Real.pi/2
  simpa only [Complex.conj_im,abs_neg] using hz

theorem targetStrip_conj (ε : ℝ) {q : ℂ} (hq : q ∈ targetStrip ε) :
    starRingEnd ℂ q ∈ targetStrip ε := by
  change |(starRingEnd ℂ q).im| ≤ Real.pi*ε/2
  simpa only [Complex.conj_im,abs_neg] using hq

theorem complexInverse_conj (ε : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε) :
    complexInverse ε (starRingEnd ℂ q) = starRingEnd ℂ (complexInverse ε q) := by
  let z := complexInverse ε q
  have hz : z ∈ closedStrip := by
    change |z.im| ≤ Real.pi/2
    exact (complexInverse_mem ε hε q hq).le
  have hzc : starRingEnd ℂ z ∈ closedStrip := closedStrip_conj hz
  have hq' : complexChart ε (starRingEnd ℂ z) = starRingEnd ℂ q := by
    rw [complexChart_conj,complexInverse_right ε hε q hq]
  rw [← hq',complexInverse_left ε hε (starRingEnd ℂ z) hzc]

theorem base_conj (ε A B : ℝ) (z : ℂ) :
    base ε A B (starRingEnd ℂ z) = starRingEnd ℂ (base ε A B z) := by
  unfold base
  simp only [map_div₀,map_add,map_mul,map_ofNat,Complex.conj_ofReal]

theorem cutoff_conj (N : ℝ) (z : ℂ) :
    cutoff N (starRingEnd ℂ z) = starRingEnd ℂ (cutoff N z) := by
  unfold cutoff
  simp only [map_div₀,map_mul,map_add,Complex.conj_ofReal]

theorem radialComplex_conj (ε : ℝ) (hε : 0 < ε) (h : ℝ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/6) (x : KFCausalEuclideanProductCoordinates.Block 2 ×
      KFCausalEuclideanProductCoordinates.Block 4) :
    radialComplex ε h (starRingEnd ℂ q) x = starRingEnd ℂ (radialComplex ε h q x) := by
  unfold radialComplex
  rw [complexInverse_conj ε hε q (sixth_strip_subset ε hε q hq),
    Complex.exp_conj,base_conj]

theorem multiplier_conj (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/6) (x : KFCausalEuclideanProductCoordinates.Block 2 ×
      KFCausalEuclideanProductCoordinates.Block 4) :
    multiplier ε h N (starRingEnd ℂ q) x = starRingEnd ℂ (multiplier ε h N q x) := by
  unfold multiplier
  rw [radialComplex_conj ε hε h q hq x,cutoff_conj]

theorem family_conj (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/6) (z : TailSpace) :
    family ε h N (starRingEnd ℂ q) z = starRingEnd ℂ (family ε h N q z) :=
  multiplier_conj ε hε h N q hq (mixedTail z)

theorem symbol_conj (ε : ℝ) (hε : 0 < ε) (h N y : ℝ)
    (hy : |y| ≤ Real.pi*ε/6) (x : Space) :
    starRingEnd ℂ (KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y x) =
      KFCausalStripFamilyExponentialGraph.symbol (family ε h N) (-y) x := by
  unfold KFCausalStripFamilyExponentialGraph.symbol
  have hq : |((x 0:ℂ)+(y:ℂ)*Complex.I).im| ≤ Real.pi*ε/6 := by
    simpa using hy
  rw [← family_conj ε hε h N ((x 0:ℂ)+(y:ℂ)*Complex.I) hq (tail x)]
  congr 1
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,
    Complex.ofReal_neg,neg_mul,mul_neg]

theorem line_conj (ε : ℝ) (hε : 0 < ε) (h N y : ℝ)
    (hy : |y| ≤ Real.pi*ε/6) (x : Space) :
    starRingEnd ℂ (line ε h N y x) = line ε h N (-y) x := by
  unfold line
  rw [map_sub,map_one,map_mul,map_inv₀,Complex.conj_ofReal,symbol_conj ε hε h N y hy x]

theorem shiftedMultiplier_coe (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/6) (f : Hilbert) :
    coordinates ε hε (KFCausalClockFloorRadialYosidaOrderedTransport.shifted ε hε h N hN y hy f)
      =ᵐ[volume]
      fun x : Space =>
        KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y x*
          (coordinates ε hε f) x := by
  have ha := KFCausalMixedStripExponentialGraph.action_coe ε hε (family ε h N)
    (Real.pi*ε/6) N (family_line_continuous ε hε h N hN) hN.le
    (family_bound ε hε h N hN) y hy f
  have hc (g : Hilbert) :
      coordinates ε hε g =
        KFCausalClockFloorDefectCoordinates.straightening ε hε
          (KFCausalMixedStripExponentialGraph.unitary ε hε g) := by
    unfold coordinates
    rfl
  simpa only [hc] using ha

theorem shiftedMultiplier_zero (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (f : Hilbert) :
    KFCausalClockFloorRadialYosidaOrderedTransport.shifted ε hε h N hN 0 (zero_shift_bound ε hε) f =
      KFCausalClockFloorRadialYosidaSymbol.action ε hε h N hN f :=
  shifted_zero ε hε h N hN (zero_shift_bound ε hε) f

theorem shiftedResolvent_zero (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (f : Hilbert) :
    shifted ε hε h N hN 0 (zero_shift_bound ε hε) f =
      KFCausalClockFloorRadialResolventRegularizer.action ε hε h N hN f := by
  simp only [shifted,KFCausalClockFloorRadialResolventRegularizer.action,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply,shifted_zero]

theorem shiftedMultiplier_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/6) (f g : Hilbert) :
    inner ℂ (KFCausalClockFloorRadialYosidaOrderedTransport.shifted ε hε h N hN y hy f) g =
      inner ℂ f (KFCausalClockFloorRadialYosidaOrderedTransport.shifted ε hε h N hN (-y)
        (neg_shift_bound ε y hy) g) := by
  rw [← (coordinates ε hε).inner_map_map,
    ← (coordinates ε hε).inner_map_map f,
    L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [shiftedMultiplier_coe ε hε h N hN y hy f,
    shiftedMultiplier_coe ε hε h N hN (-y) (neg_shift_bound ε y hy) g] with x hf hg
  rw [hf,hg]
  change inner ℂ (KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y x •
      (coordinates ε hε f) x) ((coordinates ε hε g) x) =
    inner ℂ ((coordinates ε hε f) x)
      (KFCausalStripFamilyExponentialGraph.symbol (family ε h N) (-y) x •
        (coordinates ε hε g) x)
  rw [inner_smul_left,inner_smul_right,symbol_conj ε hε h N y hy x]

theorem shiftedResolvent_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/6) (f g : Hilbert) :
    inner ℂ (shifted ε hε h N hN y hy f) g =
      inner ℂ f (shifted ε hε h N hN (-y) (neg_shift_bound ε y hy) g) := by
  rw [← (coordinates ε hε).inner_map_map,
    ← (coordinates ε hε).inner_map_map f,
    L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [shifted_coe ε hε h N hN y hy f,
    shifted_coe ε hε h N hN (-y) (neg_shift_bound ε y hy) g] with x hf hg
  rw [hf,hg]
  change inner ℂ (line ε h N y x • (coordinates ε hε f) x) ((coordinates ε hε g) x) =
    inner ℂ ((coordinates ε hε f) x) (line ε h N (-y) x • (coordinates ε hε g) x)
  rw [inner_smul_left,inner_smul_right,line_conj ε hε h N y hy x]

theorem shiftedResolvent_zero_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (f g : Hilbert) :
    inner ℂ (shifted ε hε h N hN 0 (zero_shift_bound ε hε) f) g =
      inner ℂ f (shifted ε hε h N hN 0 (zero_shift_bound ε hε) g) := by
  simpa only [neg_zero] using
    shiftedResolvent_pairing ε hε h N hN 0 (zero_shift_bound ε hε) f g

theorem shiftedResolvent_half_pairing (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi*ε/3) (f g : Hilbert) :
    inner ℂ (shifted ε hε h N hN (-h/2)
      (KFCausalClockFloorRadialYosidaOrderedTransport.shift_bound ε h hb) f) g =
      inner ℂ f (shifted ε hε h N hN (h/2) (half_shift_bound ε h hb) g) := by
  have hp := shiftedResolvent_pairing ε hε h N hN (-h/2)
    (KFCausalClockFloorRadialYosidaOrderedTransport.shift_bound ε h hb) f g
  have hneg : -(-h/2) = h/2 := by ring
  simpa only [hneg] using hp

#print axioms zero_shift_bound
#print axioms neg_shift_bound
#print axioms half_shift_bound
#print axioms complexChart_conj
#print axioms closedStrip_conj
#print axioms targetStrip_conj
#print axioms complexInverse_conj
#print axioms base_conj
#print axioms cutoff_conj
#print axioms radialComplex_conj
#print axioms multiplier_conj
#print axioms family_conj
#print axioms symbol_conj
#print axioms line_conj
#print axioms shiftedMultiplier_coe
#print axioms shiftedMultiplier_zero
#print axioms shiftedResolvent_zero
#print axioms shiftedMultiplier_pairing
#print axioms shiftedResolvent_pairing
#print axioms shiftedResolvent_zero_pairing
#print axioms shiftedResolvent_half_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialResolventShiftedPairing
