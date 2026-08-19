/-
  Audit/KFCausalCSpecHauptvermutungPhysicalBridge.lean

  Physical-growth interface for the quantitative Hauptvermutung.

  The existing checked ladder proves `global_hauptvermutung_mean`: local
  counting windows, curvature-volume bias, and pairwise chart consistency imply
  a global approximate isometry with explicit distortion.

  This file packages those hypotheses as a physical-growth certificate and
  proves that such a certificate closes the corresponding bridge field.  It
  does not assert that a specific growth law has the certificate; it turns that
  remaining claim into named, checkable data.

  Zero sorry.  Zero custom axioms.
-/

import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecKarcherClosure

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge

open Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecGluing
open UnifiedTheory.Audit.KFCausalCSpecKarcherClosure

/-- A concrete certificate that physical causal growth supplies the hypotheses
of the quantitative Hauptvermutung gluing theorem.

`X` is the finite/continuum event domain being reconstructed, `Y` is the target
linear model space, and `ι` indexes the finite family of local charts. -/
structure PhysicalGrowthHauptvermutungCertificate
    (X Y ι : Type*) [AddCommGroup Y] [Module ℝ Y] [Fintype ι] [Nonempty ι] where
  B : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ
  B_symm : ∀ x y, B x y = B y x
  G : X → X → ℝ
  pairConsistency : ℝ
  countWindow : ℝ
  curvatureBias : ℝ
  scale : ℝ
  density : ℝ
  density_pos : 0 < density
  countWindow_nonneg : 0 ≤ countWindow
  curvatureBias_nonneg : 0 ≤ curvatureBias
  chart : ι → X → Y
  count : ι → X → X → ℝ
  volume : ι → X → X → ℝ
  G_pos : ∀ x x', 0 < G x x'
  G_le_scale : ∀ x x', G x x' ≤ scale
  chart_count_eq : ∀ i x x',
    B (chart i x - chart i x') (chart i x - chart i x') =
      Real.sqrt (24 * count i x x' / (Real.pi * density))
  count_nonneg : ∀ i x x', 0 ≤ count i x x'
  volume_pos : ∀ i x x', 0 < volume i x x'
  count_concentration : ∀ i x x',
    |count i x x' / (density * volume i x x') - 1| ≤ countWindow
  curvature_bias_bound : ∀ i x x',
    |volume i x x' / ((Real.pi / 24) * (G x x') ^ 2) - 1| ≤ curvatureBias
  chart_pair_consistency : ∀ i j x x',
    |B ((chart i x - chart i x') - (chart j x - chart j x'))
       ((chart i x - chart i x') - (chart j x - chart j x'))|
      ≤ pairConsistency

namespace PhysicalGrowthHauptvermutungCertificate

/-- The arithmetic-mean global glue of the certificate's local charts. -/
noncomputable def globalGlue
    {X Y ι : Type*} [AddCommGroup Y] [Module ℝ Y] [Fintype ι] [Nonempty ι]
    (C : PhysicalGrowthHauptvermutungCertificate X Y ι) : X → Y :=
  fun x => (Fintype.card ι : ℝ)⁻¹ • ∑ i, C.chart i x

/-- The explicit distortion bound supplied by the quantitative Hauptvermutung
ladder for this certificate. -/
noncomputable def distortionBound
    {X Y ι : Type*} [AddCommGroup Y] [Module ℝ Y] [Fintype ι] [Nonempty ι]
    (C : PhysicalGrowthHauptvermutungCertificate X Y ι) : ℝ :=
  (C.countWindow + C.curvatureBias + C.countWindow * C.curvatureBias) *
    C.scale + C.pairConsistency / 2

/-- Target proposition for the bridge field
`quantitativeHauptvermutungAppliesToPhysicalGrowth`. -/
def QuantitativeHauptvermutungAppliesToPhysicalGrowth
    {X Y ι : Type*} [AddCommGroup Y] [Module ℝ Y] [Fintype ι] [Nonempty ι]
    (C : PhysicalGrowthHauptvermutungCertificate X Y ι) : Prop :=
  HasDistortion C.G
    (fun y y' => C.B (y - y') (y - y'))
    C.globalGlue
    C.distortionBound

/-- A physical-growth certificate closes the quantitative-Hauptvermutung bridge
field by applying the already-proved global mean-gluing theorem. -/
theorem applies_quantitative_hauptvermutung
    {X Y ι : Type*} [AddCommGroup Y] [Module ℝ Y] [Fintype ι] [Nonempty ι]
    (C : PhysicalGrowthHauptvermutungCertificate X Y ι) :
    C.QuantitativeHauptvermutungAppliesToPhysicalGrowth := by
  unfold QuantitativeHauptvermutungAppliesToPhysicalGrowth globalGlue distortionBound
  exact global_hauptvermutung_mean
    C.B C.B_symm C.G C.pairConsistency C.countWindow C.curvatureBias
    C.scale C.density C.density_pos C.countWindow_nonneg
    C.curvatureBias_nonneg C.chart C.count C.volume C.G_pos C.G_le_scale
    C.chart_count_eq C.count_nonneg C.volume_pos C.count_concentration
    C.curvature_bias_bound C.chart_pair_consistency

/-- Distortion bounds can always be weakened upward. -/
theorem hasDistortion_mono
    {X Y : Type*} (G : X → X → ℝ) (F : Y → Y → ℝ) (g : X → Y)
    {δ δ' : ℝ} (hδ : δ ≤ δ') :
    HasDistortion G F g δ → HasDistortion G F g δ' := by
  intro h x x'
  exact le_trans (h x x') hδ

/-- The explicit bound tends to zero when the counting window, curvature bias,
and chart-pair consistency all tend to zero while the scale is fixed. -/
theorem distortionBound_tendsto_zero
    (S : ℝ) (epsilon bias pair : ℕ → ℝ)
    (hepsilon : Tendsto epsilon atTop (𝓝 0))
    (hbias : Tendsto bias atTop (𝓝 0))
    (hpair : Tendsto pair atTop (𝓝 0)) :
    Tendsto
      (fun n => (epsilon n + bias n + epsilon n * bias n) * S + pair n / 2)
      atTop (𝓝 0) := by
  have hmain :
      Tendsto
        (fun n => (epsilon n + bias n + epsilon n * bias n) * S)
        atTop (𝓝 0) := by
    simpa using
      (((hepsilon.add hbias).add (hepsilon.mul hbias)).mul_const S)
  have hpair2 : Tendsto (fun n => pair n / 2) atTop (𝓝 0) :=
    by simpa using hpair.div_const 2
  simpa using hmain.add hpair2

/-- Certificate-sequence form: if a refinement family has fixed scale and its
three explicit error channels vanish, then its displayed Hauptvermutung
distortion bound vanishes. -/
theorem certificate_distortionBound_tendsto_zero
    {X Y ι : Type*} [AddCommGroup Y] [Module ℝ Y] [Fintype ι] [Nonempty ι]
    (C : ℕ → PhysicalGrowthHauptvermutungCertificate X Y ι) (S : ℝ)
    (hS : ∀ n, (C n).scale = S)
    (hcount : Tendsto (fun n => (C n).countWindow) atTop (𝓝 0))
    (hbias : Tendsto (fun n => (C n).curvatureBias) atTop (𝓝 0))
    (hpair : Tendsto (fun n => (C n).pairConsistency) atTop (𝓝 0)) :
    Tendsto (fun n => (C n).distortionBound) atTop (𝓝 0) := by
  have h :=
    distortionBound_tendsto_zero S
      (fun n => (C n).countWindow)
      (fun n => (C n).curvatureBias)
      (fun n => (C n).pairConsistency)
      hcount hbias hpair
  convert h using 1
  funext n
  simp [distortionBound, hS n]

#print axioms PhysicalGrowthHauptvermutungCertificate.applies_quantitative_hauptvermutung
#print axioms PhysicalGrowthHauptvermutungCertificate.hasDistortion_mono
#print axioms PhysicalGrowthHauptvermutungCertificate.distortionBound_tendsto_zero
#print axioms PhysicalGrowthHauptvermutungCertificate.certificate_distortionBound_tendsto_zero

end PhysicalGrowthHauptvermutungCertificate

end UnifiedTheory.Audit.KFCausalCSpecHauptvermutungPhysicalBridge
