/- The actual shear graph of a transverse C1 packet extends to every L2
clock factor. Closedness and smooth clock approximation remove clock
regularity assumptions without changing the physical generator. -/
import UnifiedTheory.Audit.KFCausalTransverseShearDifferentialDomain
import UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative
import UnifiedTheory.Audit.KFCausalProductPhaseTranslation
import Mathlib.Analysis.Normed.Lp.SmoothApprox

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalTransverseShearProductDomain
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding (productState productState_coe productBilinear)
open UnifiedTheory.Audit.KFCausalProductPhaseTranslation (product_norm)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative (configuration_product_memLp)
open UnifiedTheory.Audit.KFCausalCanonicalClockDerivative (clockDerivative)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum shear_closed)
open UnifiedTheory.Audit.KFCausalTransverseShearDifferentialDomain (graph_of_differentials)

abbrev ClockHilbert := Lp ℂ 2 (volume : Measure ℝ)
abbrev PacketHilbert := Lp ℂ 2 (volume : Measure Transverse)

def packetDifferential (p : Transverse → ℂ) (y : Transverse) : ℂ :=
  fderiv ℝ p y (velocity y)+p y

def insertPacket (p : PacketHilbert) : ClockHilbert →L[ℂ] Hilbert :=
  ((productBilinear volume volume).flip p).mkContinuous ‖p‖ (fun g => by
    change ‖productState volume volume g p‖ ≤ ‖p‖*‖g‖
    rw [product_norm,mul_comm])

theorem product_toLp (g : ℝ → ℂ) (p : Transverse → ℂ)
    (hg : MemLp g 2 volume) (hp : MemLp p 2 volume) :
    productState volume volume (hg.toLp g) (hp.toLp p) =
      (configuration_product_memLp g p hg hp).toLp (fun z : Configuration => g z.1*p z.2) := by
  apply Lp.ext
  filter_upwards [productState_coe volume volume (hg.toLp g) (hp.toLp p),
    MeasureTheory.Measure.quasiMeasurePreserving_fst.ae hg.coeFn_toLp,
    MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hp.coeFn_toLp,
    (configuration_product_memLp g p hg hp).coeFn_toLp] with z ha hb hc hd
  rw [ha,hd,hb,hc]

theorem product_clock (g : ℝ → ℂ) (p : Transverse → ℂ)
    (hg : Differentiable ℝ g) (hp : Differentiable ℝ p) (x : Configuration) :
    clockDerivative (fun z : Configuration => g z.1*p z.2) x =
      (fderiv ℝ g x.1) 1*p x.2 := by
  have hd := ((hg x.1).hasFDerivAt.comp x hasFDerivAt_fst).mul
    ((hp x.2).hasFDerivAt.comp x hasFDerivAt_snd)
  change HasFDerivAt (fun z : Configuration => g z.1*p z.2) _ x at hd
  rw [clockDerivative,hd.fderiv]
  simp [mul_comm]

theorem product_shear (g : ℝ → ℂ) (p : Transverse → ℂ)
    (hg : Differentiable ℝ g) (hp : Differentiable ℝ p) (x : Configuration) :
    shearDerivative (fun z : Configuration => g z.1*p z.2) x = g x.1*packetDifferential p x.2 := by
  have hd := ((hg x.1).hasFDerivAt.comp x hasFDerivAt_fst).mul
    ((hp x.2).hasFDerivAt.comp x hasFDerivAt_snd)
  change HasFDerivAt (fun z : Configuration => g z.1*p z.2) _ x at hd
  rw [shearDerivative,hd.fderiv]
  simp [packetDifferential,mul_add]

theorem compact_clock_graph (h : ℝ) (hh : h ≠ 0) (g : ℝ → ℂ)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (p : Transverse → ℂ)
    (hp : ContDiff ℝ 1 p) (hm : MemLp p 2 volume) (hd : MemLp (packetDifferential p) 2 volume) :
    (productState volume volume ((hg.continuous.memLp_of_hasCompactSupport hc).toLp g) (hm.toLp p),
      (-Complex.I*(h:ℂ)) • productState volume volume
        ((hg.continuous.memLp_of_hasCompactSupport hc).toLp g) (hd.toLp (packetDifferential p))) ∈
      (shearMomentum h).graph := by
  let hgm : MemLp g 2 (volume : Measure ℝ) := hg.continuous.memLp_of_hasCompactSupport hc
  have hgd : MemLp (fun s => fderiv ℝ g s (1:ℝ)) 2 volume :=
    ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ (1:ℝ))
  have hs := funext (product_shear g p (hg.differentiable (by norm_num)) (hp.differentiable (by norm_num)))
  have hq := funext (product_clock g p (hg.differentiable (by norm_num)) (hp.differentiable (by norm_num)))
  have hsm : MemLp (shearDerivative (fun z : Configuration => g z.1*p z.2)) 2 volume := by
    rw [hs]
    exact configuration_product_memLp g _ hgm hd
  have hqm : MemLp (clockDerivative (fun z : Configuration => g z.1*p z.2)) 2 volume := by
    rw [hq]
    exact configuration_product_memLp _ p hgd hm
  have hgraph := graph_of_differentials h hh (fun z : Configuration => g z.1*p z.2)
    (configuration_product_memLp g p hgm hm) ((hg.comp contDiff_fst).mul (hp.comp contDiff_snd)) hqm hsm
  rw [product_toLp,product_toLp]
  have he : hsm.toLp _ = (configuration_product_memLp g _ hgm hd).toLp
      (fun z : Configuration => g z.1*packetDifferential p z.2) := by
    apply Lp.ext
    filter_upwards [hsm.coeFn_toLp,(configuration_product_memLp g _ hgm hd).coeFn_toLp] with x ha hb
    rw [ha,hb,congrFun hs x]
  rw [he] at hgraph
  exact hgraph

theorem product_graph (h : ℝ) (hh : h ≠ 0) (p : Transverse → ℂ)
    (hp : ContDiff ℝ 1 p) (hm : MemLp p 2 volume) (hd : MemLp (packetDifferential p) 2 volume)
    (g : ClockHilbert) :
    (productState volume volume g (hm.toLp p),
      (-Complex.I*(h:ℂ)) • productState volume volume g (hd.toLp (packetDifferential p))) ∈
      (shearMomentum h).graph := by
  let S : Set ClockHilbert := {g | (productState volume volume g (hm.toLp p),
      (-Complex.I*(h:ℂ)) • productState volume volume g (hd.toLp (packetDifferential p))) ∈
      (shearMomentum h).graph}
  have hS : IsClosed S := (shear_closed h hh).preimage
    ((insertPacket (hm.toLp p)).continuous.prodMk
      ((insertPacket (hd.toLp (packetDifferential p))).continuous.const_smul (-Complex.I*(h:ℂ))))
  have hsub : {f : ClockHilbert | ∃ φ : ℝ → ℂ, f =ᵐ[volume] φ ∧ HasCompactSupport φ ∧ ContDiff ℝ (↑(⊤:ℕ∞)) φ} ⊆ S := by
    rintro f ⟨φ,hφ,hc,hs⟩
    have hmφ : MemLp φ 2 (volume : Measure ℝ) := hs.continuous.memLp_of_hasCompactSupport hc
    have he : f = hmφ.toLp φ := Lp.ext (hφ.trans hmφ.coeFn_toLp.symm)
    rw [he]
    exact compact_clock_graph h hh φ (hs.of_le (by norm_num)) hc p hp hm hd
  exact (closure_minimal hsub hS)
    (Lp.dense_hasCompactSupport_contDiff (E := ℝ) (F := ℂ) (μ := volume) (p := 2) (by norm_num) g)

#print axioms product_toLp
#print axioms product_clock
#print axioms product_shear
#print axioms compact_clock_graph
#print axioms product_graph
end
end UnifiedTheory.Audit.KFCausalTransverseShearProductDomain
