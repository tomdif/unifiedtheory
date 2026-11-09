/- The actual transverse shear differential of sourced Gaussian packets
is a polynomial of degree at most two times the packet and belongs to L2.
The product-domain theorem then allows arbitrary square-integrable clocks. -/
import UnifiedTheory.Audit.KFCausalGaussianQuadraticMoments
import UnifiedTheory.Audit.KFCausalTransverseShearProductDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalCoherentShearDifferential
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments (widths)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSources (linearSource)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentMoments
open UnifiedTheory.Audit.KFCausalClockFloorCoherentDerivative
open UnifiedTheory.Audit.KFCausalGaussianQuadraticMoments
open UnifiedTheory.Audit.KFCausalTransverseShearProductDomain
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

theorem sourcedPacket_contDiff (α β : ℝ) (b : Fin 5 → ℂ) : ContDiff ℝ 1 (sourcedPacket α β b) := by
  have hs : ContDiff ℝ 1 (linearSource b) := by
    unfold linearSource
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (by fun_prop : ContDiff ℝ 1 (fun x : Transverse => x i)))
  have hq : ContDiff ℝ 1 (fun x : Transverse => α*∑ i : Fin 4, (x i.castSucc)^2+β*(x 4)^2) := by
    fun_prop
  exact hs.cexp.mul (Complex.ofRealCLM.contDiff.comp hq).neg.cexp

theorem velocity_packet_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (i : Fin 5) :
    MemLp (fun y : Transverse => (velocity y i:ℂ)*sourcedPacket α β b y) 2 volume := by
  by_cases hi : i=4
  · simpa only [velocity,if_pos hi,Complex.ofReal_add,add_mul] using
      (sourcedPacket_coordinate_memLp α β hα hβ hw b 2).add
        (sourcedPacket_coordinate_memLp α β hα hβ hw b 3)
  · convert (sourcedPacket_coordinate_memLp α β hα hβ hw b i).const_mul (1/2:ℂ) using 1
    funext y
    simp only [velocity,if_neg hi,Complex.ofReal_div,Complex.ofReal_ofNat]
    ring

theorem velocity_coordinate_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (i j : Fin 5) :
    MemLp (fun y : Transverse => (velocity y i:ℂ)*(y j:ℂ)*sourcedPacket α β b y) 2 volume := by
  by_cases hi : i=4
  · simpa only [velocity,if_pos hi,Complex.ofReal_add,add_mul] using
      (sourced_mixed_memLp α β hα hβ hw b 2 j).add
        (sourced_mixed_memLp α β hα hβ hw b 3 j)
  · convert (sourced_mixed_memLp α β hα hβ hw b i j).const_mul (1/2:ℂ) using 1
    funext y
    simp only [velocity,if_neg hi,Complex.ofReal_div,Complex.ofReal_ofNat]
    ring

theorem shear_gradient_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) :
    MemLp (fun y => gradient α β b (velocity y) y) 2 volume := by
  have hfirst : MemLp (fun y => linearSource b (velocity y)*sourcedPacket α β b y) 2 volume := by
    simp only [linearSource,Finset.sum_mul]
    apply memLp_finset_sum
    intro i _
    simpa only [mul_assoc] using (velocity_packet_memLp α β hα hβ hw b i).const_mul (b i)
  apply hfirst.add
  apply memLp_finset_sum
  intro i _
  simpa only [Complex.ofReal_mul,mul_assoc] using
    (velocity_coordinate_memLp α β hα hβ hw b i i).const_mul ((-2*widths α β i:ℝ):ℂ)

theorem packetDifferential_eq (α β : ℝ) (b : Fin 5 → ℂ) (y : Transverse) :
    packetDifferential (sourcedPacket α β b) y = gradient α β b (velocity y) y+sourcedPacket α β b y := by
  have he := (sourcedPacket_hasLineDerivAt α β b (velocity y) y).unique
    ((sourcedPacket_differentiable α β b y).hasFDerivAt.hasLineDerivAt (velocity y))
  exact congrArg (fun z => z+sourcedPacket α β b y) he.symm

theorem packetDifferential_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) : MemLp (packetDifferential (sourcedPacket α β b)) 2 volume := by
  rw [funext (packetDifferential_eq α β b)]
  exact (shear_gradient_memLp α β hα hβ hw b).add (sourcedPacket_memLp α β hα hβ hw b)

def profileOutput (h : ℝ) (C : ℂ) (p α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    UnifiedTheory.Audit.KFCausalConfigurationTestSpace.Hilbert :=
  (-Complex.I*(h:ℂ)) • KFCausalL2TensorEmbedding.productState volume volume
    ((clockMultiplier_memLp C p g hg).toLp (clockMultiplier C p g))
    ((packetDifferential_memLp α β hα hβ hw b).toLp (packetDifferential (sourcedPacket α β b)))

theorem profileOutput_coe (h : ℝ) (C : ℂ) (p α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    profileOutput h C p α β hα hβ hw b g hg =ᵐ[volume] fun x =>
      (-Complex.I*(h:ℂ))*clockMultiplier C p g x.1*
        (gradient α β b (velocity x.2) x.2+sourcedPacket α β b x.2) := by
  let hm := clockMultiplier_memLp C p g hg
  let hd := packetDifferential_memLp α β hα hβ hw b
  let hp := KFCausalPhysicalGaussianDerivative.configuration_product_memLp _ _ hm hd
  have he : profileOutput h C p α β hα hβ hw b g hg =
      (-Complex.I*(h:ℂ)) • hp.toLp (fun x : Configuration =>
        clockMultiplier C p g x.1*packetDifferential (sourcedPacket α β b) x.2) :=
    congrArg (fun z => (-Complex.I*(h:ℂ)) • z) (product_toLp _ _ hm hd)
  rw [he]
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ)) (hp.toLp _),hp.coeFn_toLp] with x hx hy
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hy,packetDifferential_eq]
  ring

theorem physicalProfile_graph (h : ℝ) (hh : h ≠ 0) (C : ℂ) (p α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (b : Fin 5 → ℂ)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    ((physicalProfile_memLp C p α β hα hβ hw b g hg).toLp (physicalProfile C p α β b g),
      profileOutput h C p α β hα hβ hw b g hg) ∈ (shearMomentum h).graph := by
  have hgph := product_graph h hh (sourcedPacket α β b) (sourcedPacket_contDiff α β b)
    (sourcedPacket_memLp α β hα hβ hw b) (packetDifferential_memLp α β hα hβ hw b)
    ((clockMultiplier_memLp C p g hg).toLp (clockMultiplier C p g))
  rw [product_toLp] at hgph
  exact hgph

#print axioms sourcedPacket_contDiff
#print axioms velocity_packet_memLp
#print axioms velocity_coordinate_memLp
#print axioms shear_gradient_memLp
#print axioms packetDifferential_eq
#print axioms packetDifferential_memLp
#print axioms profileOutput_coe
#print axioms physicalProfile_graph
end
end UnifiedTheory.Audit.KFCausalCoherentShearDifferential
