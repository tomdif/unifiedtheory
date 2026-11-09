/- Explicit first and second kinetic outputs of the independent-width
packet, constructed from actual charged monomial Hilbert states. -/
import UnifiedTheory.Audit.KFCausalChargeRepresentativeAlgebra
import UnifiedTheory.Audit.KFCausalIndependentRadialPolynomialKinetic
import UnifiedTheory.Audit.KFCausalIndependentRadialPacketMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialKineticRepresentatives
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalSymmetricMomentumCoordinates (symmetricDirection)
open KFCausalAntisymmetricMomentumCoordinates (antiDirection antiSymbol)
open KFCausalIndependentRadialPolynomialMomentum (state state_charge_coe)
open KFCausalIndependentRadialPolynomialKinetic (inverseClock inverseClock_continuous inverseClock_memLp inverse_state)
open KFCausalIndependentRadialCoordinateMoments (coordinate profile monomial)
open KFCausalIndependentRadialMonomialDerivative (positionIndex)
open KFCausalIndependentRadialPacketProfiles (chargeProfile)
open KFCausalIndependentRadialKineticProfiles
  (position coefficient neutral firstProfile secondProfile profile_first_derivative profile_second_derivative)
open KFCausalNeutralLinePackets (step)
open KFCausalPairedModeCoordinates (scale)
open KFCausalChargeRepresentativeAlgebra (add_coe smul_coe)
open KFCausalClockFloorBoundedInverse (inverseL)

variable (α β wL wR c : ℝ) (hα : 0 < α) (hβ : 0 < β) (hL : 0 < wL) (hR : 0 < wR)
  (hmatch : Real.pi^2/α=α*c^2) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

def singleState (j : Fin 4) (m : ℕ) : Hilbert :=
  state α β wL wR c hα hβ hL hR hmatch b g hc hg P (Function.update 0 j m)

theorem single_coe (j : Fin 4) (m : ℕ) :
    chargeCoordinates (singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg j m)=ᵐ[volume]
      fun x => (coordinate c x j:ℂ)^m*chargeProfile α β wL wR c b P g x := by
  filter_upwards [state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P
    (Function.update 0 j m)] with x hx
  change (chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg P (Function.update 0 j m))) x=_
  rw [hx,profile]
  change KFCausalFiniteMonomialDerivative.monomial (Function.update 0 j m)
    (fun k => (coordinate c x k:ℂ))*_= _
  rw [KFCausalFiniteMonomialDerivative.exponent_update]
  simp

def baseState : Hilbert := singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg 0 0

theorem base_coe : chargeCoordinates (baseState α β wL wR c hα hβ hL hR hmatch b P g hc hg)=ᵐ[volume]
    chargeProfile α β wL wR c b P g := by
  simpa only [pow_zero,one_mul] using single_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg 0 0

private theorem position_coe (i : Fin 2) (m : ℕ) :
    chargeCoordinates (singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg (positionIndex i) m)=ᵐ[volume]
      fun x => (position i x:ℂ)^m*chargeProfile α β wL wR c b P g x := by
  have he (x : Joint 2 4) : coordinate c x (positionIndex i)=position i x := by fin_cases i <;> rfl
  simpa only [he] using single_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg (positionIndex i) m

def firstState (i : Fin 2) : Hilbert :=
  coefficient α wL wR i • singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg (positionIndex i) 1+
    (neutral i:ℂ) • baseState α β wL wR c hα hβ hL hR hmatch b (step β b P) g hc hg

def secondState (i : Fin 2) : Hilbert :=
  (coefficient α wL wR i*(2*(scale:ℂ))) • baseState α β wL wR c hα hβ hL hR hmatch b P g hc hg+
    (coefficient α wL wR i)^2 • singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg (positionIndex i) 2+
    (2*coefficient α wL wR i*(neutral i:ℂ)) •
      singleState α β wL wR c hα hβ hL hR hmatch b (step β b P) g hc hg (positionIndex i) 1+
    (neutral i:ℂ)^2 • baseState α β wL wR c hα hβ hL hR hmatch b (step β b (step β b P)) g hc hg

theorem first_coe (i : Fin 2) :
    chargeCoordinates (firstState α β wL wR c hα hβ hL hR hmatch b P g hc hg i)=ᵐ[volume]
      firstProfile α β wL wR c b P g i := by
  refine (add_coe _ _ _ _
    (smul_coe (coefficient α wL wR i) _ _ (position_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg i 1))
    (smul_coe (neutral i:ℂ) _ _ (base_coe α β wL wR c hα hβ hL hR hmatch b (step β b P) g hc hg))).trans ?_
  filter_upwards [] with x
  simp only [firstProfile,pow_one]
  ring

theorem second_coe (i : Fin 2) :
    chargeCoordinates (secondState α β wL wR c hα hβ hL hR hmatch b P g hc hg i)=ᵐ[volume]
      secondProfile α β wL wR c b P g i := by
  refine (add_coe _ _ _ _
    (add_coe _ _ _ _ (add_coe _ _ _ _
      (smul_coe (coefficient α wL wR i*(2*(scale:ℂ))) _ _ (base_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg))
      (smul_coe ((coefficient α wL wR i)^2) _ _ (position_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg i 2)))
      (smul_coe (2*coefficient α wL wR i*(neutral i:ℂ)) _ _ (position_coe α β wL wR c hα hβ hL hR hmatch b (step β b P) g hc hg i 1)))
    (smul_coe ((neutral i:ℂ)^2) _ _ (base_coe α β wL wR c hα hβ hL hR hmatch b (step β b (step β b P)) g hc hg))).trans ?_
  filter_upwards [] with x
  simp only [secondProfile,pow_one]
  ring

theorem first_graph (h : ℝ) (hh : h ≠ 0) (i : Fin 2) :
    (baseState α β wL wR c hα hβ hL hR hmatch b P g hc hg,
      (-Complex.I*(h:ℂ)) • firstState α β wL wR c hα hβ hL hR hmatch b P g hc hg i) ∈
        (transverseMomentum h (symmetricDirection i)).graph :=
  KFCausalChargeProfileMomentumGraph.derivative_graph h hh i _ _ _ _
    (base_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (first_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i)
    (profile_first_derivative α β wL wR c b P g i)

theorem second_graph (h : ℝ) (hh : h ≠ 0) (i : Fin 2) :
    (firstState α β wL wR c hα hβ hL hR hmatch b P g hc hg i,
      (-Complex.I*(h:ℂ)) • secondState α β wL wR c hα hβ hL hR hmatch b P g hc hg i) ∈
        (transverseMomentum h (symmetricDirection i)).graph :=
  KFCausalChargeProfileMomentumGraph.derivative_graph h hh i _ _ _ _
    (first_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i) (second_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i)
    (profile_second_derivative α β wL wR c b P g i)

variable (ε : ℝ) (hε : 0 < ε)

theorem inverse_single (j : Fin 4) (m : ℕ) :
    inverseL ε hε (singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg j m)=
      singleState α β wL wR c hα hβ hL hR hmatch b P (inverseClock ε g)
        (inverseClock_continuous ε hε g hc) (inverseClock_memLp ε hε g hc hg) j m :=
  inverse_state α β wL wR c hα hβ hL hR hmatch b g hc hg ε hε P _

theorem inverse_second (i : Fin 2) :
    inverseL ε hε (secondState α β wL wR c hα hβ hL hR hmatch b P g hc hg i)=
      secondState α β wL wR c hα hβ hL hR hmatch b P (inverseClock ε g)
        (inverseClock_continuous ε hε g hc) (inverseClock_memLp ε hε g hc hg) i := by
  simp only [secondState,baseState,map_add,map_smul,inverse_single]

theorem symmetric_square (h : ℝ) (hh : h ≠ 0) (i : Fin 2) :
    (baseState α β wL wR c hα hβ hL hR hmatch b P g hc hg,
      inverseL ε hε (inverseL ε hε ((-(h:ℂ)^2) • secondState α β wL wR c hα hβ hL hR hmatch b P g hc hg i))) ∈
        (KFCausalClockFloorKineticSquare.square ε h (symmetricDirection i)).graph := by
  let gd := inverseClock ε g
  let hcd := inverseClock_continuous ε hε g hc
  let hgd := inverseClock_memLp ε hε g hc hg
  have hf := first_graph α β wL wR c hα hβ hL hR hmatch b P gd hcd hgd h hh i
  have hs := (transverseMomentum h (symmetricDirection i)).graph.smul_mem (-Complex.I*(h:ℂ))
    (second_graph α β wL wR c hα hβ hL hR hmatch b P gd hcd hgd h hh i)
  have hh2 : (-Complex.I*(h:ℂ))*(-Complex.I*(h:ℂ))= -(h:ℂ)^2 := by
    calc
      _ = Complex.I*Complex.I*(h:ℂ)^2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  simp only [Prod.smul_mk,smul_smul,hh2] at hs
  apply (KFCausalClockFloorKineticSquare.square_graph ε hε h (symmetricDirection i) _ _).mpr
  refine ⟨_,_,?_,hs,?_⟩
  · simpa only [baseState,inverse_single] using hf
  · simp only [map_smul,inverse_second]
    rfl

def antiFactor (h c : ℝ) : ℂ := ((2*Real.pi*h*(2*scale)/c:ℝ):ℂ)

theorem single_zero (j : Fin 4) :
    singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg j 0=
      baseState α β wL wR c hα hβ hL hR hmatch b P g hc hg := by
  simp [singleState,baseState]

theorem antisymmetric_step (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (m : ℕ) :
    (singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg i.castSucc.castSucc m,
      antiFactor h c • singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg i.castSucc.castSucc (m+1)) ∈
        (transverseMomentum h (antiDirection i)).graph := by
  have hc0 : c ≠ 0 := by
    intro he
    have hp := (div_pos (sq_pos_of_pos Real.pi_pos) hα).ne'
    apply hp
    simpa [he] using hmatch
  apply (KFCausalAntisymmetricMomentumGraphEquivalence.antisymmetric_graph_iff h hh i _ _).mpr
  filter_upwards [smul_coe _ _ _ (single_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg i.castSucc.castSucc (m+1)),
    single_coe α β wL wR c hα hβ hL hR hmatch b P g hc hg i.castSucc.castSucc m] with x hx hy
  rw [hx,hy]
  have hi : coordinate c x i.castSucc.castSucc=c*x (.inl i) := by fin_cases i <;> rfl
  have he : antiFactor h c*(coordinate c x i.castSucc.castSucc:ℂ)=(antiSymbol h i x:ℂ) := by
    rw [antiFactor,← Complex.ofReal_mul,hi]
    congr 1
    unfold antiSymbol
    field_simp
  rw [pow_succ]
  calc
    _ = (antiFactor h c*(coordinate c x i.castSucc.castSucc:ℂ))*
      ((coordinate c x i.castSucc.castSucc:ℂ)^m*chargeProfile α β wL wR c b P g x) := by ring
    _ = _ := by rw [he]

theorem antisymmetric_square (h : ℝ) (hh : h ≠ 0) (i : Fin 2) :
    (baseState α β wL wR c hα hβ hL hR hmatch b P g hc hg,
      inverseL ε hε (inverseL ε hε ((antiFactor h c)^2 •
        singleState α β wL wR c hα hβ hL hR hmatch b P g hc hg i.castSucc.castSucc 2))) ∈
          (KFCausalClockFloorKineticSquare.square ε h (antiDirection i)).graph := by
  let gd := inverseClock ε g
  let hcd := inverseClock_continuous ε hε g hc
  let hgd := inverseClock_memLp ε hε g hc hg
  have hf := antisymmetric_step α β wL wR c hα hβ hL hR hmatch b P gd hcd hgd h hh i 0
  rw [single_zero] at hf
  have hs := (transverseMomentum h (antiDirection i)).graph.smul_mem (antiFactor h c)
    (antisymmetric_step α β wL wR c hα hβ hL hR hmatch b P gd hcd hgd h hh i 1)
  simp only [Prod.smul_mk,smul_smul,← pow_two] at hs
  apply (KFCausalClockFloorKineticSquare.square_graph ε hε h (antiDirection i) _ _).mpr
  refine ⟨_,_,?_,hs,?_⟩
  · simpa only [baseState,inverse_single] using hf
  · simp only [map_smul,inverse_single]
    rfl

#print axioms single_zero
#print axioms antisymmetric_step
#print axioms antisymmetric_square
#print axioms single_coe
#print axioms base_coe
#print axioms first_coe
#print axioms second_coe
#print axioms first_graph
#print axioms second_graph
#print axioms inverse_single
#print axioms inverse_second
#print axioms symmetric_square
end
end UnifiedTheory.Audit.KFCausalIndependentRadialKineticRepresentatives
