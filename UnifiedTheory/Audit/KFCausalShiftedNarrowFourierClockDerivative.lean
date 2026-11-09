/- Clock derivatives of the transformed Gaussian normalization, charged
radius and the complete neutral/field coefficient. Both shifts move. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredShiftedNarrowProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalShiftedNarrowFourierClockDerivative
noncomputable section
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalShiftedNarrowFourierGeometry
open KFCausalShiftedNarrowFourierSlices (neutralPacket)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredShiftedNarrowProfiles (coefficient)

def neutralSlope (rd : ℂ) (v : Block 4) : ℂ :=
  4*(KFCausalPairedModeCoordinates.scale:ℂ)*rd*(v 2:ℂ)
def fieldSlope (td : ℂ) (v : Block 4) : ℂ :=
  6*(KFCausalPairedModeCoordinates.scale:ℂ)*td*(v 2:ℂ)
def radiusSlope (A Ad : ℂ) (u : Block 2) (v : Block 4) : ℂ :=
  -((Real.pi:ℂ)^2*Ad/A^2)*(‖u‖:ℂ)^2+Ad*(broadRadius v:ℂ)
def packetSlope (β : ℝ) (r rd b : ℂ) (P : Polynomial ℂ) (v : Block 4) : ℂ :=
  Complex.exp (-(β:ℂ)*neutral r v^2+b*neutral r v)*
    ((b-2*(β:ℂ)*neutral r v)*P.eval (neutral r v)+P.derivative.eval (neutral r v))*
    neutralSlope rd v

theorem neutral_derivative (r : ℝ → ℂ) (rd : ℂ) (s : ℝ) (v : Block 4)
    (hr : HasDerivAt r rd s) :
    HasDerivAt (fun x => neutral (r x) v) (neutralSlope rd v) s := by
  convert (((hr.sub_const 1).const_mul (4*(KFCausalPairedModeCoordinates.scale:ℂ))).mul_const
    (v 2:ℂ)).const_add (v 3:ℂ) using 1

theorem field_derivative (t : ℝ → ℂ) (td : ℂ) (s : ℝ) (v : Block 4)
    (ht : HasDerivAt t td s) :
    HasDerivAt (fun x => mixedField (t x) v) (fieldSlope td v) s := by
  convert ((((ht.const_mul 3).sub_const 2).const_mul (2*(KFCausalPairedModeCoordinates.scale:ℂ))).mul_const
    (v 2:ℂ)).const_add (v 3:ℂ) using 1
  dsimp [fieldSlope]
  ring

theorem radius_derivative (A : ℝ → ℂ) (Ad : ℂ) (s : ℝ) (u : Block 2) (v : Block 4)
    (hA : HasDerivAt A Ad s) (hne : A s ≠ 0) :
    HasDerivAt (fun x => radius (A x) u v) (radiusSlope (A s) Ad u v) s := by
  convert (((hasDerivAt_const s ((Real.pi:ℂ)^2)).div hA hne).mul_const
    ((‖u‖:ℂ)^2)).add (hA.mul_const (broadRadius v:ℂ)) using 1
  dsimp [radiusSlope]
  ring

theorem packet_derivative (β : ℝ) (r : ℝ → ℂ) (rd b : ℂ) (P : Polynomial ℂ)
    (s : ℝ) (v : Block 4) (hr : HasDerivAt r rd s) :
    HasDerivAt (fun x => neutralPacket β (r x) b P v) (packetSlope β (r s) rd b P v) s := by
  have hn := neutral_derivative r rd s v hr
  have hp := (P.hasDerivAt (neutral (r s) v)).scomp s hn
  convert (((hn.pow 2).const_mul (-(β:ℂ))).add (hn.const_mul b)).cexp.mul hp using 1
  dsimp [packetSlope]
  ring

variable {m : ℕ} (f : Family m)

def coefficientSlope (c cd : Fin m → ℂ) (α β : ℝ) (r rd t td : ℂ)
    (k : ℕ) (i : Fin m) (v : Block 4) : ℂ :=
  (-((Real.pi:ℂ)*(2*(α:ℂ)*r*rd)/((α:ℂ)*r^2)^2)*f.amplitude i*c i+
    ((Real.pi:ℂ)/((α:ℂ)*r^2))*f.amplitude i*cd i)*mixedField t v^k*
      neutralPacket β r (f.source i) (f.polynomial i) v+
  ((Real.pi:ℂ)/((α:ℂ)*r^2))*f.amplitude i*c i*
    ((k:ℂ)*mixedField t v^(k-1)*fieldSlope td v)*
      neutralPacket β r (f.source i) (f.polynomial i) v+
  ((Real.pi:ℂ)/((α:ℂ)*r^2))*f.amplitude i*c i*mixedField t v^k*
    packetSlope β r rd (f.source i) (f.polynomial i) v

theorem coefficient_derivative (c : ℝ → Fin m → ℂ) (cd : Fin m → ℂ) (α β : ℝ)
    (r t : ℝ → ℂ) (rd td : ℂ) (s : ℝ) (k : ℕ) (i : Fin m) (v : Block 4)
    (hc : HasDerivAt (fun x => c x i) (cd i) s)
    (hr : HasDerivAt r rd s) (ht : HasDerivAt t td s) (hne : (α:ℂ)*(r s)^2 ≠ 0) :
    HasDerivAt (fun x => coefficient f (c x) α β (r x) (t x) k i v)
      (coefficientSlope f (c s) cd α β (r s) rd (t s) td k i v) s := by
  have hA := (hr.pow 2).const_mul (α:ℂ)
  have hnorm := (hasDerivAt_const s (Real.pi:ℂ)).div hA hne
  convert ((((hnorm.mul_const (f.amplitude i)).mul hc).mul
    ((field_derivative t td s v ht).pow k)).mul
      (packet_derivative β r rd (f.source i) (f.polynomial i) s v hr)) using 1
  dsimp [coefficientSlope]
  ring

#print axioms neutral_derivative
#print axioms field_derivative
#print axioms radius_derivative
#print axioms packet_derivative
#print axioms coefficient_derivative
end
end UnifiedTheory.Audit.KFCausalShiftedNarrowFourierClockDerivative
