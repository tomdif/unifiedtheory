/- Exact symmetric directional derivatives in the physical charge chart.
The neutral first and second derivatives are retained before the four-angle
average. This module concerns the actual packet profiles; operator graphs
are attached separately using their constructed Hilbert representatives. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPacketDerivatives
import UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialKineticProfiles
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalIndependentRadialPacketProfiles (chargeProfile chargeQuadratic
  chargeQuadratic_coordinates chargeProfile_flow)
open KFCausalIndependentRadialPacketDerivatives (leftRadius rightRadius)
open KFCausalSymmetricMomentumCoordinates (symmetricVector symmetricBlock rightVector)
open KFCausalNeutralLinePackets (packet step packet_derivative)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalNormalizedChargeFlow (flowEquiv flow_first_plane flow_second_plane)

def position (i : Fin 2) (x : Joint 2 4) : ℝ := ![x (.inr 1),x (.inr 2)] i
def rate (wL wR : ℝ) (i : Fin 2) : ℝ := ![1/wL,wR] i
def neutral (i : Fin 2) : ℝ := ![0,1] i
def radius (c : ℝ) (i : Fin 2) (x : Joint 2 4) : ℝ := ![leftRadius c x,rightRadius c x] i
def coefficient (α wL wR : ℝ) (i : Fin 2) : ℂ := -4*(scale:ℂ)*(α:ℂ)*(rate wL wR i:ℂ)

def firstProfile (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (i : Fin 2) (x : Joint 2 4) : ℂ :=
  coefficient α wL wR i*(position i x:ℂ)*chargeProfile α β wL wR c b P g x+
    (neutral i:ℂ)*chargeProfile α β wL wR c b (step β b P) g x

def secondProfile (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (i : Fin 2) (x : Joint 2 4) : ℂ :=
  coefficient α wL wR i*(2*(scale:ℂ))*chargeProfile α β wL wR c b P g x+
    (coefficient α wL wR i)^2*(position i x:ℂ)^2*chargeProfile α β wL wR c b P g x+
    2*coefficient α wL wR i*(neutral i:ℂ)*(position i x:ℂ)*
      chargeProfile α β wL wR c b (step β b P) g x+
    (neutral i:ℂ)^2*chargeProfile α β wL wR c b (step β b (step β b P)) g x

private theorem clock_translate (i : Fin 2) (x : Joint 2 4) (t : ℝ) :
    (x+t • symmetricVector i) (.inr 0)=x (.inr 0) := by
  fin_cases i <;> simp [symmetricVector,rightVector,symmetricBlock]

private theorem position_translate (i : Fin 2) (x : Joint 2 4) (t : ℝ) :
    position i (x+t • symmetricVector i)=position i x+2*scale*t := by
  fin_cases i <;> simp [position,symmetricVector,rightVector,symmetricBlock] <;> ring

private theorem neutral_translate (i : Fin 2) (x : Joint 2 4) (t : ℝ) :
    (x+t • symmetricVector i) (.inr 3)=x (.inr 3)+neutral i*t := by
  fin_cases i <;> simp [neutral,symmetricVector,rightVector,symmetricBlock]

private theorem quadratic_translate (wL wR c : ℝ) (i : Fin 2) (x : Joint 2 4) (t : ℝ) :
    chargeQuadratic wL wR c (x+t • symmetricVector i)=chargeQuadratic wL wR c x+
      rate wL wR i*(4*scale*position i x*t+4*scale^2*t^2) := by
  simp only [chargeQuadratic_coordinates]
  fin_cases i <;> simp [position,rate,symmetricVector,rightVector,symmetricBlock] <;> ring

theorem position_line (i : Fin 2) (x : Joint 2 4) :
    HasDerivAt (fun t : ℝ => position i (x+t • symmetricVector i)) (2*scale) 0 := by
  simp only [position_translate]
  simpa using ((hasDerivAt_id (0:ℝ)).const_mul (2*scale)).const_add (position i x)

theorem profile_first_derivative (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (i : Fin 2) (x : Joint 2 4) :
    HasDerivAt (fun t : ℝ => chargeProfile α β wL wR c b P g (x+t • symmetricVector i))
      (firstProfile α β wL wR c b P g i x) 0 := by
  have hq : HasDerivAt (fun t : ℝ => chargeQuadratic wL wR c (x+t • symmetricVector i))
      (rate wL wR i*(4*scale*position i x)) 0 := by
    simp only [quadratic_translate]
    convert ((((hasDerivAt_id (0:ℝ)).const_mul (4*scale*position i x)).add
      (((hasDerivAt_id (0:ℝ)).pow 2).const_mul (4*scale^2))).const_mul
        (rate wL wR i)).const_add (chargeQuadratic wL wR c x) using 1
    norm_num
  have hn : HasDerivAt (fun t : ℝ => packet β b P (x (.inr 3)+neutral i*t))
      (packet β b (step β b P) (x (.inr 3))*(neutral i:ℂ)) 0 := by
    have hd := (packet_derivative β b P (x (.inr 3)+neutral i*0)).scomp 0
      (((hasDerivAt_id (0:ℝ)).const_mul (neutral i)).const_add (x (.inr 3)))
    simpa [Complex.real_smul,mul_comm] using hd
  have he := ((hq.ofReal_comp.const_mul (-(α:ℂ))).cexp.const_mul
    ((Real.pi/α:ℝ)*g (x (.inr 0)))).mul hn
  convert he using 1
  · funext t
    simp only [chargeProfile,clock_translate,neutral_translate,Pi.mul_apply]
  · simp only [firstProfile,chargeProfile,zero_smul,add_zero,coefficient,mul_zero]
    push_cast
    ring

theorem profile_second_derivative (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (i : Fin 2) (x : Joint 2 4) :
    HasDerivAt (fun t : ℝ => firstProfile α β wL wR c b P g i (x+t • symmetricVector i))
      (secondProfile α β wL wR c b P g i x) 0 := by
  have he := (((position_line i x).ofReal_comp.mul
    (profile_first_derivative α β wL wR c b P g i x)).const_mul
      (coefficient α wL wR i)).add
    ((profile_first_derivative α β wL wR c b (step β b P) g i x).const_mul (neutral i:ℂ))
  convert he using 1
  · funext t
    simp only [firstProfile,Pi.add_apply,Pi.mul_apply,mul_assoc]
  · simp only [firstProfile,secondProfile,zero_smul,add_zero]
    push_cast
    ring

private theorem position_flow (c : ℝ) (hc : c ≠ 0) (i : Fin 2) (θ : ℝ) (x : Joint 2 4) :
    position i (flowEquiv c hc θ x)=c*Real.sin θ*x (.inl i)+Real.cos θ*position i x := by
  fin_cases i
  · exact congrArg Prod.snd (flow_first_plane c hc θ x)
  · exact congrArg Prod.snd (flow_second_plane c hc θ x)

def fourAverage (c : ℝ) (hc : c ≠ 0) (f : Joint 2 4 → ℂ) (x : Joint 2 4) : ℂ :=
  (1/4:ℂ)*(f x+f (flowEquiv c hc (Real.pi/2) x)+
    f (flowEquiv c hc Real.pi x)+f (flowEquiv c hc (-Real.pi/2) x))

theorem secondProfile_fourAverage (α β wL wR c : ℝ) (hc : c ≠ 0)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (i : Fin 2) (x : Joint 2 4) :
    fourAverage c hc (secondProfile α β wL wR c b P g i) x =
      (-4*(α:ℂ)*(rate wL wR i:ℂ)+
        4*((α:ℂ)*(rate wL wR i:ℂ))^2*(radius c i x:ℂ))*chargeProfile α β wL wR c b P g x+
        (neutral i:ℂ)*chargeProfile α β wL wR c b (step β b (step β b P)) g x := by
  unfold fourAverage secondProfile
  simp only [chargeProfile_flow α β wL wR c hc,position_flow,Real.sin_pi_div_two,
    Real.cos_pi_div_two,Real.sin_pi,Real.cos_pi,Real.sin_neg,Real.cos_neg,
    neg_div,zero_mul,mul_zero,mul_one,one_mul,zero_add,add_zero,mul_neg,neg_mul]
  have hs : (scale:ℂ)^2=(1/2:ℂ) := by
    rw [← Complex.ofReal_pow,scale_square]
    norm_num
  have hn : (neutral i:ℂ)^2=(neutral i:ℂ) := by fin_cases i <;> norm_num [neutral]
  have hr : (radius c i x:ℂ)=(c:ℂ)^2*(x (.inl i):ℂ)^2+(position i x:ℂ)^2 := by
    fin_cases i <;> simp [radius,leftRadius,rightRadius,position]
  rw [hr]
  unfold coefficient
  push_cast
  ring_nf
  rw [hs,hn]
  ring

#print axioms position_line
#print axioms profile_first_derivative
#print axioms profile_second_derivative
#print axioms secondProfile_fourAverage
end
end UnifiedTheory.Audit.KFCausalIndependentRadialKineticProfiles
