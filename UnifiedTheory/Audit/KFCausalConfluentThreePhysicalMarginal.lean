/- The actual quadratic joint-source jet, with arbitrary neutral source and
polynomial, is attached to the charged marginal coercivity. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingConfluentPolynomialDerivative
import UnifiedTheory.Audit.KFCausalJointSourceConfluenceQuadraticCooling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

namespace UnifiedTheory.Audit.KFCausalConfluentThreePhysicalMarginal
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalClusteredClockFactors (Z Zd N F E G)
open KFCausalJointSourceConfluenceFactors (Q limitDensity)
open KFCausalJointSourceConfluenceQuadraticCooling
open KFCausalChargedCoolingGramIntegral (planeMeasure)
open KFCausalChargedCoolingConfluentMoments
open KFCausalChargedCoolingConfluentPolynomialMarginal
open KFCausalChargedCoolingConfluentPolynomialDerivative
open KFCausalChargedCoolingTwoWidthResponse (fieldWeight fieldGradient)
open KFCausalReciprocalWedgeGeometry (gamma)

def innerJoint (v x : ℝ) (q : ℝ × ℝ) : Joint := ((q.1,![v,x]),q.2)
def rate (α w : ℝ) (r : ℂ) : ℝ := α*(r.re^2-r.im^2)*w
def shape (r : ℂ) : ℝ := r.re*r.im/(r.re^2-r.im^2)
def shift (α w : ℝ) (r ℓ : ℂ) (v x : ℝ) : ℂ :=
  (w:ℂ)*gamma α r*(v:ℂ)^2-(w:ℂ)*ℓ*N r (innerJoint v x (0,0))
def base (α β w : ℝ) (r b : ℂ) (P : Polynomial ℂ) (v x : ℝ) : ℝ :=
  ‖Complex.exp (E (w*α) β r b (innerJoint v x (0,0)))*
    P.eval (N r (innerJoint v x (0,0)))‖^2/w^4

def normalDirection (y v : ℝ) (q : ℝ × ℝ) : ℂ :=
  (1+(y:ℂ)*Complex.I)*((q.1:ℂ)^2+(v:ℂ)^2)+(1-(y:ℂ)*Complex.I)*(q.2:ℂ)

theorem scalar_cooling (H D : ℂ) (R : ℝ) :
    (2*(R:ℂ)*H^2*(conj H)^2-2*D*H*(conj H)^2-2*conj D*H^2*conj H).re =
      2*R*‖H‖^4-4*‖H‖^2*(conj H*D).re := by
  simp only [show ‖H‖^4=(‖H‖^2)^2 by ring,Complex.sq_norm,Complex.normSq_apply]
  norm_num [pow_two,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem normalized_cooling_pointwise (s x y v : ℝ) (z : ℂ) (q : ℝ × ℝ) :
    (normalizedCooling s x y v z q).re =
      Real.exp (-s*(q.1^2+q.2))*
        (2*(q.1^2+q.2+v^2)*‖chargedCoordinate ((s:ℂ)*halfParameter x) q+z‖^4-
          4*‖chargedCoordinate ((s:ℂ)*halfParameter x) q+z‖^2*
            (conj (chargedCoordinate ((s:ℂ)*halfParameter x) q+z)*normalDirection y v q).re) := by
  let H := chargedCoordinate ((s:ℂ)*halfParameter x) q+z
  have hc : conj H = chargedCoordinate (conj ((s:ℂ)*halfParameter x)) q+conj z := by
    simp only [H,chargedCoordinate,map_add,map_mul,map_pow,Complex.conj_ofReal]
  have he : Complex.exp (-(s:ℂ)*((q.1:ℂ)^2+(q.2:ℂ))) =
      (Real.exp (-s*(q.1^2+q.2)):ℂ) := by push_cast; rfl
  have hid : normalizedCooling s x y v z q =
      (Real.exp (-s*(q.1^2+q.2)):ℂ)*
        (2*((q.1^2+q.2+v^2:ℝ):ℂ)*H^2*(conj H)^2-
          2*normalDirection y v q*H*(conj H)^2-
          2*conj (normalDirection y v q)*H^2*conj H) := by
    simp only [normalizedCooling,weightedShifted,shiftedCross,he,hc,H,normalDirection,
      map_add,map_sub,map_mul,map_pow,Complex.conj_ofReal,Complex.conj_I,map_one]
    norm_num [Complex.ofReal_add,Complex.ofReal_pow,Matrix.cons_val_two]
    ring
  rw [hid,Complex.re_ofReal_mul,scalar_cooling]

theorem shifted_coordinate (α w : ℝ) (r ℓ : ℂ) (v x : ℝ) (q : ℝ × ℝ) :
    chargedCoordinate ((w:ℂ)*gamma α r) q+shift α w r ℓ v x =
      (w:ℂ)*Q α r ℓ (innerJoint v x q) := by
  simp only [chargedCoordinate,shift,Q,Z,N,innerJoint,
    KFCausalReciprocalWedgeGeometry.chart,map_mul,Complex.conj_ofReal]
  push_cast
  ring

theorem real_direction (α w δ : ℝ) (r : ℂ) (ha : r.re ≠ 0) (v x : ℝ) (q : ℝ × ℝ) :
    ((δ*α*r.re*w:ℝ):ℂ)*normalDirection (r.im/r.re) v q =
      (w:ℂ)*Zd α r (δ:ℂ) (innerJoint v x q) := by
  apply Complex.ext <;>
    simp only [normalDirection,Zd,innerJoint,pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,
      Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  all_goals norm_num
  all_goals field_simp [ha]

theorem rate_parameter (α w : ℝ) (r : ℂ) (hA : r.re^2-r.im^2 ≠ 0) :
    ((rate α w r:ℝ):ℂ)*halfParameter (shape r) = (w:ℂ)*gamma α r := by
  simpa only [rate,shape,Complex.re_add_im,gamma] using
    charged_parameter_identity α r.re r.im w hA

theorem exponent_split (α β w : ℝ) (r b : ℂ) (v x : ℝ) (q : ℝ × ℝ) :
    E (w*α) β r b (innerJoint v x q) =
      E (w*α) β r b (innerJoint v x (0,0))-chargedCoordinate ((w:ℂ)*gamma α r) q := by
  simp only [E,Z,G,N,innerJoint,KFCausalReciprocalWedgeGeometry.chart,
    chargedCoordinate,gamma,map_div₀,map_mul,map_pow,Complex.conj_ofReal,map_ofNat]
  push_cast
  ring

theorem charged_real (α w : ℝ) (r : ℂ) (q : ℝ × ℝ) :
    2*(chargedCoordinate ((w:ℂ)*gamma α r) q).re = rate α w r*(q.1^2+q.2) := by
  norm_num [chargedCoordinate,gamma,rate,map_mul,map_pow,map_div₀,map_ofNat,
    Complex.conj_ofReal,pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem neutral_norm (α β w : ℝ) (r b : ℂ) (P : Polynomial ℂ) (v x : ℝ) (q : ℝ × ℝ) :
    ‖Complex.exp (E (w*α) β r b (innerJoint v x q))*P.eval (N r (innerJoint v x q))‖^2 =
      ‖Complex.exp (E (w*α) β r b (innerJoint v x (0,0)))*P.eval (N r (innerJoint v x (0,0)))‖^2*
        Real.exp (-rate α w r*(q.1^2+q.2)) := by
  rw [exponent_split,sub_eq_add_neg,Complex.exp_add]
  have hN : N r (innerJoint v x q)=N r (innerJoint v x (0,0)) := rfl
  rw [hN,show Complex.exp (E (w*α) β r b (innerJoint v x (0,0)))*
    Complex.exp (-chargedCoordinate ((w:ℂ)*gamma α r) q)*P.eval (N r (innerJoint v x (0,0))) =
    (Complex.exp (E (w*α) β r b (innerJoint v x (0,0)))*P.eval (N r (innerJoint v x (0,0))))*
      Complex.exp (-chargedCoordinate ((w:ℂ)*gamma α r) q) by ring]
  have he : ‖Complex.exp (-chargedCoordinate ((w:ℂ)*gamma α r) q)‖^2 =
      Real.exp (-rate α w r*(q.1^2+q.2)) := by
    rw [Complex.norm_exp,← Real.exp_nat_mul]
    congr 1
    have h := charged_real α w r q
    simp only [Complex.neg_re]
    norm_num
    linarith
  rw [norm_mul,mul_pow,he]

theorem density_mapping (α β w : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (v x : ℝ)
    (q : ℝ × ℝ) (hw : 0 < w) (hA : r.re^2-r.im^2 ≠ 0) :
    limitDensity 2 α β w r b ℓ P (innerJoint v x q) =
      base α β w r b P v x*fieldWeight (F r (innerJoint v x (0,0)))*
        quadraticDensity (rate α w r) (((rate α w r:ℝ):ℂ)*halfParameter (shape r)) (shift α w r ℓ v x) q := by
  rw [density_factorization,neutral_norm]
  rw [rate_parameter α w r hA]
  unfold quadraticDensity base
  rw [shifted_coordinate]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw,mul_pow]
  have hF : F r (innerJoint v x q)=F r (innerJoint v x (0,0)) := rfl
  rw [hF]
  field_simp [hw.ne']

theorem direction_quotient (α δ : ℝ) (r : ℂ) (hα : α ≠ 0) (hδ : δ ≠ 0)
    (ha : r.re ≠ 0) (v x : ℝ) (q : ℝ × ℝ) :
    normalDirection (r.im/r.re) v q =
      ((1/(δ*α*r.re):ℝ):ℂ)*Zd α r (δ:ℂ) (innerJoint v x q) := by
  have h := real_direction α 1 δ r ha v x q
  simp only [mul_one,Complex.ofReal_one,one_mul] at h
  have hc : ((δ*α*r.re:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero (mul_ne_zero hδ hα) ha)
  apply (mul_left_cancel₀ hc)
  rw [h]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hα,Complex.ofReal_ne_zero.mpr hδ,Complex.ofReal_ne_zero.mpr ha]

theorem direction_real (α δ : ℝ) (r : ℂ) (v x : ℝ) (q : ℝ × ℝ) :
    (Zd α r (δ:ℂ) (innerJoint v x q)).re = δ*α*r.re*(q.1^2+q.2+v^2) := by
  simp only [Zd,innerJoint,Complex.add_re,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  norm_num
  ring

theorem response_mapping (α β w δ κ : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (v x : ℝ)
    (q : ℝ × ℝ) (hα : 0 < α) (hw : 0 < w) (hδ : 0 < δ)
    (ha : 0 < r.re) (hA : r.re^2-r.im^2 ≠ 0) :
    coolingResponse α β w δ κ r b ℓ P (innerJoint v x q) =
      base α β w r b P v x*
        (-(δ*α*r.re*w)*fieldWeight (F r (innerJoint v x (0,0)))*
          (normalizedCooling (rate α w r) (shape r) (r.im/r.re) v (shift α w r ℓ v x) q).re+
        κ*v*fieldGradient (F r (innerJoint v x (0,0)))*
          quadraticDensity (rate α w r) (((rate α w r:ℝ):ℂ)*halfParameter (shape r))
            (shift α w r ℓ v x) q) := by
  rw [response_factorization,neutral_norm,normalized_cooling_pointwise,rate_parameter α w r hA]
  have hcross :
      (conj (chargedCoordinate ((w:ℂ)*gamma α r) q+shift α w r ℓ v x)*
        normalDirection (r.im/r.re) v q).re =
      (w/(δ*α*r.re))*(conj (Q α r ℓ (innerJoint v x q))*
        Zd α r (δ:ℂ) (innerJoint v x q)).re := by
    rw [shifted_coordinate,direction_quotient α δ r hα.ne' hδ.ne' ha.ne' v x q]
    have hc : conj ((w:ℂ)*Q α r ℓ (innerJoint v x q))*
        (((1/(δ*α*r.re):ℝ):ℂ)*Zd α r (δ:ℂ) (innerJoint v x q)) =
        ((w/(δ*α*r.re):ℝ):ℂ)*(conj (Q α r ℓ (innerJoint v x q))*
          Zd α r (δ:ℂ) (innerJoint v x q)) := by
      simp only [map_mul,Complex.conj_ofReal]
      push_cast
      ring
    rw [hc,Complex.re_ofReal_mul]
  rw [hcross]
  unfold base quadraticDensity
  rw [shifted_coordinate]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hw,mul_pow]
  have hF : F r (innerJoint v x q)=F r (innerJoint v x (0,0)) := rfl
  rw [hF,direction_real]
  change _ = _
  simp only [innerJoint,Matrix.cons_val_zero]
  field_simp [hw.ne',hδ.ne',hα.ne',ha.ne']
  ring

theorem physical_density_integrable (α β w : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (v x : ℝ)
    (hα : 0 < α) (hw : 0 < w) (hr : |r.im| < r.re) :
    Integrable (fun q => limitDensity 2 α β w r b ℓ P (innerJoint v x q)) planeMeasure := by
  have hA : 0 < r.re^2-r.im^2 := by nlinarith [sq_abs r.im,abs_nonneg r.im]
  have hs : 0 < rate α w r := by unfold rate; positivity
  have hi := (quadratic_density_integrable (rate α w r) hs
    (((rate α w r:ℝ):ℂ)*halfParameter (shape r)) (shift α w r ℓ v x)).const_mul
      (base α β w r b P v x*fieldWeight (F r (innerJoint v x (0,0))))
  exact hi.congr (Filter.Eventually.of_forall (fun q =>
    (density_mapping α β w r b ℓ P v x q hw hA.ne').symm))

theorem physical_cooling_integrable (α β w δ κ : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (v x : ℝ)
    (hα : 0 < α) (hw : 0 < w) (hr : |r.im| < r.re) (hδ : 0 < δ) :
    Integrable (fun q => coolingResponse α β w δ κ r b ℓ P (innerJoint v x q)) planeMeasure := by
  have ha : 0 < r.re := lt_of_le_of_lt (abs_nonneg r.im) hr
  have hA : 0 < r.re^2-r.im^2 := by nlinarith [sq_abs r.im,abs_nonneg r.im]
  have hs : 0 < rate α w r := by unfold rate; positivity
  have hi := (((normalized_cooling_integrable (rate α w r) (shape r) (r.im/r.re) v hs
    (shift α w r ℓ v x)).re.const_mul
      (-(δ*α*r.re*w)*fieldWeight (F r (innerJoint v x (0,0))))).add
      ((quadratic_density_integrable (rate α w r) hs
        (((rate α w r:ℝ):ℂ)*halfParameter (shape r)) (shift α w r ℓ v x)).const_mul
          (κ*v*fieldGradient (F r (innerJoint v x (0,0)))))) |>.const_mul (base α β w r b P v x)
  exact hi.congr (Filter.Eventually.of_forall (fun q => by
    change _ = coolingResponse α β w δ κ r b ℓ P (innerJoint v x q)
    exact (response_mapping α β w δ κ r b ℓ P v x q hα hw hδ ha hA.ne').symm))

theorem physical_marginal_bound (α β w δ κ : ℝ) (r b ℓ : ℂ) (P : Polynomial ℂ) (v x : ℝ)
    (hα : 0 < α) (hw : 0 < w) (hr : |r.im| < r.re) (hδ : 0 < δ) :
    (∫ q, coolingResponse α β w δ κ r b ℓ P (innerJoint v x q) ∂planeMeasure) ≤
      (16*κ^2/(δ*α*r.re*w))*
        (∫ q, limitDensity 2 α β w r b ℓ P (innerJoint v x q) ∂planeMeasure) := by
  have ha : 0 < r.re := lt_of_le_of_lt (abs_nonneg r.im) hr
  have hA : 0 < r.re^2-r.im^2 := by nlinarith [sq_abs r.im,abs_nonneg r.im]
  have hs : 0 < rate α w r := by unfold rate; positivity
  obtain ⟨hy,hxy⟩ := KFCausalChargedCoolingConfluentThreeDissipation.sector_parameters r.re r.im hr
  have hD := quadratic_density_integrable (rate α w r) hs
    (((rate α w r:ℝ):ℂ)*halfParameter (shape r)) (shift α w r ℓ v x)
  have hC : Integrable (fun q =>
      (normalizedCooling (rate α w r) (shape r) (r.im/r.re) v (shift α w r ℓ v x) q).re) planeMeasure :=
    (normalized_cooling_integrable (rate α w r) (shape r) (r.im/r.re) v hs (shift α w r ℓ v x)).re
  let D := ∫ q, quadraticDensity (rate α w r) (((rate α w r:ℝ):ℂ)*halfParameter (shape r))
    (shift α w r ℓ v x) q ∂planeMeasure
  let C := ∫ q, (normalizedCooling (rate α w r) (shape r) (r.im/r.re) v
    (shift α w r ℓ v x) q).re ∂planeMeasure
  let f := F r (innerJoint v x (0,0))
  have hD0 : 0 ≤ D := integral_nonneg (fun q => by unfold quadraticDensity; positivity)
  have hCD : (v^2/16)*D ≤ C := by
    simpa only [hxy,shape,D,C] using normalized_cooling_lower
      (rate α w r) (r.im/r.re) v hs hy (shift α w r ℓ v x)
  have hbase : 0 ≤ base α β w r b P v x := by unfold base; positivity
  have hW := KFCausalChargedCoolingTwoWidthResponse.field_weight_positive f
  have hp : 0 < δ*α*r.re*w := by positivity
  have hscalar := mul_le_mul_of_nonneg_right
    (KFCausalChargedCoolingTwoWidthResponse.weighted_scalar_absorption
      (δ*α*r.re*w/16) v (-κ) f (by positivity)) hD0
  have he : (-κ)^2/(δ*α*r.re*w/16)=16*κ^2/(δ*α*r.re*w) := by field_simp
  rw [he] at hscalar
  have hcool := mul_le_mul_of_nonneg_left hCD
    (show 0 ≤ δ*α*r.re*w*fieldWeight f by positivity)
  have hbound : -(δ*α*r.re*w)*fieldWeight f*C+κ*v*fieldGradient f*D ≤
      (16*κ^2/(δ*α*r.re*w))*fieldWeight f*D := by nlinarith only [hscalar,hcool]
  have hbound' := mul_le_mul_of_nonneg_left hbound hbase
  have hEi : (∫ q, limitDensity 2 α β w r b ℓ P (innerJoint v x q) ∂planeMeasure) =
      base α β w r b P v x*fieldWeight f*D := by
    simp_rw [density_mapping α β w r b ℓ P v x _ hw hA.ne']
    rw [integral_const_mul]
  have hRi : (∫ q, coolingResponse α β w δ κ r b ℓ P (innerJoint v x q) ∂planeMeasure) =
      base α β w r b P v x*(-(δ*α*r.re*w)*fieldWeight f*C+κ*v*fieldGradient f*D) := by
    simp_rw [response_mapping α β w δ κ r b ℓ P v x _ hα hw hδ ha hA.ne']
    rw [integral_const_mul]
    have hi := integral_add (hC.const_mul (-(δ*α*r.re*w)*fieldWeight f))
      (hD.const_mul (κ*v*fieldGradient f))
    rw [hi]
    simp only [integral_const_mul]
    rfl
  rw [hEi,hRi]
  nlinarith only [hbound']

#print axioms scalar_cooling
#print axioms normalized_cooling_pointwise
#print axioms shifted_coordinate
#print axioms real_direction
#print axioms rate_parameter
#print axioms exponent_split
#print axioms charged_real
#print axioms neutral_norm
#print axioms density_mapping
#print axioms direction_quotient
#print axioms direction_real
#print axioms response_mapping
#print axioms physical_density_integrable
#print axioms physical_cooling_integrable
#print axioms physical_marginal_bound
end
end UnifiedTheory.Audit.KFCausalConfluentThreePhysicalMarginal
