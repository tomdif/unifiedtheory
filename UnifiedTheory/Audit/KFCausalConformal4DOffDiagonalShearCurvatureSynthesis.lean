import UnifiedTheory.Audit.KFCausalConformal4DAnisotropicSpatialProbeSynthesis

/-! Off-diagonal mixed second-derivative (momentum/flux and spatial shear)
curvature synthesis, diagonal polarization probe extraction, pure-shear
tracelessness, and diagonal/off-diagonal channel decomposition of the 4D
Lorentzian contracted Bianchi identity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DOffDiagonalShearCurvatureSynthesis
noncomputable section

open scoped BigOperators
open UnifiedTheory.LayerA.Bianchi (RiemannData)
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs R_metric dR_metric riemannFromMetric)
open KFCausalConformal4DDiamondBenchmark (sign eta)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein dRic divRic
  dScalar dEinstein lorentzian_metric_divergence)
open KFCausalConformal4DLorentzianBianchiTraceSynthesis (einsteinTrace dEinsteinTrace
  lorentzian_einsteinTrace_eq_neg_scalar lorentzian_dEinsteinTrace_bianchi)
open KFCausalConformal4DAnisotropicSpatialProbeSynthesis (TransformedJet4D
  anisotropicMetricDerivs ricciTensor4D scalarCurvature4D einsteinTensor4D)

/-- General 4×4 second-derivative matrix `H_{μν} = ∂_μ ∂_ν Ω(0)` of a 4D
conformal factor at the origin, including off-diagonal shear and momentum-flux
components. -/
abbrev Hessian4D := Fin 4 → Fin 4 → ℝ

/-- General 4×4×4 third-derivative tensor `K_{efg} = ∂_e ∂_f ∂_g Ω(0)` of a 4D
conformal factor at the origin. -/
abbrev ThirdJet4D := Fin 4 → Fin 4 → Fin 4 → ℝ

/-- Symmetry predicate `H μ ν = H ν μ` for a 4D Hessian matrix. -/
def IsSymmetricHessian4D (H : Hessian4D) : Prop :=
  ∀ μ ν : Fin 4, H μ ν = H ν μ

/-- Pure off-diagonal shear/flux predicate `H μ μ = 0` for all `μ : Fin 4`. -/
def IsPureOffDiagonalShear4D (H : Hessian4D) : Prop :=
  ∀ μ : Fin 4, H μ μ = 0

/-- Full 3-index symmetry predicate for a third-order jet `K`. -/
def IsSymmetricThirdJet4D (K : ThirdJet4D) : Prop :=
  (∀ e f g : Fin 4, K e f g = K f e g) ∧
  (∀ e f g : Fin 4, K e f g = K e g f)

/-- Symmetrization `(H μ ν + H ν μ) / 2` of any 4×4 matrix `H`, which equals `H`
when `H` is symmetric and automatically satisfies `h_comm`. -/
def symmetrizeHessian4D (H : Hessian4D) : Hessian4D :=
  fun μ ν => (H μ ν + H ν μ) / 2

/-- Symmetrization of a 3-index jet `K` over all 6 permutations of `(e, f, g)`. -/
def symmetrizeThirdJet4D (K : ThirdJet4D) : ThirdJet4D :=
  fun e f g =>
    (K e f g + K f e g + K e g f + K g f e + K f g e + K g e f) / 6

/-- Embedding of a 4-component diagonal jet `d : Fin 4 → ℝ` into `Hessian4D`. -/
def diagonalToHessian4D (d : TransformedJet4D) : Hessian4D :=
  fun μ ν => if μ = ν then d μ else 0

/-- Diagonal part of a 4×4 Hessian `H`, keeping only `μ = ν`. -/
def diagonalPart4D (H : Hessian4D) : Hessian4D :=
  fun μ ν => if μ = ν then H μ μ else 0

/-- Off-diagonal shear/flux part of a 4×4 Hessian `H`, keeping only `μ ≠ ν`. -/
def offDiagonalShearPart4D (H : Hessian4D) : Hessian4D :=
  fun μ ν => if μ = ν then 0 else H μ ν

/-- Flat 4D Minkowski metric `η_{μν} = diag(-1, 1, 1, 1)`. -/
def minkMetric4D (μ ν : Fin 4) : ℝ :=
  eta μ ν

/-- 4D Lorentzian wave operator `□ H = ∑ μ, sign μ * H μ μ` on a full 4×4
Hessian `H`. -/
def box4D (H : Hessian4D) : ℝ :=
  ∑ μ : Fin 4, sign μ * H μ μ

/-- Directional wave operator `□(∂_e Ω) = ∑ a, sign a * K e a a` on a third-order
conformal jet `K`. -/
def dBox4D (K : ThirdJet4D) (e : Fin 4) : ℝ :=
  ∑ a : Fin 4, sign a * K e a a

/-- Second-derivative metric tensor `∂_e ∂_f g_{ab}(0) = 2 H^{sym}_{ef} η_{ab}`
for a 4D conformal factor with Hessian `H`. -/
def fullConformalMetricSecond (H : Hessian4D) (e f a b : Fin 4) : ℝ :=
  2 * symmetrizeHessian4D H e f * eta a b

/-- Third-derivative metric tensor `∂_e ∂_f ∂_g g_{ab}(0) = 2 K^{sym}_{efg} η_{ab}`
for a 4D conformal factor with third jet `K`. -/
def fullConformalMetricThird (K : ThirdJet4D) (e f g a b : Fin 4) : ℝ :=
  2 * symmetrizeThirdJet4D K e f g * eta a b

/-- Normal-coordinate `MetricDerivs 4` for a 4D conformal factor with full 4×4
Hessian `H` and third-order jet `K`. -/
def fullConformalMetricDerivs (H : Hessian4D) (K : ThirdJet4D) : MetricDerivs 4 where
  h := fullConformalMetricSecond H
  h_metric := by
    intro e f a b
    by_cases h : a = b
    · subst b; rfl
    · simp [fullConformalMetricSecond, eta, h, Ne.symm h]
  h_comm := by
    intro e f a b
    unfold fullConformalMetricSecond symmetrizeHessian4D
    ring
  k := fullConformalMetricThird K
  k_metric := by
    intro e f g a b
    by_cases h : a = b
    · subst b; rfl
    · simp [fullConformalMetricThird, eta, h, Ne.symm h]
  k_sym12 := by
    intro e f g a b
    unfold fullConformalMetricThird symmetrizeThirdJet4D
    ring
  k_sym23 := by
    intro e f g a b
    unfold fullConformalMetricThird symmetrizeThirdJet4D
    ring

/-- Zero third-order jet. -/
def zeroThirdJet4D : ThirdJet4D := fun _ _ _ => 0

/-- 4D conformal Ricci tensor `R_{μν}(H)` for a full 4×4 Hessian `H`. -/
def fullRicciTensor4D (H : Hessian4D) (μ ν : Fin 4) : ℝ :=
  ricci (fullConformalMetricDerivs H zeroThirdJet4D) sign μ ν

/-- 4D conformal scalar curvature `R(H)` for a full 4×4 Hessian `H`. -/
def fullScalarCurvature4D (H : Hessian4D) : ℝ :=
  scalar (fullConformalMetricDerivs H zeroThirdJet4D) sign

/-- 4D conformal Einstein tensor `G_{μν}(H)` for a full 4×4 Hessian `H`. -/
def fullEinsteinTensor4D (H : Hessian4D) (μ ν : Fin 4) : ℝ :=
  einstein (fullConformalMetricDerivs H zeroThirdJet4D) sign μ ν

/-- Lorentzian trace `Tr_η(G(H)) = ∑ μ, sign μ * G_{μμ}(H)` of the full 4D
conformal Einstein tensor. -/
def fullEinsteinTrace4D (H : Hessian4D) : ℝ :=
  einsteinTrace (fullConformalMetricDerivs H zeroThirdJet4D) sign

/-- Chronological causal-diamond curvature coupling `-(1/2) R(H)` for a full
4×4 Hessian `H`. -/
def fullChronologicalCurvatureLimit4D (H : Hessian4D) : ℝ :=
  -(1 / 2) * fullScalarCurvature4D H

/-- Differentiated 4D conformal Ricci tensor `∂_e R_{bd}(K)` for a third-order
conformal jet `K`. -/
def fullDRicci4D (H : Hessian4D) (K : ThirdJet4D) (e b d : Fin 4) : ℝ :=
  dRic (riemannFromMetric (fullConformalMetricDerivs H K)) sign e b d

/-- Differentiated 4D conformal scalar curvature `∂_e R(K)` for a third-order
conformal jet `K`. -/
def fullDScalar4D (H : Hessian4D) (K : ThirdJet4D) (e : Fin 4) : ℝ :=
  dScalar (riemannFromMetric (fullConformalMetricDerivs H K)) sign e

/-- Differentiated 4D conformal Einstein tensor `∂_e G_{bd}(K)` for a third-order
conformal jet `K`. -/
def fullDEinstein4D (H : Hessian4D) (K : ThirdJet4D) (e b d : Fin 4) : ℝ :=
  dEinstein (riemannFromMetric (fullConformalMetricDerivs H K)) sign e b d

/-- Diagonal channel `sign ν * ∂_ν G_{νν}(K)` (with `e = ν`) in the contracted
Bianchi divergence `∑ e, sign e * ∂_e G_{νe}(K)`. -/
def bianchiDiagonalChannel4D (H : Hessian4D) (K : ThirdJet4D) (ν : Fin 4) : ℝ :=
  sign ν * fullDEinstein4D H K ν ν ν

/-- Off-diagonal shear/flux channel `∑_{e ≠ ν} sign e * ∂_e G_{νe}(K)` in the
contracted Bianchi divergence. -/
def bianchiOffDiagonalChannel4D (H : Hessian4D) (K : ThirdJet4D) (ν : Fin 4) : ℝ :=
  ∑ e ∈ Finset.univ.erase ν, sign e * fullDEinstein4D H K e ν e

/-- Coordinate basis vector `e_μ` in `ℝ⁴`. -/
def basisVector4D (μ : Fin 4) : Fin 4 → ℝ :=
  fun a => if a = μ then 1 else 0

/-- Diagonal polarization probe `(e_μ + e_ν) / 2`. -/
def plusPolarization4D (μ ν : Fin 4) : Fin 4 → ℝ :=
  fun a => (basisVector4D μ a + basisVector4D ν a) / 2

/-- Diagonal polarization probe `(e_μ - e_ν) / 2`. -/
def minusPolarization4D (μ ν : Fin 4) : Fin 4 → ℝ :=
  fun a => (basisVector4D μ a - basisVector4D ν a) / 2

/-- Bilinear evaluation `T(u, v) = ∑ a, ∑ b, T_{ab} u_a v_b` of a rank-2 tensor. -/
def bilinearEval4D (T : Fin 4 → Fin 4 → ℝ) (u v : Fin 4 → ℝ) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4, T a b * u a * v b

private theorem sign_sq_one (a : Fin 4) : sign a * sign a = 1 := by
  simp only [sign]
  split_ifs <;> norm_num

theorem symmetrizeHessian4D_eq_of_symm (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (μ ν : Fin 4) :
    symmetrizeHessian4D H μ ν = H μ ν := by
  unfold symmetrizeHessian4D
  rw [hH ν μ]
  ring

theorem symmetrizeThirdJet4D_eq_of_symm (K : ThirdJet4D)
    (hK : IsSymmetricThirdJet4D K) (e f g : Fin 4) :
    symmetrizeThirdJet4D K e f g = K e f g := by
  unfold symmetrizeThirdJet4D
  have h1 : K f e g = K e f g := hK.1 f e g
  have h2 : K e g f = K e f g := hK.2 e g f
  have h3 : K g f e = K e f g := by rw [hK.1 g f e, hK.2 f g e, hK.1 f e g]
  have h4 : K f g e = K e f g := by rw [hK.2 f g e, hK.1 f e g]
  have h5 : K g e f = K e f g := by rw [hK.1 g e f, hK.2 e g f]
  rw [h1, h2, h3, h4, h5]
  ring

theorem minkMetric4D_offDiag (μ ν : Fin 4) (h : μ ≠ ν) :
    minkMetric4D μ ν = 0 := by
  simp [minkMetric4D, eta, h]

theorem minkMetric4D_diag (μ : Fin 4) :
    minkMetric4D μ μ = sign μ := by
  simp [minkMetric4D, eta]

theorem hessian_diag_offDiag_split (H : Hessian4D) (μ ν : Fin 4) :
    H μ ν = diagonalPart4D H μ ν + offDiagonalShearPart4D H μ ν := by
  unfold diagonalPart4D offDiagonalShearPart4D
  by_cases h : μ = ν
  · subst ν; simp
  · simp [h]

theorem offDiagonalShearPart4D_isPureShear (H : Hessian4D) :
    IsPureOffDiagonalShear4D (offDiagonalShearPart4D H) := by
  intro μ
  simp [offDiagonalShearPart4D]

/-- General algebraic contraction identity for any 4×4 matrix `M` in a conformal
Riemann contraction:
`∑ a, sign a * (2 M_{ab} η_{ad} - 2 M_{aa} η_{bd} - 2 M_{db} η_{aa} + 2 M_{da} η_{ba}) / 2`
`= M_{db} + M_{db} - 4 M_{db} - (∑ a, sign a * M_{aa}) η_{bd} = -2 M_{db} - (□ M) η_{bd}`. -/
private theorem conformal_contraction_identity (M : Fin 4 → Fin 4 → ℝ) (b d : Fin 4) :
    (∑ a : Fin 4, sign a *
      ((2 * M a b * eta a d - 2 * M a a * eta b d -
        2 * M d b * eta a a + 2 * M d a * eta b a) / 2)) =
      -2 * M d b - (∑ a : Fin 4, sign a * M a a) * minkMetric4D b d := by
  have hterm : ∀ a : Fin 4,
      sign a * ((2 * M a b * eta a d - 2 * M a a * eta b d -
        2 * M d b * eta a a + 2 * M d a * eta b a) / 2) =
      (if a = d then (sign a * sign a) * M a b else 0) -
      (sign a * M a a * eta b d) -
      (sign a * sign a) * M d b +
      (if b = a then (sign a * sign b) * M d a else 0) := by
    intro a
    simp only [eta, if_true]
    split_ifs <;> ring
  simp_rw [hterm, sign_sq_one, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hs1 : (∑ a : Fin 4, if a = d then M a b else 0) = M d b := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ d)]
  have hs2 : (∑ a : Fin 4, sign a * M a a * eta b d) =
      (∑ a : Fin 4, sign a * M a a) * minkMetric4D b d := by
    rw [minkMetric4D, ← Finset.sum_mul]
  have hs3 : (∑ _a : Fin 4, M d b) = 4 * M d b := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hs4 : (∑ a : Fin 4, if b = a then (sign a * sign b) * M d a else 0) = M d b := by
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ b), sign_sq_one b, one_mul]
  rw [hs1, hs2, hs3, hs4]
  ring

/-- Exact master formula for the 4D conformal Ricci tensor `R_{μν}(H)` for any
symmetric 4×4 Hessian `H`:
`R_{μν}(H) = -2 H_{μν} - (□ H) η_{μν}`. -/
theorem fullRicciTensor4D_master_formula (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (μ ν : Fin 4) :
    fullRicciTensor4D H μ ν = -2 * H μ ν - box4D H * minkMetric4D μ ν := by
  simp only [fullRicciTensor4D, ricci, R_metric, fullConformalMetricDerivs,
    fullConformalMetricSecond, symmetrizeHessian4D_eq_of_symm H hH]
  rw [conformal_contraction_identity H μ ν, hH ν μ]
  rfl

/-- Exact master formula for the 4D conformal scalar curvature `R(H)` for any
4×4 Hessian `H`: `R(H) = -6 * box4D H = 6 * (H 0 0 - H 1 1 - H 2 2 - H 3 3)`.
In particular, `R(H)` is completely independent of all off-diagonal shear/flux
components `H μ ν` (`μ ≠ ν`). -/
theorem fullScalarCurvature4D_master_formula (H : Hessian4D) :
    fullScalarCurvature4D H = -6 * box4D H ∧
    fullScalarCurvature4D H = 6 * (H 0 0 - H 1 1 - H 2 2 - H 3 3) := by
  have hdiag : ∀ a : Fin 4, symmetrizeHessian4D H a a = H a a := by
    intro a; unfold symmetrizeHessian4D; ring
  have hric : ∀ b : Fin 4,
      ricci (fullConformalMetricDerivs H zeroThirdJet4D) sign b b =
        -2 * H b b - box4D H * sign b := by
    intro b
    simp only [ricci, R_metric, fullConformalMetricDerivs, fullConformalMetricSecond]
    rw [conformal_contraction_identity (symmetrizeHessian4D H) b b]
    simp_rw [hdiag, minkMetric4D_diag]
    rfl
  have h1 : fullScalarCurvature4D H = -6 * box4D H := by
    unfold fullScalarCurvature4D scalar
    simp_rw [hric]
    have hterm : ∀ b : Fin 4,
        sign b * (-2 * H b b - box4D H * sign b) =
        -2 * (sign b * H b b) - box4D H := by
      intro b
      calc sign b * (-2 * H b b - box4D H * sign b)
          = -2 * (sign b * H b b) - (sign b * sign b) * box4D H := by ring
        _ = -2 * (sign b * H b b) - box4D H := by rw [sign_sq_one b, one_mul]
    simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change -2 * box4D H - ↑4 * box4D H = -6 * box4D H
    ring
  have hbox : box4D H = -H 0 0 + H 1 1 + H 2 2 + H 3 3 := by
    unfold box4D
    rw [Fin.sum_univ_four]
    simp +decide only [sign, ite_true, ite_false]
    ring
  refine ⟨h1, ?_⟩
  rw [h1, hbox]
  ring

/-- Exact master formula for the 4D conformal Einstein tensor `G_{μν}(H)` for
any symmetric 4×4 Hessian `H`:
`G_{μν}(H) = -2 H_{μν} + 2 (□ H) η_{μν}`. -/
theorem fullEinsteinTensor4D_master_formula (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (μ ν : Fin 4) :
    fullEinsteinTensor4D H μ ν = -2 * H μ ν + 2 * box4D H * minkMetric4D μ ν := by
  unfold fullEinsteinTensor4D einstein
  change fullRicciTensor4D H μ ν -
      fullScalarCurvature4D H / 2 * minkMetric4D μ ν = _
  rw [fullRicciTensor4D_master_formula H hH μ ν,
    (fullScalarCurvature4D_master_formula H).1]
  ring

/-- Exact formula for the Lorentzian trace `Tr_η(G(H)) = 6 * box4D H = -R(H)`. -/
theorem fullEinsteinTrace4D_master_formula (H : Hessian4D) :
    fullEinsteinTrace4D H = -fullScalarCurvature4D H ∧
    fullEinsteinTrace4D H = 6 * box4D H := by
  have htr := (lorentzian_einsteinTrace_eq_neg_scalar
    (fullConformalMetricDerivs H zeroThirdJet4D)).2
  change fullEinsteinTrace4D H = -fullScalarCurvature4D H at htr
  refine ⟨htr, ?_⟩
  rw [htr, (fullScalarCurvature4D_master_formula H).1]
  ring

/-- For any off-diagonal index pair `μ ≠ ν` (`minkMetric4D μ ν = 0`), the metric
trace terms in `R_{μν}(H)` and `G_{μν}(H)` vanish identically, so
`G_{μν}(H) = R_{μν}(H) = -2 H_{μν}`. -/
theorem offDiagonal_einstein_eq_ricci_eq_neg_two_hessian (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    minkMetric4D μ ν = 0 ∧
    fullRicciTensor4D H μ ν = -2 * H μ ν ∧
    fullEinsteinTensor4D H μ ν = -2 * H μ ν ∧
    fullEinsteinTensor4D H μ ν = fullRicciTensor4D H μ ν := by
  have hη := minkMetric4D_offDiag μ ν hμν
  have hR := fullRicciTensor4D_master_formula H hH μ ν
  have hG := fullEinsteinTensor4D_master_formula H hH μ ν
  rw [hη, mul_zero, sub_zero] at hR
  rw [hη, mul_zero, add_zero] at hG
  exact ⟨hη, hR, hG, hG.trans hR.symm⟩

/-- Diagonal embedding compatibility: `fullRicciTensor4D`, `fullScalarCurvature4D`,
and `fullEinsteinTensor4D` on `diagonalToHessian4D d` coincide with
`ricciTensor4D d`, `scalarCurvature4D d`, and `einsteinTensor4D d`. -/
theorem diagonalToHessian4D_compatibility (d : TransformedJet4D) (μ ν : Fin 4) :
    box4D (diagonalToHessian4D d) =
      KFCausalConformal4DAnisotropicSpatialProbeSynthesis.fullCoordinateWaveOperator4D d ∧
    fullScalarCurvature4D (diagonalToHessian4D d) = scalarCurvature4D d ∧
    fullRicciTensor4D (diagonalToHessian4D d) μ ν = ricciTensor4D d μ ν ∧
    fullEinsteinTensor4D (diagonalToHessian4D d) μ ν = einsteinTensor4D d μ ν := by
  have hd_symm : IsSymmetricHessian4D (diagonalToHessian4D d) := by
    intro a b
    by_cases h : a = b
    · subst b; rfl
    · simp [diagonalToHessian4D, h, Ne.symm h]
  have hbox : box4D (diagonalToHessian4D d) =
      KFCausalConformal4DAnisotropicSpatialProbeSynthesis.fullCoordinateWaveOperator4D d := by
    unfold box4D
      KFCausalConformal4DAnisotropicSpatialProbeSynthesis.fullCoordinateWaveOperator4D
    apply Finset.sum_congr rfl
    intro a _
    simp [diagonalToHessian4D]
  have hS : fullScalarCurvature4D (diagonalToHessian4D d) = scalarCurvature4D d := by
    rw [(fullScalarCurvature4D_master_formula _).1, hbox,
      (KFCausalConformal4DAnisotropicSpatialProbeSynthesis.scalarCurvature4D_eq d).2]
  have hR : fullRicciTensor4D (diagonalToHessian4D d) μ ν = ricciTensor4D d μ ν := by
    rw [fullRicciTensor4D_master_formula _ hd_symm μ ν, hbox,
      KFCausalConformal4DAnisotropicSpatialProbeSynthesis.ricciTensor4D_formula]
    unfold diagonalToHessian4D minkMetric4D
    by_cases h : μ = ν <;> simp [h]
  have hG : fullEinsteinTensor4D (diagonalToHessian4D d) μ ν = einsteinTensor4D d μ ν := by
    rw [fullEinsteinTensor4D_master_formula _ hd_symm μ ν, hbox,
      KFCausalConformal4DAnisotropicSpatialProbeSynthesis.einsteinTensor4D_formula]
    unfold diagonalToHessian4D minkMetric4D
    by_cases h : μ = ν <;> simp [h]
  exact ⟨hbox, hS, hR, hG⟩

theorem bilinearEval4D_basis (T : Fin 4 → Fin 4 → ℝ) (μ ν : Fin 4) :
    bilinearEval4D T (basisVector4D μ) (basisVector4D ν) = T μ ν := by
  unfold bilinearEval4D basisVector4D
  simp only [mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ μ)]

/-- General polarization difference identity: for any 4×4 tensor `T`, the
difference between the quadratic evaluations along `(e_μ + e_ν)/2` and
`(e_μ - e_ν)/2` equals `(T μ ν + T ν μ) / 2`. -/
theorem polarization_probe_quadratic_difference (T : Fin 4 → Fin 4 → ℝ)
    (μ ν : Fin 4) :
    bilinearEval4D T (plusPolarization4D μ ν) (plusPolarization4D μ ν) -
      bilinearEval4D T (minusPolarization4D μ ν) (minusPolarization4D μ ν) =
        (T μ ν + T ν μ) / 2 ∧
    2 * (bilinearEval4D T (plusPolarization4D μ ν) (plusPolarization4D μ ν) -
      bilinearEval4D T (minusPolarization4D μ ν) (minusPolarization4D μ ν)) =
        T μ ν + T ν μ := by
  have h1 : bilinearEval4D T (plusPolarization4D μ ν) (plusPolarization4D μ ν) -
      bilinearEval4D T (minusPolarization4D μ ν) (minusPolarization4D μ ν) =
        (bilinearEval4D T (basisVector4D μ) (basisVector4D ν) +
          bilinearEval4D T (basisVector4D ν) (basisVector4D μ)) / 2 := by
    unfold bilinearEval4D plusPolarization4D minusPolarization4D
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [bilinearEval4D_basis, bilinearEval4D_basis] at h1
  refine ⟨h1, ?_⟩
  rw [h1]
  ring

/-- Off-diagonal shear and momentum-flux extraction via diagonal polarization
probes `(e_μ + e_ν)/2` and `(e_μ - e_ν)/2`: for any symmetric `H` and `μ ≠ ν`,
`G(H)((e_μ + e_ν)/2, (e_μ + e_ν)/2) - G(H)((e_μ - e_ν)/2, (e_μ - e_ν)/2) = -2 H_{μν}`
and `G_{μν}(H) + G_{νμ}(H) = -4 H_{μν}`. -/
theorem offDiagonal_polarization_probe_extraction (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    bilinearEval4D (fullEinsteinTensor4D H)
        (plusPolarization4D μ ν) (plusPolarization4D μ ν) -
      bilinearEval4D (fullEinsteinTensor4D H)
        (minusPolarization4D μ ν) (minusPolarization4D μ ν) =
      (fullEinsteinTensor4D H μ ν + fullEinsteinTensor4D H ν μ) / 2 ∧
    fullEinsteinTensor4D H μ ν + fullEinsteinTensor4D H ν μ = -4 * H μ ν ∧
    bilinearEval4D (fullEinsteinTensor4D H)
        (plusPolarization4D μ ν) (plusPolarization4D μ ν) -
      bilinearEval4D (fullEinsteinTensor4D H)
        (minusPolarization4D μ ν) (minusPolarization4D μ ν) = -2 * H μ ν ∧
    2 * (bilinearEval4D (fullEinsteinTensor4D H)
        (plusPolarization4D μ ν) (plusPolarization4D μ ν) -
      bilinearEval4D (fullEinsteinTensor4D H)
        (minusPolarization4D μ ν) (minusPolarization4D μ ν)) = -4 * H μ ν := by
  have hp := (polarization_probe_quadratic_difference
    (fullEinsteinTensor4D H) μ ν).1
  have hG1 := (offDiagonal_einstein_eq_ricci_eq_neg_two_hessian H hH μ ν hμν).2.2.1
  have hG2 := (offDiagonal_einstein_eq_ricci_eq_neg_two_hessian H hH ν μ hμν.symm).2.2.1
  have hsym := hH ν μ
  have hsum : fullEinsteinTensor4D H μ ν + fullEinsteinTensor4D H ν μ = -4 * H μ ν := by
    rw [hG1, hG2, hsym]
    ring
  refine ⟨hp, hsum, ?_, ?_⟩
  · rw [hp, hsum]; ring
  · rw [hp, hsum]; ring

/-- Pure off-diagonal shear theorem: if `H` is symmetric and has vanishing
diagonal (`H μ μ = 0` for all `μ : Fin 4`), then:
1. `box4D H = 0`,
2. `fullScalarCurvature4D H = 0`,
3. `fullChronologicalCurvatureLimit4D H = 0`,
4. `fullEinsteinTrace4D H = 0`,
5. Yet for ALL `μ, ν : Fin 4`, `fullEinsteinTensor4D H μ ν = fullRicciTensor4D H μ ν = -2 * H μ ν`. -/
theorem pure_offDiagonal_shear_curvature_synthesis (H : Hessian4D)
    (hH : IsSymmetricHessian4D H) (hshear : IsPureOffDiagonalShear4D H) :
    box4D H = 0 ∧
    fullScalarCurvature4D H = 0 ∧
    fullChronologicalCurvatureLimit4D H = 0 ∧
    fullEinsteinTrace4D H = 0 ∧
    (∀ μ : Fin 4, fullRicciTensor4D H μ μ = 0 ∧ fullEinsteinTensor4D H μ μ = 0) ∧
    (∀ μ ν : Fin 4,
      fullRicciTensor4D H μ ν = -2 * H μ ν ∧
      fullEinsteinTensor4D H μ ν = -2 * H μ ν) := by
  have hbox : box4D H = 0 := by
    unfold box4D
    apply Finset.sum_eq_zero
    intro μ _
    rw [hshear μ, mul_zero]
  have hR : fullScalarCurvature4D H = 0 := by
    rw [(fullScalarCurvature4D_master_formula H).1, hbox, mul_zero]
  have hlim : fullChronologicalCurvatureLimit4D H = 0 := by
    unfold fullChronologicalCurvatureLimit4D
    rw [hR, mul_zero]
  have htr : fullEinsteinTrace4D H = 0 := by
    rw [(fullEinsteinTrace4D_master_formula H).2, hbox, mul_zero]
  have hall : ∀ μ ν : Fin 4,
      fullRicciTensor4D H μ ν = -2 * H μ ν ∧
      fullEinsteinTensor4D H μ ν = -2 * H μ ν := by
    intro μ ν
    rw [fullRicciTensor4D_master_formula H hH μ ν,
      fullEinsteinTensor4D_master_formula H hH μ ν, hbox]
    constructor <;> ring
  have hdiag : ∀ μ : Fin 4,
      fullRicciTensor4D H μ μ = 0 ∧ fullEinsteinTensor4D H μ μ = 0 := by
    intro μ
    rw [(hall μ μ).1, (hall μ μ).2, hshear μ, mul_zero]
    exact ⟨rfl, rfl⟩
  exact ⟨hbox, hR, hlim, htr, hdiag, hall⟩

/-- Exact formula for the differentiated Ricci tensor `∂_e R_{bd}(K)` of a
symmetric third-order conformal jet `K`:
`∂_e R_{bd}(K) = -2 K_{ebd} - (□ ∂_e Ω) η_{bd}`. -/
theorem fullDRicci4D_master_formula (H : Hessian4D) (K : ThirdJet4D)
    (hK : IsSymmetricThirdJet4D K) (e b d : Fin 4) :
    fullDRicci4D H K e b d = -2 * K e b d - dBox4D K e * minkMetric4D b d := by
  simp only [fullDRicci4D, dRic, riemannFromMetric, dR_metric,
    fullConformalMetricDerivs, fullConformalMetricThird,
    symmetrizeThirdJet4D_eq_of_symm K hK]
  rw [conformal_contraction_identity (K e) b d, hK.2 e d b]
  rfl

/-- Exact formula for the differentiated scalar curvature `∂_e R(K) = -6 * dBox4D K e`. -/
theorem fullDScalar4D_master_formula (H : Hessian4D) (K : ThirdJet4D)
    (hK : IsSymmetricThirdJet4D K) (e : Fin 4) :
    fullDScalar4D H K e = -6 * dBox4D K e := by
  unfold fullDScalar4D dScalar
  change ∑ b : Fin 4, sign b * fullDRicci4D H K e b b = -6 * dBox4D K e
  simp_rw [fullDRicci4D_master_formula H K hK e, minkMetric4D_diag]
  have hterm : ∀ b : Fin 4,
      sign b * (-2 * K e b b - dBox4D K e * sign b) =
      -2 * (sign b * K e b b) - dBox4D K e := by
    intro b
    calc sign b * (-2 * K e b b - dBox4D K e * sign b)
        = -2 * (sign b * K e b b) - (sign b * sign b) * dBox4D K e := by ring
      _ = -2 * (sign b * K e b b) - dBox4D K e := by rw [sign_sq_one b, one_mul]
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change -2 * dBox4D K e - ↑4 * dBox4D K e = -6 * dBox4D K e
  ring

/-- Exact formula for the differentiated Einstein tensor `∂_e G_{bd}(K)`:
`∂_e G_{bd}(K) = -2 K_{ebd} + 2 (□ ∂_e Ω) η_{bd}`.
In particular, for `b ≠ d` (the off-diagonal shear/flux channels),
`∂_e G_{bd}(K) = ∂_e R_{bd}(K) = -2 K_{ebd}`! -/
theorem fullDEinstein4D_master_formula (H : Hessian4D) (K : ThirdJet4D)
    (hK : IsSymmetricThirdJet4D K) (e b d : Fin 4) :
    fullDEinstein4D H K e b d =
      -2 * K e b d + 2 * dBox4D K e * minkMetric4D b d := by
  unfold fullDEinstein4D dEinstein
  change fullDRicci4D H K e b d - fullDScalar4D H K e / 2 * minkMetric4D b d = _
  rw [fullDRicci4D_master_formula H K hK e b d,
    fullDScalar4D_master_formula H K hK e]
  ring

theorem fullDEinstein4D_offDiag (H : Hessian4D) (K : ThirdJet4D)
    (hK : IsSymmetricThirdJet4D K) (e b d : Fin 4) (hbd : b ≠ d) :
    fullDEinstein4D H K e b d = -2 * K e b d ∧
    fullDEinstein4D H K e b d = fullDRicci4D H K e b d := by
  have hη := minkMetric4D_offDiag b d hbd
  have hE := fullDEinstein4D_master_formula H K hK e b d
  have hR := fullDRicci4D_master_formula H K hK e b d
  rw [hη, mul_zero, add_zero] at hE
  rw [hη, mul_zero, sub_zero] at hR
  exact ⟨hE, hE.trans hR.symm⟩

/-- Exact channel decomposition of the 4D Lorentzian contracted Bianchi identity
`∑ e, sign e * ∂_e G_{νe}(K) = 0`:
1. The total divergence splits into `bianchiDiagonalChannel4D + bianchiOffDiagonalChannel4D = 0`.
2. The diagonal channel (`e = ν`) equals `2 * ∑_{e ≠ ν} sign e * K ν e e`.
3. The off-diagonal shear/flux channel (`e ≠ ν`, coming from `∂_e G_{νe} = -2 K_{eνe}`)
   equals `-2 * ∑_{e ≠ ν} sign e * K ν e e`.
4. The diagonal and off-diagonal third-derivative channels are exact negatives
   of each other and cancel to zero! -/
theorem bianchi_diagonal_offDiagonal_channel_decomposition
    (H : Hessian4D) (K : ThirdJet4D) (hK : IsSymmetricThirdJet4D K) (ν : Fin 4) :
    (∑ e : Fin 4, sign e * fullDEinstein4D H K e ν e) =
      bianchiDiagonalChannel4D H K ν + bianchiOffDiagonalChannel4D H K ν ∧
    bianchiDiagonalChannel4D H K ν =
      2 * ∑ e ∈ Finset.univ.erase ν, sign e * K ν e e ∧
    bianchiOffDiagonalChannel4D H K ν =
      -2 * ∑ e ∈ Finset.univ.erase ν, sign e * K ν e e ∧
    bianchiDiagonalChannel4D H K ν + bianchiOffDiagonalChannel4D H K ν = 0 ∧
    (∑ e : Fin 4, sign e * fullDEinstein4D H K e ν e) = 0 := by
  have hsplit : (∑ e : Fin 4, sign e * fullDEinstein4D H K e ν e) =
      bianchiDiagonalChannel4D H K ν + bianchiOffDiagonalChannel4D H K ν := by
    unfold bianchiDiagonalChannel4D bianchiOffDiagonalChannel4D
    rw [← Finset.add_sum_erase Finset.univ
      (fun e => sign e * fullDEinstein4D H K e ν e) (Finset.mem_univ ν)]
  have hdiag : bianchiDiagonalChannel4D H K ν =
      2 * ∑ e ∈ Finset.univ.erase ν, sign e * K ν e e := by
    unfold bianchiDiagonalChannel4D
    rw [fullDEinstein4D_master_formula H K hK ν ν ν, minkMetric4D_diag]
    have hsq := sign_sq_one ν
    have hbox_split : dBox4D K ν =
        sign ν * K ν ν ν + ∑ e ∈ Finset.univ.erase ν, sign e * K ν e e := by
      unfold dBox4D
      exact (Finset.add_sum_erase Finset.univ
        (fun e => sign e * K ν e e) (Finset.mem_univ ν)).symm
    rw [hbox_split]
    calc sign ν * (-2 * K ν ν ν +
          2 * (sign ν * K ν ν ν + ∑ e ∈ Finset.univ.erase ν, sign e * K ν e e) * sign ν)
        = (-2 + 2 * (sign ν * sign ν)) * (sign ν * K ν ν ν) +
          2 * (sign ν * sign ν) * ∑ e ∈ Finset.univ.erase ν, sign e * K ν e e := by ring
      _ = 2 * ∑ e ∈ Finset.univ.erase ν, sign e * K ν e e := by
        rw [hsq]; ring
  have hoff : bianchiOffDiagonalChannel4D H K ν =
      -2 * ∑ e ∈ Finset.univ.erase ν, sign e * K ν e e := by
    unfold bianchiOffDiagonalChannel4D
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hne : ν ≠ e := (Finset.ne_of_mem_erase he).symm
    rw [(fullDEinstein4D_offDiag H K hK e ν e hne).1]
    have hsym_e : K e ν e = K ν e e := hK.1 e ν e
    rw [hsym_e]
    ring
  have hcancel : bianchiDiagonalChannel4D H K ν +
      bianchiOffDiagonalChannel4D H K ν = 0 := by
    rw [hdiag, hoff]
    ring
  have hzero : (∑ e : Fin 4, sign e * fullDEinstein4D H K e ν e) = 0 :=
    lorentzian_metric_divergence (fullConformalMetricDerivs H K) ν
  exact ⟨hsplit, hdiag, hoff, hcancel, hzero⟩

#print axioms symmetrizeHessian4D_eq_of_symm
#print axioms symmetrizeThirdJet4D_eq_of_symm
#print axioms minkMetric4D_offDiag
#print axioms minkMetric4D_diag
#print axioms hessian_diag_offDiag_split
#print axioms offDiagonalShearPart4D_isPureShear
#print axioms fullRicciTensor4D_master_formula
#print axioms fullScalarCurvature4D_master_formula
#print axioms fullEinsteinTensor4D_master_formula
#print axioms fullEinsteinTrace4D_master_formula
#print axioms offDiagonal_einstein_eq_ricci_eq_neg_two_hessian
#print axioms diagonalToHessian4D_compatibility
#print axioms bilinearEval4D_basis
#print axioms polarization_probe_quadratic_difference
#print axioms offDiagonal_polarization_probe_extraction
#print axioms pure_offDiagonal_shear_curvature_synthesis
#print axioms fullDRicci4D_master_formula
#print axioms fullDScalar4D_master_formula
#print axioms fullDEinstein4D_master_formula
#print axioms fullDEinstein4D_offDiag
#print axioms bianchi_diagonal_offDiagonal_channel_decomposition

end
end UnifiedTheory.Audit.KFCausalConformal4DOffDiagonalShearCurvatureSynthesis
