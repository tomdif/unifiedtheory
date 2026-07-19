/-
  Audit/KFOrientationCPChannelTower.lean

  FINITE TOWERS OF ISOMETRIC CP COMPRESSIONS

  The preceding audit constructed two concrete normalized one-Kraus channels
  and proved the two-scale Schwarz-defect cocycle.  This file packages that
  mechanism for an arbitrary finite heterogeneous tower of matrix sizes.

  A path carries both its total compression and a recursively resolved defect.
  The main theorem says that the total defect is exactly transported old
  defect plus defect generated at every later stage.  A protected observable
  is required to lie in the multiplicative domain at every successive image,
  not merely at one selected scale.

  Finally, two paths with common endpoints define a defect curvature.  Its
  triangle and postcomposition laws make precise the proposed distinction
  between path-independent universality and coarse-graining holonomy.

  These are finite matrix-channel theorems.  No continuum channel semigroup,
  causal-set quantum state, or Einstein/QFT recovery is asserted.
-/

import UnifiedTheory.Audit.KFOrientationCPChannelComposition
import UnifiedTheory.Audit.KFOrientationPathObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationCPChannelTower

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationCPChannel
open UnifiedTheory.Audit.KFOrientationCPChannelComposition
open UnifiedTheory.Audit.KFOrientationPathObstruction

abbrev SquareMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev RectMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ

/-! ## 1. Arbitrary normalized one-Kraus compressions -/

/-- A normalized one-Kraus compression from `m` microscopic modes to `n`
retained modes.  The column isometry makes `A ↦ Vᴴ A V` unital and CP. -/
structure IsometricCompression (m n : ℕ) where
  isometry : RectMatrix m n
  isometry_condition : isometryᴴ * isometry = (1 : SquareMatrix n)

namespace IsometricCompression

variable {m n p : ℕ}

@[ext]
theorem ext {Phi Psi : IsometricCompression m n}
    (h : Phi.isometry = Psi.isometry) : Phi = Psi := by
  cases Phi
  cases Psi
  simp_all

def map (Phi : IsometricCompression m n)
    (A : SquareMatrix m) : SquareMatrix n :=
  Phi.isometryᴴ * A * Phi.isometry

theorem map_zero (Phi : IsometricCompression m n) :
    Phi.map (0 : SquareMatrix m) = 0 := by
  simp [map]

theorem map_add (Phi : IsometricCompression m n)
    (A B : SquareMatrix m) :
    Phi.map (A + B) = Phi.map A + Phi.map B := by
  unfold map
  rw [Matrix.mul_add, Matrix.add_mul]

theorem map_sub (Phi : IsometricCompression m n)
    (A B : SquareMatrix m) :
    Phi.map (A - B) = Phi.map A - Phi.map B := by
  unfold map
  rw [Matrix.mul_sub, Matrix.sub_mul]

theorem map_smul (Phi : IsometricCompression m n)
    (z : ℂ) (A : SquareMatrix m) :
    Phi.map (z • A) = z • Phi.map A := by
  unfold map
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem map_one (Phi : IsometricCompression m n) :
    Phi.map (1 : SquareMatrix m) = 1 := by
  unfold map
  rw [Matrix.mul_one, Phi.isometry_condition]

theorem map_conjTranspose (Phi : IsometricCompression m n)
    (A : SquareMatrix m) :
    Phi.map Aᴴ = (Phi.map A)ᴴ := by
  unfold map
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem map_posSemidef (Phi : IsometricCompression m n)
    {A : SquareMatrix m} (hA : A.PosSemidef) :
    (Phi.map A).PosSemidef := by
  unfold map
  exact hA.conjTranspose_mul_mul_same Phi.isometry

def rangeProjection (Phi : IsometricCompression m n) : SquareMatrix m :=
  Phi.isometry * Phi.isometryᴴ

def complementProjection (Phi : IsometricCompression m n) : SquareMatrix m :=
  1 - Phi.rangeProjection

theorem rangeProjection_isHermitian (Phi : IsometricCompression m n) :
    Phi.rangeProjection.IsHermitian := by
  exact Matrix.isHermitian_mul_conjTranspose_self Phi.isometry

theorem rangeProjection_idempotent (Phi : IsometricCompression m n) :
    Phi.rangeProjection * Phi.rangeProjection = Phi.rangeProjection := by
  unfold rangeProjection
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Phi.isometryᴴ,
    Phi.isometry_condition, Matrix.one_mul]

theorem complementProjection_isHermitian (Phi : IsometricCompression m n) :
    Phi.complementProjection.IsHermitian := by
  unfold complementProjection Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Phi.rangeProjection_isHermitian.eq]

theorem complementProjection_idempotent (Phi : IsometricCompression m n) :
    Phi.complementProjection * Phi.complementProjection =
      Phi.complementProjection := by
  unfold complementProjection
  calc
    (1 - Phi.rangeProjection) * (1 - Phi.rangeProjection) =
        1 - Phi.rangeProjection - Phi.rangeProjection +
          Phi.rangeProjection * Phi.rangeProjection := by
      noncomm_ring
    _ = 1 - Phi.rangeProjection - Phi.rangeProjection +
          Phi.rangeProjection := by
      rw [Phi.rangeProjection_idempotent]
    _ = 1 - Phi.rangeProjection := by
      abel

def leakage (Phi : IsometricCompression m n)
    (A : SquareMatrix m) : RectMatrix m n :=
  Phi.complementProjection * A * Phi.isometry

def defect (Phi : IsometricCompression m n)
    (A B : SquareMatrix m) : SquareMatrix n :=
  Phi.map (Aᴴ * B) - (Phi.map A)ᴴ * Phi.map B

theorem defect_factor (Phi : IsometricCompression m n)
    (A B : SquareMatrix m) :
    Phi.defect A B = (Phi.leakage A)ᴴ * Phi.leakage B := by
  have hdefect :
      Phi.defect A B =
        Phi.isometryᴴ * Aᴴ * Phi.complementProjection * B *
          Phi.isometry := by
    unfold defect map complementProjection rangeProjection
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.mul_assoc]
  symm
  calc
    (Phi.leakage A)ᴴ * Phi.leakage B =
        Phi.isometryᴴ * Aᴴ *
          (Phi.complementProjection * Phi.complementProjection) * B *
            Phi.isometry := by
      unfold leakage
      simp only [Matrix.conjTranspose_mul,
        Phi.complementProjection_isHermitian.eq, Matrix.mul_assoc]
    _ = Phi.isometryᴴ * Aᴴ * Phi.complementProjection * B *
          Phi.isometry := by
      rw [Phi.complementProjection_idempotent]
    _ = Phi.defect A B := hdefect.symm

theorem defect_posSemidef (Phi : IsometricCompression m n)
    (A : SquareMatrix m) :
    (Phi.defect A A).PosSemidef := by
  rw [Phi.defect_factor]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem defect_self_eq_zero_iff (Phi : IsometricCompression m n)
    (A : SquareMatrix m) :
    Phi.defect A A = 0 ↔ Phi.leakage A = 0 := by
  rw [Phi.defect_factor, Matrix.conjTranspose_mul_self_eq_zero]

/-- Both left and right multiplication must survive the compression. -/
def InMultiplicativeDomain (Phi : IsometricCompression m n)
    (A : SquareMatrix m) : Prop :=
  Phi.leakage A = 0 ∧ Phi.leakage Aᴴ = 0

theorem hermitian_mem_multiplicativeDomain_iff
    (Phi : IsometricCompression m n) (A : SquareMatrix m)
    (hA : A.IsHermitian) :
    Phi.InMultiplicativeDomain A ↔ Phi.defect A A = 0 := by
  unfold InMultiplicativeDomain
  rw [hA.eq, and_self, Phi.defect_self_eq_zero_iff]

/-- Composition is multiplication of the two column isometries. -/
def followedBy (Phi : IsometricCompression m n)
    (Psi : IsometricCompression n p) : IsometricCompression m p where
  isometry := Phi.isometry * Psi.isometry
  isometry_condition := by
    rw [Matrix.conjTranspose_mul]
    calc
      (Psi.isometryᴴ * Phi.isometryᴴ) *
          (Phi.isometry * Psi.isometry) =
        Psi.isometryᴴ * (Phi.isometryᴴ * Phi.isometry) *
          Psi.isometry := by
        simp only [Matrix.mul_assoc]
      _ = Psi.isometryᴴ * Psi.isometry := by
        rw [Phi.isometry_condition, Matrix.mul_one]
      _ = 1 := Psi.isometry_condition

@[simp]
theorem map_followedBy (Phi : IsometricCompression m n)
    (Psi : IsometricCompression n p) (A : SquareMatrix m) :
    (Phi.followedBy Psi).map A = Psi.map (Phi.map A) := by
  simp only [followedBy, map, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The two-channel cocycle in dimension-independent form. -/
theorem defect_followedBy (Phi : IsometricCompression m n)
    (Psi : IsometricCompression n p) (A B : SquareMatrix m) :
    (Phi.followedBy Psi).defect A B =
      Psi.map (Phi.defect A B) +
        Psi.defect (Phi.map A) (Phi.map B) := by
  unfold defect
  rw [map_followedBy, map_followedBy, map_followedBy, Psi.map_sub]
  abel

def identity (n : ℕ) : IsometricCompression n n where
  isometry := 1
  isometry_condition := by simp

@[simp]
theorem identity_map (A : SquareMatrix n) :
    (identity n).map A = A := by
  simp [identity, map]

@[simp]
theorem identity_defect (A B : SquareMatrix n) :
    (identity n).defect A B = 0 := by
  simp [defect]

end IsometricCompression

/-! ## 2. Heterogeneous finite scale paths -/

/-- A finite path of normalized compressions with potentially different
matrix sizes at every scale. -/
inductive CompressionPath : ℕ → ℕ → Type
  | nil (n : ℕ) : CompressionPath n n
  | cons {m n p : ℕ} (head : IsometricCompression m n)
      (tail : CompressionPath n p) : CompressionPath m p

namespace CompressionPath

variable {m n p : ℕ}

def total {m n : ℕ} : CompressionPath m n → IsometricCompression m n
  | .nil k => IsometricCompression.identity k
  | .cons head tail => head.followedBy tail.total

def map (path : CompressionPath m n)
    (A : SquareMatrix m) : SquareMatrix n :=
  path.total.map A

def defect (path : CompressionPath m n)
    (A B : SquareMatrix m) : SquareMatrix n :=
  path.total.defect A B

/-- The scale-resolved covariance budget.  The first term transports defect
already generated at the head; the second recursively records later defect. -/
def accumulatedDefect {m n : ℕ} :
    (path : CompressionPath m n) →
      SquareMatrix m → SquareMatrix m → SquareMatrix n
  | .nil _, _, _ => 0
  | .cons head tail, A, B =>
      tail.map (head.defect A B) +
      accumulatedDefect tail (head.map A) (head.map B)

/-- Arbitrary finite telescoping of the Schwarz defect. -/
theorem defect_eq_accumulatedDefect
    (path : CompressionPath m n) (A B : SquareMatrix m) :
    path.defect A B = path.accumulatedDefect A B := by
  induction path with
  | nil k =>
      simp [defect, total, accumulatedDefect]
  | @cons a b c head tail ih =>
      rw [defect, total, IsometricCompression.defect_followedBy]
      change tail.map (head.defect A B) +
          tail.defect (head.map A) (head.map B) = _
      rw [ih]
      rfl

theorem accumulatedDefect_posSemidef
    (path : CompressionPath m n) (A : SquareMatrix m) :
    (path.accumulatedDefect A A).PosSemidef := by
  rw [← path.defect_eq_accumulatedDefect]
  exact path.total.defect_posSemidef A

/-- An observable is protected along a path only when it belongs to the
multiplicative domain at every successive retained image. -/
def ProtectedAlong {m n : ℕ} :
    (path : CompressionPath m n) → SquareMatrix m → Prop
  | .nil _, _ => True
  | .cons head tail, A =>
      head.InMultiplicativeDomain A ∧ ProtectedAlong tail (head.map A)

/-- The same all-scale gate expressed through local diagonal defects. -/
def EveryStageDefectZero {m n : ℕ} :
    (path : CompressionPath m n) → SquareMatrix m → Prop
  | .nil _, _ => True
  | .cons head tail, A =>
      head.defect A A = 0 ∧ EveryStageDefectZero tail (head.map A)

theorem map_isHermitian (path : CompressionPath m n)
    {A : SquareMatrix m} (hA : A.IsHermitian) :
    (path.map A).IsHermitian := by
  unfold map Matrix.IsHermitian
  rw [← path.total.map_conjTranspose, hA.eq]

/-- For observables, the all-stage zero-defect test is exactly the all-scale
multiplicative-domain test. -/
theorem protectedAlong_iff_everyStageDefectZero
    (path : CompressionPath m n) (A : SquareMatrix m)
    (hA : A.IsHermitian) :
    path.ProtectedAlong A ↔ path.EveryStageDefectZero A := by
  induction path with
  | nil k => rfl
  | @cons a b c head tail ih =>
      simp only [ProtectedAlong, EveryStageDefectZero]
      have hMap : (head.map A).IsHermitian := by
        unfold Matrix.IsHermitian
        rw [← head.map_conjTranspose, hA.eq]
      rw [head.hermitian_mem_multiplicativeDomain_iff A hA,
        ih (head.map A) hMap]

/-- All-scale protection is sufficient for zero total Schwarz defect. -/
theorem protectedAlong_totalDefect_zero
    (path : CompressionPath m n) (A : SquareMatrix m)
    (hProtected : path.ProtectedAlong A) :
    path.defect A A = 0 := by
  induction path with
  | nil k => simp [defect, total]
  | @cons a b c head tail ih =>
      rcases hProtected with ⟨hHead, hTail⟩
      rw [defect, total, IsometricCompression.defect_followedBy]
      have hHeadDefect : head.defect A A = 0 :=
        (head.defect_self_eq_zero_iff A).2 hHead.1
      rw [hHeadDefect, tail.total.map_zero, zero_add]
      exact ih (head.map A) hTail

def single (Phi : IsometricCompression m n) : CompressionPath m n :=
  .cons Phi (.nil n)

def append {m n p : ℕ} :
    CompressionPath m n → CompressionPath n p → CompressionPath m p
  | .nil _, right => right
  | .cons head tail, right => .cons head (append tail right)

theorem total_append (left : CompressionPath m n)
    (right : CompressionPath n p) :
    (left.append right).total = left.total.followedBy right.total := by
  induction left with
  | nil k =>
      apply IsometricCompression.ext
      simp [append, total, IsometricCompression.followedBy,
        IsometricCompression.identity]
  | @cons a b c head tail ih =>
      apply IsometricCompression.ext
      simp only [append, total, IsometricCompression.followedBy]
      rw [ih]
      simp [IsometricCompression.followedBy, Matrix.mul_assoc]

theorem map_append (left : CompressionPath m n)
    (right : CompressionPath n p) (A : SquareMatrix m) :
    (left.append right).map A = right.map (left.map A) := by
  unfold map
  rw [total_append, IsometricCompression.map_followedBy]

theorem defect_append (left : CompressionPath m n)
    (right : CompressionPath n p) (A B : SquareMatrix m) :
    (left.append right).defect A B =
      right.map (left.defect A B) +
        right.defect (left.map A) (left.map B) := by
  unfold defect map
  rw [total_append, IsometricCompression.defect_followedBy]

/-! ## 3. Defect curvature between coarse-graining paths -/

/-- Difference of accumulated covariance between two paths with common
microscopic and infrared matrix algebras. -/
def defectCurvature (left right : CompressionPath m n)
    (A B : SquareMatrix m) : SquareMatrix n :=
  left.defect A B - right.defect A B

theorem defectCurvature_self (path : CompressionPath m n)
    (A B : SquareMatrix m) :
    path.defectCurvature path A B = 0 := by
  simp [defectCurvature]

theorem defectCurvature_swap (left right : CompressionPath m n)
    (A B : SquareMatrix m) :
    right.defectCurvature left A B = -left.defectCurvature right A B := by
  simp [defectCurvature]

/-- Curvature differences themselves obey a path-space cocycle law. -/
theorem defectCurvature_triangle
    (left middle right : CompressionPath m n)
    (A B : SquareMatrix m) :
    left.defectCurvature right A B =
      left.defectCurvature middle A B +
        middle.defectCurvature right A B := by
  unfold defectCurvature
  abel

theorem map_sub (path : CompressionPath m n)
    (A B : SquareMatrix m) :
    path.map (A - B) = path.map A - path.map B := by
  exact path.total.map_sub A B

/-- Under a common later compression, old curvature is transported and a new
term measures the difference between the two retained endpoint pairs. -/
theorem defectCurvature_append
    (left right : CompressionPath m n) (tail : CompressionPath n p)
    (A B : SquareMatrix m) :
    (left.append tail).defectCurvature (right.append tail) A B =
      tail.map (left.defectCurvature right A B) +
        (tail.defect (left.map A) (left.map B) -
          tail.defect (right.map A) (right.map B)) := by
  rw [defectCurvature, left.defect_append, right.defect_append,
    defectCurvature, tail.map_sub]
  abel

/-- If the two paths retain the same endpoint observables, later blocking
transports their existing curvature without generating a new path mismatch. -/
theorem defectCurvature_append_of_same_images
    (left right : CompressionPath m n) (tail : CompressionPath n p)
    (A B : SquareMatrix m)
    (hA : left.map A = right.map A)
    (hB : left.map B = right.map B) :
    (left.append tail).defectCurvature (right.append tail) A B =
      tail.map (left.defectCurvature right A B) := by
  rw [defectCurvature_append, hA, hB, sub_self, add_zero]

/-- Equal retained linear and product data force zero curvature on the tested
pair.  This is a falsifiable path-independence gate, not a definition. -/
theorem defectCurvature_eq_zero_of_same_retained_data
    (left right : CompressionPath m n) (A B : SquareMatrix m)
    (hA : left.map A = right.map A)
    (hB : left.map B = right.map B)
    (hAB : left.map (Aᴴ * B) = right.map (Aᴴ * B)) :
    left.defectCurvature right A B = 0 := by
  unfold defectCurvature defect
  unfold map at hA hB hAB
  unfold IsometricCompression.defect
  rw [hA, hB, hAB]
  simp

end CompressionPath

/-! ## 4. Recovery of the concrete two-scale orientation channel -/

def diamondCompression : IsometricCompression 6 3 where
  isometry := normalizedBlockIsometry
  isometry_condition := normalizedBlockIsometry_isometry

def infraredCompression : IsometricCompression 3 2 where
  isometry := secondBlockIsometry
  isometry_condition := secondBlockIsometry_isometry

def orientationOneScalePath : CompressionPath 6 3 :=
  CompressionPath.single diamondCompression

def orientationTwoScalePath : CompressionPath 6 2 :=
  .cons diamondCompression (CompressionPath.single infraredCompression)

theorem diamondCompression_map (A : SquareMatrix 6) :
    diamondCompression.map A = blockCompression A := rfl

theorem infraredCompression_map (A : SquareMatrix 3) :
    infraredCompression.map A = secondCompression A := rfl

theorem orientationTwoScalePath_map (A : SquareMatrix 6) :
    orientationTwoScalePath.map A = composedBlockCompression A := by
  simp [orientationTwoScalePath, CompressionPath.map,
    CompressionPath.total, CompressionPath.single,
    IsometricCompression.map_followedBy, composedBlockCompression,
    diamondCompression_map, infraredCompression_map]

theorem orientationTwoScalePath_defect (A B : SquareMatrix 6) :
    orientationTwoScalePath.defect A B = composedCompressionDefect A B := by
  unfold CompressionPath.defect IsometricCompression.defect
    composedCompressionDefect
  change orientationTwoScalePath.map (Aᴴ * B) -
      (orientationTwoScalePath.map A)ᴴ * orientationTwoScalePath.map B = _
  rw [orientationTwoScalePath_map, orientationTwoScalePath_map,
    orientationTwoScalePath_map]

theorem fineOrientation_protected_one_scale :
    orientationOneScalePath.ProtectedAlong
      fineDiamondOrientationHamiltonian := by
  change InCompressionMultiplicativeDomain
      fineDiamondOrientationHamiltonian ∧ True
  exact ⟨fineDiamondOrientationHamiltonian_mem_multiplicativeDomain,
    trivial⟩

/-- The tower formulation exposes the delayed-loss result as failure of
all-scale protection, despite exact protection at the first scale. -/
theorem fineOrientation_not_protected_two_scales :
    ¬ orientationTwoScalePath.ProtectedAlong
      fineDiamondOrientationHamiltonian := by
  intro hProtected
  have hZero := orientationTwoScalePath.protectedAlong_totalDefect_zero
    fineDiamondOrientationHamiltonian hProtected
  rw [orientationTwoScalePath_defect] at hZero
  exact composedOrientationDefect_ne_zero hZero

theorem fineOrientation_protection_is_scale_relative :
    orientationOneScalePath.ProtectedAlong fineDiamondOrientationHamiltonian
      ∧ ¬ orientationTwoScalePath.ProtectedAlong
        fineDiamondOrientationHamiltonian :=
  ⟨fineOrientation_protected_one_scale,
    fineOrientation_not_protected_two_scales⟩

/-! ## 5. A finite binary orientation-holonomy witness -/

/-- Difference between the two exact rational quotient-path defects.  This is
the quotient analogue of `CompressionPath.defectCurvature`; it is kept
separate because the unnormalized rational pushforwards are not CP channels. -/
def quotientOrientationCurvature : Matrix (Fin 2) (Fin 2) ℚ :=
  chainFourPath13Defect - chainFourPath22Defect

/-- The two quotient routes differ by exactly one native orientation unit. -/
theorem quotientOrientationCurvature_exact :
    quotientOrientationCurvature =
      (-1 : ℚ) • chainTwoOrientationRankOne := by
  rw [quotientOrientationCurvature, chainFourPath13_defect_exact,
    chainFourPath22_defect_exact]
  module

theorem quotientOrientationCurvature_ne_zero :
    quotientOrientationCurvature ≠ 0 := by
  rw [quotientOrientationCurvature_exact]
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [chainTwoOrientationRankOne] at h01

/-- Multiplication by `i` turns the real skew path curvature into a Hermitian
two-sector observable. -/
def quotientCurvatureHamiltonian : SquareMatrix 2 :=
  Complex.I • quotientOrientationCurvature.map (Rat.castHom ℂ)

theorem quotientCurvatureHamiltonian_exact :
    quotientCurvatureHamiltonian =
      !![(0 : ℂ), -Complex.I;
         Complex.I, 0] := by
  rw [quotientCurvatureHamiltonian, quotientOrientationCurvature_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chainTwoOrientationRankOne, Fin.ext_iff]

theorem quotientCurvatureHamiltonian_isHermitian :
    quotientCurvatureHamiltonian.IsHermitian := by
  rw [quotientCurvatureHamiltonian_exact]
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.conjTranspose_apply, Fin.ext_iff]

/-- The normalized curvature is an involution: its only possible spectral
values are the binary orientation labels `+1` and `-1`. -/
theorem quotientCurvatureHamiltonian_sq :
    quotientCurvatureHamiltonian * quotientCurvatureHamiltonian = 1 := by
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Fin.ext_iff,
      Complex.I_sq]

theorem quotientCurvatureHamiltonian_trace :
    Matrix.trace quotientCurvatureHamiltonian = 0 := by
  rw [quotientCurvatureHamiltonian_exact]
  norm_num [Matrix.trace, Fin.sum_univ_succ]

def positiveOrientationProjector : SquareMatrix 2 :=
  (1 / 2 : ℂ) • (1 + quotientCurvatureHamiltonian)

def negativeOrientationProjector : SquareMatrix 2 :=
  (1 / 2 : ℂ) • (1 - quotientCurvatureHamiltonian)

theorem orientationProjectors_sum :
    positiveOrientationProjector + negativeOrientationProjector = 1 := by
  unfold positiveOrientationProjector negativeOrientationProjector
  module

theorem positiveOrientationProjector_idempotent :
    positiveOrientationProjector * positiveOrientationProjector =
      positiveOrientationProjector := by
  unfold positiveOrientationProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    quotientCurvatureHamiltonian_sq]
  module

theorem negativeOrientationProjector_idempotent :
    negativeOrientationProjector * negativeOrientationProjector =
      negativeOrientationProjector := by
  unfold negativeOrientationProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    quotientCurvatureHamiltonian_sq]
  module

theorem orientationProjectors_orthogonal :
    positiveOrientationProjector * negativeOrientationProjector = 0 := by
  unfold positiveOrientationProjector negativeOrientationProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    quotientCurvatureHamiltonian_sq]
  module

theorem positiveOrientationProjector_eigen :
    quotientCurvatureHamiltonian * positiveOrientationProjector =
      positiveOrientationProjector := by
  unfold positiveOrientationProjector
  simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one,
    quotientCurvatureHamiltonian_sq]
  module

theorem negativeOrientationProjector_eigen :
    quotientCurvatureHamiltonian * negativeOrientationProjector =
      -negativeOrientationProjector := by
  unfold negativeOrientationProjector
  simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
    quotientCurvatureHamiltonian_sq]
  module

theorem positiveOrientationProjector_trace :
    Matrix.trace positiveOrientationProjector = 1 := by
  unfold positiveOrientationProjector
  rw [quotientCurvatureHamiltonian_exact]
  norm_num [Matrix.trace, Fin.sum_univ_succ]

theorem negativeOrientationProjector_trace :
    Matrix.trace negativeOrientationProjector = 1 := by
  unfold negativeOrientationProjector
  rw [quotientCurvatureHamiltonian_exact]
  norm_num [Matrix.trace, Fin.sum_univ_succ]

/-- Exact finite synthesis: path-dependent blocking supplies a nonzero
Hermitian involution with two complementary orthogonal sectors. -/
theorem binary_orientation_holonomy :
    quotientOrientationCurvature ≠ 0
      ∧ quotientCurvatureHamiltonian.IsHermitian
      ∧ quotientCurvatureHamiltonian * quotientCurvatureHamiltonian = 1
      ∧ Matrix.trace quotientCurvatureHamiltonian = 0
      ∧ positiveOrientationProjector + negativeOrientationProjector = 1
      ∧ positiveOrientationProjector * negativeOrientationProjector = 0
      ∧ quotientCurvatureHamiltonian * positiveOrientationProjector =
          positiveOrientationProjector
      ∧ quotientCurvatureHamiltonian * negativeOrientationProjector =
          -negativeOrientationProjector
      ∧ Matrix.trace positiveOrientationProjector = 1
      ∧ Matrix.trace negativeOrientationProjector = 1 :=
  ⟨quotientOrientationCurvature_ne_zero,
    quotientCurvatureHamiltonian_isHermitian,
    quotientCurvatureHamiltonian_sq,
    quotientCurvatureHamiltonian_trace,
    orientationProjectors_sum,
    orientationProjectors_orthogonal,
    positiveOrientationProjector_eigen,
    negativeOrientationProjector_eigen,
    positiveOrientationProjector_trace,
    negativeOrientationProjector_trace⟩

#print axioms IsometricCompression.defect_factor
#print axioms IsometricCompression.defect_followedBy
#print axioms CompressionPath.defect_eq_accumulatedDefect
#print axioms CompressionPath.protectedAlong_iff_everyStageDefectZero
#print axioms CompressionPath.protectedAlong_totalDefect_zero
#print axioms CompressionPath.defectCurvature_triangle
#print axioms CompressionPath.defectCurvature_append
#print axioms fineOrientation_protection_is_scale_relative
#print axioms quotientOrientationCurvature_exact
#print axioms binary_orientation_holonomy

end

end UnifiedTheory.Audit.KFOrientationCPChannelTower
