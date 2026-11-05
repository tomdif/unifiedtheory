/- Exact spatial block/exterior decomposition. All crossing plaquettes are
retained as a nonnegative boundary cost, with no volume-sized replacement. -/
import UnifiedTheory.Clay.YangMills.WilsonHighFieldDecay

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonSpatialCutEnergy
noncomputable section
open WilsonTimeSlab WilsonSlabOperator WilsonTemporalGauge WilsonSlabGauge
open WilsonSingleLinkStaples (character character_continuous character_classFunction)

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (SpatialVertex n × Fin 3) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (SpatialVertex n × SpatialPlane) :=
  Classical.decEq _

abbrev Plaquette := SpatialVertex n × SpatialPlane

def support (p : Plaquette n) : Finset (SpatialVertex n × Fin 3) :=
  {(p.1,p.2.1.1), (spatialStep n p.1 p.2.1.1,p.2.1.2),
    (spatialStep n p.1 p.2.1.2,p.2.1.1), (p.1,p.2.1.2)}

def bulk (S : Finset (SpatialVertex n × Fin 3)) : Finset (Plaquette n) :=
  Finset.univ.filter (fun p => support n p ⊆ S)

def boundary (S : Finset (SpatialVertex n × Fin 3)) : Finset (Plaquette n) :=
  Finset.univ \ (bulk n S ∪ bulk n Sᶜ)

def defect (u : Slice n) (p : Plaquette n) : ℝ :=
  2-(character (spatialHolonomy u p.1 p.2.1.1 p.2.1.2)).re

def partPotential (P : Finset (Plaquette n)) (u : Slice n) : ℝ := ∑ p ∈ P, defect n u p

def bulkPotential (S : Finset (SpatialVertex n × Fin 3)) (u : Slice n) : ℝ :=
  partPotential n (bulk n S) u

def boundaryPotential (S : Finset (SpatialVertex n × Fin 3)) (u : Slice n) : ℝ :=
  partPotential n (boundary n S) u

theorem bulk_disjoint (S : Finset (SpatialVertex n × Fin 3)) :
    Disjoint (bulk n S) (bulk n Sᶜ) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hi := (Finset.mem_filter.mp hp).2 (by simp [support] : (p.1,p.2.1.1) ∈ support n p)
  have ho := (Finset.mem_filter.mp hq).2 (by simp [support] : (p.1,p.2.1.1) ∈ support n p)
  exact (Finset.mem_compl.mp ho) hi

omit [NeZero n] in
theorem part_bounds (P : Finset (Plaquette n)) (u : Slice n) :
    0 ≤ partPotential n P u ∧ partPotential n P u ≤ 4*(P.card : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun p _ => (WilsonSlabBounds.characterDefect_bounds _).1)
  · have h := Finset.sum_le_sum (s := P) (f := fun p => defect n u p) (g := fun _ => (4:ℝ))
      (fun p _ => (WilsonSlabBounds.characterDefect_bounds _).2)
    simpa only [partPotential, Finset.sum_const, nsmul_eq_mul, mul_comm] using h

theorem potential_split (S : Finset (SpatialVertex n × Fin 3)) (u : Slice n) :
    potential character 2 u = bulkPotential n S u+bulkPotential n Sᶜ u+boundaryPotential n S u := by
  have h := Finset.sum_sdiff (Finset.subset_univ (bulk n S ∪ bulk n Sᶜ)) (f := defect n u)
  rw [Finset.sum_union (bulk_disjoint n S)] at h
  have he : (∑ p : Plaquette n, defect n u p) = potential character 2 u := by
    simp only [Fintype.sum_prod_type, defect, potential]
  rw [he] at h
  change boundaryPotential n S u+(bulkPotential n S u+bulkPotential n Sᶜ u) = _ at h
  linarith

omit [NeZero n] in
theorem part_continuous (P : Finset (Plaquette n)) : Continuous (partPotential n P) := by
  have hc := character_continuous
  unfold partPotential defect spatialHolonomy
  fun_prop

omit [NeZero n] in
theorem part_gauge (P : Finset (Plaquette n)) (h : SliceGauge n Q) (u : Slice n) :
    partPotential n P (gaugeSlice h u) = partPotential n P u := by
  have hc := character_classFunction
  unfold RegulatedGauge.ClassFunction at hc
  simp only [partPotential, defect, spatialHolonomy_gauge, hc]

omit [NeZero n] in
theorem defect_congr (p : Plaquette n) (u v : Slice n)
    (h : ∀ e ∈ support n p, u e = v e) : defect n u p = defect n v p := by
  unfold defect spatialHolonomy
  rw [h (p.1,p.2.1.1) (by simp [support]),
    h (spatialStep n p.1 p.2.1.1,p.2.1.2) (by simp [support]),
    h (spatialStep n p.1 p.2.1.2,p.2.1.1) (by simp [support]),
    h (p.1,p.2.1.2) (by simp [support])]

theorem bulk_congr (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n)
    (h : ∀ e ∈ S, u e = v e) : bulkPotential n S u = bulkPotential n S v := by
  apply Finset.sum_congr rfl
  intro p hp
  exact defect_congr n p u v (fun e he => h e ((Finset.mem_filter.mp hp).2 he))

def kineticPart (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n) : ℝ :=
  ∑ e ∈ S, (2-(character ((u e)⁻¹*v e)).re)

omit [NeZero n] in
theorem kinetic_nonneg (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n) :
    0 ≤ kineticPart n S u v :=
  Finset.sum_nonneg (fun _ _ => (WilsonSlabBounds.characterDefect_bounds _).1)

theorem kinetic_split (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n) :
    kineticAction character 2 u v = kineticPart n S u v+kineticPart n Sᶜ u v := by
  exact (Finset.sum_add_sum_compl S (fun e => 2-(character ((u e)⁻¹*v e)).re)).symm

omit [NeZero n] in
theorem kinetic_congr (S : Finset (SpatialVertex n × Fin 3)) (u v u' v' : Slice n)
    (hu : ∀ e ∈ S, u e = u' e) (hv : ∀ e ∈ S, v e = v' e) :
    kineticPart n S u v = kineticPart n S u' v' := by
  apply Finset.sum_congr rfl
  intro e he
  rw [hu e he, hv e he]

def piece (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n) : ℝ :=
  Real.exp (-β*(bulkPotential n S u/2+kineticPart n S u v+bulkPotential n S v/2))

theorem piece_pos (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n) :
    0 < piece n β S u v := Real.exp_pos _

theorem piece_continuous (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) :
    Continuous (fun z : Slice n × Slice n => piece n β S z.1 z.2) := by
  have hc := character_continuous
  have hp := part_continuous n (bulk n S)
  unfold piece bulkPotential kineticPart
  fun_prop

theorem piece_congr (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) (u v u' v' : Slice n)
    (hu : ∀ e ∈ S, u e = u' e) (hv : ∀ e ∈ S, v e = v' e) :
    piece n β S u v = piece n β S u' v' := by
  rw [piece, piece, bulk_congr n S u u' hu, bulk_congr n S v v' hv,
    kinetic_congr n S u v u' v' hu hv]

theorem piece_high (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (R : ℝ) (u v : Slice n) (hv : R ≤ bulkPotential n S v) :
    piece n β S u v ≤ Real.exp (-β*R/2) := by
  apply Real.exp_le_exp.mpr
  have hu := (part_bounds n (bulk n S) u).1
  change 0 ≤ bulkPotential n S u at hu
  have hk := kinetic_nonneg n S u v
  have h := mul_le_mul_of_nonneg_left (show R/2 ≤
    bulkPotential n S u/2+kineticPart n S u v+bulkPotential n S v/2 by linarith) hβ
  change -β*(bulkPotential n S u/2+kineticPart n S u v+bulkPotential n S v/2) ≤ _
  nlinarith

theorem raw_split (β : ℝ) (S : Finset (SpatialVertex n × Fin 3)) (u v : Slice n) :
    rawKernel character β 2 u v =
      Real.exp (-β*(boundaryPotential n S u+boundaryPotential n S v)/2)*
        (piece n β S u v*piece n β Sᶜ u v) := by
  unfold rawKernel spatialWeight kineticWeight piece
  rw [potential_split n S u, potential_split n S v, kinetic_split n S u v]
  simp only [← Real.exp_add]
  congr 1
  ring

theorem raw_cut_upper (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (u v : Slice n) : rawKernel character β 2 u v ≤ piece n β S u v*piece n β Sᶜ u v := by
  rw [raw_split n β S]
  have hb : Real.exp (-β*(boundaryPotential n S u+boundaryPotential n S v)/2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hu := (part_bounds n (boundary n S) u).1
    have hv := (part_bounds n (boundary n S) v).1
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hβ) (add_nonneg hu hv)) (by norm_num)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hb
    (mul_pos (piece_pos n β S u v) (piece_pos n β Sᶜ u v)).le

theorem raw_cut_lower (β : ℝ) (hβ : 0 ≤ β) (S : Finset (SpatialVertex n × Fin 3))
    (u v : Slice n) :
    Real.exp (-4*β*(boundary n S).card)*(piece n β S u v*piece n β Sᶜ u v) ≤
      rawKernel character β 2 u v := by
  rw [raw_split n β S]
  apply mul_le_mul_of_nonneg_right _ (mul_pos (piece_pos n β S u v) (piece_pos n β Sᶜ u v)).le
  apply Real.exp_le_exp.mpr
  have hu := (part_bounds n (boundary n S) u).2
  have hv := (part_bounds n (boundary n S) v).2
  change boundaryPotential n S u ≤ _ at hu
  change boundaryPotential n S v ≤ _ at hv
  have h := mul_le_mul_of_nonneg_left (show boundaryPotential n S u+boundaryPotential n S v ≤
    8*((boundary n S).card : ℝ) by linarith) hβ
  nlinarith

end
end UnifiedTheory.Clay.YangMills.WilsonSpatialCutEnergy
