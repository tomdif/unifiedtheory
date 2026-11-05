/- Exact time-slab Wilson weights, including spatial plaquettes and temporal
link integration. The plaquette identities refer to the actual four-dimensional
periodic lattice. No continuum limit, transfer eigenpair or uniform estimate
is assumed to have been constructed. -/
import UnifiedTheory.Clay.YangMills.WilsonMomentBounds
import UnifiedTheory.Clay.YangMills.PeriodicPlaquetteReflection
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonTimeSlab
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicPlaquetteReflection PeriodicTimeReflection

abbrev SpatialVertex (n : ℕ) := Fin 3 → ZMod n
abbrev SpatialLinks (n : ℕ) (G : Type*) := SpatialVertex n × Fin 3 → G
abbrev SliceGauge (n : ℕ) (G : Type*) := SpatialVertex n → G
abbrev SpatialPlane := {p : Fin 3 × Fin 3 // p.1 < p.2}

def embed (n : ℕ) (t : ZMod n) (x : SpatialVertex n) : Vertex n := Fin.cases t x
def spatialStep (n : ℕ) (x : SpatialVertex n) (i : Fin 3) : SpatialVertex n :=
  x + Pi.single i 1

theorem embed_time_step (n : ℕ) (t : ZMod n) (x : SpatialVertex n) :
    step n (embed n t x) 0 = embed n (t+1) x := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [step, embed]
  · simp [step, embed]

theorem embed_spatial_step (n : ℕ) (t : ZMod n) (x : SpatialVertex n) (i : Fin 3) :
    step n (embed n t x) i.succ = embed n t (spatialStep n x i) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [step, embed, spatialStep]
  · simp [step, embed, spatialStep, Pi.single_apply, Fin.succ_inj]

variable {n : ℕ} {G : Type*} [Group G]

def slice (U : Configuration (Vertex n) G) (t : ZMod n) : SpatialLinks n G :=
  fun e => U ⟨embed n t e.1, step n (embed n t e.1) e.2.succ,
    forward n (embed n t e.1) e.2.succ⟩

def temporal (U : Configuration (Vertex n) G) (t : ZMod n) : SliceGauge n G :=
  fun x => U ⟨embed n t x, step n (embed n t x) 0, forward n (embed n t x) 0⟩

def gaugeSlice (h : SliceGauge n G) (u : SpatialLinks n G) : SpatialLinks n G :=
  fun e => h e.1 * u e * (h (spatialStep n e.1 e.2))⁻¹

def spatialHolonomy (u : SpatialLinks n G) (x : SpatialVertex n) (i j : Fin 3) : G :=
  u (x,i) * u (spatialStep n x i,j) * (u (spatialStep n x j,i))⁻¹ * (u (x,j))⁻¹

def temporalHolonomy (u v : SpatialLinks n G) (h : SliceGauge n G)
    (x : SpatialVertex n) (i : Fin 3) : G :=
  h x * v (x,i) * (h (spatialStep n x i))⁻¹ * (u (x,i))⁻¹

theorem actual_temporal_plaquette (U : Configuration (Vertex n) G) (t : ZMod n)
    (x : SpatialVertex n) (i : Fin 3) :
    holonomy (Quiver.Symmetrify (Vertex n)) G (orientedExtension (Vertex n) G U)
      (plaquette n (embed n t x) 0 i.succ) =
    temporalHolonomy (slice U t) (slice U (t+1)) (temporal U t) x i := by
  simp only [plaquette_holonomy_eq_product, plaquetteProduct,
    embed_spatial_step, embed_time_step]
  rfl

theorem actual_spatial_plaquette (U : Configuration (Vertex n) G) (t : ZMod n)
    (x : SpatialVertex n) (i j : Fin 3) :
    holonomy (Quiver.Symmetrify (Vertex n)) G (orientedExtension (Vertex n) G U)
      (plaquette n (embed n t x) i.succ j.succ) =
    spatialHolonomy (slice U t) x i j := by
  simp only [plaquette_holonomy_eq_product, plaquetteProduct, embed_spatial_step]
  rfl

theorem temporal_character (χ : G → ℂ) (hχ : ClassFunction G χ)
    (u v : SpatialLinks n G) (h : SliceGauge n G) (x : SpatialVertex n) (i : Fin 3) :
    χ (temporalHolonomy u v h x i) = χ ((u (x,i))⁻¹ * gaugeSlice h v (x,i)) := by
  have hc := hχ (u (x,i)) ((u (x,i))⁻¹ * gaugeSlice h v (x,i))
  simpa [temporalHolonomy, gaugeSlice, mul_assoc] using hc

variable [NeZero n]

def potential (χ : G → ℂ) (c : ℝ) (u : SpatialLinks n G) : ℝ :=
  ∑ x : SpatialVertex n, ∑ p : SpatialPlane,
    (c - (χ (spatialHolonomy u x p.1.1 p.1.2)).re)

def kineticAction (χ : G → ℂ) (c : ℝ) (u v : SpatialLinks n G) : ℝ :=
  ∑ e : SpatialVertex n × Fin 3, (c - (χ ((u e)⁻¹ * v e)).re)

def temporalAction (χ : G → ℂ) (c : ℝ) (u v : SpatialLinks n G)
    (h : SliceGauge n G) : ℝ :=
  ∑ x : SpatialVertex n, ∑ i : Fin 3, (c - (χ (temporalHolonomy u v h x i)).re)

theorem temporalAction_eq (χ : G → ℂ) (hχ : ClassFunction G χ) (c : ℝ)
    (u v : SpatialLinks n G) (h : SliceGauge n G) :
    temporalAction χ c u v h = kineticAction χ c u (gaugeSlice h v) := by
  simp only [temporalAction, kineticAction, Fintype.sum_prod_type, temporal_character χ hχ]

def spatialWeight (χ : G → ℂ) (β c : ℝ) (u : SpatialLinks n G) : ℝ :=
  Real.exp (-(β / 2) * potential χ c u)

def kineticWeight (χ : G → ℂ) (β c : ℝ) (u v : SpatialLinks n G) : ℝ :=
  Real.exp (-β * kineticAction χ c u v)

def slabAction (χ : G → ℂ) (β c : ℝ) (u v : SpatialLinks n G)
    (h : SliceGauge n G) : ℝ :=
  β * (potential χ c u / 2 + temporalAction χ c u v h + potential χ c v / 2)

theorem slab_factorization (χ : G → ℂ) (hχ : ClassFunction G χ) (β c : ℝ)
    (u v : SpatialLinks n G) (h : SliceGauge n G) :
    Real.exp (-slabAction χ β c u v h) =
      spatialWeight χ β c u * kineticWeight χ β c u (gaugeSlice h v) *
        spatialWeight χ β c v := by
  unfold spatialWeight kineticWeight slabAction
  rw [temporalAction_eq χ hχ]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

def vertexCoordinates : Vertex n ≃ ZMod n × SpatialVertex n where
  toFun x := (x 0, fun i => x i.succ)
  invFun tx := embed n tx.1 tx.2
  left_inv x := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv tx := rfl

theorem sum_vertices (F : Vertex n → ℝ) :
    ∑ x, F x = ∑ t : ZMod n, ∑ x : SpatialVertex n, F (embed n t x) := by
  simpa only [Fintype.sum_prod_type] using (vertexCoordinates (n := n)).symm.sum_comp F |>.symm

private theorem sum_planes (F : Fin 4 → Fin 4 → ℝ) :
    ∑ p : Plane, F p.1.1 p.1.2 =
      (∑ i : Fin 3, F 0 i.succ) + ∑ p : SpatialPlane, F p.1.1.succ p.1.2.succ := by
  have h4 : (Finset.univ : Finset Plane) =
      {⟨(0,1),by decide⟩, ⟨(0,2),by decide⟩, ⟨(0,3),by decide⟩,
       ⟨(1,2),by decide⟩, ⟨(1,3),by decide⟩, ⟨(2,3),by decide⟩} := by decide
  have h3 : (Finset.univ : Finset SpatialPlane) =
      {⟨(0,1),by decide⟩, ⟨(0,2),by decide⟩, ⟨(1,2),by decide⟩} := by decide
  rw [h4, h3]
  repeat rw [Finset.sum_insert (by decide)]
  simp only [Finset.sum_singleton, Fin.sum_univ_three]
  norm_num
  simp only [show (2 : Fin 3).succ = 3 from rfl]
  ring

theorem action_by_slices (χ : G → ℂ) (β c : ℝ) (U : Configuration (Vertex n) G) :
    orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c U =
      β * ∑ t : ZMod n, (potential χ c (slice U t) +
        temporalAction χ c (slice U t) (slice U (t+1)) (temporal U t)) := by
  change β * ∑ p : PlaquetteIndex n,
    (c - (χ (holonomy (Quiver.Symmetrify (Vertex n)) G (orientedExtension (Vertex n) G U)
      (plaquette n p.1 p.2.1.1 p.2.1.2))).re) = _
  rw [Fintype.sum_prod_type, sum_vertices]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  trans ∑ x : SpatialVertex n,
    ((∑ i : Fin 3, (c - (χ (holonomy (Quiver.Symmetrify (Vertex n)) G
      (orientedExtension (Vertex n) G U) (plaquette n (embed n t x) 0 i.succ))).re)) +
     ∑ p : SpatialPlane, (c - (χ (holonomy (Quiver.Symmetrify (Vertex n)) G
      (orientedExtension (Vertex n) G U)
        (plaquette n (embed n t x) p.1.1.succ p.1.2.succ))).re))
  · exact Finset.sum_congr rfl (fun x _ => sum_planes (fun i j => c - (χ
      (holonomy (Quiver.Symmetrify (Vertex n)) G (orientedExtension (Vertex n) G U)
        (plaquette n (embed n t x) i j))).re))
  · simp_rw [actual_temporal_plaquette, actual_spatial_plaquette]
    rw [Finset.sum_add_distrib]
    exact add_comm _ _

/-- Summing half of each adjacent spatial action counts every spatial
plaquette exactly once, including the periodic seam. -/
theorem action_eq_sum_slabs (χ : G → ℂ) (β c : ℝ) (U : Configuration (Vertex n) G) :
    orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c U =
      ∑ t : ZMod n, slabAction χ β c (slice U t) (slice U (t+1)) (temporal U t) := by
  rw [action_by_slices]
  have hs : (∑ t : ZMod n, potential χ c (slice U (t+1))) =
      ∑ t : ZMod n, potential χ c (slice U t) :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) (fun t => potential χ c (slice U t))
  simp only [slabAction, Finset.sum_add_distrib,
    mul_add, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hs]
  ring

theorem boltzmann_eq_product_slabs (χ : G → ℂ) (hχ : ClassFunction G χ) (β c : ℝ)
    (U : Configuration (Vertex n) G) :
    Real.exp (-orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c U) =
      ∏ t : ZMod n, spatialWeight χ β c (slice U t) *
        kineticWeight χ β c (slice U t) (gaugeSlice (temporal U t) (slice U (t+1))) *
          spatialWeight χ β c (slice U (t+1)) := by
  rw [action_eq_sum_slabs, ← Finset.sum_neg_distrib, Real.exp_sum]
  exact Finset.prod_congr rfl (fun t _ => slab_factorization χ hχ β c _ _ _)

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def temporalHaar : Measure (SliceGauge n G) :=
  Measure.pi (fun _ : SpatialVertex n => compactHaar G)

instance temporalHaar_probability : IsProbabilityMeasure (temporalHaar (n := n) (G := G)) := by
  unfold temporalHaar
  infer_instance

/-- Temporal links are integrated, rather than set to the identity. -/
def kernel (χ : G → ℂ) (β c : ℝ) (u v : SpatialLinks n G) : ℝ :=
  ∫ h, Real.exp (-slabAction χ β c u v h) ∂temporalHaar

omit [SecondCountableTopology G] in
theorem kernel_eq_gauge_average (χ : G → ℂ) (hχ : ClassFunction G χ) (β c : ℝ)
    (u v : SpatialLinks n G) :
    kernel χ β c u v = spatialWeight χ β c u *
      (∫ h, kineticWeight χ β c u (gaugeSlice h v) ∂temporalHaar) *
        spatialWeight χ β c v := by
  simp only [kernel, slab_factorization χ hχ, integral_mul_const, integral_const_mul]

theorem kernel_positive (χ : G → ℂ) (hc : Continuous χ) (β c : ℝ)
    (u v : SpatialLinks n G) : 0 < kernel χ β c u v := by
  apply integral_exp_pos
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  unfold slabAction temporalAction temporalHolonomy
  fun_prop

theorem kernel_continuous (χ : G → ℂ) (hc : Continuous χ) (β c : ℝ) :
    Continuous (fun uv : SpatialLinks n G × SpatialLinks n G => kernel χ β c uv.1 uv.2) := by
  let f : (SpatialLinks n G × SpatialLinks n G) → SliceGauge n G → ℝ :=
    fun uv h => Real.exp (-slabAction χ β c uv.1 uv.2 h)
  have hf : Continuous f.uncurry := by
    unfold f Function.uncurry slabAction temporalAction temporalHolonomy potential spatialHolonomy
    fun_prop
  simpa only [Measure.restrict_univ, kernel] using
    (continuous_parametric_integral_of_continuous (μ := temporalHaar) hf isCompact_univ)

end
end UnifiedTheory.Clay.YangMills.WilsonTimeSlab
