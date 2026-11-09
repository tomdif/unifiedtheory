/- Bridge connecting the discrete Ambrose-Singer holonomy theorem
(`holonomySubgroup conn v₀ = Subgroup.closure (basedCurvatureSet conn v₀)`,
lollipop loop holonomy conjugation, discrete Stokes theorem, path concatenation
and reversal holonomy homomorphisms, and gauge transformation telescoping and
loop holonomy conjugation in `DiscreteAmbroseSinger`) and the 4D Gauss-Bonnet
tensor vanishing (`genKronecker_vanishes`, `gaussBonnet_vanishes_4d`, and the
all-orders Lovelock rank exclusion `2 * k + 1 > 4` for `k ≥ 2` in
`GaussBonnet4D`) to multi-packet sector superpositions on `Fin 4` (spacetime
dimension) and `Fin 5` (rank-5 generalized Kronecker indices), Cauchy-Schwarz
weight ratios, and degree-`M` energy and response lower bounds. -/
import UnifiedTheory.LayerA.DiscreteAmbroseSinger
import UnifiedTheory.LayerA.GaussBonnet4D
import UnifiedTheory.Audit.KFCausalDimensionTripleCoincidenceNoExtraDimensionsMultiPacketBridge
import UnifiedTheory.Audit.KFCausalArbitrarySourceDominantConstantModeResponseLowerBound

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalDiscreteAmbroseSingerHolonomyMultiPacketBridge
noncomputable section
open UnifiedTheory.LayerA.DiscreteBundles
  (DirectedGraph GraphPath GraphLoop Plaquette
   DiscreteConnection GaugeTransformation gaugeTransform holonomy)
open UnifiedTheory.LayerA.DiscreteAmbroseSinger
  (HasReversal ReversibleConnection
   hol hol_eq_holonomy hol_nil hol_singleton hol_append
   revEdges revEdges_length hol_reverse_eq_inv lollipop_hol
   holonomySet holonomySubgroup basedCurvatureSet
   lollipopLoop lollipop_base lollipop_holonomy
   basedCurvature_is_holonomy discrete_ambrose_singer_converse
   discrete_stokes discrete_ambrose_singer_forward
   discrete_ambrose_singer_eq holonomy_minimal
   pathConcat holonomy_concat pathReverse holonomy_reverse
   hol_gaugeTransform_telescope gauge_conjugates_loop_holonomy)
open UnifiedTheory.LayerA.GaussBonnet4D
  (genKronecker fin_pigeonhole genKronecker_vanishes
   gaussBonnetTensor gaussBonnet_vanishes_4d
   kretschnerScalar ricciNormSq scalarCurvatureSq
   gaussBonnetScalarStd gaussBonnet_standard_defined
   higher_lovelock_rank_exceeds_4d lovelock_4d_all_orders)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalReciprocalNeutralHamiltonian (fullEnergy fullResponse)
open KFCausalReciprocalNeutralArbitrarySourceClockKineticResponse (scaleAmplitude)
open KFCausalReciprocalNeutralArbitraryDegreePolynomialDecomposition (unitMonomialPolyProfile)
open KFCausalCommonComplexDegreeMPolynomialResponseLowerBound
  (degreeMPolyProfile cauchySchwarzWeightRatio full_bound_degreeM_neutral)
open KFCausalSMFrameworkAtomicCrossSectorMultiPacketSynthesis
  (uniformSectorWeights uniformSectorWeights_cauchySchwarzWeightRatio
   uniformSectorWeights_degreeM_fullEnergy_lower)
open KFCausalArbitrarySourceDominantConstantModeResponseLowerBound
  (state_degreeM_dominant_constant_norm_ge
   constant_mode_fullResponse_zero_couplings_lower_arbitrary_source)

/-! ### 1. Discrete Holonomy Algebra, Lollipop Loops, and Discrete Ambrose-Singer Theorem -/

theorem hol_eq_holonomy_bridge {Γ : DirectedGraph} {G : Type*} [Group G]
    (conn : DiscreteConnection Γ G) (p : GraphPath Γ) :
    hol conn p.edges = holonomy conn p :=
  hol_eq_holonomy conn p

theorem hol_nil_bridge {Γ : DirectedGraph} {G : Type*} [Group G]
    (conn : DiscreteConnection Γ G) :
    hol conn ([] : List Γ.Edge) = 1 :=
  hol_nil conn

theorem hol_singleton_bridge {Γ : DirectedGraph} {G : Type*} [Group G]
    (conn : DiscreteConnection Γ G) (e : Γ.Edge) :
    hol conn [e] = conn.transport e :=
  hol_singleton conn e

theorem hol_append_bridge {Γ : DirectedGraph} {G : Type*} [Group G]
    (conn : DiscreteConnection Γ G) (l₁ l₂ : List Γ.Edge) :
    hol conn (l₁ ++ l₂) = hol conn l₁ * hol conn l₂ :=
  hol_append conn l₁ l₂

theorem revEdges_length_bridge {Γ : DirectedGraph} [HasReversal Γ]
    (l : List Γ.Edge) :
    (revEdges l).length = l.length :=
  revEdges_length l

theorem hol_reverse_eq_inv_bridge {Γ : DirectedGraph} {G : Type*} [Group G]
    [HasReversal Γ] (conn : DiscreteConnection Γ G)
    [ReversibleConnection Γ G conn] (l : List Γ.Edge) :
    hol conn (revEdges l) = (hol conn l)⁻¹ :=
  hol_reverse_eq_inv conn l

theorem lollipop_hol_bridge {Γ : DirectedGraph} {G : Type*} [Group G]
    [HasReversal Γ] (conn : DiscreteConnection Γ G)
    [ReversibleConnection Γ G conn]
    (γ_edges loop_edges : List Γ.Edge) :
    hol conn (γ_edges ++ loop_edges ++ revEdges γ_edges) =
      hol conn γ_edges * hol conn loop_edges * (hol conn γ_edges)⁻¹ :=
  lollipop_hol conn γ_edges loop_edges

theorem lollipop_base_bridge {Γ : DirectedGraph} [HasReversal Γ]
    (γ : GraphPath Γ) (L : GraphLoop Γ)
    (hγne : 0 < γ.edges.length)
    (hjoin : Γ.tgt (γ.edges[γ.edges.length - 1]'(by omega)) =
             Γ.src (L.edges[0]'L.nonempty)) :
    Γ.src ((lollipopLoop γ L hγne hjoin).edges[0]'
      (lollipopLoop γ L hγne hjoin).nonempty) =
    Γ.src (γ.edges[0]'hγne) :=
  lollipop_base γ L hγne hjoin

theorem lollipop_holonomy_bridge {Γ : DirectedGraph} {G : Type*} [Group G]
    [HasReversal Γ] (conn : DiscreteConnection Γ G)
    [ReversibleConnection Γ G conn]
    (γ : GraphPath Γ) (L : GraphLoop Γ)
    (hγne : 0 < γ.edges.length)
    (hjoin : Γ.tgt (γ.edges[γ.edges.length - 1]'(by omega)) =
             Γ.src (L.edges[0]'L.nonempty)) :
    holonomy conn (lollipopLoop γ L hγne hjoin).toGraphPath =
      hol conn γ.edges * hol conn L.edges * (hol conn γ.edges)⁻¹ :=
  lollipop_holonomy conn γ L hγne hjoin

theorem basedCurvature_is_holonomy_bridge
    {Γ : DirectedGraph} {G : Type*} [Group G]
    [HasReversal Γ] (conn : DiscreteConnection Γ G)
    [ReversibleConnection Γ G conn]
    (v₀ : Γ.Vertex) (γ : GraphPath Γ) (plaq : Plaquette Γ)
    (hγne : 0 < γ.edges.length)
    (hstart : Γ.src (γ.edges[0]'hγne) = v₀)
    (hjoin : Γ.tgt (γ.edges[γ.edges.length - 1]'(by omega)) =
             Γ.src (plaq.edges[0]'plaq.nonempty)) :
    hol conn γ.edges * hol conn plaq.edges * (hol conn γ.edges)⁻¹ ∈
      holonomySet conn v₀ :=
  basedCurvature_is_holonomy conn v₀ γ plaq hγne hstart hjoin

theorem discrete_ambrose_singer_converse_bridge
    {Γ : DirectedGraph} {G : Type*} [Group G]
    [HasReversal Γ] (conn : DiscreteConnection Γ G)
    [ReversibleConnection Γ G conn] (v₀ : Γ.Vertex) :
    Subgroup.closure (basedCurvatureSet conn v₀) ≤ holonomySubgroup conn v₀ :=
  discrete_ambrose_singer_converse conn v₀

theorem discrete_stokes_bridge
    {Γ : DirectedGraph} {G : Type*} [Group G]
    [HasReversal Γ] (conn : DiscreteConnection Γ G)
    [ReversibleConnection Γ G conn] (v₀ : Γ.Vertex) :
    holonomySet conn v₀ ⊆ Subgroup.closure (basedCurvatureSet conn v₀) :=
  discrete_stokes conn v₀

theorem discrete_ambrose_singer_forward_bridge
    {Γ : DirectedGraph} {G : Type*} [Group G]
    [HasReversal Γ] (conn : DiscreteConnection Γ G)
    [ReversibleConnection Γ G conn] (v₀ : Γ.Vertex) :
    holonomySubgroup conn v₀ ≤ Subgroup.closure (basedCurvatureSet conn v₀) :=
  discrete_ambrose_singer_forward conn v₀

theorem discrete_ambrose_singer_eq_bridge
    {Γ : DirectedGraph} {G : Type*} [Group G]
    [HasReversal Γ] (conn : DiscreteConnection Γ G)
    [ReversibleConnection Γ G conn] (v₀ : Γ.Vertex) :
    holonomySubgroup conn v₀ = Subgroup.closure (basedCurvatureSet conn v₀) :=
  discrete_ambrose_singer_eq conn v₀

theorem holonomy_minimal_bridge
    {Γ : DirectedGraph} {G : Type*} [Group G]
    (conn : DiscreteConnection Γ G) (v₀ : Γ.Vertex)
    (K : Subgroup G) (hK : holonomySet conn v₀ ⊆ K) :
    holonomySubgroup conn v₀ ≤ K :=
  holonomy_minimal conn v₀ K hK

theorem holonomy_concat_bridge {Γ : DirectedGraph} {G : Type*} [Group G]
    (conn : DiscreteConnection Γ G) (p₁ p₂ : GraphPath Γ)
    (h₁ : 0 < p₁.edges.length) (h₂ : 0 < p₂.edges.length)
    (hjoin : Γ.tgt (p₁.edges[p₁.edges.length - 1]'(by omega)) =
             Γ.src (p₂.edges[0]'h₂)) :
    holonomy conn (pathConcat p₁ p₂ h₁ h₂ hjoin) =
      holonomy conn p₁ * holonomy conn p₂ :=
  holonomy_concat conn p₁ p₂ h₁ h₂ hjoin

theorem holonomy_reverse_bridge {Γ : DirectedGraph} {G : Type*} [Group G]
    [HasReversal Γ] (conn : DiscreteConnection Γ G)
    [ReversibleConnection Γ G conn] (p : GraphPath Γ) :
    holonomy conn (pathReverse p) = (holonomy conn p)⁻¹ :=
  holonomy_reverse conn p

theorem hol_gaugeTransform_telescope_bridge
    {Γ : DirectedGraph} {G : Type*} [Group G]
    (conn : DiscreteConnection Γ G) (g : GaugeTransformation Γ G)
    (l : List Γ.Edge) (hne : 0 < l.length)
    (hcomp : ∀ i : Fin (l.length - 1),
      Γ.tgt (l[i.val]'(by omega)) = Γ.src (l[i.val + 1]'(by omega))) :
    hol (gaugeTransform conn g) l =
      (g (Γ.src (l[0]'hne)))⁻¹ *
      hol conn l *
      g (Γ.tgt (l[l.length - 1]'(by omega))) :=
  hol_gaugeTransform_telescope conn g l hne hcomp

theorem gauge_conjugates_loop_holonomy_bridge
    {Γ : DirectedGraph} {G : Type*} [Group G]
    (conn : DiscreteConnection Γ G) (g : GaugeTransformation Γ G)
    (loop : GraphLoop Γ) :
    holonomy (gaugeTransform conn g) loop.toGraphPath =
      (g (Γ.src (loop.edges[0]'loop.nonempty)))⁻¹ *
      holonomy conn loop.toGraphPath *
      g (Γ.src (loop.edges[0]'loop.nonempty)) :=
  gauge_conjugates_loop_holonomy conn g loop

/-! ### 2. 4D Gauss-Bonnet Tensor Vanishing and All-Orders Lovelock Rank Exclusion -/

theorem fin_pigeonhole_4d_bridge (f : Fin 5 → Fin 4) :
    ∃ i j : Fin 5, i ≠ j ∧ f i = f j :=
  fin_pigeonhole (by decide : 4 < 5) f

theorem genKronecker_vanishes_4d_bridge (a b : Fin 5 → Fin 4) :
    genKronecker a b = 0 :=
  genKronecker_vanishes (by decide : 4 < 5) a b

theorem gaussBonnetTensor_vanishes_4d_bridge
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (a b : Fin 4) :
    gaussBonnetTensor R a b = 0 :=
  gaussBonnet_vanishes_4d R a b

theorem gaussBonnet_standard_defined_bridge
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    gaussBonnetScalarStd R =
      kretschnerScalar R - 4 * ricciNormSq R + scalarCurvatureSq R :=
  gaussBonnet_standard_defined R

theorem higher_lovelock_rank_exceeds_4d_bridge (k : ℕ) (hk : 2 ≤ k) :
    4 < 2 * k + 1 :=
  higher_lovelock_rank_exceeds_4d k hk

theorem lovelock_4d_all_orders_bridge :
    (∀ R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ,
      ∀ a b : Fin 4, gaussBonnetTensor R a b = 0) ∧
    (∀ p : ℕ, 2 ≤ p → 4 < 2 * p + 1) :=
  lovelock_4d_all_orders

/-! ### 3. Multi-Packet Bridges on `Fin 4` (Spacetime) and `Fin 5` (Generalized Kronecker Rank) -/

theorem gaussBonnet_spacetime_dim_weight_ratio :
    cauchySchwarzWeightRatio (uniformSectorWeights 4) = 4 := by
  simpa using uniformSectorWeights_cauchySchwarzWeightRatio 4 (by decide)

theorem gaussBonnet_kronecker_rank_weight_ratio :
    cauchySchwarzWeightRatio (uniformSectorWeights 5) = 5 := by
  simpa using uniformSectorWeights_cauchySchwarzWeightRatio 5 (by decide)

theorem gaussBonnet_rank_exceeds_spacetime_weight_ratio :
    cauchySchwarzWeightRatio (uniformSectorWeights 4) <
      cauchySchwarzWeightRatio (uniformSectorWeights 5) := by
  rw [gaussBonnet_spacetime_dim_weight_ratio, gaussBonnet_kronecker_rank_weight_ratio]
  norm_num

theorem gaussBonnet_rank_sub_spacetime_weight_ratio :
    cauchySchwarzWeightRatio (uniformSectorWeights 5) -
      cauchySchwarzWeightRatio (uniformSectorWeights 4) = 1 := by
  rw [gaussBonnet_spacetime_dim_weight_ratio, gaussBonnet_kronecker_rank_weight_ratio]
  norm_num

theorem gaussBonnet_lovelock_k2_rank_eq_five :
    2 * 2 + 1 = 5 ∧
      cauchySchwarzWeightRatio (uniformSectorWeights (2 * 2 + 1)) = 5 := by
  refine ⟨by norm_num, ?_⟩
  simpa using gaussBonnet_kronecker_rank_weight_ratio

variable (M : ℕ) (ε h a₀ w₀ p₀ : ℝ) (b₀ z₀ : ℂ)
  (d4 : Fin M → Fin 4 → ℂ) (d5 : Fin M → Fin 5 → ℂ)
  (hε : 0 < ε) (ha₀ : 0 < a₀) (hh : h ≠ 0) (hw₀ : 1 ≤ w₀)
  (hb : |h| ≤ 2 * Real.pi * ε / 3) (mass2 quartic vacuum t : ℝ)

theorem gaussBonnet_fin4_degreeM_fullEnergy_lower
    (hneutral : ∀ r : Fin M, ∑ i : Fin 4, uniformSectorWeights 4 i * d4 r i = 0) :
    4 * ‖z₀‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
      fullEnergy 4 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        (uniformSectorWeights 4) (fun _ => b₀)
        (degreeMPolyProfile M (fun _ => z₀) d4)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
  simpa using uniformSectorWeights_degreeM_fullEnergy_lower
    M ε h a₀ w₀ p₀ b₀ z₀ hε ha₀ hh hw₀ hb 4 (by decide) d4 hneutral mass2 quartic vacuum t

theorem gaussBonnet_fin5_degreeM_fullEnergy_lower
    (hneutral : ∀ r : Fin M, ∑ i : Fin 5, uniformSectorWeights 5 i * d5 r i = 0) :
    5 * ‖z₀‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
      fullEnergy 5 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        (uniformSectorWeights 5) (fun _ => b₀)
        (degreeMPolyProfile M (fun _ => z₀) d5)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t := by
  simpa using uniformSectorWeights_degreeM_fullEnergy_lower
    M ε h a₀ w₀ p₀ b₀ z₀ hε ha₀ hh hw₀ hb 5 (by decide) d5 hneutral mass2 quartic vacuum t

theorem gaussBonnet_fin4_state_dominant_constant_norm_ge
    (a4 w4 p4 : Fin 4 → ℝ) (C4 b4 c₀4 : Fin 4 → ℂ)
    (ha4 : ∀ i, 0 < a4 i) (hw4 : ∀ i, 1 ≤ w4 i) (θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖state 4 ε h a4 w4 p4 (scaleAmplitude C4 (d4 r)) b4
          (unitMonomialPolyProfile 4 ((r : ℕ) + 1)) hε ha4 hh hw4‖ ≤
      θ * ‖state 4 ε h a4 w4 p4 (scaleAmplitude C4 c₀4) b4 (fun _ => 1) hε ha4 hh hw4‖) :
    (1 - θ) * ‖state 4 ε h a4 w4 p4 (scaleAmplitude C4 c₀4) b4 (fun _ => 1) hε ha4 hh hw4‖ ≤
      ‖state 4 ε h a4 w4 p4 C4 b4 (degreeMPolyProfile M c₀4 d4) hε ha4 hh hw4‖ :=
  state_degreeM_dominant_constant_norm_ge 4 M ε h a4 w4 p4 C4 b4 c₀4 d4 hε ha4 hh hw4 θ hdom

theorem gaussBonnet_fin5_state_dominant_constant_norm_ge
    (a5 w5 p5 : Fin 5 → ℝ) (C5 b5 c₀5 : Fin 5 → ℂ)
    (ha5 : ∀ i, 0 < a5 i) (hw5 : ∀ i, 1 ≤ w5 i) (θ : ℝ)
    (hdom : ∑ r : Fin M,
        ‖state 5 ε h a5 w5 p5 (scaleAmplitude C5 (d5 r)) b5
          (unitMonomialPolyProfile 5 ((r : ℕ) + 1)) hε ha5 hh hw5‖ ≤
      θ * ‖state 5 ε h a5 w5 p5 (scaleAmplitude C5 c₀5) b5 (fun _ => 1) hε ha5 hh hw5‖) :
    (1 - θ) * ‖state 5 ε h a5 w5 p5 (scaleAmplitude C5 c₀5) b5 (fun _ => 1) hε ha5 hh hw5‖ ≤
      ‖state 5 ε h a5 w5 p5 C5 b5 (degreeMPolyProfile M c₀5 d5) hε ha5 hh hw5‖ :=
  state_degreeM_dominant_constant_norm_ge 5 M ε h a5 w5 p5 C5 b5 c₀5 d5 hε ha5 hh hw5 θ hdom

theorem gaussBonnet_fin4_constant_mode_zero_couplings_response_lower
    (a4 w4 p4 : Fin 4 → ℝ) (C4 b4 c₀4 : Fin 4 → ℂ)
    (ha4 : ∀ i, 0 < a4 i) (hw4 : ∀ i, 1 ≤ w4 i) :
    -(1 / (4 * ε)) *
        fullEnergy 4 ε h a4 w4 p4 C4 b4 (fun i => Polynomial.C (c₀4 i)) hε ha4 hh hw4 hb 0 0 0 t ≤
      fullResponse 4 ε h a4 w4 p4 C4 b4 (fun i => Polynomial.C (c₀4 i)) hε ha4 hh hw4 hb 0 0 0 t :=
  constant_mode_fullResponse_zero_couplings_lower_arbitrary_source
    4 ε h a4 w4 p4 C4 b4 c₀4 hε ha4 hh hw4 hb t

theorem gaussBonnet_fin5_constant_mode_zero_couplings_response_lower
    (a5 w5 p5 : Fin 5 → ℝ) (C5 b5 c₀5 : Fin 5 → ℂ)
    (ha5 : ∀ i, 0 < a5 i) (hw5 : ∀ i, 1 ≤ w5 i) :
    -(1 / (4 * ε)) *
        fullEnergy 5 ε h a5 w5 p5 C5 b5 (fun i => Polynomial.C (c₀5 i)) hε ha5 hh hw5 hb 0 0 0 t ≤
      fullResponse 5 ε h a5 w5 p5 C5 b5 (fun i => Polynomial.C (c₀5 i)) hε ha5 hh hw5 hb 0 0 0 t :=
  constant_mode_fullResponse_zero_couplings_lower_arbitrary_source
    5 ε h a5 w5 p5 C5 b5 c₀5 hε ha5 hh hw5 hb t

theorem ambrose_singer_and_gauss_bonnet_joint_bridge
    {Γ : DirectedGraph} {G : Type*} [Group G]
    [HasReversal Γ] (conn : DiscreteConnection Γ G)
    [ReversibleConnection Γ G conn] (v₀ : Γ.Vertex) :
    (holonomySubgroup conn v₀ = Subgroup.closure (basedCurvatureSet conn v₀)) ∧
    (∀ R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ,
      ∀ a b : Fin 4, gaussBonnetTensor R a b = 0) :=
  ⟨discrete_ambrose_singer_eq_bridge conn v₀, gaussBonnetTensor_vanishes_4d_bridge⟩

theorem discrete_ambrose_singer_holonomy_multi_packet_master_synthesis
    {Γ : DirectedGraph} {G : Type*} [Group G]
    [HasReversal Γ] (conn : DiscreteConnection Γ G)
    [ReversibleConnection Γ G conn] (v₀ : Γ.Vertex)
    (g : GaugeTransformation Γ G) (loop : GraphLoop Γ)
    (hneutral4 : ∀ r : Fin M, ∑ i : Fin 4, uniformSectorWeights 4 i * d4 r i = 0)
    (hneutral5 : ∀ r : Fin M, ∑ i : Fin 5, uniformSectorWeights 5 i * d5 r i = 0) :
    (holonomySubgroup conn v₀ = Subgroup.closure (basedCurvatureSet conn v₀)) ∧
    (holonomy (gaugeTransform conn g) loop.toGraphPath =
      (g (Γ.src (loop.edges[0]'loop.nonempty)))⁻¹ *
      holonomy conn loop.toGraphPath *
      g (Γ.src (loop.edges[0]'loop.nonempty))) ∧
    ((∀ R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ,
        ∀ a b : Fin 4, gaussBonnetTensor R a b = 0) ∧
      (∀ p : ℕ, 2 ≤ p → 4 < 2 * p + 1)) ∧
    (cauchySchwarzWeightRatio (uniformSectorWeights 4) <
      cauchySchwarzWeightRatio (uniformSectorWeights 5)) ∧
    (4 * ‖z₀‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
      fullEnergy 4 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        (uniformSectorWeights 4) (fun _ => b₀)
        (degreeMPolyProfile M (fun _ => z₀) d4)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t) ∧
    (5 * ‖z₀‖ ^ 2 *
        fullEnergy 1 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀) (fun _ => 1) (fun _ => b₀)
          (fun _ => 1) hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t ≤
      fullEnergy 5 ε h (fun _ => a₀) (fun _ => w₀) (fun _ => p₀)
        (uniformSectorWeights 5) (fun _ => b₀)
        (degreeMPolyProfile M (fun _ => z₀) d5)
        hε (fun _ => ha₀) hh (fun _ => hw₀) hb mass2 quartic vacuum t) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ (m2 q4 v0 : ℝ),
      0 ≤ m2 → 0 ≤ q4 → 0 ≤ v0 →
      ∀ (n' M' : ℕ) (ε' h' a₀' w₀' p₀' : ℝ) (b₀' : ℂ) (C' c₀' : Fin n' → ℂ)
      (d' : Fin M' → Fin n' → ℂ)
      (hε' : 0 < ε') (ha₀' : 0 < a₀') (hh' : h' ≠ 0) (hw₀' : 1 ≤ w₀')
      (hb' : |h'| ≤ 2 * Real.pi * ε' / 3)
      (_hneutral : ∀ r : Fin M', ∑ i : Fin n', C' i * d' r i = 0) (t' : ℝ),
      -(K / ε') * fullEnergy n' ε' h' (fun _ => a₀') (fun _ => w₀') (fun _ => p₀') C' (fun _ => b₀')
        (degreeMPolyProfile M' c₀' d') hε' (fun _ => ha₀') hh' (fun _ => hw₀')
        hb' m2 q4 v0 t' ≤
      fullResponse n' ε' h' (fun _ => a₀') (fun _ => w₀') (fun _ => p₀') C' (fun _ => b₀')
        (degreeMPolyProfile M' c₀' d') hε' (fun _ => ha₀') hh' (fun _ => hw₀')
        hb' m2 q4 v0 t') :=
  ⟨discrete_ambrose_singer_eq_bridge conn v₀,
   gauge_conjugates_loop_holonomy_bridge conn g loop,
   lovelock_4d_all_orders_bridge,
   gaussBonnet_rank_exceeds_spacetime_weight_ratio,
   gaussBonnet_fin4_degreeM_fullEnergy_lower
     M ε h a₀ w₀ p₀ b₀ z₀ d4 hε ha₀ hh hw₀ hb mass2 quartic vacuum t hneutral4,
   gaussBonnet_fin5_degreeM_fullEnergy_lower
     M ε h a₀ w₀ p₀ b₀ z₀ d5 hε ha₀ hh hw₀ hb mass2 quartic vacuum t hneutral5,
   full_bound_degreeM_neutral⟩

#print axioms hol_eq_holonomy_bridge
#print axioms hol_nil_bridge
#print axioms hol_singleton_bridge
#print axioms hol_append_bridge
#print axioms revEdges_length_bridge
#print axioms hol_reverse_eq_inv_bridge
#print axioms lollipop_hol_bridge
#print axioms lollipop_base_bridge
#print axioms lollipop_holonomy_bridge
#print axioms basedCurvature_is_holonomy_bridge
#print axioms discrete_ambrose_singer_converse_bridge
#print axioms discrete_stokes_bridge
#print axioms discrete_ambrose_singer_forward_bridge
#print axioms discrete_ambrose_singer_eq_bridge
#print axioms holonomy_minimal_bridge
#print axioms holonomy_concat_bridge
#print axioms holonomy_reverse_bridge
#print axioms hol_gaugeTransform_telescope_bridge
#print axioms gauge_conjugates_loop_holonomy_bridge
#print axioms fin_pigeonhole_4d_bridge
#print axioms genKronecker_vanishes_4d_bridge
#print axioms gaussBonnetTensor_vanishes_4d_bridge
#print axioms gaussBonnet_standard_defined_bridge
#print axioms higher_lovelock_rank_exceeds_4d_bridge
#print axioms lovelock_4d_all_orders_bridge
#print axioms gaussBonnet_spacetime_dim_weight_ratio
#print axioms gaussBonnet_kronecker_rank_weight_ratio
#print axioms gaussBonnet_rank_exceeds_spacetime_weight_ratio
#print axioms gaussBonnet_rank_sub_spacetime_weight_ratio
#print axioms gaussBonnet_lovelock_k2_rank_eq_five
#print axioms gaussBonnet_fin4_degreeM_fullEnergy_lower
#print axioms gaussBonnet_fin5_degreeM_fullEnergy_lower
#print axioms gaussBonnet_fin4_state_dominant_constant_norm_ge
#print axioms gaussBonnet_fin5_state_dominant_constant_norm_ge
#print axioms gaussBonnet_fin4_constant_mode_zero_couplings_response_lower
#print axioms gaussBonnet_fin5_constant_mode_zero_couplings_response_lower
#print axioms ambrose_singer_and_gauss_bonnet_joint_bridge
#print axioms discrete_ambrose_singer_holonomy_multi_packet_master_synthesis
end
end UnifiedTheory.Audit.KFCausalDiscreteAmbroseSingerHolonomyMultiPacketBridge
