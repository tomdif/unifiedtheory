/- The actual pure-clock momentum of each finite clustered state has
a derived physical representative. Its L2 limit closes the momentum
graph on the already constructed input limit. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredClockDifferential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPureMomentumLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift)
open KFCausalCorrelatedClusteredInputProfiles (finiteState finiteState_coe inputAmplitude_memLp)
open KFCausalCorrelatedClusteredInputGraphLimit (limitingState state_tendsto)
open KFCausalCorrelatedClusteredMomentumAmplitudes (amplitudes amplitude_continuous amplitude_memLp input_derivative)
open KFCausalCorrelatedClusteredClockVectors (profile profile_memLp vector vector_coe limitingVector vector_tendsto)
open KFCausalCorrelatedClusteredClockDifferential (profile_differentiable input_differential)
open KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open KFCausalClockFloorPureClockDerivative (differential)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalStandingChargeOperator (zeroSector zeroSector_closed standingCharge standingCharge_zero_iff)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => neutralWidth_positive h hh
local notation "hw" => neutralWidth_bound h
local notation "c" => amplitudes ε a p
local notation "hc" => fun i => amplitude_continuous ε (a i) (p i) hε
local notation "hc2" => fun i => amplitude_memLp ε (a i) (p i) hε (ha i)
local notation "D" => vector f c α β hα hβ hw hc2
local notation "U" => finiteState f ε h a p hε hh ha

def finiteMomentum (δ : ℝ) : Hilbert := if hδ : 0 < δ then
  KFCausalReciprocalNeutralSuperposition.momentum (count f) ε h (lift f a) (widths f δ) (lift f p)
    (coefficients f δ) (sources f) (polynomials f) hε (fun j => ha (index f j).1) hh
    (widths_admissible f δ hδ.le) else 0

theorem finite_graph (δ : ℝ) (hδ : 0 < δ) :
    (U δ,finiteMomentum f ε h a p hε hh ha δ) ∈ (pureMomentum ε hε h).graph := by
  rw [finiteState,finiteMomentum,dif_pos hδ,dif_pos hδ]
  exact KFCausalReciprocalNeutralSuperposition.momentum_graph (count f) ε h (lift f a) (widths f δ)
    (lift f p) (coefficients f δ) (sources f) (polynomials f) hε (fun j => ha (index f j).1) hh
    (widths_admissible f δ hδ.le)

theorem differential_graph (δ : ℝ) (hδ : 0 < δ) :
    (U δ,(-Complex.I*(h:ℂ)) • D δ) ∈ (pureMomentum ε hε h).graph := by
  let F := profile f (KFCausalCorrelatedClusteredInputProfiles.amplitudes ε a p) α β δ
  have hF : MemLp F 2 volume := profile_memLp f _ α β hα hβ hw
    (fun i => inputAmplitude_memLp ε (a i) (p i) hε (ha i)) δ hδ
  have he : differential ε F = profile f c α β δ := funext (input_differential f α β δ ε a p hε)
  have hd : MemLp (differential ε F) 2 volume := by
    rw [he]
    exact profile_memLp f c α β hα hβ hw hc2 δ hδ
  have hs : Differentiable ℝ F := profile_differentiable f _ α β δ
    (fun i s => (input_derivative ε (a i) (p i) s hε).differentiableAt)
  have hu : hF.toLp F = U δ := Lp.ext
    (hF.coeFn_toLp.trans (finiteState_coe f ε h a p hε hh ha δ hδ).symm)
  have hv : hd.toLp (differential ε F) = D δ := by
    apply Lp.ext
    filter_upwards [hd.coeFn_toLp,vector_coe f c α β hα hβ hw hc2 δ hδ] with x hd' hv'
    rw [hd',hv',he]
  have hg := KFCausalClockFloorPureClockDifferential.differential_graph ε hε h hh F hF hd hs
  rwa [hu,hv] at hg

theorem finiteMomentum_eq (δ : ℝ) (hδ : 0 < δ) :
    finiteMomentum f ε h a p hε hh ha δ = (-Complex.I*(h:ℂ)) • D δ :=
  (pureMomentum ε hε h).mem_graph_snd_inj' (finite_graph f ε h a p hε hh ha δ hδ)
    (differential_graph f ε h a p hε hh ha δ hδ) rfl

def limitingMomentum : Hilbert := (-Complex.I*(h:ℂ)) • limitingVector f c α β hα hβ hw hc2 hc

theorem momentum_tendsto : Tendsto (finiteMomentum f ε h a p hε hh ha) (𝓝[>] 0)
    (𝓝 (limitingMomentum f ε h a p hε hh ha)) := by
  apply Tendsto.congr' _ ((vector_tendsto f c α β hα hβ hw hc2 hc).const_smul (-Complex.I*(h:ℂ)))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (finiteMomentum_eq f ε h a p hε hh ha δ hδ).symm

theorem limiting_graph :
    (limitingState f ε h a p hε hh ha,limitingMomentum f ε h a p hε hh ha) ∈
      (pureMomentum ε hε h).graph := by
  apply (pure_closed ε hε h hh).mem_of_tendsto
    ((state_tendsto f ε h a p hε hh ha).prodMk_nhds (momentum_tendsto f ε h a p hε hh ha))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_graph f ε h a p hε hh ha δ hδ

theorem limiting_domain : limitingState f ε h a p hε hh ha ∈ (pureMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (limiting_graph f ε h a p hε hh ha)

theorem graph_tendsto :
    Tendsto (fun δ => (U δ,finiteMomentum f ε h a p hε hh ha δ)) (𝓝[>] 0)
      (𝓝 (limitingState f ε h a p hε hh ha,limitingMomentum f ε h a p hε hh ha)) :=
  (state_tendsto f ε h a p hε hh ha).prodMk_nhds (momentum_tendsto f ε h a p hε hh ha)

theorem momentum_zeroSector : limitingMomentum f ε h a p hε hh ha ∈ zeroSector h hh := by
  apply (zeroSector_closed h hh).mem_of_tendsto (momentum_tendsto f ε h a p hε hh ha)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  rw [finiteMomentum,dif_pos hδ]
  exact KFCausalReciprocalNeutralSuperposition.momentum_zeroSector (count f) ε h (lift f a) (widths f δ)
    (lift f p) (coefficients f δ) (sources f) (polynomials f) hε (fun j => ha (index f j).1) hh
    (widths_admissible f δ hδ.le)

theorem momentum_charge_graph :
    (limitingMomentum f ε h a p hε hh ha,0) ∈ (standingCharge h hh).graph :=
  (standingCharge_zero_iff h hh _).mpr (momentum_zeroSector f ε h a p hε hh ha)

#print axioms finite_graph
#print axioms differential_graph
#print axioms finiteMomentum_eq
#print axioms momentum_tendsto
#print axioms limiting_graph
#print axioms limiting_domain
#print axioms graph_tendsto
#print axioms momentum_zeroSector
#print axioms momentum_charge_graph
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPureMomentumLimit
