/- The actual six-dimensional free Hamiltonian acts on circular charged
packets with the derived oscillator energy, clock weight, and neutral momentum. -/
import UnifiedTheory.Audit.KFCausalPhysicalSpectatorPackets
import UnifiedTheory.Audit.KFCausalFourCircularKineticPotential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFreeCircularPacketGraph
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates
open KFCausalPhysicalSpectatorPackets
open KFCausalFreeHamiltonianCoordinates
open KFCausalChargedSpectatorCoordinates (physicalCoordinates)
open KFCausalClockFloorFlow (clock)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero)
open KFCausalHermiteProductBasis (Index)
open KFCausalFourCircularKineticPotential

theorem clock_ae {u u' : BlockHilbert 1} {a : Block 1 → ℂ}
    (hu : u' =ᵐ[volume] fun x => a x*u x) :
    ∀ᵐ x : Block 4 × Block 2, u' (one (x.2 0))=a (one (x.2 0))*u (one (x.2 0)) := by
  have ht := (Measure.quasiMeasurePreserving_fst.comp
    (KFCausalJoinedFourierProduct.separate_preserves 1 1).quasiMeasurePreserving).comp
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Block 4))) )
  have he := ht.ae hu
  convert he using 1
  funext x
  have hx : one (x.2 0) = (KFCausalJoinedFourierProduct.separate 1 1 x.2).1 := by
    ext j
    fin_cases j <;> rfl
  rw [hx]
  rfl

theorem neutral_ae {v v' : BlockHilbert 1} {a : Block 1 → ℂ}
    (hv : v' =ᵐ[volume] fun x => a x*v x) :
    ∀ᵐ x : Block 4 × Block 2, v' (one (x.2 1))=a (one (x.2 1))*v (one (x.2 1)) := by
  have ht := (Measure.quasiMeasurePreserving_snd.comp
    (KFCausalJoinedFourierProduct.separate_preserves 1 1).quasiMeasurePreserving).comp
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Block 4))) )
  have he := ht.ae hv
  convert he using 1
  funext x
  have hx : one (x.2 1) = (KFCausalJoinedFourierProduct.separate 1 1 x.2).2 := by
    ext j
    fin_cases j <;> rfl
  rw [hx]
  rfl

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0) (b : ℝ) (hb : 0 < b)
local notation "c" => momentumScale h
local notation "hc" => momentumScale_ne_zero h hh
local notation "B" => KFCausalFourCircularChargeBasis.basis c hc b hb
local notation "K" => kinetic4 c hc b hb
local notation "V" => potential4 c hc b hb

theorem radial_packet_graph (i : Index) (u uInv v : BlockHilbert 1)
    (hu : uInv =ᵐ[volume] fun s => ((clock ε (s 0))⁻¹:ℂ)*u s) :
    (packet (B i) u v, ((8*b^2*c^2:ℝ)⁻¹:ℂ) • packet (V i) uInv v) ∈
      (KFCausalClockFloorRadialYosidaDomain.operator ε hε h).graph := by
  apply (radial_graph_iff ε hε h _ _).mpr
  rw [map_smul, position_packet, position_packet]
  let v' := (Lp.fourierTransformₗᵢ (Block 1) ℂ).symm v
  filter_upwards [Lp.coeFn_smul (((8*b^2*c^2:ℝ)⁻¹:ℂ)) (triple (V i) uInv v'),
    triple_coe (V i) uInv v', triple_coe (B i) u v', clock_ae hu,
    Measure.quasiMeasurePreserving_fst.ae (potential_coe4 c hc b hb i)]
      with x hs hp hf hu' hv
  change _ = (positionWeight ε h x:ℂ)*(triple (B i) u v') x
  simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply] at *
  rw [hs, hp, hf]
  rw [hv, hu']
  unfold positionWeight
  change _ = (((c^2*(x.1 0^2+x.1 2^2)+x.1 1^2+x.1 3^2)/(2*clock ε (x.2 0)):ℝ):ℂ)*_
  simp only [one, Matrix.cons_val_zero]
  push_cast
  have hbc : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hcc : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  field_simp [hbc, hcc]
  <;> ring

theorem static_packet_graph (i : Index) (u uC uInv v v2 : BlockHilbert 1)
    (huC : uC =ᵐ[volume] fun s => (clock ε (s 0):ℂ)*u s)
    (hu : uInv =ᵐ[volume] fun s => ((clock ε (s 0))⁻¹:ℂ)*u s)
    (hv : v2 =ᵐ[volume] fun x => (x 0:ℂ)^2*v x) :
    (packet (B i) u v,
      (1/2:ℂ) • packet (B i) uC v +
        ((8*Real.pi^2:ℝ)⁻¹:ℂ) • packet (K i) uInv v +
        ((c^2/2:ℝ):ℂ) • packet (B i) uInv v2) ∈
      (KFCausalClockFloorStaticOperator.operator ε hε h).graph := by
  apply (static_graph_iff ε hε h _ _).mpr
  simp only [map_add, map_smul, dual_packet]
  let F := Lp.fourierTransformₗᵢ (Block 4) ℂ
  let A := (1/2:ℂ) • triple (F (B i)) uC v
  let D := ((8*Real.pi^2:ℝ)⁻¹:ℂ) • triple (F (K i)) uInv v
  let E := ((c^2/2:ℝ):ℂ) • triple (F (B i)) uInv v2
  filter_upwards [Lp.coeFn_add (A+D) E, Lp.coeFn_add A D,
    Lp.coeFn_smul (1/2:ℂ) (triple (F (B i)) uC v),
    Lp.coeFn_smul (((8*Real.pi^2:ℝ)⁻¹:ℂ)) (triple (F (K i)) uInv v),
    Lp.coeFn_smul (((c^2/2:ℝ):ℂ)) (triple (F (B i)) uInv v2),
    triple_coe (F (B i)) uC v, triple_coe (F (K i)) uInv v,
    triple_coe (F (B i)) uInv v2, triple_coe (F (B i)) u v,
    clock_ae huC, clock_ae hu, neutral_ae hv,
    Measure.quasiMeasurePreserving_fst.ae (kinetic_fourier4 c hc b hb i)]
      with x hsum hsum' hA hD hE h1 h2 h3 h4 huC' hu' hv' hk
  change (A+D+E) x = (staticWeight ε h x:ℂ)*(triple (F (B i)) u v) x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at *
  rw [hsum, hsum']
  change A x+D x+E x = _
  dsimp only [A, D, E]
  rw [hA, hD, hE]
  rw [h1, h2, h3, h4, huC', hu', hv', hk]
  unfold staticWeight
  simp only [one, Matrix.cons_val_zero]
  push_cast
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  <;> ring

include hh in
theorem matched_scaling (t : ℝ) :
    Real.exp (2*t) * (8*(Real.exp t/(2*h))^2*c^2)⁻¹ = (8*Real.pi^2)⁻¹ := by
  unfold momentumScale
  rw [show 2*t = t+t by ring, Real.exp_add]
  field_simp [hh, Real.pi_ne_zero, (Real.exp_pos t).ne']
  <;> ring

theorem hamiltonian_packet_graph (hpos : 0 < h)
    (hbound : |h| ≤ Real.pi*ε/3) (t : ℝ)
    (i : Index) (u uC uInv v v2 : BlockHilbert 1)
    (huC : uC =ᵐ[volume] fun s => (clock ε (s 0):ℂ)*u s)
    (hu : uInv =ᵐ[volume] fun s => ((clock ε (s 0))⁻¹:ℂ)*u s)
    (hv : v2 =ᵐ[volume] fun x => (x 0:ℂ)^2*v x) :
    let b₀ := Real.exp t/(2*h);
    let hb₀ : 0 < b₀ := div_pos (Real.exp_pos t) (mul_pos (by norm_num) hpos);
    let basis₀ := KFCausalFourCircularChargeBasis.basis c hc b₀ hb₀;
    (packet (basis₀ i) u v,
      (1/2:ℂ) • packet (basis₀ i) uC v +
        ((h*Real.exp t*((KFCausalCircularZeroLevelCounting.occupation i:ℝ)+2):ℝ):ℂ) •
          packet (basis₀ i) uInv v +
        ((c^2/2:ℝ):ℂ) • packet (basis₀ i) uInv v2) ∈
      (KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh
        (KFCausalClockFloorRadialYosidaReference.wide_bound ε hε h hbound) 0 0 0 t).graph := by
  dsimp only
  let b' := Real.exp t/(2*h)
  have hb' : 0 < b' := div_pos (Real.exp_pos t) (mul_pos (by norm_num) hpos)
  let B' := KFCausalFourCircularChargeBasis.basis c hc b' hb'
  let K' := kinetic4 c hc b' hb' i
  let V' := potential4 c hc b' hb' i
  have hr := radial_packet_graph ε hε h hh b' hb' i u uInv v hu
  have hs := static_packet_graph ε hε h hh b' hb' i u uC uInv v v2 huC hu hv
  have hg := KFCausalClockFloorFreeOperatorSum.graph_from_components ε hε h hh hbound t
    (packet (B' i) u v) _ _ hr hs
  have hm : (Real.exp (2*t):ℂ)*((8*b'^2*c^2:ℝ)⁻¹:ℂ) = ((8*Real.pi^2:ℝ)⁻¹:ℂ) := by
    exact_mod_cast matched_scaling h hh t
  rw [smul_smul, hm] at hg
  have he : packet K' uInv v+packet V' uInv v =
      (KFCausalFourCircularOscillatorDomain.energy4 c b' i:ℂ) • packet (B' i) uInv v := by
    rw [← packet_add_left, KFCausalFourCircularKineticPotential.sum, packet_smul_left]
  have hn := KFCausalFourCircularOscillatorDomain.matched_energy_scale h hh t i
  have hn' : ((8*Real.pi^2:ℝ)⁻¹:ℂ)*
      (KFCausalFourCircularOscillatorDomain.energy4 c b' i:ℂ) =
        ((h*Real.exp t*((KFCausalCircularZeroLevelCounting.occupation i:ℝ)+2):ℝ):ℂ) := by
    have hn'' := congrArg Complex.ofReal hn
    simpa only [b', momentumScale, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using hn''
  have hout : ((8*Real.pi^2:ℝ)⁻¹:ℂ) • packet V' uInv v +
      ((1/2:ℂ) • packet (B' i) uC v +
        ((8*Real.pi^2:ℝ)⁻¹:ℂ) • packet K' uInv v +
        ((c^2/2:ℝ):ℂ) • packet (B' i) uInv v2) =
      (1/2:ℂ) • packet (B' i) uC v +
        ((h*Real.exp t*((KFCausalCircularZeroLevelCounting.occupation i:ℝ)+2):ℝ):ℂ) •
          packet (B' i) uInv v +
        ((c^2/2:ℝ):ℂ) • packet (B' i) uInv v2 := by
    calc
      _ = (1/2:ℂ) • packet (B' i) uC v +
        ((8*Real.pi^2:ℝ)⁻¹:ℂ) • (packet K' uInv v+packet V' uInv v) +
        ((c^2/2:ℝ):ℂ) • packet (B' i) uInv v2 := by rw [smul_add]; abel
      _ = _ := by rw [he, smul_smul, hn']
  rw [hout] at hg
  exact hg

#print axioms matched_scaling
#print axioms hamiltonian_packet_graph

#print axioms radial_packet_graph
#print axioms static_packet_graph
end
end UnifiedTheory.Audit.KFCausalFreeCircularPacketGraph
