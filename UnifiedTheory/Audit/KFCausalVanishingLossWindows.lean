/- Finite telescoping selects low-loss intervals in arbitrarily late
blocks. The convergence input is a finite energy limit, not a decay rate. -/
import UnifiedTheory.Audit.KFCausalLossSensitiveComparison

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalVanishingLossWindows
noncomputable section
open Filter
open scoped Topology

theorem small_partition_drop (e : ℝ → ℝ) (R L : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ j : ℕ, j < N ∧ e (R+j*L)-e (R+(j+1)*L) ≤ (e R-e (R+N*L))/N := by
  have hs : ∀ n : ℕ, (∑ j ∈ Finset.range n, (e (R+j*L)-e (R+(j+1)*L))) = e R-e (R+n*L) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ,ih]
      push_cast
      abel
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  obtain ⟨j,hj,he⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN))
    (show (∑ j ∈ Finset.range N, (e (R+j*L)-e (R+(j+1)*L))) ≤
        ∑ _j ∈ Finset.range N, (e R-e (R+N*L))/N from by
      rw [hs]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_div_cancel₀ _ hn]
      field_simp
      exact le_rfl)
  exact ⟨j,Finset.mem_range.mp hj,he⟩

theorem block_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun N : ℕ => c*(N:ℝ)^2) atTop atTop :=
  ((tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hc

theorem block_drop_limit (e : ℝ → ℝ) (b c : ℝ) (hc : 0 < c)
    (he : Tendsto e atTop (𝓝 b)) :
    Tendsto (fun N : ℕ => e (c*(N:ℝ)^2)-e (2*(c*(N:ℝ)^2))) atTop (𝓝 0) := by
  simpa only [sub_self] using (he.comp (block_tendsto c hc)).sub
    (he.comp ((block_tendsto c hc).const_mul_atTop (by norm_num)))

theorem late_small_block (e : ℝ → ℝ) (b c delta R : ℝ) (hc : 0 < c) (hd : 0 < delta)
    (he : Tendsto e atTop (𝓝 b)) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ 0 < N ∧ R ≤ c*(N:ℝ)^2 ∧
      e (c*(N:ℝ)^2)-e (2*(c*(N:ℝ)^2)) ≤ delta := by
  have ht := (block_drop_limit e b c hc he).eventually (eventually_lt_nhds hd)
  have hr := (block_tendsto c hc).eventually (eventually_ge_atTop R)
  obtain ⟨N,hN,hp,hR,hD⟩ := ((eventually_ge_atTop M).and
    ((eventually_gt_atTop (0:ℕ)).and (hr.and ht))).exists
  exact ⟨N,hN,hp,hR,hD.le⟩

private theorem coefficients (H c E beta : ℝ) (hH : 0 < H) (hc : 0 < c)
    (hE : 0 ≤ E) (hb : 0 < beta) :
    ∃ eta delta : ℝ, 0 < eta ∧ 0 < delta ∧ c/(2*H)*(delta/eta+eta*E) ≤ beta := by
  let eta := beta*H/(c*(E+1))
  have he : 0 < eta := by dsimp [eta]; positivity
  refine ⟨eta,eta*beta*H/c,he,by positivity,?_⟩
  have hcancel : eta*(E+1)=beta*H/c := by dsimp [eta]; field_simp
  have hd : eta*beta*H/c/eta=beta*H/c := by field_simp
  rw [hd]
  have hb' : eta*E ≤ beta*H/c := by nlinarith only [hcancel,he]
  calc
    _ ≤ c/(2*H)*(beta*H/c+beta*H/c) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hb') (by positivity)
    _ = beta := by field_simp; ring

private theorem block_bound (H c N U eta delta E E0 drop : ℝ)
    (hH : 0 < H) (hc : 0 < c) (hN : 0 < N) (hU : c*N^2 ≤ U)
    (he : 0 < eta) (hE0 : 0 ≤ E0) (hE : E ≤ E0) (hd : drop ≤ delta/N) :
    (c*N)/(2*H*eta)*drop+eta*E*(c*N)^2/(2*H*U) ≤
      c/(2*H)*(delta/eta+eta*E0) := by
  have hU0 : 0 < U := (mul_pos hc (sq_pos_of_pos hN)).trans_le hU
  calc
    _ ≤ (c*N)/(2*H*eta)*(delta/N)+eta*E0*(c*N)^2/(2*H*U) :=
      add_le_add (mul_le_mul_of_nonneg_left hd (by positivity))
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hE he.le) (sq_nonneg _)) (by positivity))
    _ ≤ (c*N)/(2*H*eta)*(delta/N)+eta*E0*(c*N)^2/(2*H*(c*N^2)) :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hU (by positivity)))
    _ = _ := by field_simp

theorem selected_window (e : ℝ → ℝ) (err : ℝ → ℝ → ℝ) (H a R C beta E0 : ℝ)
    (hH : 0 < H) (hC : 0 < C) (hb' : 0 < beta) (hE0 : 0 ≤ E0)
    (hlim : ∃ b : ℝ, Tendsto e atTop (𝓝 b)) (hbound : ∀ U, a ≤ U → e U ≤ E0)
    (herror : ∀ U L eta t, 0 < U → 0 ≤ t → t ≤ L → 0 < eta →
      err U t ≤ L/(2*H*eta)*(e U-e (U+L))+eta*e U*L^2/(2*H*U)) (M : ℕ) :
    ∃ U L : ℝ, 0 < U ∧ 0 < L ∧ R ≤ U ∧ a ≤ U ∧ C*U ≤ L^2 ∧
      L/U ≤ 1/((M:ℝ)+1) ∧ ∀ t, 0 ≤ t → t ≤ L → err U t ≤ beta := by
  let c := 2*C
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨eta,delta,he,hd,hcoef⟩ := coefficients H c E0 beta hH hc hE0 hb'
  obtain ⟨b,ht⟩ := hlim
  obtain ⟨N,hMN,hN,hR,hD⟩ := KFCausalVanishingLossWindows.late_small_block
    e b c delta (max R a) hc hd ht (M+1)
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  let L := c*(N:ℝ)
  let B := c*(N:ℝ)^2
  obtain ⟨j,hj,hjD⟩ := KFCausalVanishingLossWindows.small_partition_drop
    e B L N hN
  let U := B+(j:ℝ)*L
  have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
  have hjN : (j:ℝ) < N := by exact_mod_cast hj
  have hL : 0 < L := mul_pos hc hn
  have hB : 0 < B := mul_pos hc (sq_pos_of_pos hn)
  have hBU : B ≤ U := le_add_of_nonneg_right (mul_nonneg hj0 hL.le)
  have hU0 : 0 < U := hB.trans_le hBU
  have hU2 : U ≤ 2*B := by
    have hjm := mul_le_mul_of_nonneg_right hjN.le hL.le
    change c*(N:ℝ)^2+(j:ℝ)*(c*(N:ℝ)) ≤ 2*(c*(N:ℝ)^2)
    change (j:ℝ)*(c*(N:ℝ)) ≤ (N:ℝ)*(c*(N:ℝ)) at hjm
    nlinarith only [hjm]
  have haU : a ≤ U := (le_max_right R a).trans (hR.trans hBU)
  have htail : e U-e (U+L) ≤ delta/N := by
    have hlast : B+(N:ℝ)*L=2*(c*(N:ℝ)^2) := by dsimp [B,L]; ring
    have hnext : B+((j:ℝ)+1)*L=U+L := by dsimp [U]; ring
    rw [hlast,hnext] at hjD
    exact hjD.trans (div_le_div_of_nonneg_right hD hn.le)
  refine ⟨U,L,hU0,hL,(le_max_left R a).trans (hR.trans hBU),haU,?_,?_,?_⟩
  · have heq : L^2=2*C*B := by dsimp [L,B,c]; ring
    rw [heq]
    nlinarith only [mul_le_mul_of_nonneg_left hU2 hC.le]
  · have hMN' : (M:ℝ)+1 ≤ N := by exact_mod_cast hMN
    have hl : L/U ≤ 1/(N:ℝ) := by
      apply (div_le_div_iff₀ hU0 hn).mpr
      exact (show L*(N:ℝ)=B by dsimp [L,B]; ring).le.trans (by simpa only [one_mul] using hBU)
    exact hl.trans (one_div_le_one_div_of_le (by positivity) hMN')
  · intro t ht0 htL
    exact (herror U L eta t hU0 ht0 htL he).trans
      ((block_bound H c N U eta delta (e U) E0 (e U-e (U+L))
        hH hc hn hBU he hE0 (hbound U haU) htail).trans hcoef)

#print axioms selected_window
#print axioms small_partition_drop
#print axioms block_tendsto
#print axioms block_drop_limit
#print axioms late_small_block
end
end UnifiedTheory.Audit.KFCausalVanishingLossWindows
