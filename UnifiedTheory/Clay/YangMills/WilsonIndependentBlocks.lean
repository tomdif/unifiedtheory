/- Exact independent-link blocks in the actual four-dimensional periodic Wilson
action. Independence is checked on geometric plaquette incidence. No action
factorization, continuum limit or renormalization estimate is assumed. -/
import UnifiedTheory.Clay.YangMills.SingleLinkWilsonOscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonIndependentBlocks
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonMomentBounds WilsonUniformVariance
open SingleLinkWilsonOscillation

variable (n : ℕ) [NeZero n]

abbrev Link := Vertex n × Fin 4

def edgeCoord (e : Edge (Vertex n)) : Link n := (e.1, e.2.2.val)

omit [NeZero n] in
theorem edgeCoord_selected (a : Link n) :
    edgeCoord n (selectedLink n a.1 a.2) = a := rfl

omit [NeZero n] in
theorem selected_edgeCoord (e : Edge (Vertex n)) :
    selectedLink n (edgeCoord n e).1 (edgeCoord n e).2 = e := by
  rcases e with ⟨x, y, μ, h⟩
  cases h
  rfl

/-- The actual four positive link coordinates occurring in an oriented square. -/
def incident (p : PlaquetteIndex n) (a : Link n) : Prop :=
  a = (p.1, p.2.1.1) ∨ a = (step n p.1 p.2.1.1, p.2.1.2) ∨
    a = (step n p.1 p.2.1.2, p.2.1.1) ∨ a = (p.1, p.2.1.2)

theorem incident_affected (p : PlaquetteIndex n) (a : Link n) (h : incident n p a) :
    p ∈ affected n a.1 a.2 := by
  have hne : p.2.1.1 ≠ p.2.1.2 := ne_of_lt p.2.2
  rcases h with rfl | rfl | rfl | rfl
  · exact base_mem n p.1 p.2.1.1 p.2 (Or.inl rfl)
  · have hh := shifted_mem n (step n p.1 p.2.1.1) p.2.1.2 p.2 (Or.inr rfl)
    simpa [transverse, hne, step] using hh
  · have hh := shifted_mem n (step n p.1 p.2.1.2) p.2.1.1 p.2 (Or.inl rfl)
    simpa [transverse, step] using hh
  · exact base_mem n p.1 p.2.1.2 p.2 (Or.inr rfl)

/-- Distinct selected links have disjoint sets of affected plaquettes. -/
def Independent (S : Finset (Link n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
    Disjoint (affected n a.1 a.2) (affected n b.1 b.2)

omit [NeZero n] in
theorem independent_unique (S : Finset (Link n)) (hS : Independent n S)
    (a b : Link n) (ha : a ∈ S) (hb : b ∈ S) (p : PlaquetteIndex n)
    (hpa : p ∈ affected n a.1 a.2) (hpb : p ∈ affected n b.1 b.2) : a = b := by
  by_contra h
  exact Finset.disjoint_left.mp (hS a ha b hb h) hpa hpb

omit [NeZero n] in
/-- Every plaquette touching a mu-link has the same mu-coordinate as that
link's base. The displacement to the other mu-link is transverse. -/
theorem affected_preserves_parallel_coordinate (x : Vertex n) (μ : Fin 4)
    (p : PlaquetteIndex n) (hp : p ∈ affected n x μ) : p.1 μ = x μ := by
  classical
  simp only [affected, Finset.mem_biUnion] at hp
  obtain ⟨q,hq,hp⟩ := hp
  have hq' : q.1.1 = μ ∨ q.1.2 = μ := by simpa [planes] using hq
  have ht : transverse μ q ≠ μ := by
    rcases hq' with h | h
    · simp only [transverse, h]
      rw [← h]
      exact (ne_of_lt q.2).symm
    · have hn : q.1.1 ≠ μ := by rw [← h]; exact ne_of_lt q.2
      simp [transverse, hn]
  rcases Finset.mem_insert.mp hp with hp | hp
  · exact congrArg (fun p : PlaquetteIndex n => p.1 μ) hp
  · have he := congrArg (fun p : PlaquetteIndex n => p.1 μ) (Finset.mem_singleton.mp hp)
    simpa [Pi.single_apply, ht, ht.symm] using he

/-- An explicit block containing one parallel link at every position along
a full periodic coordinate line. -/
def parallelLine (x : Vertex n) (μ : Fin 4) : Finset (Link n) := by
  classical
  exact Finset.univ.image (fun t : ZMod n => (Function.update x μ t, μ))

theorem parallelLine_independent (x : Vertex n) (μ : Fin 4) :
    Independent n (parallelLine n x μ) := by
  classical
  intro a ha b hb hab
  obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hb
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hst := (affected_preserves_parallel_coordinate n _ μ p hp).symm.trans
    (affected_preserves_parallel_coordinate n _ μ p hq)
  have heq : s = t := by simpa using hst
  exact hab (heq ▸ rfl)

theorem parallelLine_card (x : Vertex n) (μ : Fin 4) :
    (parallelLine n x μ).card = n := by
  classical
  have hinj : Function.Injective (fun t : ZMod n => (Function.update x μ t, μ)) := by
    intro s t h
    have hh := congrArg (fun a : Link n => a.1 μ) h
    simpa using hh
  simp only [parallelLine, Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]

omit [NeZero n] in
theorem mem_affected_iff (x : Vertex n) (μ : Fin 4) (p : PlaquetteIndex n) :
    p ∈ affected n x μ ↔ p.2 ∈ planes μ ∧
      (p.1 = x ∨ p.1 = x-Pi.single (transverse μ p.2) 1) := by
  classical
  constructor
  · intro hp
    simp only [affected, Finset.mem_biUnion] at hp
    obtain ⟨q,hq,hp⟩ := hp
    rcases Finset.mem_insert.mp hp with hp | hp
    · have hq' : p.2 = q := congrArg Prod.snd hp
      subst q
      exact ⟨hq, Or.inl (congrArg Prod.fst hp)⟩
    · have hp' := Finset.mem_singleton.mp hp
      have hq' : p.2 = q := congrArg Prod.snd hp'
      subst q
      exact ⟨hq, Or.inr (congrArg Prod.fst hp')⟩
  · rintro ⟨hq,hp⟩
    simp only [affected, Finset.mem_biUnion]
    refine ⟨p.2,hq,?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hp with hp | hp
    · exact Or.inl (Prod.ext hp rfl)
    · exact Or.inr (Prod.ext hp rfl)

omit [NeZero n] in
/-- Two parallel links sharing a plaquette either coincide or their bases
are nearest neighbors in a transverse direction. -/
theorem common_affected_parallel (x y : Vertex n) (μ : Fin 4) (p : PlaquetteIndex n)
    (hx : p ∈ affected n x μ) (hy : p ∈ affected n y μ) :
    x = y ∨ ∃ ν : Fin 4, ν ≠ μ ∧ (x = step n y ν ∨ y = step n x ν) := by
  obtain ⟨hq,hx⟩ := (mem_affected_iff n x μ p).mp hx
  obtain ⟨_,hy⟩ := (mem_affected_iff n y μ p).mp hy
  have hq' : p.2.1.1 = μ ∨ p.2.1.2 = μ := by simpa [planes] using hq
  have ht : transverse μ p.2 ≠ μ := by
    rcases hq' with h | h
    · simp only [transverse, h]
      rw [← h]
      exact (ne_of_lt p.2.2).symm
    · have hn : p.2.1.1 ≠ μ := by rw [← h]; exact ne_of_lt p.2.2
      simp [transverse, hn]
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (hx.symm.trans hy)
  · exact Or.inr ⟨_,ht,Or.inr (eq_sub_iff_add_eq.mp (hx.symm.trans hy)).symm⟩
  · exact Or.inr ⟨_,ht,Or.inl (eq_sub_iff_add_eq.mp (hy.symm.trans hx)).symm⟩
  · have hh := congrArg (fun z : Vertex n => z+Pi.single (transverse μ p.2) 1) (hx.symm.trans hy)
    exact Or.inl (by simpa using hh)

omit [NeZero n] in
/-- A geometric separation criterion suitable for larger parallel-link
blocks, including a transverse checkerboard once that coloring is supplied. -/
theorem independent_of_transverse_separation (S : Finset (Link n)) (μ : Fin 4)
    (hdir : ∀ a ∈ S, a.2 = μ)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ ν : Fin 4, ν ≠ μ → a.1 ≠ step n b.1 ν) :
    Independent n S := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro p hpa hpb
  rw [hdir a ha] at hpa
  rw [hdir b hb] at hpb
  rcases common_affected_parallel n a.1 b.1 μ p hpa hpb with heq | ⟨ν,hν,hstep⟩
  · exact hab (Prod.ext heq ((hdir a ha).trans (hdir b hb).symm))
  · rcases hstep with hstep | hstep
    · exact hsep a ha b hb hab ν hν hstep
    · exact hsep b hb a ha hab.symm ν hν hstep

variable (G : Type*) [Group G]

/-- Simultaneous assignment to selected positive links. The edge coordinates
are inverse to the repo's actual selectedLink map. -/
def blockUpdate (U : Configuration (Vertex n) G) (S : Finset (Link n))
    (V : Link n → G) : Configuration (Vertex n) G := by
  classical
  exact fun e => if edgeCoord n e ∈ S then V (edgeCoord n e) else U e

omit [NeZero n] [Group G] in
theorem blockUpdate_selected (U : Configuration (Vertex n) G) (S : Finset (Link n))
    (V : Link n → G) (a : Link n) (ha : a ∈ S) :
    blockUpdate n G U S V (selectedLink n a.1 a.2) = V a := by
  simp [blockUpdate, edgeCoord_selected, ha]

omit [NeZero n] [Group G] in
theorem blockUpdate_outside (U : Configuration (Vertex n) G) (S : Finset (Link n))
    (V : Link n → G) (e : Edge (Vertex n)) (he : edgeCoord n e ∉ S) :
    blockUpdate n G U S V e = U e := by simp [blockUpdate, he]

omit [NeZero n] [Group G] in
theorem blockUpdate_singleton [DecidableEq (Edge (Vertex n))]
    (U : Configuration (Vertex n) G) (V : Link n → G)
    (a : Link n) :
    blockUpdate n G U {a} V = Function.update U (selectedLink n a.1 a.2) (V a) := by
  classical
  funext e
  by_cases he : edgeCoord n e = a
  · have he' : e = selectedLink n a.1 a.2 := by
      rw [← he]
      exact (selected_edgeCoord n e).symm
    subst e
    simp [blockUpdate, edgeCoord_selected]
  · have he' : e ≠ selectedLink n a.1 a.2 := by
      intro h
      exact he (h ▸ edgeCoord_selected n a)
    simp [blockUpdate, he, Function.update_of_ne he']

omit [NeZero n] in
theorem plaquette_congr (p : PlaquetteIndex n) (U W : Configuration (Vertex n) G)
    (h : ∀ e : Edge (Vertex n), incident n p (edgeCoord n e) → U e = W e) :
    holonomy (Quiver.Symmetrify (Vertex n)) G (orientedExtension (Vertex n) G U) (loops n p) =
      holonomy (Quiver.Symmetrify (Vertex n)) G (orientedExtension (Vertex n) G W) (loops n p) := by
  have h1 := h (⟨p.1, step n p.1 p.2.1.1, forward n p.1 p.2.1.1⟩ : Edge (Vertex n))
    (by simp [incident, edgeCoord, forward])
  have h2 := h (⟨step n p.1 p.2.1.1, step n (step n p.1 p.2.1.1) p.2.1.2,
    forward n (step n p.1 p.2.1.1) p.2.1.2⟩ : Edge (Vertex n))
    (by simp [incident, edgeCoord, forward])
  have h3 := h (⟨step n p.1 p.2.1.2, step n (step n p.1 p.2.1.1) p.2.1.2,
    ⟨p.2.1.1, step_comm n p.1 p.2.1.2 p.2.1.1⟩⟩ : Edge (Vertex n))
    (by simp [incident, edgeCoord])
  have h4 := h (⟨p.1, step n p.1 p.2.1.2, forward n p.1 p.2.1.2⟩ : Edge (Vertex n))
    (by simp [incident, edgeCoord, forward])
  simp only [loops, plaquette, holonomy, link, orientedExtension, base]
  rw [h1, h2, h3, h4]

def plaquetteTerm (χ : G → ℂ) (c : ℝ) (U : Configuration (Vertex n) G)
    (p : PlaquetteIndex n) : ℝ := c-(loopObservable (Vertex n) G χ (loops n p) U).re

theorem term_update_unchanged (χ : G → ℂ) (c : ℝ) (U : Configuration (Vertex n) G)
    (S : Finset (Link n)) (V : Link n → G) (p : PlaquetteIndex n)
    (hp : ∀ a ∈ S, p ∉ affected n a.1 a.2) :
    plaquetteTerm n G χ c (blockUpdate n G U S V) p = plaquetteTerm n G χ c U p := by
  have hh := plaquette_congr n G p (blockUpdate n G U S V) U (by
    intro e he
    apply blockUpdate_outside
    intro hm
    exact hp (edgeCoord n e) hm (incident_affected n p (edgeCoord n e) he))
  unfold plaquetteTerm loopObservable wilson
  rw [hh]

theorem term_update_single (χ : G → ℂ) (c : ℝ) (U : Configuration (Vertex n) G)
    (S : Finset (Link n)) (hS : Independent n S) (V : Link n → G)
    (p : PlaquetteIndex n) (a : Link n) (ha : a ∈ S) (hp : p ∈ affected n a.1 a.2) :
    plaquetteTerm n G χ c (blockUpdate n G U S V) p =
      plaquetteTerm n G χ c (blockUpdate n G U {a} V) p := by
  classical
  have hh := plaquette_congr n G p (blockUpdate n G U S V) (blockUpdate n G U {a} V) (by
    intro e he
    by_cases hm : edgeCoord n e ∈ S
    · have heq := independent_unique n S hS (edgeCoord n e) a hm ha p
        (incident_affected n p (edgeCoord n e) he) hp
      simp [blockUpdate, heq, ha]
    · have hne : edgeCoord n e ≠ a := fun h => hm (h ▸ ha)
      simp [blockUpdate, hm, hne])
  unfold plaquetteTerm loopObservable wilson
  rw [hh]

/-- Local additivity follows from the actual holonomy, with at most one
selected link contributing to each plaquette. -/
theorem term_decomposition (χ : G → ℂ) (c : ℝ) (U : Configuration (Vertex n) G)
    (S : Finset (Link n)) (hS : Independent n S) (V : Link n → G) (p : PlaquetteIndex n) :
    plaquetteTerm n G χ c (blockUpdate n G U S V) p-plaquetteTerm n G χ c U p =
      ∑ a ∈ S, (plaquetteTerm n G χ c (blockUpdate n G U {a} V) p-plaquetteTerm n G χ c U p) := by
  classical
  by_cases hex : ∃ a ∈ S, p ∈ affected n a.1 a.2
  · obtain ⟨a,ha,hp⟩ := hex
    rw [term_update_single n G χ c U S hS V p a ha hp]
    symm
    apply Finset.sum_eq_single a
    · intro b hb hba
      have hpb : p ∉ affected n b.1 b.2 := fun h =>
        hba (independent_unique n S hS b a hb ha p h hp)
      rw [term_update_unchanged n G χ c U {b} V p (by simpa using hpb)]
      exact sub_self _
    · exact fun h => (h ha).elim
  · have hp : ∀ a ∈ S, p ∉ affected n a.1 a.2 := by simpa only [not_exists, not_and] using hex
    rw [term_update_unchanged n G χ c U S V p hp, sub_self]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    rw [term_update_unchanged n G χ c U {a} V p (by simpa using hp a ha), sub_self]

/-- Exact action decomposition; the action factorization is a conclusion. -/
theorem action_decomposition (χ : G → ℂ) (β c : ℝ) (U : Configuration (Vertex n) G)
    (S : Finset (Link n)) (hS : Independent n S) (V : Link n → G) :
    orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c (blockUpdate n G U S V) -
        orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c U =
      ∑ a ∈ S, (orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c
          (blockUpdate n G U {a} V) -
        orientedWilsonAction (Vertex n) G χ (base n) (loops n) β c U) := by
  classical
  change β*(∑ p, plaquetteTerm n G χ c (blockUpdate n G U S V) p)-
      β*(∑ p, plaquetteTerm n G χ c U p) =
    ∑ a ∈ S, (β*(∑ p, plaquetteTerm n G χ c (blockUpdate n G U {a} V) p)-
      β*(∑ p, plaquetteTerm n G χ c U p))
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [term_decomposition n G χ c U S hS V]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_sub_distrib, mul_sub]

/-- Arbitrary real plaquette sources have the same exact block additivity.
The source is evaluated on the actual Wilson loop observable. -/
theorem weighted_plaquette_decomposition (χ : G → ℂ) (f : PlaquetteIndex n → ℝ)
    (U : Configuration (Vertex n) G) (S : Finset (Link n)) (hS : Independent n S)
    (V : Link n → G) :
    (∑ p, f p*(loopObservable (Vertex n) G χ (loops n p) (blockUpdate n G U S V)).re) -
        (∑ p, f p*(loopObservable (Vertex n) G χ (loops n p) U).re) =
      ∑ a ∈ S, ((∑ p, f p*(loopObservable (Vertex n) G χ (loops n p)
          (blockUpdate n G U {a} V)).re) -
        (∑ p, f p*(loopObservable (Vertex n) G χ (loops n p) U).re)) := by
  classical
  have hp (p : PlaquetteIndex n) :
      (loopObservable (Vertex n) G χ (loops n p) (blockUpdate n G U S V)).re-
          (loopObservable (Vertex n) G χ (loops n p) U).re =
        ∑ a ∈ S, ((loopObservable (Vertex n) G χ (loops n p) (blockUpdate n G U {a} V)).re-
          (loopObservable (Vertex n) G χ (loops n p) U).re) := by
    have h := congrArg (fun z : ℝ => -z) (term_decomposition n G χ 0 U S hS V p)
    simpa only [plaquetteTerm, zero_sub, neg_sub_neg, ← Finset.sum_neg_distrib, neg_sub] using h
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  simp_rw [hp, Finset.mul_sum]
  exact Finset.sum_comm

end
end UnifiedTheory.Clay.YangMills.WilsonIndependentBlocks
