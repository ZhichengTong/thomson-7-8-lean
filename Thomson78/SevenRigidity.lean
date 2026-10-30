import Thomson78.SevenPentagon

noncomputable section
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace Thomson78.Seven

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The five-cycle accounts for five indices; the centroid identifies the other two. -/
theorem five_cycle_and_poles {x : Fin 7 → V} (h : Configuration x) :
    ∃ (c : Fin 5 → Fin 7) (p q : Fin 7),
      Function.Injective c ∧ p ≠ q ∧
      (∀ k, c k ≠ p ∧ c k ≠ q) ∧
      (∀ i, i = p ∨ i = q ∨ ∃ k, c k = i) ∧
      x q = -x p ∧
      (∀ k, x (c k) = Real.cos (k * theta) • x (c 0) +
        Real.sin (k * theta) • ((Real.sin theta)⁻¹ • (x (c 1) - b • x (c 0)))) ∧
      ⟪x (c 0), x (c 1)⟫_ℝ = b := by
  classical
  obtain ⟨i, j, hij⟩ := exists_edge h
  let c : Fin 5 → Fin 7 := fun k => walk h i j k
  have hcinj : Function.Injective c := walk_first_five_injective h i j hij
  let s : Finset (Fin 7) := Finset.univ.image c
  have hs : s.card = 5 := by
    rw [Finset.card_image_of_injective _ hcinj]
    simp
  have hcomp : (Finset.univ \ s).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hs]
  obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hcomp
  have hpm : p ∈ Finset.univ \ s := by rw [hset]; simp
  have hqm : q ∈ Finset.univ \ s := by rw [hset]; simp
  have hpnot : p ∉ s := (Finset.mem_sdiff.mp hpm).2
  have hqnot : q ∉ s := (Finset.mem_sdiff.mp hqm).2
  have hcnot : ∀ k, c k ≠ p ∧ c k ≠ q := by
    intro k
    have hkm : c k ∈ s := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    constructor
    · intro he; exact hpnot (he ▸ hkm)
    · intro he; exact hqnot (he ▸ hkm)
  have hcover : ∀ l, l = p ∨ l = q ∨ ∃ k, c k = l := by
    intro l
    by_cases hl : l ∈ s
    · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hl
      exact Or.inr (Or.inr ⟨k, hk⟩)
    · have hm : l ∈ Finset.univ \ s := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hl⟩
      rw [hset] at hm
      rcases Finset.mem_insert.mp hm with hlp | hlq
      · exact Or.inl hlp
      · exact Or.inr (Or.inl (Finset.mem_singleton.mp hlq))
  have hsum_s : ∑ l ∈ s, x l = 0 := by
    dsimp [s]
    rw [Finset.sum_image (fun k _ l _ hkl => hcinj hkl)]
    exact recurrence_sum_five (fun k => x (walk h i j k)) (walk_recurrence h i j hij)
  have hsum_comp : ∑ l ∈ Finset.univ \ s, x l = 0 := by
    have hh := Finset.sum_sdiff (f := x) (Finset.subset_univ s)
    rw [hsum_s, h.centroid, add_zero] at hh
    exact hh
  have hanti : x q = -x p := by
    rw [hset, Finset.sum_pair hpq] at hsum_comp
    exact eq_neg_of_add_eq_zero_right hsum_comp
  refine ⟨c, p, q, hcinj, hpq, hcnot, hcover, hanti, ?_, ?_⟩
  · intro k
    exact recurrence_circle (fun k => x (walk h i j k)) (walk_recurrence h i j hij) k
  · exact hij

/-- The seven-point rigidity theorem in an arbitrary real inner product space.
The angle 4π/5 traverses the same regular pentagon as the angle 2π/5. -/
theorem rigidity_star {x : Fin 7 → V} (h : Configuration x) :
    ∃ e₁ e₂ e₃ : V,
      ⟪e₁, e₁⟫_ℝ = 1 ∧ ⟪e₂, e₂⟫_ℝ = 1 ∧ ⟪e₃, e₃⟫_ℝ = 1 ∧
      ⟪e₁, e₂⟫_ℝ = 0 ∧ ⟪e₁, e₃⟫_ℝ = 0 ∧ ⟪e₂, e₃⟫_ℝ = 0 ∧
      Set.range x = {e₃, -e₃} ∪ Set.range (fun k : Fin 5 =>
        Real.cos (k * theta) • e₁ + Real.sin (k * theta) • e₂) := by
  classical
  obtain ⟨c, p, q, hcinj, hpq, hcnot, hcover, hanti, hcircle, h01⟩ := five_cycle_and_poles h
  let e₁ := x (c 0)
  let e₂ := (Real.sin theta)⁻¹ • (x (c 1) - b • x (c 0))
  let e₃ := x p
  have hb := circle_basis (x (c 0)) (x (c 1)) (h.unit _) (h.unit _) h01
  have horth (k : Fin 5) : ⟪e₃, x (c k)⟫_ℝ = 0 := by
    apply antipodal_pair_orthogonal
    · exact h.contacts p (c k) (hcnot k).1.symm
    · rw [show -e₃ = x q from hanti.symm]
      exact h.contacts q (c k) (hcnot k).2.symm
  refine ⟨e₁, e₂, e₃, h.unit _, hb.2, h.unit _, hb.1, ?_, ?_, ?_⟩
  · rw [real_inner_comm]
    exact horth 0
  · dsimp [e₂]
    rw [real_inner_smul_left, inner_sub_left, real_inner_smul_left,
      real_inner_comm e₃ (x (c 1)), horth 1, real_inner_comm e₃ (x (c 0)), horth 0]
    ring
  · ext y
    constructor
    · rintro ⟨l, rfl⟩
      rcases hcover l with rfl | rfl | ⟨k, rfl⟩
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr hanti)
      · exact Or.inr ⟨k, (hcircle k).symm⟩
    · intro hy
      rcases hy with hp | ⟨k, hk⟩
      · rcases hp with hp | hq
        · exact ⟨p, hp.symm⟩
        · have hyq : y = -e₃ := by simpa using hq
          exact ⟨q, hanti.trans hyq.symm⟩
      · exact ⟨c k, (hcircle k).trans hk⟩

/-- Proposition 4.1 of the manuscript, with the ordinary cyclic parametrization. -/
theorem rigidity {x : Fin 7 → V} (h : Configuration x) :
    ∃ e₁ e₂ e₃ : V,
      ⟪e₁, e₁⟫_ℝ = 1 ∧ ⟪e₂, e₂⟫_ℝ = 1 ∧ ⟪e₃, e₃⟫_ℝ = 1 ∧
      ⟪e₁, e₂⟫_ℝ = 0 ∧ ⟪e₁, e₃⟫_ℝ = 0 ∧ ⟪e₂, e₃⟫_ℝ = 0 ∧
      Set.range x = {e₃, -e₃} ∪ Set.range (fun k : Fin 5 =>
        Real.cos (2 * Real.pi * k / 5) • e₁ + Real.sin (2 * Real.pi * k / 5) • e₂) := by
  obtain ⟨e₁, e₂, e₃, h1, h2, h3, h12, h13, h23, hr⟩ := rigidity_star h
  refine ⟨e₁, e₂, e₃, h1, h2, h3, h12, h13, h23, ?_⟩
  rw [← pentagon_reindex e₁ e₂]
  exact hr

#print axioms rigidity

theorem rigidity_of_norm {x : Fin 7 → V} (hu : ∀ i, ‖x i‖ = 1)
    (hc : ∀ i j, i ≠ j → Contact ⟪x i, x j⟫_ℝ) (hz : ∑ i, x i = 0) :
    ∃ e₁ e₂ e₃ : V,
      ⟪e₁, e₁⟫_ℝ = 1 ∧ ⟪e₂, e₂⟫_ℝ = 1 ∧ ⟪e₃, e₃⟫_ℝ = 1 ∧
      ⟪e₁, e₂⟫_ℝ = 0 ∧ ⟪e₁, e₃⟫_ℝ = 0 ∧ ⟪e₂, e₃⟫_ℝ = 0 ∧
      Set.range x = {e₃, -e₃} ∪ Set.range (fun k : Fin 5 =>
        Real.cos (2 * Real.pi * k / 5) • e₁ + Real.sin (2 * Real.pi * k / 5) • e₂) := by
  apply rigidity
  exact ⟨fun i => by rw [real_inner_self_eq_norm_sq, hu i]; norm_num, hc, hz⟩

end Thomson78.Seven
