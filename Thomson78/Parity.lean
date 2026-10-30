import Thomson78.Basic

namespace Thomson78

theorem no_fixedPointFree_involution_fin7 (f : Fin 7 → Fin 7)
    (hf : Function.Involutive f) (hn : ∀ i, f i ≠ i) : False := by
  classical
  let s := Finset.univ.filter (fun i : Fin 7 => i < f i)
  let t := Finset.univ.filter (fun i : Fin 7 => f i < i)
  have himage : s.image f = t := by
    ext i
    simp only [Finset.mem_image, s, t, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simpa only [hf j] using hj
    · intro hi
      exact ⟨f i, by simpa only [hf i] using hi, hf i⟩
  have hcard : s.card = t.card := by
    rw [← himage, Finset.card_image_of_injective _ hf.injective]
  have hdisj : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_gt (Finset.mem_filter.mp hi).2) (Finset.mem_filter.mp hj).2
  have hunion : s ∪ t = Finset.univ := by
    ext i
    simp only [Finset.mem_union, s, t, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact lt_or_gt_of_ne (hn i).symm
  have hseven : s.card + t.card = 7 := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    simp
  omega

end Thomson78

#print axioms Thomson78.no_fixedPointFree_involution_fin7
