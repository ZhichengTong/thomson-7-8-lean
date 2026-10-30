import Thomson78.EightCandidate
import Thomson78.EightParameter
import Thomson78.SphereEnergy

/-! Candidate admissibility and the exact binding between its geometric
Coulomb energy, its contact multiplicities, and the one-variable function. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Thomson78.Eight

theorem gramEntry_lt_one (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (k : Fin 8) (hk : k ≠ 0) : gramEntry t k < 1 := by
  obtain ⟨hdb,hbc,hcq,hqa,_,_⟩ := contact_inequalities t hL hU
  have ha : a t < 1 := by dsimp [a]; linarith
  have hb : b t < 1 := by linarith
  have hc : c t < 1 := by linarith
  have hd : d t < 1 := by linarith
  fin_cases k <;> simp [gramEntry] at * <;> assumption

theorem candidate_injective (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25) :
    Function.Injective (candidate t) := by
  intro i j hij
  by_contra hne
  have ht : 0 ≤ t := by linarith
  have ht1 : t ≤ 1 := by linarith
  have hi := candidate_gram t ht ht1 i j
  rw [hij,real_inner_self_eq_norm_sq,candidate_unit t ht ht1 j] at hi
  have hk : j-i ≠ 0 := sub_ne_zero.mpr (fun he => hne he.symm)
  have hlt := gramEntry_lt_one t hL hU (j-i) hk
  norm_num at hi
  linarith

theorem candidate_admissible_interval (t : ℝ)
    (hL : (39:ℝ)/125 < t) (hU : t < 8/25) : Thomson78.Admissible (candidate t) := by
  exact ⟨candidate_unit t (by linarith) (by linarith),candidate_injective t hL hU⟩

theorem candidate_admissible : Thomson78.Admissible (candidate tStar) :=
  candidate_admissible_interval tStar tStar_bounds.1 tStar_bounds.2

/-- The twenty-eight pairs have multiplicities `8,4,8,8`. -/
theorem candidate_pairEnergy (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    Thomson78.pairEnergy f (candidate t)=8*f (a t)+4*f (b t)+8*f (c t)+8*f (d t) := by
  unfold Thomson78.pairEnergy Thomson78.gram
  simp_rw [candidate_gram t ht ht1]
  simp [Thomson78.pairs,Finset.sum_filter,Fintype.sum_prod_type,Fin.sum_univ_succ,gramEntry]
  ring

theorem candidate_coulombEnergy (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Thomson78.coulombEnergy (candidate t)=phi t := by
  rw [Thomson78.coulombEnergy_eq_pairEnergy _ (candidate_unit t ht.le ht1.le),
    candidate_pairEnergy _ t ht.le ht1.le,phi_eq_weighted_coulomb t ht ht1]

theorem candidate_tStar_energy : Thomson78.coulombEnergy (candidate tStar)=phi tStar :=
  candidate_coulombEnergy tStar tStar_mem.1 tStar_mem.2

end Thomson78.Eight

#print axioms Thomson78.Eight.candidate_admissible
#print axioms Thomson78.Eight.candidate_pairEnergy
#print axioms Thomson78.Eight.candidate_tStar_energy

