import Thomson78.SevenMinorantRemainder

noncomputable section
open scoped BigOperators
open Polynomial Set
namespace Thomson78.Seven
open Thomson78.Analysis

theorem omega7_pos {u : ℝ} (hu : ¬ Contact u) : 0 < omega7.eval u := by
  have hn : ∀ i : Fin 4, u ≠ nodes i := by
    intro i he
    apply hu
    fin_cases i
    · exact Or.inl he
    · exact Or.inr (Or.inr (Or.inr he))
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inl he))
  unfold omega7 omega
  rw [eval_pow]
  apply sq_pos_of_ne_zero
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  simpa using sub_ne_zero.mpr (hn i)

theorem H7_strict {u : ℝ} (hL : -1 ≤ u) (hU : u < 1) (hnot : ¬ Contact u) :
    H7.eval u < coulomb u := by
  have ha := contact_bounds
  have hn0 : u ≠ -1 := fun he => hnot (Or.inl he)
  have hn1 : u ≠ b := fun he => hnot (Or.inr (Or.inr (Or.inr he)))
  have hn2 : u ≠ 0 := fun he => hnot (Or.inr (Or.inl he))
  have hn3 : u ≠ a := fun he => hnot (Or.inr (Or.inr (Or.inl he)))
  have hw := omega7_pos hnot
  have hu : -1 < u := lt_of_le_of_ne hL hn0.symm
  have hh : ∃ ξ, ξ < 1 ∧ coulomb u - H7.eval u =
      coulombDerivative 9 ξ / (Nat.factorial 9) * (u+1) * omega7.eval u := by
    rcases lt_or_gt_of_ne hn1 with hb | hb
    · obtain ⟨ξ, hξ, he⟩ := H7_remainder_case0 u hu hb
      exact ⟨ξ, hξ.2.trans ha.2.2.2, he⟩
    rcases lt_or_gt_of_ne hn2 with hz | hz
    · obtain ⟨ξ, hξ, he⟩ := H7_remainder_case1 u hb hz
      exact ⟨ξ, hξ.2.trans ha.2.2.2, he⟩
    rcases lt_or_gt_of_ne hn3 with hap | hap
    · obtain ⟨ξ, hξ, he⟩ := H7_remainder_case2 u hz hap
      exact ⟨ξ, hξ.2.trans ha.2.2.2, he⟩
    · obtain ⟨ξ, hξ, he⟩ := H7_remainder_case3 u hap hU
      exact ⟨ξ, hξ.2.trans hU, he⟩
  obtain ⟨ξ, hξ, he⟩ := hh
  have hp := coulombDerivative_pos 9 ξ hξ
  have hplus : 0 < u+1 := by linarith
  have hpos : 0 < coulombDerivative 9 ξ / (Nat.factorial 9) * (u+1) * omega7.eval u := by positivity
  linarith

theorem H7_contact {u : ℝ} (hu : Contact u) : H7.eval u = coulomb u := by
  rcases hu with rfl | rfl | rfl | rfl
  · exact H7_value 0
  · exact H7_value 2
  · exact H7_value 3
  · exact H7_value 1

theorem H7_minorant {u : ℝ} (hL : -1 ≤ u) (hU : u < 1) : H7.eval u ≤ coulomb u := by
  by_cases hc : Contact u
  · exact (H7_contact hc).le
  · exact (H7_strict hL hU hc).le

theorem H7_equality_iff {u : ℝ} (hL : -1 ≤ u) (hU : u < 1) :
    H7.eval u = coulomb u ↔ Contact u := by
  constructor
  · intro he
    by_contra hc
    exact (ne_of_lt (H7_strict hL hU hc)) he
  · exact H7_contact

theorem h7_lt_H7 {u : ℝ} (hu : ¬ Contact u) : h7.eval u < H7.eval u := by
  have hw := omega7_pos hu
  have hg := gamma7_pos
  simp only [H7, eval_add, eval_mul, eval_C]
  exact lt_add_of_pos_right _ (mul_pos hg hw)

theorem h7_le_H7 (u : ℝ) : h7.eval u ≤ H7.eval u := by
  have hw := omega_nonneg nodes u
  have hg := gamma7_pos
  simp only [H7, eval_add, eval_mul, eval_C]
  have hw' : 0 ≤ omega7.eval u := hw
  nlinarith

theorem h7_minorant {u : ℝ} (hL : -1 ≤ u) (hU : u < 1) : h7.eval u ≤ coulomb u :=
  (h7_le_H7 u).trans (H7_minorant hL hU)

theorem h7_equality_iff {u : ℝ} (hL : -1 ≤ u) (hU : u < 1) :
    h7.eval u = coulomb u ↔ Contact u := by
  constructor
  · intro he
    by_contra hc
    have hh := (h7_le_H7 u).trans_lt (H7_strict hL hU hc)
    exact (ne_of_lt hh) he
  · intro hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact h7_value 0
    · exact h7_value 2
    · exact h7_value 3
    · exact h7_value 1

theorem H7_degree : H7.natDegree = 8 := by
  have hle := H7_degree_le
  by_contra hne
  have hlt : H7.natDegree < 8 := by omega
  have hz := iterate_derivative_eq_zero hlt
  rw [H7_eighth_derivative] at hz
  have hh := congrArg (fun p : ℝ[X] => p.eval 0) hz
  norm_num [Nat.factorial] at hh
  linarith [gamma7_pos]

/-- The ninth-order remainder also identifies the largest admissible endpoint
coefficient: near -1 its extra factor is u+1, while the derivative is bounded
above by its value at the last interpolation node. -/
theorem gamma7_maximal (c : ℝ) :
    (∀ u, -1 ≤ u → u < 1 → (h7 + C c * omega7).eval u ≤ coulomb u) ↔ c ≤ gamma7 := by
  constructor
  · intro hminor
    by_contra hle
    have hc : 0 < c-gamma7 := by linarith
    let M : ℝ := coulombDerivative 9 a / (Nat.factorial 9)
    have hM : 0 < M := by
      dsimp [M]
      exact div_pos (coulombDerivative_pos 9 a contact_bounds.2.2.2) (by positivity)
    let δ : ℝ := min ((b+1)/2) ((c-gamma7)/(2*M))
    have hb : 0 < b+1 := by linarith [contact_bounds.1]
    have hδ : 0 < δ := lt_min (by positivity) (by positivity)
    have hδb : δ < b+1 := by
      have hh := min_le_left ((b+1)/2) ((c-gamma7)/(2*M))
      dsimp [δ]
      linarith
    have hδM : δ*M < c-gamma7 := by
      have hh : δ ≤ (c-gamma7)/(2*M) := min_le_right _ _
      have hhm := (le_div_iff₀ (by positivity : 0 < 2*M)).mp hh
      nlinarith
    let u : ℝ := -1+δ
    have hL : -1 < u := by dsimp [u]; linarith
    have hB : u < b := by dsimp [u]; linarith
    have hU : u < 1 := hB.trans (lt_trans contact_bounds.2.1 (by norm_num))
    have hnot : ¬ Contact u := by
      intro hh
      have ha := contact_bounds
      rcases hh with hh | hh | hh | hh <;> linarith
    have hw := omega7_pos hnot
    obtain ⟨ξ, hξ, he⟩ := H7_remainder_case0 u hL hB
    have hlow := hminor u hL.le hU
    have hD : coulombDerivative 9 ξ / (Nat.factorial 9) ≤ M := by
      apply div_le_div_of_nonneg_right
      · exact (coulombDerivative_strictMono 9 ξ a hξ.2 contact_bounds.2.2.2).le
      · positivity
    have he' : coulomb u - (h7.eval u + gamma7 * omega7.eval u) =
        (coulombDerivative 9 ξ / (Nat.factorial 9) * δ) * omega7.eval u := by
      simpa only [H7, eval_add, eval_mul, eval_C,
        show u+1=δ by dsimp [u]; ring] using he
    simp only [eval_add, eval_mul, eval_C] at hlow
    have hprod : (c-gamma7) * omega7.eval u ≤
        (coulombDerivative 9 ξ / (Nat.factorial 9) * δ) * omega7.eval u := by nlinarith
    have hcoeff := (mul_le_mul_iff_left₀ hw).mp hprod
    have hupper := mul_le_mul_of_nonneg_right hD hδ.le
    nlinarith
  · intro hc u hL hU
    have hh := H7_minorant hL hU
    have hw : 0 ≤ omega7.eval u := omega_nonneg nodes u
    simp only [H7, eval_add, eval_mul, eval_C] at hh ⊢
    nlinarith

#print axioms gamma7_maximal

end Thomson78.Seven
