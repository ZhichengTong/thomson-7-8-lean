import Thomson78.AnalysisFourRemainder

/-! Strict degree-seven and degree-eight Coulomb minorants. -/
noncomputable section
open Polynomial Set
open scoped BigOperators
namespace Thomson78.Analysis

/-- Every correction coefficient up to the eighth derivative at `-1` gives a
strict minorant with exactly the four interpolation contacts. -/
theorem four_node_strict_minorant
    (z₀ z₁ z₂ z₃ u γ : ℝ) (p : ℝ[X])
    (hz₀ : -1 ≤ z₀) (hz₁ : z₀ < z₁) (hz₂ : z₁ < z₂) (hz₃ : z₂ < z₃)
    (hz₄ : z₃ < 1) (hu₀ : -1 ≤ u) (hu₁ : u < 1)
    (hγ : γ ≤ 6435/16777216) (hp : p.natDegree ≤ 7)
    (hv₀ : p.eval z₀ = coulomb z₀) (hv₁ : p.eval z₁ = coulomb z₁)
    (hv₂ : p.eval z₂ = coulomb z₂) (hv₃ : p.eval z₃ = coulomb z₃)
    (hd₀ : p.derivative.eval z₀ = coulombDerivative 1 z₀)
    (hd₁ : p.derivative.eval z₁ = coulombDerivative 1 z₁)
    (hd₂ : p.derivative.eval z₂ = coulombDerivative 1 z₂)
    (hd₃ : p.derivative.eval z₃ = coulombDerivative 1 z₃) :
    p.eval u + γ*((u-z₀)*(u-z₁)*(u-z₂)*(u-z₃))^2 ≤ coulomb u ∧
    (p.eval u + γ*((u-z₀)*(u-z₁)*(u-z₂)*(u-z₃))^2 = coulomb u ↔
      u = z₀ ∨ u = z₁ ∨ u = z₂ ∨ u = z₃) := by
  by_cases hcontact : u = z₀ ∨ u = z₁ ∨ u = z₂ ∨ u = z₃
  · rcases hcontact with h | h | h | h <;> subst u <;> simp [hv₀, hv₁, hv₂, hv₃]
  · have hn₀ : u ≠ z₀ := fun h => hcontact (Or.inl h)
    have hn₁ : u ≠ z₁ := fun h => hcontact (Or.inr (Or.inl h))
    have hn₂ : u ≠ z₂ := fun h => hcontact (Or.inr (Or.inr (Or.inl h)))
    have hn₃ : u ≠ z₃ := fun h => hcontact (Or.inr (Or.inr (Or.inr h)))
    obtain ⟨ξ, hξ, heq⟩ := four_node_remainder z₀ z₁ z₂ z₃ u p hz₀ hz₁ hz₂ hz₃ hz₄
      hu₀ hu₁ hn₀ hn₁ hn₂ hn₃ hp hv₀ hv₁ hv₂ hv₃ hd₀ hd₁ hd₂ hd₃
    have hder := coulombDerivative_strictMono 8 (-1) ξ hξ.1 hξ.2
    have hcoeff : (6435/16777216 : ℝ) < coulombDerivative 8 ξ / ↑(Nat.factorial 8) := by
      rw [← coulombDerivative_eight_endpoint]
      exact (div_lt_div_iff_of_pos_right (by norm_num [Nat.factorial])).2 hder
    have hprod : 0 < ((u-z₀)*(u-z₁)*(u-z₂)*(u-z₃))^2 :=
      sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hn₀)
        (sub_ne_zero.mpr hn₁)) (sub_ne_zero.mpr hn₂)) (sub_ne_zero.mpr hn₃))
    have hless := mul_lt_mul_of_pos_right (hγ.trans_lt hcoeff) hprod
    rw [← heq] at hless
    have hstrict : p.eval u + γ*((u-z₀)*(u-z₁)*(u-z₂)*(u-z₃))^2 < coulomb u := by
      simpa only [add_comm] using (lt_sub_iff_add_lt.mp hless)
    exact ⟨hstrict.le, iff_of_false (ne_of_lt hstrict) hcontact⟩

/-- The auxiliary degree-seven polynomial determined by four Coulomb contacts. -/
def hermiteCoulomb (z : Fin 4 → ℝ) : ℝ[X] :=
  hermite z (fun i => coulomb (z i)) (fun i => coulombDerivative 1 (z i))

/-- The degree-eight minorant used for eight points in the manuscript. -/
def correctedHermite (z : Fin 4 → ℝ) : ℝ[X] :=
  hermiteCoulomb z + C (6435/16777216) * omega z

theorem hermiteCoulomb_degree (z : Fin 4 → ℝ) (hz : Function.Injective z) :
    (hermiteCoulomb z).natDegree ≤ 7 := hermite_natDegree_le _ _ _ hz

theorem hermiteCoulomb_eval (z : Fin 4 → ℝ) (hz : Function.Injective z) (i : Fin 4) :
    (hermiteCoulomb z).eval (z i) = coulomb (z i) := hermite_eval _ _ _ hz i

theorem hermiteCoulomb_derivative_eval (z : Fin 4 → ℝ) (hz : Function.Injective z) (i : Fin 4) :
    (hermiteCoulomb z).derivative.eval (z i) = coulombDerivative 1 (z i) :=
  hermite_derivative_eval _ _ _ hz i

theorem omega_eval_four (z : Fin 4 → ℝ) (u : ℝ) :
    (omega z).eval u = ((u-z 0)*(u-z 1)*(u-z 2)*(u-z 3))^2 := by
  simp [omega, eval_prod, Fin.prod_univ_succ]
  ring

theorem omega_degree (z : Fin 4 → ℝ) : (omega z).natDegree = 8 := by
  have hp : (∏ i : Fin 4, (X-C (z i) : ℝ[X])).natDegree = 4 := by
    rw [natDegree_prod_of_monic _ _ (fun i hi => monic_X_sub_C _)]
    simp
  simp only [omega, natDegree_pow, hp]

theorem correctedHermite_degree (z : Fin 4 → ℝ) (hz : Function.Injective z) :
    (correctedHermite z).natDegree ≤ 8 := by
  apply natDegree_add_le_of_degree_le
  · exact (hermiteCoulomb_degree z hz).trans (by decide)
  · calc
      _ ≤ (C (6435/16777216 : ℝ)).natDegree + (omega z).natDegree := natDegree_mul_le
      _ = 8 := by simp only [natDegree_C, omega_degree, zero_add]

theorem correctedHermite_degree_exact (z : Fin 4 → ℝ) (hz : Function.Injective z) :
    (correctedHermite z).natDegree = 8 := by
  have hcor : (C (6435/16777216 : ℝ) * omega z).natDegree = 8 := by
    rw [natDegree_C_mul (by norm_num), omega_degree]
  have hlt : (hermiteCoulomb z).natDegree < (C (6435/16777216 : ℝ)*omega z).natDegree := by
    rw [hcor]
    exact (hermiteCoulomb_degree z hz).trans_lt (by decide)
  rw [correctedHermite, natDegree_add_eq_right_of_natDegree_lt hlt, hcor]

theorem correctedHermite_eval (z : Fin 4 → ℝ) (hz : Function.Injective z) (i : Fin 4) :
    (correctedHermite z).eval (z i) = coulomb (z i) := by
  exact (correction_preserves_contacts z _ _ hz (6435/16777216) i).1

theorem correctedHermite_derivative_eval (z : Fin 4 → ℝ) (hz : Function.Injective z)
    (i : Fin 4) : (correctedHermite z).derivative.eval (z i) = coulombDerivative 1 (z i) := by
  exact (correction_preserves_contacts z _ _ hz (6435/16777216) i).2

theorem correctedHermite_strict_minorant (z : Fin 4 → ℝ) (hz : StrictMono z)
    (hz₀ : -1 ≤ z 0) (hz₃ : z 3 < 1) (u : ℝ) (hu₀ : -1 ≤ u) (hu₁ : u < 1) :
    (correctedHermite z).eval u ≤ coulomb u ∧
      ((correctedHermite z).eval u = coulomb u ↔
        u = z 0 ∨ u = z 1 ∨ u = z 2 ∨ u = z 3) := by
  have h := four_node_strict_minorant (z 0) (z 1) (z 2) (z 3) u (6435/16777216)
    (hermiteCoulomb z) hz₀ (hz (by decide)) (hz (by decide)) (hz (by decide)) hz₃
    hu₀ hu₁ le_rfl (hermiteCoulomb_degree z hz.injective)
    (hermiteCoulomb_eval z hz.injective 0) (hermiteCoulomb_eval z hz.injective 1)
    (hermiteCoulomb_eval z hz.injective 2) (hermiteCoulomb_eval z hz.injective 3)
    (hermiteCoulomb_derivative_eval z hz.injective 0)
    (hermiteCoulomb_derivative_eval z hz.injective 1)
    (hermiteCoulomb_derivative_eval z hz.injective 2)
    (hermiteCoulomb_derivative_eval z hz.injective 3)
  simpa only [correctedHermite, eval_add, eval_mul, eval_C, omega_eval_four] using h

theorem hermiteCoulomb_strict_minorant (z : Fin 4 → ℝ) (hz : StrictMono z)
    (hz₀ : -1 ≤ z 0) (hz₃ : z 3 < 1) (u : ℝ) (hu₀ : -1 ≤ u) (hu₁ : u < 1) :
    (hermiteCoulomb z).eval u ≤ coulomb u ∧
      ((hermiteCoulomb z).eval u = coulomb u ↔
        u = z 0 ∨ u = z 1 ∨ u = z 2 ∨ u = z 3) := by
  have h := four_node_strict_minorant (z 0) (z 1) (z 2) (z 3) u 0
    (hermiteCoulomb z) hz₀ (hz (by decide)) (hz (by decide)) (hz (by decide)) hz₃
    hu₀ hu₁ (by norm_num) (hermiteCoulomb_degree z hz.injective)
    (hermiteCoulomb_eval z hz.injective 0) (hermiteCoulomb_eval z hz.injective 1)
    (hermiteCoulomb_eval z hz.injective 2) (hermiteCoulomb_eval z hz.injective 3)
    (hermiteCoulomb_derivative_eval z hz.injective 0)
    (hermiteCoulomb_derivative_eval z hz.injective 1)
    (hermiteCoulomb_derivative_eval z hz.injective 2)
    (hermiteCoulomb_derivative_eval z hz.injective 3)
  simpa using h

end Thomson78.Analysis
