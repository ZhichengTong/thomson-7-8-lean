import Thomson78.AnalysisHermite
import Thomson78.AnalysisCoulomb
import Mathlib.Tactic.FinCases

/-! Four-node strict Hermite minorants for the Coulomb kernel. -/
noncomputable section
open scoped BigOperators
open Polynomial Set
namespace Thomson78.Analysis

private theorem four_remainder_case0
    (z₀ z₁ z₂ z₃ u : ℝ) (p : ℝ[X])
    (hz₀ : -1 ≤ z₀) (hz₁ : z₀ < z₁) (hz₂ : z₁ < z₂) (hz₃ : z₂ < z₃)
    (hz₄ : z₃ < 1) (hu₀ : -1 ≤ u) (hu₁ : u < 1) (hcase : u < z₀)
    (hp : p.natDegree ≤ 7)
    (hv₀ : p.eval z₀ = coulomb z₀) (hv₁ : p.eval z₁ = coulomb z₁)
    (hv₂ : p.eval z₂ = coulomb z₂) (hv₃ : p.eval z₃ = coulomb z₃)
    (hd₀ : p.derivative.eval z₀ = coulombDerivative 1 z₀)
    (hd₁ : p.derivative.eval z₁ = coulombDerivative 1 z₁)
    (hd₂ : p.derivative.eval z₂ = coulombDerivative 1 z₂)
    (hd₃ : p.derivative.eval z₃ = coulombDerivative 1 z₃) :
    ∃ ξ ∈ Ioo (-1 : ℝ) 1, coulomb u - p.eval u =
      coulombDerivative 8 ξ / (Nat.factorial 8) *
        ((u-z₀)*(u-z₁)*(u-z₂)*(u-z₃))^2 := by
  let x : Fin 9 → ℝ := ![u,z₀,z₀,z₁,z₁,z₂,z₂,z₃,z₃]
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith
  have hm : ∀ i, x i ∈ Icc (-1 : ℝ) z₃ := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith
  have hs : x 0 < x (Fin.last 8) := by norm_num [x]; linarith
  have hu : ∀ i, x i = x 0 → i = 0 := by
    intro i heq
    fin_cases i <;> norm_num [x] at * <;> linarith
  have hi : ∀ i j, i ≤ j → x i = x j → i ≠ 0 →
      coulombDerivative (j.val-i.val) (x i) =
        (derivative^[j.val-i.val] p).eval (x i) := by
    intro i j hij heq hne
    fin_cases i <;> fin_cases j <;>
      norm_num [x, Function.iterate_succ_apply', coulombDerivative_zero] at * <;>
      first | assumption | linarith
  obtain ⟨ξ, hξ, heq⟩ := hermite_remainder 8 coulombDerivative (-1) z₃ x 0 p hx hm hs hu
    (by omega) hi (fun k hk t ht => coulombDerivative_hasDerivAt k t (ht.2.trans_lt hz₄))
  refine ⟨ξ, ?_, ?_⟩
  · norm_num [x] at hξ
    constructor <;> linarith [hξ.1, hξ.2]
  · have huniv : (Finset.univ : Finset (Fin 9)) = {0,1,2,3,4,5,6,7,8} := by decide
    simp only [nodalPolynomial, eval_prod] at heq
    rw [huniv] at heq
    have herase : ({0,1,2,3,4,5,6,7,8} : Finset (Fin 9)).erase 0 = {1,2,3,4,5,6,7,8} := by decide
    rw [herase] at heq
    norm_num [x, coulombDerivative_zero] at heq
    convert heq using 1 <;> ring

private theorem four_remainder_case1
    (z₀ z₁ z₂ z₃ u : ℝ) (p : ℝ[X])
    (hz₀ : -1 ≤ z₀) (hz₁ : z₀ < z₁) (hz₂ : z₁ < z₂) (hz₃ : z₂ < z₃)
    (hz₄ : z₃ < 1) (hu₀ : -1 ≤ u) (hu₁ : u < 1) (hleft : z₀ < u) (hright : u < z₁)
    (hp : p.natDegree ≤ 7)
    (hv₀ : p.eval z₀ = coulomb z₀) (hv₁ : p.eval z₁ = coulomb z₁)
    (hv₂ : p.eval z₂ = coulomb z₂) (hv₃ : p.eval z₃ = coulomb z₃)
    (hd₀ : p.derivative.eval z₀ = coulombDerivative 1 z₀)
    (hd₁ : p.derivative.eval z₁ = coulombDerivative 1 z₁)
    (hd₂ : p.derivative.eval z₂ = coulombDerivative 1 z₂)
    (hd₃ : p.derivative.eval z₃ = coulombDerivative 1 z₃) :
    ∃ ξ ∈ Ioo (-1 : ℝ) 1, coulomb u - p.eval u =
      coulombDerivative 8 ξ / (Nat.factorial 8) *
        ((u-z₀)*(u-z₁)*(u-z₂)*(u-z₃))^2 := by
  let x : Fin 9 → ℝ := ![z₀,z₀,u,z₁,z₁,z₂,z₂,z₃,z₃]
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith
  have hm : ∀ i, x i ∈ Icc (-1 : ℝ) z₃ := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith
  have hs : x 0 < x (Fin.last 8) := by norm_num [x]; linarith
  have hu : ∀ i, x i = x 2 → i = 2 := by
    intro i heq
    fin_cases i <;> norm_num [x] at * <;> linarith
  have hi : ∀ i j, i ≤ j → x i = x j → i ≠ 2 →
      coulombDerivative (j.val-i.val) (x i) =
        (derivative^[j.val-i.val] p).eval (x i) := by
    intro i j hij heq hne
    fin_cases i <;> fin_cases j <;>
      norm_num [x, Function.iterate_succ_apply', coulombDerivative_zero] at * <;>
      first | assumption | linarith
  obtain ⟨ξ, hξ, heq⟩ := hermite_remainder 8 coulombDerivative (-1) z₃ x 2 p hx hm hs hu
    (by omega) hi (fun k hk t ht => coulombDerivative_hasDerivAt k t (ht.2.trans_lt hz₄))
  refine ⟨ξ, ?_, ?_⟩
  · norm_num [x] at hξ
    constructor <;> linarith [hξ.1, hξ.2]
  · have huniv : (Finset.univ : Finset (Fin 9)) = {0,1,2,3,4,5,6,7,8} := by decide
    simp only [nodalPolynomial, eval_prod] at heq
    rw [huniv] at heq
    have herase : ({0,1,2,3,4,5,6,7,8} : Finset (Fin 9)).erase 2 = {0,1,3,4,5,6,7,8} := by decide
    rw [herase] at heq
    norm_num [x, coulombDerivative_zero] at heq
    convert heq using 1 <;> ring

private theorem four_remainder_case2
    (z₀ z₁ z₂ z₃ u : ℝ) (p : ℝ[X])
    (hz₀ : -1 ≤ z₀) (hz₁ : z₀ < z₁) (hz₂ : z₁ < z₂) (hz₃ : z₂ < z₃)
    (hz₄ : z₃ < 1) (hu₀ : -1 ≤ u) (hu₁ : u < 1) (hleft : z₁ < u) (hright : u < z₂)
    (hp : p.natDegree ≤ 7)
    (hv₀ : p.eval z₀ = coulomb z₀) (hv₁ : p.eval z₁ = coulomb z₁)
    (hv₂ : p.eval z₂ = coulomb z₂) (hv₃ : p.eval z₃ = coulomb z₃)
    (hd₀ : p.derivative.eval z₀ = coulombDerivative 1 z₀)
    (hd₁ : p.derivative.eval z₁ = coulombDerivative 1 z₁)
    (hd₂ : p.derivative.eval z₂ = coulombDerivative 1 z₂)
    (hd₃ : p.derivative.eval z₃ = coulombDerivative 1 z₃) :
    ∃ ξ ∈ Ioo (-1 : ℝ) 1, coulomb u - p.eval u =
      coulombDerivative 8 ξ / (Nat.factorial 8) *
        ((u-z₀)*(u-z₁)*(u-z₂)*(u-z₃))^2 := by
  let x : Fin 9 → ℝ := ![z₀,z₀,z₁,z₁,u,z₂,z₂,z₃,z₃]
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith
  have hm : ∀ i, x i ∈ Icc (-1 : ℝ) z₃ := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith
  have hs : x 0 < x (Fin.last 8) := by norm_num [x]; linarith
  have hu : ∀ i, x i = x 4 → i = 4 := by
    intro i heq
    fin_cases i <;> norm_num [x] at * <;> linarith
  have hi : ∀ i j, i ≤ j → x i = x j → i ≠ 4 →
      coulombDerivative (j.val-i.val) (x i) =
        (derivative^[j.val-i.val] p).eval (x i) := by
    intro i j hij heq hne
    fin_cases i <;> fin_cases j <;>
      norm_num [x, Function.iterate_succ_apply', coulombDerivative_zero] at * <;>
      first | assumption | linarith
  obtain ⟨ξ, hξ, heq⟩ := hermite_remainder 8 coulombDerivative (-1) z₃ x 4 p hx hm hs hu
    (by omega) hi (fun k hk t ht => coulombDerivative_hasDerivAt k t (ht.2.trans_lt hz₄))
  refine ⟨ξ, ?_, ?_⟩
  · norm_num [x] at hξ
    constructor <;> linarith [hξ.1, hξ.2]
  · have huniv : (Finset.univ : Finset (Fin 9)) = {0,1,2,3,4,5,6,7,8} := by decide
    simp only [nodalPolynomial, eval_prod] at heq
    rw [huniv] at heq
    have herase : ({0,1,2,3,4,5,6,7,8} : Finset (Fin 9)).erase 4 = {0,1,2,3,5,6,7,8} := by decide
    rw [herase] at heq
    norm_num [x, coulombDerivative_zero] at heq
    convert heq using 1 <;> ring

private theorem four_remainder_case3
    (z₀ z₁ z₂ z₃ u : ℝ) (p : ℝ[X])
    (hz₀ : -1 ≤ z₀) (hz₁ : z₀ < z₁) (hz₂ : z₁ < z₂) (hz₃ : z₂ < z₃)
    (hz₄ : z₃ < 1) (hu₀ : -1 ≤ u) (hu₁ : u < 1) (hleft : z₂ < u) (hright : u < z₃)
    (hp : p.natDegree ≤ 7)
    (hv₀ : p.eval z₀ = coulomb z₀) (hv₁ : p.eval z₁ = coulomb z₁)
    (hv₂ : p.eval z₂ = coulomb z₂) (hv₃ : p.eval z₃ = coulomb z₃)
    (hd₀ : p.derivative.eval z₀ = coulombDerivative 1 z₀)
    (hd₁ : p.derivative.eval z₁ = coulombDerivative 1 z₁)
    (hd₂ : p.derivative.eval z₂ = coulombDerivative 1 z₂)
    (hd₃ : p.derivative.eval z₃ = coulombDerivative 1 z₃) :
    ∃ ξ ∈ Ioo (-1 : ℝ) 1, coulomb u - p.eval u =
      coulombDerivative 8 ξ / (Nat.factorial 8) *
        ((u-z₀)*(u-z₁)*(u-z₂)*(u-z₃))^2 := by
  let x : Fin 9 → ℝ := ![z₀,z₀,z₁,z₁,z₂,z₂,u,z₃,z₃]
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith
  have hm : ∀ i, x i ∈ Icc (-1 : ℝ) z₃ := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith
  have hs : x 0 < x (Fin.last 8) := by norm_num [x]; linarith
  have hu : ∀ i, x i = x 6 → i = 6 := by
    intro i heq
    fin_cases i <;> norm_num [x] at * <;> linarith
  have hi : ∀ i j, i ≤ j → x i = x j → i ≠ 6 →
      coulombDerivative (j.val-i.val) (x i) =
        (derivative^[j.val-i.val] p).eval (x i) := by
    intro i j hij heq hne
    fin_cases i <;> fin_cases j <;>
      norm_num [x, Function.iterate_succ_apply', coulombDerivative_zero] at * <;>
      first | assumption | linarith
  obtain ⟨ξ, hξ, heq⟩ := hermite_remainder 8 coulombDerivative (-1) z₃ x 6 p hx hm hs hu
    (by omega) hi (fun k hk t ht => coulombDerivative_hasDerivAt k t (ht.2.trans_lt hz₄))
  refine ⟨ξ, ?_, ?_⟩
  · norm_num [x] at hξ
    constructor <;> linarith [hξ.1, hξ.2]
  · have huniv : (Finset.univ : Finset (Fin 9)) = {0,1,2,3,4,5,6,7,8} := by decide
    simp only [nodalPolynomial, eval_prod] at heq
    rw [huniv] at heq
    have herase : ({0,1,2,3,4,5,6,7,8} : Finset (Fin 9)).erase 6 = {0,1,2,3,4,5,7,8} := by decide
    rw [herase] at heq
    norm_num [x, coulombDerivative_zero] at heq
    convert heq using 1 <;> ring

private theorem four_remainder_case4
    (z₀ z₁ z₂ z₃ u : ℝ) (p : ℝ[X])
    (hz₀ : -1 ≤ z₀) (hz₁ : z₀ < z₁) (hz₂ : z₁ < z₂) (hz₃ : z₂ < z₃)
    (hz₄ : z₃ < 1) (hu₀ : -1 ≤ u) (hu₁ : u < 1) (hcase : z₃ < u)
    (hp : p.natDegree ≤ 7)
    (hv₀ : p.eval z₀ = coulomb z₀) (hv₁ : p.eval z₁ = coulomb z₁)
    (hv₂ : p.eval z₂ = coulomb z₂) (hv₃ : p.eval z₃ = coulomb z₃)
    (hd₀ : p.derivative.eval z₀ = coulombDerivative 1 z₀)
    (hd₁ : p.derivative.eval z₁ = coulombDerivative 1 z₁)
    (hd₂ : p.derivative.eval z₂ = coulombDerivative 1 z₂)
    (hd₃ : p.derivative.eval z₃ = coulombDerivative 1 z₃) :
    ∃ ξ ∈ Ioo (-1 : ℝ) 1, coulomb u - p.eval u =
      coulombDerivative 8 ξ / (Nat.factorial 8) *
        ((u-z₀)*(u-z₁)*(u-z₂)*(u-z₃))^2 := by
  let x : Fin 9 → ℝ := ![z₀,z₀,z₁,z₁,z₂,z₂,z₃,z₃,u]
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith
  have hm : ∀ i, x i ∈ Icc (-1 : ℝ) u := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith
  have hs : x 0 < x (Fin.last 8) := by norm_num [x]; linarith
  have hu : ∀ i, x i = x 8 → i = 8 := by
    intro i heq
    fin_cases i <;> norm_num [x] at * <;> linarith
  have hi : ∀ i j, i ≤ j → x i = x j → i ≠ 8 →
      coulombDerivative (j.val-i.val) (x i) =
        (derivative^[j.val-i.val] p).eval (x i) := by
    intro i j hij heq hne
    fin_cases i <;> fin_cases j <;>
      norm_num [x, Function.iterate_succ_apply', coulombDerivative_zero] at * <;>
      first | assumption | linarith
  obtain ⟨ξ, hξ, heq⟩ := hermite_remainder 8 coulombDerivative (-1) u x 8 p hx hm hs hu
    (by omega) hi (fun k hk t ht => coulombDerivative_hasDerivAt k t (ht.2.trans_lt hu₁))
  refine ⟨ξ, ?_, ?_⟩
  · norm_num [x] at hξ
    constructor <;> linarith [hξ.1, hξ.2]
  · have huniv : (Finset.univ : Finset (Fin 9)) = {0,1,2,3,4,5,6,7,8} := by decide
    simp only [nodalPolynomial, eval_prod] at heq
    rw [huniv] at heq
    have herase : ({0,1,2,3,4,5,6,7,8} : Finset (Fin 9)).erase 8 = {0,1,2,3,4,5,6,7} := by decide
    rw [herase] at heq
    norm_num [x, coulombDerivative_zero] at heq
    convert heq using 1 <;> ring

/-- Degree-seven Hermite remainder for any four ordered nodes in `[-1,1)`.
The evaluation point is distinct from the four interpolation nodes. -/
theorem four_node_remainder
    (z₀ z₁ z₂ z₃ u : ℝ) (p : ℝ[X])
    (hz₀ : -1 ≤ z₀) (hz₁ : z₀ < z₁) (hz₂ : z₁ < z₂) (hz₃ : z₂ < z₃)
    (hz₄ : z₃ < 1) (hu₀ : -1 ≤ u) (hu₁ : u < 1)
    (hne₀ : u ≠ z₀) (hne₁ : u ≠ z₁) (hne₂ : u ≠ z₂) (hne₃ : u ≠ z₃)
    (hp : p.natDegree ≤ 7)
    (hv₀ : p.eval z₀ = coulomb z₀) (hv₁ : p.eval z₁ = coulomb z₁)
    (hv₂ : p.eval z₂ = coulomb z₂) (hv₃ : p.eval z₃ = coulomb z₃)
    (hd₀ : p.derivative.eval z₀ = coulombDerivative 1 z₀)
    (hd₁ : p.derivative.eval z₁ = coulombDerivative 1 z₁)
    (hd₂ : p.derivative.eval z₂ = coulombDerivative 1 z₂)
    (hd₃ : p.derivative.eval z₃ = coulombDerivative 1 z₃) :
    ∃ ξ ∈ Ioo (-1 : ℝ) 1, coulomb u - p.eval u =
      coulombDerivative 8 ξ / (Nat.factorial 8) *
        ((u-z₀)*(u-z₁)*(u-z₂)*(u-z₃))^2 := by
  rcases lt_or_gt_of_ne hne₀ with h0 | h0
  · exact four_remainder_case0 z₀ z₁ z₂ z₃ u p hz₀ hz₁ hz₂ hz₃ hz₄ hu₀ hu₁ h0
      hp hv₀ hv₁ hv₂ hv₃ hd₀ hd₁ hd₂ hd₃
  rcases lt_or_gt_of_ne hne₁ with h1 | h1
  · exact four_remainder_case1 z₀ z₁ z₂ z₃ u p hz₀ hz₁ hz₂ hz₃ hz₄ hu₀ hu₁ h0 h1
      hp hv₀ hv₁ hv₂ hv₃ hd₀ hd₁ hd₂ hd₃
  rcases lt_or_gt_of_ne hne₂ with h2 | h2
  · exact four_remainder_case2 z₀ z₁ z₂ z₃ u p hz₀ hz₁ hz₂ hz₃ hz₄ hu₀ hu₁ h1 h2
      hp hv₀ hv₁ hv₂ hv₃ hd₀ hd₁ hd₂ hd₃
  rcases lt_or_gt_of_ne hne₃ with h3 | h3
  · exact four_remainder_case3 z₀ z₁ z₂ z₃ u p hz₀ hz₁ hz₂ hz₃ hz₄ hu₀ hu₁ h2 h3
      hp hv₀ hv₁ hv₂ hv₃ hd₀ hd₁ hd₂ hd₃
  · exact four_remainder_case4 z₀ z₁ z₂ z₃ u p hz₀ hz₁ hz₂ hz₃ hz₄ hu₀ hu₁ h3
      hp hv₀ hv₁ hv₂ hv₃ hd₀ hd₁ hd₂ hd₃


end Thomson78.Analysis
