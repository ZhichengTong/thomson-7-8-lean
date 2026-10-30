import Thomson78.AnalysisHermite
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FinCases

/-! Uniqueness of the four-node Hermite interpolant. -/
noncomputable section
open Polynomial Set
namespace Thomson78.Analysis

/-- Eight value-and-slope conditions uniquely determine a polynomial of degree
at most seven. The proof uses the general Hermite remainder for a polynomial. -/
theorem four_double_interpolation_unique (z : Fin 4 → ℝ) (hz : StrictMono z)
    (p q : ℝ[X]) (hp : p.natDegree ≤ 7) (hq : q.natDegree ≤ 7)
    (hv : ∀ i, p.eval (z i) = q.eval (z i))
    (hd : ∀ i, p.derivative.eval (z i) = q.derivative.eval (z i)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioo_infinite (show z 0 - 1 < z 0 by linarith)).mono
  intro u hu
  have hz₁ := hz (show (0 : Fin 4) < 1 by decide)
  have hz₂ := hz (show (1 : Fin 4) < 2 by decide)
  have hz₃ := hz (show (2 : Fin 4) < 3 by decide)
  let x : Fin 9 → ℝ := ![u,z 0,z 0,z 1,z 1,z 2,z 2,z 3,z 3]
  let f : ℕ → ℝ → ℝ := fun k t => (derivative^[k] p).eval t
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith [hu.2]
  have hm : ∀ i, x i ∈ Icc u (z 3) := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith [hu.2]
  have hs : x 0 < x (Fin.last 8) := by norm_num [x]; linarith [hu.2]
  have hu' : ∀ i, x i = x 0 → i = 0 := by
    intro i heq
    fin_cases i <;> norm_num [x] at heq ⊢ <;> linarith [hu.2]
  have hv₀ := hv 0
  have hv₁ := hv 1
  have hv₂ := hv 2
  have hv₃ := hv 3
  have hd₀ := hd 0
  have hd₁ := hd 1
  have hd₂ := hd 2
  have hd₃ := hd 3
  have hi : ∀ i j, i ≤ j → x i = x j → i ≠ 0 →
      f (j.val-i.val) (x i) = (derivative^[j.val-i.val] q).eval (x i) := by
    intro i j hij heq hne
    fin_cases i <;> fin_cases j
    all_goals norm_num [x, f, Function.iterate_succ_apply'] at hij
    all_goals norm_num [x, f, Function.iterate_succ_apply'] at heq
    all_goals norm_num [x, f, Function.iterate_succ_apply'] at hne
    all_goals norm_num [x, f, Function.iterate_succ_apply']
    all_goals first
      | solve | simp only [hv₀,hv₁,hv₂,hv₃,hd₀,hd₁,hd₂,hd₃]
      | linarith only [hz₁,hz₂,hz₃,hu.2,heq]
  have hderiv : ∀ k < 8, ∀ t ∈ Icc u (z 3), HasDerivAt (f k) (f (k+1) t) t := by
    intro k hk t ht
    convert ((derivative^[k] p).hasDerivAt t) using 1 <;>
      simp only [f, Function.iterate_succ_apply']
  obtain ⟨ξ,hξ,he⟩ := hermite_remainder 8 f u (z 3) x 0 q hx hm hs hu' (by omega) hi hderiv
  have hp0 : derivative^[8] p = 0 := iterate_derivative_eq_zero (by omega)
  change p.eval u - q.eval u = (derivative^[8] p).eval ξ / (Nat.factorial 8) *
    (nodalPolynomial x 0).eval u at he
  rw [hp0] at he
  norm_num at he
  exact sub_eq_zero.mp he

/-- Existence and uniqueness of the degree-seven interpolant at four ordered nodes. -/
theorem hermite_unique (z v d : Fin 4 → ℝ) (hz : StrictMono z)
    (p : ℝ[X]) (hp : p.natDegree ≤ 7)
    (hv : ∀ i, p.eval (z i) = v i)
    (hd : ∀ i, p.derivative.eval (z i) = d i) : p = hermite z v d := by
  apply four_double_interpolation_unique z hz p _ hp (hermite_natDegree_le z v d hz.injective)
  · intro i
    rw [hv i, hermite_eval z v d hz.injective i]
  · intro i
    rw [hd i, hermite_derivative_eval z v d hz.injective i]

end Thomson78.Analysis
