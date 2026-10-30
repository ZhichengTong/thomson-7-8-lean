import Thomson78.SevenMinorant

noncomputable section
open scoped BigOperators
open Polynomial Set
namespace Thomson78.Seven
open Thomson78.Analysis

theorem H7_remainder_case0 (u : ℝ) (hL : -1 < u) (hU : u < b) :
    ∃ ξ ∈ Ioo (-1 : ℝ) a, coulomb u - H7.eval u =
      coulombDerivative 9 ξ / (Nat.factorial 9) * (u+1) * omega7.eval u := by
  let x : Fin 10 → ℝ := ![-1,-1,-1,u,b,b,0,0,a,a]
  have ha := contact_bounds
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith
  have hm : ∀ i, x i ∈ Icc (-1 : ℝ) a := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith
  have hs : x 0 < x (Fin.last 9) := by norm_num [x]; linarith
  have hu : ∀ i, x i = x 3 → i = 3 := by
    intro i heq
    fin_cases i <;> norm_num [x] at * <;> linarith
  have hv0 := H7_value 0
  have hv1 := H7_value 1
  have hv2 := H7_value 2
  have hv3 := H7_value 3
  have hd0 := H7_slope 0
  have hd1 := H7_slope 1
  have hd2 := H7_slope 2
  have hd3 := H7_slope 3
  have hdd := H7_second_endpoint
  norm_num [nodes] at hv0 hv1 hv2 hv3 hd0 hd1 hd2 hd3
  have hi : ∀ i j, i ≤ j → x i = x j → i ≠ 3 →
      coulombDerivative (j.val-i.val) (x i) =
        (derivative^[j.val-i.val] H7).eval (x i) := by
    intro i j hij heq hne
    fin_cases i <;> fin_cases j <;>
      norm_num [x, Function.iterate_succ_apply', coulombDerivative_zero] at * <;>
      first | assumption | linarith
  have htop : a < 1 := by linarith
  obtain ⟨ξ, hξ, heq⟩ := hermite_remainder 9 coulombDerivative (-1) a x 3 H7
    hx hm hs hu (by have := H7_degree_le; omega) hi
    (fun k hk t ht => coulombDerivative_hasDerivAt k t (ht.2.trans_lt htop))
  refine ⟨ξ, ?_, ?_⟩
  · simpa [x] using hξ
  · have huniv : (Finset.univ : Finset (Fin 10)) = {0,1,2,3,4,5,6,7,8,9} := by decide
    simp only [nodalPolynomial, eval_prod] at heq
    rw [huniv] at heq
    have herase : ({0,1,2,3,4,5,6,7,8,9} : Finset (Fin 10)).erase 3 = {0,1,2,4,5,6,7,8,9} := by decide
    rw [herase] at heq
    norm_num [x, coulombDerivative_zero] at heq
    norm_num [omega7, omega, nodes, Fin.prod_univ_succ]
    convert heq using 1 <;> ring

theorem H7_remainder_case1 (u : ℝ) (hL : b < u) (hU : u < 0) :
    ∃ ξ ∈ Ioo (-1 : ℝ) a, coulomb u - H7.eval u =
      coulombDerivative 9 ξ / (Nat.factorial 9) * (u+1) * omega7.eval u := by
  let x : Fin 10 → ℝ := ![-1,-1,-1,b,b,u,0,0,a,a]
  have ha := contact_bounds
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith
  have hm : ∀ i, x i ∈ Icc (-1 : ℝ) a := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith
  have hs : x 0 < x (Fin.last 9) := by norm_num [x]; linarith
  have hu : ∀ i, x i = x 5 → i = 5 := by
    intro i heq
    fin_cases i <;> norm_num [x] at * <;> linarith
  have hv0 := H7_value 0
  have hv1 := H7_value 1
  have hv2 := H7_value 2
  have hv3 := H7_value 3
  have hd0 := H7_slope 0
  have hd1 := H7_slope 1
  have hd2 := H7_slope 2
  have hd3 := H7_slope 3
  have hdd := H7_second_endpoint
  norm_num [nodes] at hv0 hv1 hv2 hv3 hd0 hd1 hd2 hd3
  have hi : ∀ i j, i ≤ j → x i = x j → i ≠ 5 →
      coulombDerivative (j.val-i.val) (x i) =
        (derivative^[j.val-i.val] H7).eval (x i) := by
    intro i j hij heq hne
    fin_cases i <;> fin_cases j <;>
      norm_num [x, Function.iterate_succ_apply', coulombDerivative_zero] at * <;>
      first | assumption | linarith
  have htop : a < 1 := by linarith
  obtain ⟨ξ, hξ, heq⟩ := hermite_remainder 9 coulombDerivative (-1) a x 5 H7
    hx hm hs hu (by have := H7_degree_le; omega) hi
    (fun k hk t ht => coulombDerivative_hasDerivAt k t (ht.2.trans_lt htop))
  refine ⟨ξ, ?_, ?_⟩
  · simpa [x] using hξ
  · have huniv : (Finset.univ : Finset (Fin 10)) = {0,1,2,3,4,5,6,7,8,9} := by decide
    simp only [nodalPolynomial, eval_prod] at heq
    rw [huniv] at heq
    have herase : ({0,1,2,3,4,5,6,7,8,9} : Finset (Fin 10)).erase 5 = {0,1,2,3,4,6,7,8,9} := by decide
    rw [herase] at heq
    norm_num [x, coulombDerivative_zero] at heq
    norm_num [omega7, omega, nodes, Fin.prod_univ_succ]
    convert heq using 1 <;> ring

theorem H7_remainder_case2 (u : ℝ) (hL : 0 < u) (hU : u < a) :
    ∃ ξ ∈ Ioo (-1 : ℝ) a, coulomb u - H7.eval u =
      coulombDerivative 9 ξ / (Nat.factorial 9) * (u+1) * omega7.eval u := by
  let x : Fin 10 → ℝ := ![-1,-1,-1,b,b,0,0,u,a,a]
  have ha := contact_bounds
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith
  have hm : ∀ i, x i ∈ Icc (-1 : ℝ) a := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith
  have hs : x 0 < x (Fin.last 9) := by norm_num [x]; linarith
  have hu : ∀ i, x i = x 7 → i = 7 := by
    intro i heq
    fin_cases i <;> norm_num [x] at * <;> linarith
  have hv0 := H7_value 0
  have hv1 := H7_value 1
  have hv2 := H7_value 2
  have hv3 := H7_value 3
  have hd0 := H7_slope 0
  have hd1 := H7_slope 1
  have hd2 := H7_slope 2
  have hd3 := H7_slope 3
  have hdd := H7_second_endpoint
  norm_num [nodes] at hv0 hv1 hv2 hv3 hd0 hd1 hd2 hd3
  have hi : ∀ i j, i ≤ j → x i = x j → i ≠ 7 →
      coulombDerivative (j.val-i.val) (x i) =
        (derivative^[j.val-i.val] H7).eval (x i) := by
    intro i j hij heq hne
    fin_cases i <;> fin_cases j <;>
      norm_num [x, Function.iterate_succ_apply', coulombDerivative_zero] at * <;>
      first | assumption | linarith
  have htop : a < 1 := by linarith
  obtain ⟨ξ, hξ, heq⟩ := hermite_remainder 9 coulombDerivative (-1) a x 7 H7
    hx hm hs hu (by have := H7_degree_le; omega) hi
    (fun k hk t ht => coulombDerivative_hasDerivAt k t (ht.2.trans_lt htop))
  refine ⟨ξ, ?_, ?_⟩
  · simpa [x] using hξ
  · have huniv : (Finset.univ : Finset (Fin 10)) = {0,1,2,3,4,5,6,7,8,9} := by decide
    simp only [nodalPolynomial, eval_prod] at heq
    rw [huniv] at heq
    have herase : ({0,1,2,3,4,5,6,7,8,9} : Finset (Fin 10)).erase 7 = {0,1,2,3,4,5,6,8,9} := by decide
    rw [herase] at heq
    norm_num [x, coulombDerivative_zero] at heq
    norm_num [omega7, omega, nodes, Fin.prod_univ_succ]
    convert heq using 1 <;> ring

theorem H7_remainder_case3 (u : ℝ) (hL : a < u) (hU : u < 1) :
    ∃ ξ ∈ Ioo (-1 : ℝ) u, coulomb u - H7.eval u =
      coulombDerivative 9 ξ / (Nat.factorial 9) * (u+1) * omega7.eval u := by
  let x : Fin 10 → ℝ := ![-1,-1,-1,b,b,0,0,a,a,u]
  have ha := contact_bounds
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith
  have hm : ∀ i, x i ∈ Icc (-1 : ℝ) u := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith
  have hs : x 0 < x (Fin.last 9) := by norm_num [x]; linarith
  have hu : ∀ i, x i = x 9 → i = 9 := by
    intro i heq
    fin_cases i <;> norm_num [x] at * <;> linarith
  have hv0 := H7_value 0
  have hv1 := H7_value 1
  have hv2 := H7_value 2
  have hv3 := H7_value 3
  have hd0 := H7_slope 0
  have hd1 := H7_slope 1
  have hd2 := H7_slope 2
  have hd3 := H7_slope 3
  have hdd := H7_second_endpoint
  norm_num [nodes] at hv0 hv1 hv2 hv3 hd0 hd1 hd2 hd3
  have hi : ∀ i j, i ≤ j → x i = x j → i ≠ 9 →
      coulombDerivative (j.val-i.val) (x i) =
        (derivative^[j.val-i.val] H7).eval (x i) := by
    intro i j hij heq hne
    fin_cases i <;> fin_cases j <;>
      norm_num [x, Function.iterate_succ_apply', coulombDerivative_zero] at * <;>
      first | assumption | linarith
  have htop : u < 1 := by linarith
  obtain ⟨ξ, hξ, heq⟩ := hermite_remainder 9 coulombDerivative (-1) u x 9 H7
    hx hm hs hu (by have := H7_degree_le; omega) hi
    (fun k hk t ht => coulombDerivative_hasDerivAt k t (ht.2.trans_lt htop))
  refine ⟨ξ, ?_, ?_⟩
  · simpa [x] using hξ
  · have huniv : (Finset.univ : Finset (Fin 10)) = {0,1,2,3,4,5,6,7,8,9} := by decide
    simp only [nodalPolynomial, eval_prod] at heq
    rw [huniv] at heq
    have herase : ({0,1,2,3,4,5,6,7,8,9} : Finset (Fin 10)).erase 9 = {0,1,2,3,4,5,6,7,8} := by decide
    rw [herase] at heq
    norm_num [x, coulombDerivative_zero] at heq
    norm_num [omega7, omega, nodes, Fin.prod_univ_succ]
    convert heq using 1 <;> ring

end Thomson78.Seven

