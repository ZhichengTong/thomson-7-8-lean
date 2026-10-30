import Thomson78.SevenMinorant
import Mathlib.Order.Interval.Set.Infinite

noncomputable section
open scoped BigOperators
open Polynomial Set
namespace Thomson78.Seven
open Thomson78.Analysis
set_option maxHeartbeats 1200000

/-- The nine endpoint Hermite conditions uniquely determine the degree-eight polynomial. -/
theorem H7_unique (p : ℝ[X]) (hp : p.natDegree ≤ 8)
    (hv : ∀ i : Fin 4, p.eval (nodes i) = coulomb (nodes i))
    (hdp : ∀ i : Fin 4, p.derivative.eval (nodes i) = coulombDerivative 1 (nodes i))
    (hddp : p.derivative.derivative.eval (-1) = coulombDerivative 2 (-1)) : p = H7 := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioo_infinite contact_bounds.1).mono
  intro u hu
  let x : Fin 10 → ℝ := ![-1,-1,-1,u,b,b,0,0,a,a]
  let f : ℕ → ℝ → ℝ := fun k t => (derivative^[k] p).eval t
  have ha := contact_bounds
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith [hu.1, hu.2]
  have hm : ∀ i, x i ∈ Icc (-1 : ℝ) a := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith [hu.1, hu.2]
  have hs : x 0 < x (Fin.last 9) := by norm_num [x]; linarith
  have hu' : ∀ i, x i = x 3 → i = 3 := by
    intro i heq
    fin_cases i <;> norm_num [x] at * <;> linarith [hu.1, hu.2]
  have hv0 := H7_value 0
  have hv1 := H7_value 1
  have hv2 := H7_value 2
  have hv3 := H7_value 3
  have hd0 := H7_slope 0
  have hd1 := H7_slope 1
  have hd2 := H7_slope 2
  have hd3 := H7_slope 3
  have hdd := H7_second_endpoint
  have hpv0 := hv 0
  have hpv1 := hv 1
  have hpv2 := hv 2
  have hpv3 := hv 3
  have hpd0 := hdp 0
  have hpd1 := hdp 1
  have hpd2 := hdp 2
  have hpd3 := hdp 3
  norm_num [nodes] at hv0 hv1 hv2 hv3 hd0 hd1 hd2 hd3 hpv0 hpv1 hpv2 hpv3 hpd0 hpd1 hpd2 hpd3
  have hi : ∀ i j, i ≤ j → x i = x j → i ≠ 3 →
      f (j.val-i.val) (x i) = (derivative^[j.val-i.val] H7).eval (x i) := by
    intro i j hij heq hne
    fin_cases i <;> fin_cases j
    all_goals norm_num [x, f, Function.iterate_succ_apply'] at hij
    all_goals norm_num [x, f, Function.iterate_succ_apply'] at heq
    all_goals norm_num [x, f, Function.iterate_succ_apply'] at hne
    all_goals norm_num [x, f, Function.iterate_succ_apply']
    all_goals first
      | solve | simp only [hpv0, hpv1, hpv2, hpv3, hpd0, hpd1, hpd2, hpd3, hddp,
          hv0, hv1, hv2, hv3, hd0, hd1, hd2, hd3, hdd]
      | linarith only [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, hu.1, hu.2, heq]
  have hd : ∀ k < 9, ∀ t ∈ Icc (-1 : ℝ) a, HasDerivAt (f k) (f (k+1) t) t := by
    intro k hk t ht
    convert ((derivative^[k] p).hasDerivAt t) using 1 <;>
      simp only [f, Function.iterate_succ_apply']
  obtain ⟨ξ, hξ, he⟩ := hermite_remainder 9 f (-1) a x 3 H7
    hx hm hs hu' (by have := H7_degree_le; omega) hi hd
  have hz : derivative^[9] p = 0 := iterate_derivative_eq_zero (by omega)
  change p.eval u - H7.eval u = (derivative^[9] p).eval ξ / (Nat.factorial 9) *
    (nodalPolynomial x 3).eval u at he
  rw [hz] at he
  norm_num [x] at he
  exact sub_eq_zero.mp he

#print axioms H7_unique

/-- Uniqueness of the original degree-seven double interpolant. -/
theorem h7_unique (p : ℝ[X]) (hp : p.natDegree ≤ 7)
    (hv : ∀ i : Fin 4, p.eval (nodes i) = coulomb (nodes i))
    (hdp : ∀ i : Fin 4, p.derivative.eval (nodes i) = coulombDerivative 1 (nodes i)) : p = h7 := by
  let γ : ℝ := 8 * (3/32-p.derivative.derivative.eval (-1))
  let P : ℝ[X] := p + C γ * omega7
  have hPdeg : P.natDegree ≤ 8 := by
    apply natDegree_add_le_of_degree_le
    · exact hp.trans (by norm_num)
    · calc
        _ ≤ (C γ).natDegree + omega7.natDegree := natDegree_mul_le
        _ = 8 := by rw [natDegree_C, omega7_degree]
  have hPv (i : Fin 4) : P.eval (nodes i) = coulomb (nodes i) := by
    simp [P, omega7, omega_eval, hv i]
  have hPd (i : Fin 4) : P.derivative.eval (nodes i) = coulombDerivative 1 (nodes i) := by
    simp [P, derivative_C_mul, omega7, omega_derivative_eval, hdp i]
  have hPdd : P.derivative.derivative.eval (-1) = coulombDerivative 2 (-1) := by
    simp only [P, derivative_add, derivative_C_mul, eval_add, eval_mul, eval_C,
      omega7_second_endpoint]
    norm_num [coulombDerivative, oddFactor, γ]
    ring
  have hPeq : P = H7 := H7_unique P hPdeg hPv hPd hPdd
  have hp8 : derivative^[8] p = 0 := iterate_derivative_eq_zero (by omega)
  have hP8 : derivative^[8] P = C (Nat.factorial 8 * γ) := by
    have hw := monic_top_derivative omega7 8 omega7_monic omega7_degree
    simp only [P, ← Module.End.pow_apply, map_add]
    change derivative^[8] p + derivative^[8] (C γ * omega7) = _
    rw [hp8, iterate_derivative_C_mul, hw, zero_add, ← C_mul]
    congr 1
    ring
  have he := congrArg (fun q : ℝ[X] => (derivative^[8] q).eval 0) hPeq
  rw [hP8, H7_eighth_derivative] at he
  norm_num [Nat.factorial] at he
  have hγ : γ = gamma7 := by linarith
  dsimp only [P, H7] at hPeq
  rw [hγ] at hPeq
  exact add_right_cancel hPeq

#print axioms h7_unique

end Thomson78.Seven
