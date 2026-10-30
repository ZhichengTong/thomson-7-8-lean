import Thomson78.Seven
import Thomson78.AnalysisHermite
import Thomson78.AnalysisCoulomb

noncomputable section
open scoped BigOperators
open Polynomial Set

namespace Thomson78.Seven
open Thomson78.Analysis

def nodes : Fin 4 → ℝ := ![-1,b,0,a]

theorem nodes_injective : Function.Injective nodes := by
  intro i j hij
  have ha := contact_bounds
  fin_cases i <;> fin_cases j <;> norm_num [nodes] at * <;> linarith

def h7 : ℝ[X] := hermite nodes (fun i => coulomb (nodes i))
  (fun i => coulombDerivative 1 (nodes i))

def omega7 : ℝ[X] := omega nodes

def gamma7 : ℝ := 8 * (3/32 - h7.derivative.derivative.eval (-1))

def H7 : ℝ[X] := h7 + C gamma7 * omega7

theorem h7_degree : h7.natDegree ≤ 7 := hermite_natDegree_le _ _ _ nodes_injective

theorem h7_value (i : Fin 4) : h7.eval (nodes i) = coulomb (nodes i) :=
  hermite_eval _ _ _ nodes_injective i

theorem h7_slope (i : Fin 4) : h7.derivative.eval (nodes i) =
    coulombDerivative 1 (nodes i) := hermite_derivative_eval _ _ _ nodes_injective i

theorem omega7_monic : omega7.Monic := by
  apply Monic.pow
  apply monic_prod_of_monic
  intro i hi
  exact monic_X_sub_C _

theorem omega7_degree : omega7.natDegree = 8 := by
  unfold omega7 omega
  rw [natDegree_pow, natDegree_prod_of_monic _ _ (fun i hi => monic_X_sub_C _)]
  norm_num

theorem omega7_second_endpoint : omega7.derivative.derivative.eval (-1) = 1/8 := by
  have hab := contact_arithmetic.1
  have hp := contact_arithmetic.2.1
  have hprod : (1+a)*(1+b) = (1/4 : ℝ) := by nlinarith
  have hsq := congrArg (fun t : ℝ => t^2) hprod
  norm_num [omega7, omega, nodes, Fin.prod_univ_succ, derivative_mul, derivative_pow]
  nlinarith [hsq]

theorem H7_value (i : Fin 4) : H7.eval (nodes i) = coulomb (nodes i) := by
  exact (correction_preserves_contacts nodes _ _ nodes_injective gamma7 i).1

theorem H7_slope (i : Fin 4) : H7.derivative.eval (nodes i) =
    coulombDerivative 1 (nodes i) := by
  exact (correction_preserves_contacts nodes _ _ nodes_injective gamma7 i).2

theorem H7_second_endpoint : H7.derivative.derivative.eval (-1) =
    coulombDerivative 2 (-1) := by
  simp only [H7, derivative_add, derivative_C_mul, eval_add, eval_mul, eval_C,
    omega7_second_endpoint]
  norm_num [coulombDerivative, oddFactor, gamma7]
  ring

theorem H7_degree_le : H7.natDegree ≤ 8 := by
  apply natDegree_add_le_of_degree_le
  · exact h7_degree.trans (by norm_num)
  · calc
      _ ≤ (C gamma7).natDegree + omega7.natDegree := natDegree_mul_le
      _ = 8 := by rw [natDegree_C, omega7_degree]

theorem H7_eighth_derivative : derivative^[8] H7 = C (Nat.factorial 8 * gamma7) := by
  have hh : derivative^[8] h7 = 0 := iterate_derivative_eq_zero (by have := h7_degree; omega)
  have hw := monic_top_derivative omega7 8 omega7_monic omega7_degree
  simp only [H7, ← Module.End.pow_apply, map_add]
  change derivative^[8] h7 + derivative^[8] (C gamma7 * omega7) = _
  rw [hh, iterate_derivative_C_mul, hw, zero_add, ← C_mul]
  congr 1
  ring

theorem gamma7_pos : 0 < gamma7 := by
  let x : Fin 9 → ℝ := ![-1,-1,-1,b,b,0,0,a,a]
  let F : ℕ → ℝ → ℝ := fun k t => coulombDerivative k t - (derivative^[k] H7).eval t
  have ha := contact_bounds
  have hx : Monotone x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [x] at * <;> linarith
  have hm : ∀ i, x i ∈ Icc (-1 : ℝ) a := by
    intro i
    fin_cases i <;> constructor <;> norm_num [x] <;> linarith
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
  have hj : VanishingJets F x := by
    intro i j hij heq
    fin_cases i <;> fin_cases j <;>
      norm_num [x, F, Function.iterate_succ_apply', coulombDerivative_zero] at * <;>
      first | assumption | linarith
  have hd : ∀ k < 8, ∀ t ∈ Icc (-1 : ℝ) a, HasDerivAt (F k) (F (k+1) t) t := by
    intro k hk t ht
    convert (coulombDerivative_hasDerivAt k t (ht.2.trans_lt ha.2.2.2)).sub
      ((derivative^[k] H7).hasDerivAt t) using 1 <;>
      simp only [F, Function.iterate_succ_apply']
  obtain ⟨ξ, hξ, hz⟩ := repeated_rolle 8 F (-1) a x hx hm hj hd
  have hp := coulombDerivative_pos 8 ξ (hξ.2.trans_lt ha.2.2.2)
  dsimp only [F] at hz
  rw [H7_eighth_derivative] at hz
  norm_num [Nat.factorial] at hz
  linarith

end Thomson78.Seven
