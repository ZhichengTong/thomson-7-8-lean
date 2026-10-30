import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Real.Sqrt

/-! Analytic and interpolation arguments for Sections 2, 4, and 5.
The interpolation construction is the classical squared Lagrange basis formula.
The sixth-moment estimate below is verified by the Lean kernel using an exact
Bernstein expansion; it is not an assumed numerical bound. -/
noncomputable section
open scoped BigOperators
open Polynomial

namespace Thomson78.Analysis

/-- The degree-seven Hermite interpolant at four distinct nodes. -/
def basis (z : Fin 4 → ℝ) (i : Fin 4) : ℝ[X] :=
  Lagrange.basis Finset.univ z i

def hermiteTerm (z v d : Fin 4 → ℝ) (i : Fin 4) : ℝ[X] :=
  (C (v i) + C (d i - 2 * v i * (basis z i).derivative.eval (z i)) *
      (X - C (z i))) * (basis z i)^2

def hermite (z v d : Fin 4 → ℝ) : ℝ[X] := ∑ i, hermiteTerm z v d i

theorem basis_eval (z : Fin 4 → ℝ) (hz : Function.Injective z) (i j : Fin 4) :
    (basis z i).eval (z j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [basis, Lagrange.eval_basis_self hz.injOn]
  · simp [basis, h, Lagrange.eval_basis_of_ne h]

theorem hermiteTerm_eval (z v d : Fin 4 → ℝ) (hz : Function.Injective z)
    (i j : Fin 4) :
    (hermiteTerm z v d i).eval (z j) = if i = j then v j else 0 := by
  by_cases h : i = j
  · subst j
    simp [hermiteTerm, basis_eval z hz]
  · simp [hermiteTerm, basis_eval z hz, h]

theorem hermiteTerm_derivative_eval (z v d : Fin 4 → ℝ) (hz : Function.Injective z)
    (i j : Fin 4) :
    (hermiteTerm z v d i).derivative.eval (z j) = if i = j then d j else 0 := by
  by_cases h : i = j
  · subst j
    simp [hermiteTerm, derivative_mul, derivative_pow, basis_eval z hz]
    ring
  · simp [hermiteTerm, derivative_mul, derivative_pow, basis_eval z hz, h]

theorem hermite_eval (z v d : Fin 4 → ℝ) (hz : Function.Injective z) (i : Fin 4) :
    (hermite z v d).eval (z i) = v i := by
  simp [hermite, eval_finsetSum, hermiteTerm_eval z v d hz]

theorem hermite_derivative_eval (z v d : Fin 4 → ℝ) (hz : Function.Injective z)
    (i : Fin 4) : (hermite z v d).derivative.eval (z i) = d i := by
  simp [hermite, eval_finsetSum, hermiteTerm_derivative_eval z v d hz]


theorem hermite_natDegree_le (z v d : Fin 4 → ℝ) (hz : Function.Injective z) :
    (hermite z v d).natDegree ≤ 7 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hb : (basis z i).natDegree = 3 := by
    simpa [basis] using Lagrange.natDegree_basis hz.injOn (Finset.mem_univ i)
  calc
    (hermiteTerm z v d i).natDegree ≤
        (C (v i) + C (d i - 2*v i*(basis z i).derivative.eval (z i)) *
          (X-C (z i))).natDegree + ((basis z i)^2).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 1 + 6 := by
      gcongr
      · apply Polynomial.natDegree_add_le_of_degree_le
        · simp
        · calc
            _ ≤ (C (d i - 2*v i*(basis z i).derivative.eval (z i))).natDegree +
                (X-C (z i)).natDegree := Polynomial.natDegree_mul_le
            _ ≤ 1 := by simp only [natDegree_C, natDegree_X_sub_C, zero_add, le_refl]
      · simp [Polynomial.natDegree_pow, hb]
    _ = 7 := by norm_num

/-- The nonnegative correction that preserves four values and four slopes. -/
def omega (z : Fin 4 → ℝ) : ℝ[X] := (∏ i, (X-C (z i)))^2

theorem omega_nonneg (z : Fin 4 → ℝ) (t : ℝ) : 0 ≤ (omega z).eval t := by
  simp only [omega, eval_pow]
  exact sq_nonneg _

theorem omega_eval (z : Fin 4 → ℝ) (i : Fin 4) : (omega z).eval (z i) = 0 := by
  have h : (∏ j : Fin 4, (X-C (z j) : ℝ[X])).eval (z i) = 0 := by
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  simp [omega, h]

theorem omega_derivative_eval (z : Fin 4 → ℝ) (i : Fin 4) :
    (omega z).derivative.eval (z i) = 0 := by
  have h : (∏ j : Fin 4, (X-C (z j) : ℝ[X])).eval (z i) = 0 := by
    rw [eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  simp [omega, derivative_pow, h]

theorem correction_preserves_contacts (z v d : Fin 4 → ℝ)
    (hz : Function.Injective z) (c : ℝ) (i : Fin 4) :
    (hermite z v d + C c * omega z).eval (z i) = v i ∧
    (hermite z v d + C c * omega z).derivative.eval (z i) = d i := by
  constructor
  · simp [hermite_eval z v d hz, omega_eval]
  · simp [derivative_mul, hermite_derivative_eval z v d hz,
      omega_eval, omega_derivative_eval]

/-- Once the endpoint coefficient has been identified, every smaller
coefficient retains the minorant inequality. -/
theorem smaller_correction_is_minorant (z : Fin 4 → ℝ) (p : ℝ[X])
    (f : ℝ → ℝ) (s : Set ℝ) (c γ : ℝ)
    (hc : c ≤ γ) (hγ : ∀ t ∈ s, (p + C γ * omega z).eval t ≤ f t) :
    ∀ t ∈ s, (p + C c * omega z).eval t ≤ f t := by
  intro t ht
  have hω := omega_nonneg z t
  have hh := hγ t ht
  simp only [eval_add, eval_mul, eval_C] at hh ⊢
  nlinarith

/-- Sixth edge moment of the square antiprism. -/
def sixthMoment (t : ℝ) : ℝ :=
  (231*t^6 - 630*t^5 + 735*t^4 - 460*t^3 + 165*t^2 - 30*t + 3)/14

def sixthMomentSlope (t : ℝ) : ℝ :=
  (1386*t^5 - 3150*t^4 + 2940*t^3 - 1380*t^2 + 330*t - 30)/14

/-- Contact values written with `sqrt 2 / 2` to keep algebraic expansions small. -/
def antiprismContacts (t : ℝ) : Fin 4 → ℝ :=
  ![t, 2*t-1, -t+(1-t)*Real.sqrt 2/2, -t-(1-t)*Real.sqrt 2/2]

def antiprismWeights : Fin 4 → ℝ := ![8,4,8,8]

theorem contact_first_moment (t : ℝ) :
    ∑ i, antiprismWeights i * antiprismContacts t i = -4 := by
  norm_num [antiprismWeights, antiprismContacts, Fin.sum_univ_succ]
  ring

theorem contact_third_moment (t : ℝ) :
    ∑ i, antiprismWeights i * (antiprismContacts t i)^3 = -4 := by
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  norm_num [antiprismWeights, antiprismContacts, Fin.sum_univ_succ]
  ring_nf
  rw [hs]
  ring

theorem sixthMoment_eq_contacts (t : ℝ) :
    sixthMoment t = (∑ i, antiprismWeights i * (antiprismContacts t i)^6)/28 := by
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hs4 : Real.sqrt 2 ^ 4 = (4 : ℝ) := by
    calc
      _ = (Real.sqrt 2 ^ 2)^2 := by ring
      _ = 4 := by rw [hs]; norm_num
  have hs6 : Real.sqrt 2 ^ 6 = (8 : ℝ) := by
    calc
      _ = (Real.sqrt 2 ^ 2)^3 := by ring
      _ = 8 := by rw [hs]; norm_num
  norm_num [sixthMoment, antiprismWeights, antiprismContacts, Fin.sum_univ_succ]
  ring_nf
  rw [hs, hs4, hs6]
  ring

theorem sixthMoment_hasDerivAt (t : ℝ) :
    HasDerivAt sixthMoment (sixthMomentSlope t) t := by
  have h6 := ((hasDerivAt_id t).pow 6).const_mul (231 : ℝ)
  have h5 := ((hasDerivAt_id t).pow 5).const_mul (630 : ℝ)
  have h4 := ((hasDerivAt_id t).pow 4).const_mul (735 : ℝ)
  have h3 := ((hasDerivAt_id t).pow 3).const_mul (460 : ℝ)
  have h2 := ((hasDerivAt_id t).pow 2).const_mul (165 : ℝ)
  have h1 := (hasDerivAt_id t).const_mul (30 : ℝ)
  convert ((((((h6.sub h5).add h4).sub h3).add h2).sub h1).add_const 3).div_const 14 using 1
  · ext x
    simp only [sixthMoment, Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
  · dsimp [sixthMomentSlope]
    ring

theorem sixthMoment_deriv (t : ℝ) : deriv sixthMoment t = sixthMomentSlope t :=
  (sixthMoment_hasDerivAt t).deriv

theorem sixthMomentSlope_lower_endpoint :
    sixthMomentSlope (39/125) = 33046048032 / 213623046875 := by
  norm_num [sixthMomentSlope]

/-- Bernstein expansion on the interval used in the manuscript. -/
theorem sixthMomentSlope_bernstein (z : ℝ) :
    sixthMomentSlope ((39 + z)/125) - 3/20 =
      (4010364003/854492187500)*(1-z)^5 +
      (143719713/24414062500)*5*z*(1-z)^4 +
      (241266027/34179687500)*10*z^2*(1-z)^3 +
      (56126919/6835937500)*10*z^3*(1-z)^2 +
      (12774243/1367187500)*5*z^4*(1-z) +
      (2859771/273437500)*z^5 := by
  unfold sixthMomentSlope
  ring

theorem sixthMomentSlope_gt (t : ℝ) (hL : 39/125 ≤ t) (hU : t < 8/25) :
    3/20 < sixthMomentSlope t := by
  let z := 125*t-39
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : 0 < 1-z := by dsimp [z]; linarith
  have ht : t = (39+z)/125 := by dsimp [z]; ring
  rw [ht]
  have he := sixthMomentSlope_bernstein z
  have h0 : 0 < (4010364003/854492187500 : ℝ)*(1-z)^5 := by positivity
  have h1 : 0 ≤ (143719713/24414062500 : ℝ)*5*z*(1-z)^4 := by positivity
  have h2 : 0 ≤ (241266027/34179687500 : ℝ)*10*z^2*(1-z)^3 := by positivity
  have h3 : 0 ≤ (56126919/6835937500 : ℝ)*10*z^3*(1-z)^2 := by positivity
  have h4 : 0 ≤ (12774243/1367187500 : ℝ)*5*z^4*(1-z) := by positivity
  have h5 : 0 ≤ (2859771/273437500 : ℝ)*z^5 := by positivity
  linarith

/-- The final two scalar equations in the coordinate-recovery argument. -/
theorem recover_two_coordinates (t r₀ r₆ : ℝ)
    (hL : 39/125 ≤ t) (hU : t < 8/25)
    (hvalue : r₀ + sixthMoment t * r₆ = 0)
    (hslope : deriv sixthMoment t * r₆ = 0) : r₀ = 0 ∧ r₆ = 0 := by
  have hp := sixthMomentSlope_gt t hL hU
  rw [sixthMoment_deriv] at hslope
  have hne : sixthMomentSlope t ≠ 0 := by linarith
  have hr : r₆ = 0 := (mul_eq_zero.mp hslope).resolve_left hne
  simp only [hr, mul_zero, add_zero] at hvalue
  exact ⟨hvalue, hr⟩

/-- A nonnegative differentiable scalar function vanishes to first order at
an interior zero. This is the analytic step used for PSD compressions. -/
theorem derivative_eq_zero_of_nonneg (g : ℝ → ℝ) (t d : ℝ)
    (hnonneg : ∀ s, 0 ≤ g s) (hzero : g t = 0)
    (hd : HasDerivAt g d t) : d = 0 := by
  have hmin : IsLocalMin g t := (show IsMinOn g Set.univ t from by
    intro s hs
    rw [hzero]
    exact hnonneg s).isLocalMin Filter.univ_mem
  exact hmin.hasDerivAt_eq_zero hd

end Thomson78.Analysis


