import Thomson78.AnalysisEightRecovery

/-! Polynomial block families discharge the differentiability and tightness
requirements in the two-coordinate recovery argument. -/
noncomputable section
open scoped BigOperators
open Matrix Polynomial Set
namespace Thomson78

variable {J K L : Type*} [Fintype J] [Fintype K] [Fintype L]

def tracePolynomial (Z : Matrix K K ℝ) (M : Matrix K K ℝ[X]) : ℝ[X] :=
  ∑ i, ∑ k, C (Z i k) * M k i

def evalMatrix (M : Matrix K K ℝ[X]) (t : ℝ) : Matrix K K ℝ :=
  fun a b => (M a b).eval t

theorem tracePolynomial_eval (Z : Matrix K K ℝ) (M : Matrix K K ℝ[X]) (t : ℝ) :
    (tracePolynomial Z M).eval t = Matrix.trace (Z * evalMatrix M t) := by
  simp [tracePolynomial, evalMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Polynomial.eval_finsetSum]

theorem polynomial_two_coordinates_zero
    (r₀ r₆ : ℝ) (M : J → Matrix K K ℝ[X]) (F : J → Matrix K L ℝ)
    (hM : ∀ t ∈ Ioo (0:ℝ) 1, ∀ j,
      (evalMatrix (M j) t).PosSemidef)
    (hkernel : ∀ j, evalMatrix (M j) Eight.tStar * (F j * (F j)ᴴ) = 0)
    (hidentity : ∀ t ∈ Ioo (0:ℝ) 1,
      r₀ + Analysis.sixthMoment t * r₆ = Eight.auxiliaryEnergy Eight.tStar t -
      Eight.phi Eight.tStar -
      ∑ j, Matrix.trace ((F j * (F j)ᴴ) * evalMatrix (M j) t)) :
    r₀ = 0 ∧ r₆ = 0 := by
  let g : ℝ[X] := ∑ j, tracePolynomial (F j * (F j)ᴴ) (M j)
  have he (t : ℝ) : g.eval t =
      ∑ j, Matrix.trace ((F j * (F j)ᴴ) * evalMatrix (M j) t) := by
    simp only [g, Polynomial.eval_finsetSum, tracePolynomial_eval]
  apply Eight.certificate_two_coordinates_zero r₀ r₆ g.eval
  · intro t ht
    rw [he]
    exact hidentity t ht
  · intro t ht
    rw [he]
    exact Finset.sum_nonneg fun j _ => trace_factor_nonneg _ _ (hM t ht j)
  · rw [he]
    apply Finset.sum_eq_zero
    intro j _
    rw [Matrix.trace_mul_comm, hkernel j, Matrix.trace_zero]
  · exact g.differentiableAt

end Thomson78

#print axioms Thomson78.polynomial_two_coordinates_zero
