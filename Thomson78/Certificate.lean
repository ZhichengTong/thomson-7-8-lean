import Thomson78.Moments
import Thomson78.Energy

/-! The computational input consists of a finite coefficient identity, signs of
two scalar coefficients, and Gram factors for the certificate matrices.
This file proves how the coefficient identity evaluates on a moment vector.
No minimization, contact classification or analytic minorant is assumed as
part of the computational input. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace Thomson78

variable {D R J K L : Type*} [Fintype D] [DecidableEq D]
  [Fintype R] [Fintype J] [Fintype K] [Fintype L]

def momentMatrix (B : D → Matrix K K ℝ) (m : D → ℝ) : Matrix K K ℝ :=
  ∑ d, m d • B d

def traceCoefficient (Z : Matrix K K ℝ) (B : D → Matrix K K ℝ) : D → ℝ :=
  fun d => Matrix.trace (Z * B d)

theorem traceCoefficient_pairing (Z : Matrix K K ℝ) (B : D → Matrix K K ℝ)
    (m : D → ℝ) : traceCoefficient Z B ⬝ᵥ m = Matrix.trace (Z * momentMatrix B m) := by
  simp only [traceCoefficient, dotProduct, momentMatrix, Matrix.mul_sum,
    Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem constraint_pairing_zero (A : Matrix R D ℝ) (lam : R → ℝ) (m : D → ℝ)
    (hA : A *ᵥ m = 0) : (Aᵀ *ᵥ lam) ⬝ᵥ m = 0 := by
  rw [mulVec_transpose, ← dotProduct_mulVec]
  rw [hA]
  simp

/-- Evaluation of the finite certificate identity. -/
theorem certificate_pairing
    (e : D) (c v₁ v₃ m : D → ℝ) (A : Matrix R D ℝ) (lam : R → ℝ)
    (B : J → D → Matrix K K ℝ) (Z : J → Matrix K K ℝ) (τ μ₁ μ₃ : ℝ)
    (hm : m e = 1) (hA : A *ᵥ m = 0)
    (hid : c + Aᵀ *ᵥ lam =
      τ • Pi.single e 1 + μ₁ • v₁ + μ₃ • v₃ + ∑ j, traceCoefficient (Z j) (B j)) :
    c ⬝ᵥ m - τ = μ₁ * (v₁ ⬝ᵥ m) + μ₃ * (v₃ ⬝ᵥ m) +
      ∑ j, Matrix.trace (Z j * momentMatrix (B j) m) := by
  have he := congrArg (fun v : D → ℝ => v ⬝ᵥ m) hid
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, sum_dotProduct,
    traceCoefficient_pairing, constraint_pairing_zero A lam m hA] at he
  have hsingle : Pi.single e (1:ℝ) ⬝ᵥ m = 1 := by simp [dotProduct, Pi.single_apply, hm]
  rw [hsingle] at he
  linarith

/-- A factorized certificate gives nonnegative matrix terms for every moment
vector whose corresponding blocks are positive semidefinite. -/
theorem certificate_trace_nonneg
    (B : J → D → Matrix K K ℝ) (F : J → Matrix K L ℝ) (m : D → ℝ)
    (hB : ∀ j, (momentMatrix (B j) m).PosSemidef) :
    ∀ j, 0 ≤ Matrix.trace ((F j * (F j)ᴴ) * momentMatrix (B j) m) := by
  intro j
  exact trace_factor_nonneg _ _ (hB j)

end Thomson78

#print axioms Thomson78.certificate_pairing
