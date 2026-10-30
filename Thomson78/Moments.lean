import Thomson78.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-! Positivity of the moment and localizing matrices.

The index sets are general, so the same proofs apply to the manuscript's
monomials of degrees four, three and two, and to its five-point injections.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix
namespace Thomson78

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def averagedGram (w : I → ℝ) (v : I → J → V) : Matrix J J ℝ :=
  ∑ i, w i • (fun a b => ⟪v i a,v i b⟫_ℝ)

theorem matrixGram_posSemidef (v : J → V) :
    Matrix.PosSemidef (fun a b => ⟪v a,v b⟫_ℝ) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.ext
    intro i j
    change ⟪v j,v i⟫_ℝ = ⟪v i,v j⟫_ℝ
    exact real_inner_comm _ _
  · intro c
    have hn : 0 ≤ ⟪∑ i, c i • v i, ∑ i, c i • v i⟫_ℝ := real_inner_self_nonneg
    convert hn using 1
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    rw [Finset.sum_comm]
    congr 1
    ext i
    congr 1
    ext j
    ring

theorem averagedGram_posSemidef (w : I → ℝ) (v : I → J → V)
    (hw : ∀ i, 0 ≤ w i) : (averagedGram w v).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact (matrixGram_posSemidef (v i)).smul (hw i)

theorem scalar_moment_posSemidef (w : I → ℝ) (p : I → J → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    Matrix.PosSemidef (∑ i, w i • (fun a b => p i a * p i b)) := by
  simpa only [averagedGram, RCLike.inner_apply, conj_trivial, mul_comm] using
    averagedGram_posSemidef w p hw

theorem localized_moment_posSemidef (w u : I → ℝ) (p : I → J → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, |u i| ≤ 1) :
    Matrix.PosSemidef (∑ i, (w i * (1 - (u i)^2)) •
      (fun a b => p i a * p i b)) := by
  apply scalar_moment_posSemidef
  intro i
  apply mul_nonneg (hw i)
  have hi := (abs_le.mp (hu i))
  nlinarith

theorem gram_localized_moment_posSemidef (w : I → ℝ) (x : I → K → V)
    (p : I → J → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (averagedGram w (fun i (a : K × J) => p i a.2 • x i a.1)).PosSemidef :=
  averagedGram_posSemidef _ _ hw

/-- A Gram-factor representation of a positive semidefinite certificate block
turns its trace pairing into a sum of nonnegative quadratic forms. -/
theorem trace_factor_nonneg (B : Matrix J J ℝ) (R : Matrix J K ℝ)
    (hB : B.PosSemidef) : 0 ≤ Matrix.trace ((R * Rᴴ) * B) := by
  have h := (hB.conjTranspose_mul_mul_same R).trace_nonneg
  rwa [Matrix.trace_mul_cycle] at h

end Thomson78

#print axioms Thomson78.averagedGram_posSemidef
#print axioms Thomson78.localized_moment_posSemidef
#print axioms Thomson78.trace_factor_nonneg
