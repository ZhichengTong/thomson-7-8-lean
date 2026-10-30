import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-! Shared notation and elementary Gram identities for the manuscript. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace InnerProductSpace

namespace Thomson78

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def gram {n : ℕ} (x : Fin n → V) (i j : Fin n) : ℝ := ⟪x i, x j⟫_ℝ

theorem gram_symmetric {n : ℕ} (x : Fin n → V) (i j : Fin n) :
    gram x i j = gram x j i := real_inner_comm _ _

theorem centroid_norm_sq {n : ℕ} (x : Fin n → V) :
    ‖∑ i, x i‖ ^ 2 = ∑ i, ∑ j, gram x i j := by
  simp only [gram, ← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
  rw [Finset.sum_comm]

end Thomson78
