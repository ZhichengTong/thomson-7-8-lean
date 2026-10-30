import Thomson78.SphereEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Rank-three Gram relations underlying the five-point moment constraints. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix
namespace Thomson78

theorem four_point_gram_det_zero (x : Fin 4 → EuclideanSpace ℝ (Fin 3)) :
    Matrix.det (fun i j => ⟪x i,x j⟫_ℝ) = 0 := by
  let M : Matrix (Fin 4) (Fin 3) ℝ := fun i k => x i k
  have he : (fun i j => ⟪x i,x j⟫_ℝ) = M * Mᵀ := by
    ext i j
    change (∑ k, (x j) k * (x i) k) = ∑ k, (x i) k * (x j) k
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]
  by_contra hd
  have hr := (Matrix.rank_mul_le_left M Mᵀ).trans (Matrix.rank_le_card_width M)
  rw [Matrix.rank_of_det_ne_zero hd] at hr
  norm_num at hr

theorem averaged_gram_relation {I : Type*} [Fintype I]
    (w p : I → ℝ) (x : I → Fin 4 → EuclideanSpace ℝ (Fin 3)) :
    (∑ i, w i * p i * Matrix.det (fun a b => ⟪x i a,x i b⟫_ℝ)) = 0 := by
  simp only [four_point_gram_det_zero, mul_zero, Finset.sum_const_zero]

end Thomson78

#print axioms Thomson78.four_point_gram_det_zero
