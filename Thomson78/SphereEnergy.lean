import Thomson78.Energy
import Thomson78.AnalysisCoulomb

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Thomson78

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def Admissible {n : ℕ} (x : Fin n → V) : Prop :=
  (∀ i, ‖x i‖ = 1) ∧ Function.Injective x

/-- Coulomb energy on the domain of distinct points. -/
def coulombEnergy {n : ℕ} (x : Fin n → V) : ℝ :=
  ∑ p ∈ pairs n, ‖x p.1 - x p.2‖⁻¹

theorem distance_coulomb (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u-v‖⁻¹ = Analysis.coulomb ⟪u,v⟫_ℝ := by
  have hsq : ‖u-v‖^2 = 2-2*⟪u,v⟫_ℝ := by
    rw [norm_sub_sq_real, hu, hv]
    ring
  rw [Analysis.coulomb, ← hsq, Real.sqrt_sq (norm_nonneg _)]

theorem coulombEnergy_eq_pairEnergy {n : ℕ} (x : Fin n → V)
    (hu : ∀ i, ‖x i‖ = 1) :
    coulombEnergy x = pairEnergy Analysis.coulomb x := by
  apply Finset.sum_congr rfl
  intro p _
  exact distance_coulomb _ _ (hu _) (hu _)

theorem admissible_inner_interval {n : ℕ} {x : Fin n → V}
    (hx : Admissible x) {i j : Fin n} (hij : i ≠ j) :
    -1 ≤ gram x i j ∧ gram x i j < 1 := by
  constructor
  · exact neg_one_le_real_inner_of_norm_eq_one (hx.1 i) (hx.1 j)
  · have hs : 0 < ‖x i-x j‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hx.2.ne hij)))
    rw [norm_sub_sq_real, hx.1 i, hx.1 j] at hs
    dsimp [gram]
    nlinarith

theorem norm_configuration_unit_inner {n : ℕ} {x : Fin n → V}
    (hx : ∀ i, ‖x i‖=1) : ∀ i, ⟪x i,x i⟫_ℝ=1 := by
  intro i
  rw [real_inner_self_eq_norm_sq, hx i]
  norm_num

end Thomson78

#print axioms Thomson78.coulombEnergy_eq_pairEnergy
