import Thomson78.AnalysisLegendreKernel

/-! The positive semidefinite Legendre matrices for all degrees used by the
five-point moment certificate, including fixed-label and averaged blocks. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix
namespace Thomson78.LegendreKernel

def feature (l : Fin 9) (k : Fin 9 × Fin 2) (u : Fin 3 → ℝ) : ℝ :=
  if k.2 = 0 then realFeature l k.1 u else imagFeature l k.1 u

theorem legendre_addition (l : Fin 9) (u v : Fin 3 → ℝ)
    (hu : squareNorm u = 1) (hv : squareNorm v = 1) :
    legendre l (∑ i, u i*v i) =
      ∑ k : Fin 9 × Fin 2, weight l k.1 * feature l k u * feature l k v := by
  have h := homogeneous_addition l u v
  rw [hu,hv,mul_one] at h
  change legendre l (∑ i, u i*v i) = _ at h
  rw [h,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro m hm
  simp [feature,Fin.sum_univ_two]
  ring

theorem legendre_addition_R3 (l : Fin 9) (u v : R3) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    legendre l ⟪u,v⟫_ℝ =
      ∑ k : Fin 9 × Fin 2, weight l k.1 * feature l k u * feature l k v := by
  rw [Harmonics.inner_coordinates]
  apply legendre_addition
  · unfold squareNorm
    rw [Harmonics.sum_sq_coordinates,hu]
    norm_num
  · unfold squareNorm
    rw [Harmonics.sum_sq_coordinates,hv]
    norm_num

/-- The common notation for the first and third Legendre terms agrees with
the explicit family used for the matrix kernels. -/
theorem legendre_three (t : ℝ) : legendre 3 t = Harmonics.P3 t := by
  norm_num [legendre,homogeneousKernel,Harmonics.P3]
  ring

variable {I J A : Type*} [Fintype I] [Fintype J] [Fintype A]

/-- The normalized Legendre kernel is positive semidefinite in every degree
from zero through eight. -/
theorem kernel_posSemidef (l : Fin 9) (x : I → R3) (hu : ∀ i, ‖x i‖=1) :
    Matrix.PosSemidef (fun i j => legendre l ⟪x i,x j⟫_ℝ) := by
  have h := Thomson78.scalar_moment_posSemidef
    (fun k : Fin 9 × Fin 2 => weight l k.1)
    (fun k (i : I) => feature l k (x i)) (fun k => weight_nonneg l k.1)
  have he : (fun i j => legendre l ⟪x i,x j⟫_ℝ) =
      ∑ k : Fin 9 × Fin 2, weight l k.1 •
        (fun i j => feature l k (x i)*feature l k (x j)) := by
    ext i j
    rw [legendre_addition_R3 _ _ _ (hu i) (hu j)]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_assoc]
  rw [he]
  exact h

/-- All weighted Legendre sums used in the certificate are nonnegative. -/
theorem weighted_sum_nonneg (l : Fin 9) (x : I → R3) (hu : ∀ i, ‖x i‖=1) (w : I → ℝ) :
    0 ≤ ∑ i, ∑ j, w i*w j*legendre l ⟪x i,x j⟫_ℝ := by
  have h := (kernel_posSemidef l x hu).dotProduct_mulVec_nonneg w
  simpa only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
    Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] using h

theorem harmonic_sum_nonneg (l : Fin 9) (x : I → R3) (hu : ∀ i, ‖x i‖=1) :
    0 ≤ ∑ i, ∑ j, legendre l ⟪x i,x j⟫_ℝ := by
  simpa using weighted_sum_nonneg l x hu (fun _ => 1)

/-- Multiplication by arbitrary polynomial features preserves the positive
semidefinite Legendre kernel. Labels excluded from the sums can be represented
by zero feature values. -/
theorem fixed_label_matrix_posSemidef (l : Fin 9) (x : I → R3)
    (hu : ∀ i, ‖x i‖=1) (p : J → I → ℝ) :
    Matrix.PosSemidef (fun a b => ∑ i, ∑ j,
      p a i*p b j*legendre l ⟪x i,x j⟫_ℝ) := by
  let P : Matrix I J ℝ := Matrix.of (fun i a => p a i)
  have h := (kernel_posSemidef l x hu).conjTranspose_mul_mul_same P
  have he : (fun a b => ∑ i, ∑ j, p a i*p b j*legendre l ⟪x i,x j⟫_ℝ) =
      P.conjTranspose * Matrix.of (fun i j => legendre l ⟪x i,x j⟫_ℝ) * P := by
    ext a b
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.of_apply,star_trivial,P]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact h

/-- Averaging over the fixed labels gives all matrices `F_l`, `0 ≤ l ≤ 8`.
The weights include the reciprocal of the number of ordered label triples. -/
theorem averaged_fixed_label_matrix_posSemidef (l : Fin 9) (x : I → R3)
    (hu : ∀ i, ‖x i‖=1) (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (p : A → J → I → ℝ) :
    Matrix.PosSemidef (∑ a, w a • (fun b c => ∑ i, ∑ j,
      p a b i*p a c j*legendre l ⟪x i,x j⟫_ℝ)) := by
  apply Matrix.posSemidef_sum
  intro a ha
  exact (fixed_label_matrix_posSemidef l x hu (p a)).smul (hw a)

end Thomson78.LegendreKernel

#print axioms Thomson78.LegendreKernel.homogeneous_addition
#print axioms Thomson78.LegendreKernel.legendre_recurrence
#print axioms Thomson78.LegendreKernel.legendre_addition_R3
#print axioms Thomson78.LegendreKernel.kernel_posSemidef
#print axioms Thomson78.LegendreKernel.averaged_fixed_label_matrix_posSemidef
