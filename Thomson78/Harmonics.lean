import Thomson78.Moments
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.LinearCombination

/-! An explicit addition formula for the degree-three Legendre polynomial.
The feature tensor is the traceless part of the symmetric cubic tensor in
three dimensions. All polynomial identities are checked by `ring`.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Thomson78.Harmonics

abbrev R3 := EuclideanSpace ℝ (Fin 3)

def P3 (t : ℝ) : ℝ := (5*t^3-3*t)/2

def cubicFeature (u : Fin 3 → ℝ) (a b c : Fin 3) : ℝ :=
  u a*u b*u c -
    (u a*(if b=c then 1 else 0) + u b*(if a=c then 1 else 0) +
      u c*(if a=b then 1 else 0))/5

/- The tensor contraction before imposing the unit-sphere conditions. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem cubic_contraction (u v : Fin 3 → ℝ) :
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      cubicFeature u a b c * cubicFeature v a b c) =
    (∑ a : Fin 3, u a*v a)^3 -
      (3/5:ℝ)*(∑ a : Fin 3, u a*v a)*
        ((∑ a : Fin 3, (u a)^2)+(∑ a : Fin 3, (v a)^2)) +
      (3/5:ℝ)*(∑ a : Fin 3, u a*v a) := by
  simp [cubicFeature,Fin.sum_univ_succ]
  ring

/-- Explicit addition formula for `P₃`, with twenty-seven real features. -/
theorem P3_addition (u v : Fin 3 → ℝ)
    (hu : ∑ a : Fin 3, (u a)^2=1) (hv : ∑ a : Fin 3, (v a)^2=1) :
    P3 (∑ a : Fin 3, u a*v a) =
      (5/2:ℝ)*∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        cubicFeature u a b c * cubicFeature v a b c := by
  rw [cubic_contraction,hu,hv]
  unfold P3
  ring

theorem sum_sq_coordinates (u : R3) : (∑ a : Fin 3, (u a)^2)=‖u‖^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,pow_two]

theorem inner_coordinates (u v : R3) : ⟪u,v⟫_ℝ=∑ a : Fin 3, u a*v a := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm]

theorem P3_addition_R3 (u v : R3) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    P3 ⟪u,v⟫_ℝ=(5/2:ℝ)*∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      cubicFeature u a b c * cubicFeature v a b c := by
  rw [inner_coordinates]
  apply P3_addition
  · rw [sum_sq_coordinates,hu]
    norm_num
  · rw [sum_sq_coordinates,hv]
    norm_num

variable {I : Type*} [Fintype I]


/-- Finite Gram sums are sums of squares of feature sums. -/
theorem feature_sum_squares {K : Type*} [Fintype K] (F : I → K → ℝ) :
    (∑ i, ∑ j, ∑ k, F i k*F j k) = ∑ k, (∑ i, F i k)^2 := by
  calc
    _ = ∑ i, ∑ k, ∑ j, F i k*F j k := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, F i k*F j k := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_two,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

/-- Summing the explicit addition formula gives a sum of twenty-seven squares. -/
theorem P3_sum_squares (x : I → R3) (hu : ∀ i, ‖x i‖=1) :
    (∑ i, ∑ j, P3 ⟪x i,x j⟫_ℝ) =
      (5/2:ℝ)*∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        (∑ i, cubicFeature (x i) a b c)^2 := by
  simp_rw [P3_addition_R3 _ _ (hu _) (hu _)]
  simp only [← Finset.mul_sum]
  congr 1
  have h := feature_sum_squares (fun i (k : Fin 3 × Fin 3 × Fin 3) =>
    cubicFeature (x i) k.1 k.2.1 k.2.2)
  simpa only [Fintype.sum_prod_type] using h

/-- Nonnegativity of the third spherical-harmonic sum. -/
theorem P3_sum_nonneg (x : I → R3) (hu : ∀ i, ‖x i‖=1) :
    0 ≤ ∑ i, ∑ j, P3 ⟪x i,x j⟫_ℝ := by
  rw [P3_sum_squares x hu]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun c _ => sq_nonneg _



/-- The degree-three Legendre kernel is a positive semidefinite matrix. -/
theorem P3_matrix_posSemidef (x : I → R3) (hu : ∀ i, ‖x i‖=1) :
    Matrix.PosSemidef (fun i j => P3 ⟪x i,x j⟫_ℝ) := by
  have h := Thomson78.scalar_moment_posSemidef
    (fun _ : Fin 3 × Fin 3 × Fin 3 => (5/2:ℝ))
    (fun k (i : I) => cubicFeature (x i) k.1 k.2.1 k.2.2)
    (fun _ => by norm_num)
  have he : (fun i j => P3 ⟪x i,x j⟫_ℝ) =
      ∑ k : Fin 3 × Fin 3 × Fin 3, (5/2:ℝ) •
        (fun i j => cubicFeature (x i) k.1 k.2.1 k.2.2 *
          cubicFeature (x j) k.1 k.2.1 k.2.2) := by
    ext i j
    rw [P3_addition_R3 _ _ (hu i) (hu j)]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Fintype.sum_prod_type,Finset.mul_sum]
  rw [he]
  exact h

/-- Any finitely weighted `P₃` sum is nonnegative. -/
theorem P3_weighted_sum_nonneg (x : I → R3) (hu : ∀ i, ‖x i‖=1) (w : I → ℝ) :
    0 ≤ ∑ i, ∑ j, w i*w j*P3 ⟪x i,x j⟫_ℝ := by
  have h := (P3_matrix_posSemidef x hu).dotProduct_mulVec_nonneg w
  simpa only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
    Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm] using h

/-- Multiplying a positive semidefinite kernel by polynomial features
preserves positivity; this is the block used after fixing three labels. -/
theorem feature_kernel_posSemidef {J : Type*} [Fintype J]
    (x : I → R3) (hu : ∀ i, ‖x i‖=1) (p : J → I → ℝ) :
    Matrix.PosSemidef (fun a b => ∑ i, ∑ j,
      p a i*p b j*P3 ⟪x i,x j⟫_ℝ) := by
  let P : Matrix I J ℝ := Matrix.of (fun i a => p a i)
  have h := (P3_matrix_posSemidef x hu).conjTranspose_mul_mul_same P
  have he : (fun a b => ∑ i, ∑ j, p a i*p b j*P3 ⟪x i,x j⟫_ℝ) =
      P.conjTranspose * Matrix.of (fun i j => P3 ⟪x i,x j⟫_ℝ) * P := by
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

end Thomson78.Harmonics

#print axioms Thomson78.Harmonics.P3_addition_R3
#print axioms Thomson78.Harmonics.P3_sum_nonneg
#print axioms Thomson78.Harmonics.P3_matrix_posSemidef
#print axioms Thomson78.Harmonics.P3_weighted_sum_nonneg
#print axioms Thomson78.Harmonics.feature_kernel_posSemidef

