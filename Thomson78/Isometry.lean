import Thomson78.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.Isomorphisms

/-! Equal Gram matrices induce an isometry of the spans, constructed through
the quotient of the coefficient space by the kernel of the summation map. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Thomson78

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def total (x : I → V) : (I → ℝ) →ₗ[ℝ] V where
  toFun c := ∑ i, c i • x i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [mul_smul, Finset.smul_sum]

theorem total_single (x : I → V) (i : I) : total x (Pi.single i 1) = x i := by
  simp [total, Pi.single_apply]

theorem range_total (x : I → V) :
    LinearMap.range (total x) = Submodule.span ℝ (Set.range x) := by
  apply le_antisymm
  · rintro z ⟨c, rfl⟩
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))
  · apply Submodule.span_le.mpr
    rintro z ⟨i,rfl⟩
    exact ⟨Pi.single i 1, total_single x i⟩

omit [DecidableEq I] in
theorem inner_total (x : I → V) (c d : I → ℝ) :
    ⟪total x c, total x d⟫_ℝ = ∑ i, ∑ j, c i * d j * ⟪x i, x j⟫_ℝ := by
  simp only [total, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  ring

theorem total_inner_eq (x : I → V) (y : I → W)
    (h : ∀ i j, ⟪x i, x j⟫_ℝ = ⟪y i, y j⟫_ℝ) (c d : I → ℝ) :
    ⟪total x c, total x d⟫_ℝ = ⟪total y c, total y d⟫_ℝ := by
  simp only [inner_total, h]

theorem total_ker_le (x : I → V) (y : I → W)
    (h : ∀ i j, ⟪x i, x j⟫_ℝ = ⟪y i, y j⟫_ℝ) :
    (total y).ker ≤ (total x).ker := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [total_inner_eq x y h, hc]
  simp

def gramMap (x : I → V) (y : I → W)
    (h : ∀ i j, ⟪x i, x j⟫_ℝ = ⟪y i, y j⟫_ℝ) :
    LinearMap.range (total y) →ₗ[ℝ] V :=
  ((total y).ker.liftQ (total x) (total_ker_le x y h)).comp
    (total y).quotKerEquivRange.symm.toLinearMap

theorem gramMap_total (x : I → V) (y : I → W)
    (h : ∀ i j, ⟪x i, x j⟫_ℝ = ⟪y i, y j⟫_ℝ) (c : I → ℝ)
    (hc : total y c ∈ LinearMap.range (total y)) :
    gramMap x y h ⟨total y c, hc⟩ = total x c := by
  simp only [gramMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

def gramIsometry (x : I → V) (y : I → W)
    (h : ∀ i j, ⟪x i, x j⟫_ℝ = ⟪y i, y j⟫_ℝ) :
    LinearMap.range (total y) →ₗᵢ[ℝ] V where
  toLinearMap := gramMap x y h
  norm_map' u := by
    obtain ⟨c, hc⟩ := u.property
    have hu : u = ⟨total y c, ⟨c, rfl⟩⟩ := Subtype.ext hc.symm
    rw [hu]
    erw [gramMap_total]
    have he := total_inner_eq x y h c c
    simp only [real_inner_self_eq_norm_sq] at he
    change ‖total x c‖ = ‖total y c‖
    nlinarith [norm_nonneg (total x c), norm_nonneg (total y c)]

theorem gramIsometry_vertex (x : I → V) (y : I → W)
    (h : ∀ i j, ⟪x i, x j⟫_ℝ = ⟪y i, y j⟫_ℝ) (i : I)
    (hi : y i ∈ LinearMap.range (total y)) :
    gramIsometry x y h ⟨y i, hi⟩ = x i := by
  change gramMap x y h ⟨y i, hi⟩ = x i
  have hval := gramMap_total x y h (Pi.single i 1) ⟨Pi.single i 1, rfl⟩
  simpa only [total_single] using hval

def fullGramIsometry (x : I → V) (y : I → W)
    (h : ∀ i j, ⟪x i, x j⟫_ℝ = ⟪y i, y j⟫_ℝ)
    (hy : Function.Surjective (total y)) : W →ₗᵢ[ℝ] V :=
  (gramIsometry x y h).comp
    (LinearIsometryEquiv.ofTop W (LinearMap.range (total y))
      (LinearMap.range_eq_top.mpr hy)).symm.toLinearIsometry

theorem fullGramIsometry_vertex (x : I → V) (y : I → W)
    (h : ∀ i j, ⟪x i, x j⟫_ℝ = ⟪y i, y j⟫_ℝ)
    (hy : Function.Surjective (total y)) (i : I) :
    fullGramIsometry x y h hy (y i) = x i := by
  apply gramIsometry_vertex
  exact h

end Thomson78

#print axioms Thomson78.gramIsometry
