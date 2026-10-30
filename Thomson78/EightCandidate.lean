import Thomson78.EightGeometryRigidity
import Thomson78.Isometry
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Thomson78.Eight

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Square-antiprism coordinates in the eight-cycle order of the manuscript. -/
def candidate (t : ℝ) : Fin 8 → R3 :=
  let r := Real.sqrt (1-t)
  let h := Real.sqrt t
  let q := r * Real.sqrt 2 / 2
  ![!₂[r,0,h], !₂[-q,q,-h], !₂[0,-r,h], !₂[q,q,-h],
    !₂[-r,0,h], !₂[q,-q,-h], !₂[0,r,h], !₂[-q,-q,-h]]

theorem candidate_gram (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (i j : Fin 8) :
    ⟪candidate t i, candidate t j⟫_ℝ = gramEntry t (j-i) := by
  have hr := Real.sq_sqrt (show 0 ≤ 1-t by linarith)
  have hh := Real.sq_sqrt ht
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  fin_cases i <;> fin_cases j <;>
    simp [candidate, gramEntry, Fin.sum_univ_succ, a,b,c,d,s] <;>
    ring_nf <;> (try simp [hr,hh,hs]) <;> (try ring)

theorem candidate_unit (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 8) :
    ‖candidate t i‖ = 1 := by
  have hi := candidate_gram t ht ht1 i i
  simp only [sub_self, gramEntry, Matrix.cons_val_zero] at hi
  rw [real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (candidate t i)]

theorem candidate_centroid (t : ℝ) : ∑ i, candidate t i = 0 := by
  ext j
  fin_cases j <;> simp [candidate, Fin.sum_univ_succ]

theorem candidate_spans (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Function.Surjective (Thomson78.total (candidate t)) := by
  intro v
  let r := Real.sqrt (1-t)
  let h := Real.sqrt t
  have hr : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  have hh : h ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  refine ⟨![v 0/(2*r)+v 2/(2*h),0,-v 1/(2*r),0,
    -v 0/(2*r)+v 2/(2*h),0,v 1/(2*r),0], ?_⟩
  ext j
  fin_cases j <;>
    simp [Thomson78.total, candidate, Fin.sum_univ_succ, r, h] <;>
    field_simp [hr, hh] <;> ring

/-- Rigidity as a three-dimensional linear isometric embedding. -/
theorem rigidity_isometry (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : Fin 8 → V) (hu : ∀ i, ⟪x i,x i⟫_ℝ=1)
    (hc : ∀ i j, i ≠ j →
      ⟪x i,x j⟫_ℝ=a t ∨ ⟪x i,x j⟫_ℝ=b t ∨ ⟪x i,x j⟫_ℝ=c t ∨ ⟪x i,x j⟫_ℝ=d t)
    (hz : ∑ i, x i=0) :
    ∃ (σ : Equiv.Perm (Fin 8)) (U : R3 →ₗᵢ[ℝ] V), ∀ i, U (candidate t i)=x (σ i) := by
  obtain ⟨σ,hσ⟩ := gram_classification_entrywise t hL hU x hu hc hz
  have ht : 0 < t := by linarith
  have ht1 : t < 1 := by linarith
  have hg : ∀ i j, ⟪x (σ i),x (σ j)⟫_ℝ = ⟪candidate t i,candidate t j⟫_ℝ := by
    intro i j
    rw [hσ, candidate_gram t ht.le ht1.le]
  exact ⟨σ, fullGramIsometry (x ∘ σ) (candidate t) hg (candidate_spans t ht ht1),
    fullGramIsometry_vertex (x ∘ σ) (candidate t) hg (candidate_spans t ht ht1)⟩

theorem rigidity_finrank (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : Fin 8 → V) (hu : ∀ i, ⟪x i,x i⟫_ℝ=1)
    (hc : ∀ i j, i ≠ j →
      ⟪x i,x j⟫_ℝ=a t ∨ ⟪x i,x j⟫_ℝ=b t ∨ ⟪x i,x j⟫_ℝ=c t ∨ ⟪x i,x j⟫_ℝ=d t)
    (hz : ∑ i, x i=0) : Module.finrank ℝ (Submodule.span ℝ (Set.range x)) = 3 := by
  obtain ⟨σ,U,hUx⟩ := rigidity_isometry t hL hU x hu hc hz
  have hspan : Submodule.span ℝ (Set.range x) = U.toLinearMap.range := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro z ⟨i,rfl⟩
      exact ⟨candidate t (σ.symm i), by simpa using hUx (σ.symm i)⟩
    · rintro z ⟨v,rfl⟩
      obtain ⟨c,hc⟩ := candidate_spans t (by linarith) (by linarith) v
      rw [← hc]
      change U (∑ i, c i • candidate t i) ∈ _
      simp only [map_sum, map_smul, hUx]
      exact Submodule.sum_mem _ (fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ i,rfl⟩))
  rw [hspan, LinearMap.finrank_range_of_inj U.injective]
  simp [R3]

end Thomson78.Eight

#print axioms Thomson78.Eight.rigidity_isometry
#print axioms Thomson78.Eight.rigidity_finrank
