import Thomson78.SevenRigidity
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
open scoped InnerProductSpace
namespace Thomson78.Seven
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem rigidity_finrank {x : Fin 7 → V} (h : Configuration x) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range x)) = 3 := by
  classical
  obtain ⟨e₁,e₂,e₃,h1,h2,h3,h12,h13,h23,hr⟩ := rigidity h
  have hn1 : ‖e₁‖ = 1 := by rw [real_inner_self_eq_norm_sq] at h1; nlinarith [norm_nonneg e₁]
  have hn2 : ‖e₂‖ = 1 := by rw [real_inner_self_eq_norm_sq] at h2; nlinarith [norm_nonneg e₂]
  have hn3 : ‖e₃‖ = 1 := by rw [real_inner_self_eq_norm_sq] at h3; nlinarith [norm_nonneg e₃]
  have h21 : ⟪e₂,e₁⟫_ℝ=0 := by rw [real_inner_comm]; exact h12
  have h31 : ⟪e₃,e₁⟫_ℝ=0 := by rw [real_inner_comm]; exact h13
  have h32 : ⟪e₃,e₂⟫_ℝ=0 := by rw [real_inner_comm]; exact h23
  let E : Fin 3 → V := ![e₁,e₂,e₃]
  have hE : Orthonormal ℝ E := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [E,hn1,hn2,hn3,h12,h13,h23,h21,h31,h32]
  let S := Submodule.span ℝ (Set.range x)
  have he3 : e₃ ∈ S := Submodule.subset_span (by rw [hr]; exact Or.inl (Or.inl rfl))
  have hp (k : Fin 5) :
      Real.cos (2*Real.pi*k/5) • e₁ + Real.sin (2*Real.pi*k/5) • e₂ ∈ S := by
    apply Submodule.subset_span
    rw [hr]
    exact Or.inr ⟨k,rfl⟩
  have he1 : e₁ ∈ S := by simpa using hp 0
  have hs : Real.sin (2*Real.pi/5) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos]))
  have he2 : e₂ ∈ S := by
    have hc : Real.sin (2*Real.pi/5) • e₂ ∈ S := by
      have hm := S.sub_mem (hp 1) (S.smul_mem (Real.cos (2*Real.pi/5)) he1)
      simpa using hm
    have hm := S.smul_mem (Real.sin (2*Real.pi/5))⁻¹ hc
    simpa [smul_smul, hs] using hm
  have hspan : S = Submodule.span ℝ (Set.range E) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro z hz
      rw [hr] at hz
      have hEm (i : Fin 3) : E i ∈ Submodule.span ℝ (Set.range E) :=
        Submodule.subset_span ⟨i,rfl⟩
      have hEm1 : e₁ ∈ Submodule.span ℝ (Set.range E) := hEm 0
      have hEm2 : e₂ ∈ Submodule.span ℝ (Set.range E) := hEm 1
      have hEm3 : e₃ ∈ Submodule.span ℝ (Set.range E) := hEm 2
      rcases hz with hz | ⟨k,rfl⟩
      · rcases hz with rfl | hz
        · exact hEm3
        · have hz' : z = -e₃ := by simpa using hz
          rw [hz']
          exact Submodule.neg_mem _ hEm3
      · exact Submodule.add_mem _ (Submodule.smul_mem _ _ hEm1) (Submodule.smul_mem _ _ hEm2)
    · apply Submodule.span_le.mpr
      rintro z ⟨i,rfl⟩
      fin_cases i
      · exact he1
      · exact he2
      · exact he3
  change Module.finrank ℝ S = 3
  rw [hspan, finrank_span_eq_card hE.linearIndependent]
  simp

end Thomson78.Seven

#print axioms Thomson78.Seven.rigidity_finrank
