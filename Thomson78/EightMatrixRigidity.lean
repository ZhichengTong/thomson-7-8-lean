import Thomson78.EightCandidate
import Thomson78.Moments
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Passage from an abstract positive semidefinite Gram matrix to vectors.
The separation quotient of its nonnegative bilinear form supplies a genuine
real inner product space, so the vector rigidity theorem applies directly. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix
namespace Thomson78.Eight

private def GramCoordinates : Type := Fin 8 → ℝ

private instance : AddCommGroup GramCoordinates := inferInstanceAs (AddCommGroup (Fin 8 → ℝ))
private instance : Module ℝ GramCoordinates := inferInstanceAs (Module ℝ (Fin 8 → ℝ))

private def gramBasis (i : Fin 8) : GramCoordinates := Pi.single i (1:ℝ)

private def gramVector (x : GramCoordinates) : Fin 8 → ℝ := x

@[instance_reducible]
private def gramCore (G : Matrix (Fin 8) (Fin 8) ℝ) (hG : G.PosSemidef) :
    PreInnerProductSpace.Core ℝ GramCoordinates where
  inner x y := (G *ᵥ gramVector y) ⬝ᵥ gramVector x
  conj_inner_symm x y := by
    simp only [conj_trivial,Matrix.mulVec,dotProduct,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hs : G i j=G j i := by simpa using hG.isHermitian.apply j i
    rw [hs]
    ring
  re_inner_nonneg x := by
    simpa only [RCLike.re_to_real,Pi.star_def,star_trivial,dotProduct_comm]
      using hG.dotProduct_mulVec_nonneg (gramVector x)
  add_left x y z := by
    change (G *ᵥ gramVector z) ⬝ᵥ gramVector (x+y) = _
    rw [show gramVector (x+y)=gramVector x+gramVector y from rfl]
    exact dotProduct_add _ _ _
  smul_left x y r := by
    change (G *ᵥ gramVector y) ⬝ᵥ gramVector (r • x) = _
    rw [show gramVector (r • x)=r • gramVector x from rfl,dotProduct_smul]
    rfl

/-- Matrix form of the eight-point rigidity theorem in the manuscript. -/
theorem matrix_circulant (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (G : Matrix (Fin 8) (Fin 8) ℝ) (hG : G.PosSemidef)
    (hd : ∀ i, G i i=1) (hr : ∀ i, ∑ j, G i j=0)
    (hc : ∀ i j, i ≠ j → G i j=a t ∨ G i j=b t ∨ G i j=c t ∨ G i j=d t) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ i j, G (σ i) (σ j)=gramEntry t (j-i) := by
  let C := gramCore G hG
  let : SeminormedAddCommGroup GramCoordinates :=
    @InnerProductSpace.Core.toSeminormedAddCommGroup ℝ GramCoordinates _ _ _ C
  let : InnerProductSpace ℝ GramCoordinates := InnerProductSpace.ofCore C
  let x : Fin 8 → SeparationQuotient GramCoordinates :=
    fun i => SeparationQuotient.mk (gramBasis i)
  have hg (i j : Fin 8) : ⟪x i,x j⟫_ℝ=G i j := by
    rw [show x i=SeparationQuotient.mk (gramBasis i) by rfl,
      show x j=SeparationQuotient.mk (gramBasis j) by rfl,
      SeparationQuotient.inner_mk_mk]
    change (G *ᵥ Pi.single j (1:ℝ)) ⬝ᵥ Pi.single i (1:ℝ)=G i j
    simp
  have hu (i : Fin 8) : ⟪x i,x i⟫_ℝ=1 := by rw [hg,hd]
  have hz : ∑ i, x i=0 := by
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner,inner_sum,hg]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun i _ => hr i)
  have hcontact (i j : Fin 8) (hij : i ≠ j) :
      ⟪x i,x j⟫_ℝ=a t ∨ ⟪x i,x j⟫_ℝ=b t ∨ ⟪x i,x j⟫_ℝ=c t ∨ ⟪x i,x j⟫_ℝ=d t := by
    rw [hg]
    exact hc i j hij
  obtain ⟨σ,hσ⟩ := gram_classification_entrywise t hL hU x hu hcontact hz
  exact ⟨σ,fun i j => (hg (σ i) (σ j)).symm.trans (hσ i j)⟩



/-- The circulant matrix identified by the contact graph. -/
def circulantGram (t : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of (fun i j => gramEntry t (j-i))

/-- Its rank is exactly three; a three-point minor supplies the lower bound. -/
theorem circulantGram_rank (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (circulantGram t).rank=3 := by
  let M : Matrix (Fin 8) (Fin 3) ℝ := Matrix.of (fun i k => candidate t i k)
  have he : circulantGram t=M*Mᵀ := by
    ext i j
    change gramEntry t (j-i)=_
    rw [← candidate_gram t ht.le ht1.le i j]
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
      Matrix.mul_apply,Matrix.transpose_apply,M,Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hupper : (circulantGram t).rank ≤ 3 := by
    rw [he]
    have h := (Matrix.rank_mul_le_left M Mᵀ).trans (Matrix.rank_le_card_width M)
    simpa using h
  let q : Fin 3 → Fin 8 := ![0,2,4]
  have hdet : ((circulantGram t).submatrix q q).det=4*t*(1-t)^2 := by
    rw [Matrix.det_fin_three]
    simp [circulantGram,Matrix.submatrix,q,gramEntry,a,b]
    ring
  have hdetpos : 0 < ((circulantGram t).submatrix q q).det := by
    rw [hdet]
    positivity
  have hminor : ((circulantGram t).submatrix q q).rank=3 := by
    rw [Matrix.rank_of_det_ne_zero hdetpos.ne']
    rfl
  have hlower := Matrix.rank_submatrix_le (circulantGram t) q q
  rw [hminor] at hlower
  exact le_antisymm hupper hlower

theorem matrix_rank_three (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (G : Matrix (Fin 8) (Fin 8) ℝ) (hG : G.PosSemidef)
    (hd : ∀ i, G i i=1) (hr : ∀ i, ∑ j, G i j=0)
    (hc : ∀ i j, i ≠ j → G i j=a t ∨ G i j=b t ∨ G i j=c t ∨ G i j=d t) :
    G.rank=3 := by
  obtain ⟨σ,hσ⟩ := matrix_circulant t hL hU G hG hd hr hc
  have he : G.submatrix σ σ=circulantGram t := by
    ext i j
    exact hσ i j
  have h := Matrix.rank_submatrix G σ σ
  rw [he,circulantGram_rank t (by linarith) (by linarith)] at h
  exact h.symm

/-- The published matrix formulation, with `G·1=0` as its balance condition. -/
theorem matrix_rigidity (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (G : Matrix (Fin 8) (Fin 8) ℝ) (hG : G.PosSemidef)
    (hd : ∀ i, G i i=1) (hr : G *ᵥ (fun _ => (1:ℝ))=0)
    (hc : ∀ i j, i ≠ j → G i j=a t ∨ G i j=b t ∨ G i j=c t ∨ G i j=d t) :
    (∃ σ : Equiv.Perm (Fin 8), G.submatrix σ σ=circulantGram t) ∧ G.rank=3 := by
  have hrow (i : Fin 8) : ∑ j, G i j=0 := by
    have h := congrFun hr i
    simpa [Matrix.mulVec,dotProduct] using h
  refine ⟨?_,matrix_rank_three t hL hU G hG hd hrow hc⟩
  obtain ⟨σ,hσ⟩ := matrix_circulant t hL hU G hG hd hrow hc
  exact ⟨σ,Matrix.ext hσ⟩

end Thomson78.Eight

#print axioms Thomson78.Eight.matrix_circulant
#print axioms Thomson78.Eight.circulantGram_rank
#print axioms Thomson78.Eight.matrix_rigidity
