import Thomson78.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-! Analytic and local geometric steps of the eight-point rigidity proof.
All proofs here are checked by the Lean kernel; no external certificate is used. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace InnerProductSpace
namespace Thomson78.Eight

abbrev s : ℝ := Real.sqrt 2
def a (t : ℝ) : ℝ := t
def b (t : ℝ) : ℝ := 2 * t - 1
def c (t : ℝ) : ℝ := -t + (1-t) * s / 2
def d (t : ℝ) : ℝ := -t - (1-t) * s / 2

theorem sqrt_bounds : (7:ℝ)/5 < s ∧ s < 3/2 := by
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  dsimp [s] at *
  constructor <;> nlinarith

theorem contact_division (t : ℝ) :
    c t = -t + (1-t) / Real.sqrt 2 ∧
    d t = -t - (1-t) / Real.sqrt 2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  constructor
  · dsimp [c,s]
    field_simp
    linear_combination (1-t)*hs
  · dsimp [d,s]
    field_simp
    linear_combination (-(1-t))*hs

/-- The strict scalar inequalities that control every local Gram argument. -/
theorem contact_inequalities (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25) :
    d t < b t ∧ b t < c t ∧ c t < 2*(d t)^2-1 ∧
    2*(d t)^2-1 < a t ∧ 1+a t+2*d t < 0 ∧
    (1+b t)*(1+d t)-(a t+d t)^2 < 0 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  change s^2 = 2 at hs
  obtain ⟨hsL,hsU⟩ := sqrt_bounds
  have ht : 0 < t := by linarith
  have ht1 : t < 1 := by linarith
  have ht2 : 0 < 1-t := by linarith
  have hsProdL := mul_pos ht2 (sub_pos.mpr hsL)
  have hsProdU := mul_pos ht2 (sub_pos.mpr hsU)
  have hd : d t < -(79:ℝ)/100 := by dsimp [d]; nlinarith
  have hcl : 0 < c t := by dsimp [c]; nlinarith
  have hcu : c t < (21:ℝ)/100 := by dsimp [c]; nlinarith
  have hid1 : 2*(d t)^2-1-a t = (3-2*s)*t*(t-1) := by
    dsimp [d,a]
    linear_combination ((1-t)^2/2)*hs
  have hid2 : 1+a t+2*d t = (s-1)*(t-1) := by dsimp [a,d]; ring
  have hid3 : (1+b t)*(1+d t)-(a t+d t)^2 =
      (t-1)/2*(1-(5-2*s)*t) := by
    dsimp [a,b,d]
    linear_combination (-(1-t)^2/4)*hs
  have hprod := mul_pos ht (show 0 < s-7/5 by linarith)
  have hlast : 0 < 1-(5-2*s)*t := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [b]; linarith
  · dsimp [b]; linarith
  · nlinarith [sq_nonneg (d t + 79/100)]
  · rw [← sub_neg, hid1]
    exact mul_neg_of_pos_of_neg (mul_pos (by linarith) ht) (by linarith)
  · rw [hid2]
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  · rw [hid3]
    exact mul_neg_of_neg_of_pos (by linarith) hlast

/-- Separation of the coefficients of `1, √2, t, t√2`. -/
def CoefficientSeparation (t : ℝ) : Prop :=
  ∀ A B C D : ℚ,
    (A:ℝ)+(B:ℝ)*s+t*((C:ℝ)+(D:ℝ)*s)=0 →
    A=0 ∧ B=0 ∧ C=0 ∧ D=0

/-- A zero row sum determines the four integer contact multiplicities. -/
theorem multiplicities_from_row_sum (t : ℝ) (hsep : CoefficientSeparation t)
    (n₁ n₂ n₃ n₄ : ℕ) (hn : n₁+n₂+n₃+n₄=7)
    (hrow : 1+(n₁:ℝ)*a t+(n₂:ℝ)*b t+(n₃:ℝ)*c t+(n₄:ℝ)*d t=0) :
    n₁=2 ∧ n₂=1 ∧ n₃=2 ∧ n₄=2 := by
  have he := hsep (1-(n₂:ℚ)) (((n₃:ℚ)-n₄)/2)
    ((n₁:ℚ)+2*n₂-n₃-n₄) (-((n₃:ℚ)-n₄)/2) (by
      push_cast
      dsimp [a,b,c,d] at hrow
      nlinarith [hrow])
  obtain ⟨h₁,h₂,h₃,h₄⟩ := he
  have e₂ : (n₂:ℚ)=1 := by linarith
  have e₃ : (n₃:ℚ)=(n₄:ℚ) := by linarith
  have e₁ : (n₁:ℚ)+2*(n₂:ℚ)=(n₃:ℚ)+(n₄:ℚ) := by linarith
  have en : (n₁:ℚ)+(n₂:ℚ)+(n₃:ℚ)+(n₄:ℚ)=7 := by exact_mod_cast hn
  have E₁ : (n₁:ℚ)=2 := by linarith
  have E₃ : (n₃:ℚ)=2 := by linarith
  have E₄ : (n₄:ℚ)=2 := by linarith
  exact ⟨by exact_mod_cast E₁, by exact_mod_cast e₂,
    by exact_mod_cast E₃, by exact_mod_cast E₄⟩


/- A second, finite proof of the multiplicities, using only the parameter interval.
The finite case split is checked by the kernel, independently of the field lemma. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem multiplicities_from_interval (t : ℝ)
    (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (n₁ n₂ n₃ n₄ : ℕ) (hn : n₁+n₂+n₃+n₄=7)
    (hrow : 1+(n₁:ℝ)*a t+(n₂:ℝ)*b t+(n₃:ℝ)*c t+(n₄:ℝ)*d t=0) :
    n₁=2 ∧ n₂=1 ∧ n₃=2 ∧ n₄=2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  change s^2=2 at hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsL : (7071:ℝ)/5000 < s := by nlinarith
  have hsU : s < (14143:ℝ)/10000 := by nlinarith
  have hLL := mul_nonneg (sub_nonneg.mpr hL.le) (sub_nonneg.mpr hsL.le)
  have hLU := mul_nonneg (sub_nonneg.mpr hL.le) (sub_nonneg.mpr hsU.le)
  have hUL := mul_nonneg (sub_nonneg.mpr hU.le) (sub_nonneg.mpr hsL.le)
  have hUU := mul_nonneg (sub_nonneg.mpr hU.le) (sub_nonneg.mpr hsU.le)
  have hn₁ : n₁ ≤ 7 := by omega
  have hn₂ : n₂ ≤ 7 := by omega
  have hn₃ : n₃ ≤ 7 := by omega
  have hn₄ : n₄ ≤ 7 := by omega
  interval_cases n₁ <;> interval_cases n₂ <;> interval_cases n₃ <;>
    first | omega | (interval_cases n₄ <;>
      first | omega | (norm_num [a,b,c,d] at hrow; nlinarith only [hrow,hLL,hLU,hUL,hUU]))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The nonnegative squared norm is the three-point Gram constraint. -/
theorem neighbors_inner_lower (x y z : V) (δ : ℝ)
    (hx : ⟪x,x⟫_ℝ=1) (hy : ⟪y,y⟫_ℝ=1) (hz : ⟪z,z⟫_ℝ=1)
    (hxy : ⟪x,y⟫_ℝ=δ) (hxz : ⟪x,z⟫_ℝ=δ) :
    2*δ^2-1 ≤ ⟪y,z⟫_ℝ := by
  have h := real_inner_self_nonneg (x:=y+z-(2*δ) • x)
  simp only [inner_sub_left,inner_sub_right,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right] at h
  have hyx := (real_inner_comm x y).trans hxy
  have hzx := (real_inner_comm x z).trans hxz
  rw [hx,hy,hz,hxy,hxz,hyx,hzx,real_inner_comm y z] at h
  nlinarith

/-- Thus the endpoints of each two-edge path have contact value `a`. -/
theorem neighbors_contact (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (x y z : V) (hx : ⟪x,x⟫_ℝ=1) (hy : ⟪y,y⟫_ℝ=1) (hz : ⟪z,z⟫_ℝ=1)
    (hxy : ⟪x,y⟫_ℝ=d t) (hxz : ⟪x,z⟫_ℝ=d t)
    (hcontact : ⟪y,z⟫_ℝ=a t ∨ ⟪y,z⟫_ℝ=b t ∨ ⟪y,z⟫_ℝ=c t ∨ ⟪y,z⟫_ℝ=d t) :
    ⟪y,z⟫_ℝ=a t := by
  have h := neighbors_inner_lower x y z (d t) hx hy hz hxy hxz
  obtain ⟨hdb,hbc,hcq,_,_,_⟩ := contact_inequalities t hL hU
  rcases hcontact with h'|h'|h'|h'
  · exact h'
  all_goals linarith

/-- A four-cycle would have a negative squared norm for its vertex sum. -/
theorem exclude_four_cycle (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (x₀ x₁ x₂ x₃ : V)
    (h₀ : ⟪x₀,x₀⟫_ℝ=1) (h₁ : ⟪x₁,x₁⟫_ℝ=1)
    (h₂ : ⟪x₂,x₂⟫_ℝ=1) (h₃ : ⟪x₃,x₃⟫_ℝ=1)
    (h₀₁ : ⟪x₀,x₁⟫_ℝ=d t) (h₁₂ : ⟪x₁,x₂⟫_ℝ=d t)
    (h₂₃ : ⟪x₂,x₃⟫_ℝ=d t) (h₀₃ : ⟪x₀,x₃⟫_ℝ=d t)
    (h₀₂ : ⟪x₀,x₂⟫_ℝ=a t) (h₁₃ : ⟪x₁,x₃⟫_ℝ=a t) : False := by
  have h := real_inner_self_nonneg (x:=x₀+x₁+x₂+x₃)
  simp only [inner_add_left,inner_add_right] at h
  have h₁₀ := (real_inner_comm x₀ x₁).trans h₀₁
  have h₂₀ := (real_inner_comm x₀ x₂).trans h₀₂
  have h₃₀ := (real_inner_comm x₀ x₃).trans h₀₃
  have h₂₁ := (real_inner_comm x₁ x₂).trans h₁₂
  have h₃₁ := (real_inner_comm x₁ x₃).trans h₁₃
  have h₃₂ := (real_inner_comm x₂ x₃).trans h₂₃
  rw [h₀,h₁,h₂,h₃,h₀₁,h₁₂,h₂₃,h₀₃,h₀₂,h₁₃,h₁₀,h₂₀,h₃₀,h₂₁,h₃₁,h₃₂] at h
  have hn := (contact_inequalities t hL hU).2.2.2.2.1
  linarith


/-- The two-dimensional compression excludes contact `b` at distance three. -/
theorem exclude_path_three_b (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (x₀ x₁ x₂ x₃ : V)
    (h₀ : ⟪x₀,x₀⟫_ℝ=1) (h₁ : ⟪x₁,x₁⟫_ℝ=1)
    (h₂ : ⟪x₂,x₂⟫_ℝ=1) (h₃ : ⟪x₃,x₃⟫_ℝ=1)
    (h₀₁ : ⟪x₀,x₁⟫_ℝ=d t) (h₁₂ : ⟪x₁,x₂⟫_ℝ=d t)
    (h₂₃ : ⟪x₂,x₃⟫_ℝ=d t) (h₀₃ : ⟪x₀,x₃⟫_ℝ=b t)
    (h₀₂ : ⟪x₀,x₂⟫_ℝ=a t) (h₁₃ : ⟪x₁,x₃⟫_ℝ=a t) : False := by
  have h := real_inner_mul_inner_self_le (x₀+x₃) (x₁+x₂)
  simp only [inner_add_left,inner_add_right] at h
  have h₃₀ := (real_inner_comm x₀ x₃).trans h₀₃
  have h₂₁ := (real_inner_comm x₁ x₂).trans h₁₂
  have h₃₁ := (real_inner_comm x₁ x₃).trans h₁₃
  have h₃₂ := (real_inner_comm x₂ x₃).trans h₂₃
  rw [h₀,h₁,h₂,h₃,h₀₁,h₁₂,h₀₃,h₀₂,h₃₀,h₂₁,h₃₁,h₃₂] at h
  have hn := (contact_inequalities t hL hU).2.2.2.2.2
  nlinarith

end Thomson78.Eight
