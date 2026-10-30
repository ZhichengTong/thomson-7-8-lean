import Thomson78.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module

/-! The seven-point argument: exact contact arithmetic and the vector recurrence.
The statements in this file have no computer-assisted hypotheses. -/
noncomputable section
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace Thomson78.Seven

def a : ℝ := (Real.sqrt 5 - 1) / 4
def b : ℝ := -(Real.sqrt 5 + 1) / 4
def Contact (u : ℝ) : Prop := u = -1 ∨ u = 0 ∨ u = a ∨ u = b

theorem sqrt_five_bounds : 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  constructor <;> nlinarith

theorem contact_arithmetic :
    a + b = -1 / 2 ∧ a * b = -1 / 4 ∧ 2 * b ^ 2 - 1 = a ∧
    4 * b ^ 2 + 2 * b - 1 = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [a, b]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ring
  all_goals nlinarith

theorem contact_bounds : -1 < b ∧ b < 0 ∧ 0 < a ∧ a < 1 := by
  have hs := sqrt_five_bounds
  dsimp [a, b]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem contact_le_a {u : ℝ} (hu : Contact u) : u ≤ a := by
  have h := contact_bounds
  rcases hu with rfl | rfl | rfl | rfl <;> linarith

theorem contact_lt_one {u : ℝ} (hu : Contact u) : u < 1 :=
  lt_of_le_of_lt (contact_le_a hu) contact_bounds.2.2.2

theorem contact_neg_intersection {u : ℝ} (hu : Contact u) (hnu : Contact (-u)) :
    u = 0 := by
  have ha := contact_arithmetic.1
  have hb := contact_bounds
  rcases hu with h | h | h | h <;>
    rcases hnu with hn | hn | hn | hn <;> linarith

theorem row_counts (m n₀ nₐ nᵦ : ℕ) (hm : m ≤ 1)
    (hsum : m + n₀ + nₐ + nᵦ = 6)
    (hrow : (1 : ℝ) - m + a * nₐ + b * nᵦ = 0) :
    nₐ = 2 * (1 - m) ∧ nᵦ = 2 * (1 - m) ∧ n₀ = 2 + 3 * m := by
  have hirr : Irrational (Real.sqrt 5) := by
    simpa using (show Nat.Prime 5 by decide).irrational_sqrt
  have heq : nₐ = nᵦ := by
    by_contra hne
    have hnz : (nₐ : ℝ) - nᵦ ≠ 0 := by
      intro hz
      apply hne
      exact_mod_cast (sub_eq_zero.mp hz)
    have hbad := hirr.ne_rational ((4 : ℤ) * m + nₐ + nᵦ - 4) ((nₐ : ℤ) - nᵦ)
    apply hbad
    push_cast
    apply (eq_div_iff hnz).mpr
    dsimp [a, b] at hrow
    linarith
  have hreal : (nₐ : ℝ) = 2 * (1 - (m : ℝ)) := by
    rw [heq] at hrow ⊢
    have hab := contact_arithmetic.1
    nlinarith
  interval_cases m <;> norm_num at hreal ⊢ <;> norm_cast at hreal <;> omega

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem zero_centroid_row {n : ℕ} (x : Fin n → V)
    (hc : ∑ j, x j = 0) (i : Fin n) : ∑ j, ⟪x i, x j⟫_ℝ = 0 := by
  rw [← inner_sum, hc, inner_zero_right]

theorem antipodal_of_inner (x y : V) (hx : ⟪x, x⟫_ℝ = 1)
    (hy : ⟪y, y⟫_ℝ = 1) (hxy : ⟪x, y⟫_ℝ = -1) : y = -x := by
  have hyx : ⟪y, x⟫_ℝ = -1 := by rw [real_inner_comm, hxy]
  have hzero : ⟪y + x, y + x⟫_ℝ = 0 := by
    simp only [inner_add_left, inner_add_right, hx, hy, hxy, hyx]
    norm_num
  have hsum : y + x = 0 := (inner_self_eq_zero).mp hzero
  exact eq_neg_of_add_eq_zero_left hsum

theorem antipodal_pair_orthogonal (e y : V)
    (he : Contact ⟪e, y⟫_ℝ) (hne : Contact ⟪-e, y⟫_ℝ) : ⟪e, y⟫_ℝ = 0 := by
  apply contact_neg_intersection he
  simpa only [inner_neg_left] using hne

/-- The nonnegative squared norm replaces the equivalent three by three Gram minor. -/
theorem neighbor_recurrence (x y z : V)
    (hx : ⟪x, x⟫_ℝ = 1) (hy : ⟪y, y⟫_ℝ = 1) (hz : ⟪z, z⟫_ℝ = 1)
    (hxy : ⟪x, y⟫_ℝ = b) (hxz : ⟪x, z⟫_ℝ = b)
    (hyz : Contact ⟪y, z⟫_ℝ) :
    ⟪y, z⟫_ℝ = a ∧ y + z = (2 * b) • x := by
  have hyx : ⟪y, x⟫_ℝ = b := by simpa [real_inner_comm] using hxy
  have hzx : ⟪z, x⟫_ℝ = b := by simpa [real_inner_comm] using hxz
  have hzy : ⟪z, y⟫_ℝ = ⟪y, z⟫_ℝ := real_inner_comm _ _
  have hn : 0 ≤ ⟪y + z - (2 * b) • x, y + z - (2 * b) • x⟫_ℝ :=
    real_inner_self_nonneg
  have hexp : ⟪y + z - (2 * b) • x, y + z - (2 * b) • x⟫_ℝ =
      2 + 2 * ⟪y, z⟫_ℝ - 4 * b ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hx, hy, hz, hxy, hxz, hyx, hzx, hzy]
    ring
  have hmax := contact_le_a hyz
  have harith := contact_arithmetic.2.2.1
  have hyza : ⟪y, z⟫_ℝ = a := by rw [hexp] at hn; linarith
  refine ⟨hyza, ?_⟩
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [hexp, hyza]
  linarith

/-- Five steps of the second-order vector recurrence close exactly. -/
theorem recurrence_five (v : ℕ → V)
    (hv : ∀ k, v (k + 2) = (2 * b) • v (k + 1) - v k) :
    v 5 = v 0 ∧ v 6 = v 1 := by
  have hb := contact_arithmetic.2.2.2
  have h2 := hv 0
  have h3 := hv 1
  have h4 := hv 2
  have h5 := hv 3
  have h6 := hv 4
  norm_num at h2 h3 h4 h5 h6
  have hb3 : 8 * b ^ 3 = 4 * b - 1 := by nlinarith [sq_nonneg (2 * b + 1)]
  have hb4 : 16 * b ^ 4 = 2 - 6 * b := by nlinarith [sq_nonneg (2 * b + 1)]
  have hv5 : v 5 = v 0 := by
    rw [h5, h4, h3, h2]
    match_scalars <;> nlinarith
  refine ⟨hv5, ?_⟩
  rw [h6, hv5, h4, h3, h2]
  match_scalars <;> nlinarith

theorem recurrence_periodic (v : ℕ → V)
    (hv : ∀ k, v (k + 2) = (2 * b) • v (k + 1) - v k) :
    ∀ k, v (k + 5) = v k := by
  have hinit := recurrence_five v hv
  apply Nat.twoStepInduction
  · simpa using hinit.1
  · simpa using hinit.2
  · intro k hk hk1
    have hstep := hv (k + 5)
    rw [show k + 5 + 2 = k + 2 + 5 by omega,
      show k + 5 + 1 = k + 1 + 5 by omega, hk1, hk] at hstep
    simpa only [hv k] using hstep

end Thomson78.Seven
