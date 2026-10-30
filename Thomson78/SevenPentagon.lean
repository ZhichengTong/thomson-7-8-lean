import Thomson78.SevenConfiguration
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace Thomson78.Seven

def theta : ℝ := 4 * Real.pi / 5

theorem theta_cos : Real.cos theta = b := by
  rw [show theta = Real.pi - Real.pi / 5 by dsimp [theta]; ring,
    Real.cos_pi_sub, Real.cos_pi_div_five]
  dsimp [b]
  ring

theorem theta_sin_pos : 0 < Real.sin theta := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · dsimp [theta]; positivity
  · dsimp [theta]; linarith [Real.pi_pos]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem recurrence_unique (v w : ℕ → V)
    (hv : ∀ k, v (k + 2) = (2 * b) • v (k + 1) - v k)
    (hw : ∀ k, w (k + 2) = (2 * b) • w (k + 1) - w k)
    (h0 : v 0 = w 0) (h1 : v 1 = w 1) : ∀ k, v k = w k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more k hk hk1 => rw [hv, hw, hk, hk1]

theorem circle_recurrence (e₁ e₂ : V) :
    ∀ k : ℕ,
      Real.cos ((k + 2) * theta) • e₁ + Real.sin ((k + 2) * theta) • e₂ =
      (2 * b) • (Real.cos ((k + 1) * theta) • e₁ +
        Real.sin ((k + 1) * theta) • e₂) -
      (Real.cos (k * theta) • e₁ + Real.sin (k * theta) • e₂) := by
  intro k
  have hc := Real.cos_add_cos ((k + 2) * theta) (k * theta)
  have hs := Real.sin_add_sin ((k + 2) * theta) (k * theta)
  have hp : ((k + 2 : ℝ) * theta + k * theta) / 2 = (k + 1) * theta := by ring
  have hm : ((k + 2 : ℝ) * theta - k * theta) / 2 = theta := by ring
  rw [hp, hm, theta_cos] at hc hs
  match_scalars <;> linarith

theorem recurrence_circle (v : ℕ → V)
    (hv : ∀ k, v (k + 2) = (2 * b) • v (k + 1) - v k) :
    ∀ k, v k = Real.cos (k * theta) • v 0 +
      Real.sin (k * theta) • ((Real.sin theta)⁻¹ • (v 1 - b • v 0)) := by
  let e₂ := (Real.sin theta)⁻¹ • (v 1 - b • v 0)
  apply recurrence_unique v (fun k => Real.cos (k * theta) • v 0 +
    Real.sin (k * theta) • e₂) hv
  · intro k
    convert circle_recurrence (v 0) e₂ k using 1 <;> push_cast <;> rfl
  · simp
  · dsimp [e₂]
    simp only [Nat.cast_one, one_mul, theta_cos, smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt theta_sin_pos), one_smul]
    module

theorem circle_basis (x y : V) (hx : ⟪x, x⟫_ℝ = 1)
    (hy : ⟪y, y⟫_ℝ = 1) (hxy : ⟪x, y⟫_ℝ = b) :
    let e₂ := (Real.sin theta)⁻¹ • (y - b • x)
    ⟪x, e₂⟫_ℝ = 0 ∧ ⟪e₂, e₂⟫_ℝ = 1 := by
  dsimp
  have hyx : ⟪y, x⟫_ℝ = b := by rw [real_inner_comm, hxy]
  have hs := Real.sin_sq_add_cos_sq theta
  rw [theta_cos] at hs
  have hsn := ne_of_gt theta_sin_pos
  constructor
  · simp only [real_inner_smul_right, inner_sub_right, hxy,
      real_inner_smul_right, hx]
    ring
  · simp only [real_inner_smul_left, real_inner_smul_right,
      inner_sub_left, inner_sub_right, hx, hy, hxy, hyx]
    field_simp
    nlinarith

theorem recurrence_sum_five (v : ℕ → V)
    (hv : ∀ k, v (k + 2) = (2 * b) • v (k + 1) - v k) :
    ∑ k : Fin 5, v k = 0 := by
  have h2 := hv 0
  have h3 := hv 1
  have h4 := hv 2
  norm_num at h2 h3 h4
  have hb := contact_arithmetic.2.2.2
  have hb3 : 8 * b ^ 3 = 4 * b - 1 := by nlinarith [sq_nonneg (2 * b + 1)]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
    zero_add, add_zero]
  norm_num
  rw [h4, h3, h2]
  match_scalars <;> nlinarith

theorem pentagon_reindex (e₁ e₂ : V) :
    Set.range (fun k : Fin 5 => Real.cos (k * theta) • e₁ + Real.sin (k * theta) • e₂) =
      Set.range (fun k : Fin 5 => Real.cos (2 * Real.pi * k / 5) • e₁ +
        Real.sin (2 * Real.pi * k / 5) • e₂) := by
  let star (k : Fin 5) := Real.cos (k * theta) • e₁ + Real.sin (k * theta) • e₂
  let regular (k : Fin 5) := Real.cos (2 * Real.pi * k / 5) • e₁ +
    Real.sin (2 * Real.pi * k / 5) • e₂
  have h0 : star 0 = regular 0 := by simp [star, regular]
  have h1 : star 1 = regular 2 := by
    dsimp [star, regular, theta]
    congr 2 <;> ring
  have h2 : star 2 = regular 4 := by
    dsimp [star, regular, theta]
    congr 2 <;> ring
  have h3 : star 3 = regular 1 := by
    dsimp [star, regular, theta]
    norm_num only [Nat.cast_ofNat]
    rw [show (3 : ℝ) * (4 * Real.pi / 5) = 2 * Real.pi * 1 / 5 + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.sin_add_two_pi]
  have h4 : star 4 = regular 3 := by
    dsimp [star, regular, theta]
    norm_num only [Nat.cast_ofNat]
    rw [show (4 : ℝ) * (4 * Real.pi / 5) = 2 * Real.pi * 3 / 5 + 2 * Real.pi by ring,
      Real.cos_add_two_pi, Real.sin_add_two_pi]
  change Set.range star = Set.range regular
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact ⟨0, h0.symm⟩
    · exact ⟨2, h1.symm⟩
    · exact ⟨4, h2.symm⟩
    · exact ⟨1, h3.symm⟩
    · exact ⟨3, h4.symm⟩
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact ⟨0, h0⟩
    · exact ⟨3, h3⟩
    · exact ⟨1, h1⟩
    · exact ⟨4, h4⟩
    · exact ⟨2, h2⟩

end Thomson78.Seven
