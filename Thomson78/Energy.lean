import Thomson78.Basic

/-! The energy/equality implication in Proposition 3.2.

The certificate identity is an explicit hypothesis. Its mathematical consequence
is proved here, including termwise equality and the zero centroid. This module
introduces no axiom and does not assume an energy minimum or rigidity theorem.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace InnerProductSpace
namespace Thomson78

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def pairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

def pairEnergy {n : ℕ} (f : ℝ → ℝ) (x : Fin n → V) : ℝ :=
  ∑ p ∈ pairs n, f (gram x p.1 p.2)

theorem pairEnergy_sub {n : ℕ} (f h : ℝ → ℝ) (x : Fin n → V) :
    pairEnergy f x - pairEnergy h x =
      ∑ p ∈ pairs n, (f (gram x p.1 p.2) - h (gram x p.1 p.2)) := by
  simp only [pairEnergy, Finset.sum_sub_distrib]

theorem energy_bound_and_equality
    {n : ℕ} (x : Fin n → V) (f h : ℝ → ℝ) (S : Set ℝ)
    (τ μ₁ μ₃ A₃ : ℝ) {J : Type*} [Fintype J] (T : J → ℝ)
    (hμ₁ : 0 < μ₁) (hμ₃ : 0 ≤ μ₃) (hA₃ : 0 ≤ A₃)
    (hT : ∀ j, 0 ≤ T j)
    (hminorant : ∀ i j, i ≠ j → h (gram x i j) ≤ f (gram x i j))
    (hcontact : ∀ i j, i ≠ j →
      (h (gram x i j) = f (gram x i j) ↔ gram x i j ∈ S))
    (hcertificate : pairEnergy h x - τ =
      μ₁ * ‖∑ i, x i‖ ^ 2 + μ₃ * A₃ + ∑ j, T j) :
    τ ≤ pairEnergy f x ∧
      (pairEnergy f x = τ →
        (∀ i j, i ≠ j → gram x i j ∈ S) ∧ ∑ i, x i = 0) := by
  classical
  let D : Fin n × Fin n → ℝ :=
    fun p => f (gram x p.1 p.2) - h (gram x p.1 p.2)
  have hD : ∀ p ∈ pairs n, 0 ≤ D p := by
    intro p hp
    have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    exact sub_nonneg.mpr (hminorant _ _ (ne_of_lt hp'))
  have hsumD : 0 ≤ ∑ p ∈ pairs n, D p := Finset.sum_nonneg hD
  have hsumT : 0 ≤ ∑ j, T j := Finset.sum_nonneg (fun j _ => hT j)
  have hcentroid : 0 ≤ μ₁ * ‖∑ i, x i‖ ^ 2 := mul_nonneg hμ₁.le (sq_nonneg _)
  have hthird : 0 ≤ μ₃ * A₃ := mul_nonneg hμ₃ hA₃
  have hdecomposition : pairEnergy f x - τ =
      (∑ p ∈ pairs n, D p) + μ₁ * ‖∑ i, x i‖ ^ 2 + μ₃ * A₃ + ∑ j, T j := by
    have hp := pairEnergy_sub f h x
    change pairEnergy f x - pairEnergy h x = ∑ p ∈ pairs n, D p at hp
    linarith
  constructor
  · linarith
  intro heq
  have hzD : ∑ p ∈ pairs n, D p = 0 := by linarith
  have hzcentroid : μ₁ * ‖∑ i, x i‖ ^ 2 = 0 := by linarith
  have hpair : ∀ i j, i < j → gram x i j ∈ S := by
    intro i j hij
    have hmem : (i,j) ∈ pairs n := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
    have hz : D (i,j) = 0 := (Finset.sum_eq_zero_iff_of_nonneg hD).mp hzD _ hmem
    apply (hcontact i j (ne_of_lt hij)).mp
    dsimp [D] at hz
    linarith
  constructor
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hpair i j hlt
    · rw [gram_symmetric]
      exact hpair j i hgt
  · have hs : ‖∑ i, x i‖ ^ 2 = 0 := (mul_eq_zero.mp hzcentroid).resolve_left (ne_of_gt hμ₁)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)

end Thomson78

#print axioms Thomson78.energy_bound_and_equality
