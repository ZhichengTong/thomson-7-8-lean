import Thomson78.Main
import Mathlib.Algebra.MvPolynomial.Eval

/-! A certificate interface involving only a finite polynomial identity and
scalar signs. A matrix certificate can be expanded into this sum-of-squares
form using its factors and the feature identities. All variables are actual
Cartesian coordinates; evaluation and the sphere relations are proved here.
No configuration-dependent realization equation is a hypothesis of the final
seven- and eight-point theorems in this file. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Polynomial
namespace Thomson78.Coordinates

abbrev Poly (n : ℕ) := MvPolynomial (Fin n × Fin 3) ℝ

def evaluate {n : ℕ} (x : Fin n → R3) : Poly n →+* ℝ :=
  MvPolynomial.eval (fun p => x p.1 p.2)

def g {n : ℕ} (i j : Fin n) : Poly n :=
  ∑ k : Fin 3, MvPolynomial.X (i,k) * MvPolynomial.X (j,k)

def unit {n : ℕ} (i : Fin n) : Poly n := g i i - 1

def energy {n : ℕ} (h : ℝ[X]) : Poly n :=
  ∑ p ∈ pairs n, h.eval₂ MvPolynomial.C (g p.1 p.2)

def centroid (n : ℕ) : Poly n := ∑ i, ∑ j, g (n := n) i j

def third (n : ℕ) : Poly n :=
  ∑ i, ∑ j, (MvPolynomial.C (5/2:ℝ) * (g (n := n) i j)^3 -
    MvPolynomial.C (3/2:ℝ) * g i j)

theorem evaluate_g {n : ℕ} (x : Fin n → R3) (i j : Fin n) :
    evaluate x (g i j) = gram x i j := by
  simp only [evaluate, g, map_sum, map_mul, MvPolynomial.eval_X, gram,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem evaluate_unit {n : ℕ} (x : Fin n → R3) (hu : ∀ i, ‖x i‖ = 1) (i : Fin n) :
    evaluate x (unit i) = 0 := by
  simp only [unit, map_sub, map_one, evaluate_g, gram,
    real_inner_self_eq_norm_sq, hu, one_pow, sub_self]

theorem evaluate_lift {n : ℕ} (x : Fin n → R3) (h : ℝ[X]) (p : Poly n) :
    evaluate x (h.eval₂ MvPolynomial.C p) = h.eval (evaluate x p) := by
  induction h using Polynomial.induction_on' with
  | add h k hh hk => simp only [Polynomial.eval₂_add, map_add, Polynomial.eval_add, hh, hk]
  | monomial k a =>
    simp [Polynomial.eval₂_monomial, Polynomial.eval_monomial, evaluate]

theorem evaluate_energy {n : ℕ} (x : Fin n → R3) (h : ℝ[X]) :
    evaluate x (energy h) = pairEnergy h.eval x := by
  simp only [energy, map_sum, evaluate_lift, evaluate_g, pairEnergy]

theorem evaluate_centroid {n : ℕ} (x : Fin n → R3) :
    evaluate x (centroid n) = ‖∑ i, x i‖^2 := by
  simp only [centroid, map_sum, evaluate_g]
  exact (centroid_norm_sq x).symm

theorem evaluate_third {n : ℕ} (x : Fin n → R3) :
    evaluate x (third n) = harmonic3 x := by
  simp only [third, map_sum, map_sub, map_mul, map_pow, evaluate, MvPolynomial.eval_C]
  change (∑ i, ∑ j, ((5/2:ℝ) * evaluate x (g i j)^3 -
    (3/2:ℝ) * evaluate x (g i j))) = harmonic3 x
  simp only [evaluate_g, harmonic3, gram, Harmonics.P3]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- All data in this proposition are finite real polynomials and scalars. -/
def Identity {n m : ℕ} (h : ℝ[X]) (τ μ₁ μ₃ : ℝ)
    (q : Fin m → Poly n) (lam : Fin n → Poly n) : Prop :=
  energy h - MvPolynomial.C τ =
    MvPolynomial.C μ₁ * centroid n + MvPolynomial.C μ₃ * third n +
    ∑ k, (q k)^2 + ∑ i, lam i * unit i

theorem evaluate_identity {n m : ℕ} (x : Fin n → R3) (hu : ∀ i, ‖x i‖ = 1)
    (h : ℝ[X]) (τ μ₁ μ₃ : ℝ) (q : Fin m → Poly n) (lam : Fin n → Poly n)
    (hid : Identity h τ μ₁ μ₃ q lam) :
    pairEnergy h.eval x - τ = μ₁ * ‖∑ i, x i‖^2 + μ₃ * harmonic3 x +
      ∑ k, (evaluate x (q k))^2 := by
  have he := congrArg (evaluate x) hid
  simp only [map_sub, map_add, map_mul, map_sum, map_pow, evaluate_unit x hu,
    mul_zero, Finset.sum_const_zero, add_zero, evaluate_energy, evaluate_centroid,
    evaluate_third] at he
  simpa only [evaluate, MvPolynomial.eval_C] using he

theorem certificate_equality {n m : ℕ}
    (h : ℝ[X]) (S : Set ℝ) (τ μ₁ μ₃ : ℝ)
    (q : Fin m → Poly n) (lam : Fin n → Poly n)
    (hμ₁ : 0 < μ₁) (hμ₃ : 0 ≤ μ₃) (hid : Identity h τ μ₁ μ₃ q lam)
    (hminorant : ∀ u, -1 ≤ u → u < 1 → h.eval u ≤ Analysis.coulomb u)
    (hcontact : ∀ u, -1 ≤ u → u < 1 →
      (h.eval u = Analysis.coulomb u ↔ u ∈ S)) :
    ∀ x : Fin n → R3, Admissible x →
      τ ≤ coulombEnergy x ∧
      (coulombEnergy x = τ →
        (∀ i j, i ≠ j → gram x i j ∈ S) ∧ ∑ i, x i = 0) := by
  intro x hx
  have hp := energy_bound_and_equality x Analysis.coulomb h.eval S τ μ₁ μ₃
    (harmonic3 x) (fun k => (evaluate x (q k))^2) hμ₁ hμ₃
    (Harmonics.P3_sum_nonneg x hx.1) (fun k => sq_nonneg _)
    (fun i j hij => hminorant _ (admissible_inner_interval hx hij).1
      (admissible_inner_interval hx hij).2)
    (fun i j hij => hcontact _ (admissible_inner_interval hx hij).1
      (admissible_inner_interval hx hij).2)
    (evaluate_identity x hx.1 h τ μ₁ μ₃ q lam hid)
  rwa [← coulombEnergy_eq_pairEnergy x hx.1] at hp

/-- The finite identity is fixed before the arbitrary configuration. -/
theorem seven_minimum {m : ℕ} (μ₁ μ₃ : ℝ)
    (q : Fin m → Poly 7) (lam : Fin 7 → Poly 7)
    (hμ₁ : 0 < μ₁) (hμ₃ : 0 ≤ μ₃)
    (hid : Identity Seven.h7 (coulombEnergy Seven.candidate) μ₁ μ₃ q lam) :
    ∀ x : Fin 7 → R3, Admissible x →
      coulombEnergy Seven.candidate ≤ coulombEnergy x ∧
      (coulombEnergy x = coulombEnergy Seven.candidate → Seven.Configuration x) := by
  intro x hx
  obtain ⟨hb,he⟩ := certificate_equality Seven.h7 {u | Seven.Contact u}
    (coulombEnergy Seven.candidate) μ₁ μ₃ q lam hμ₁ hμ₃ hid
    (fun _ hu hv => Seven.h7_minorant hu hv)
    (fun _ hu hv => Seven.h7_equality_iff hu hv) x hx
  exact ⟨hb, fun hh => ⟨norm_configuration_unit_inner hx.1, (he hh).1, (he hh).2⟩⟩

theorem eight_minimum {m : ℕ} (μ₁ μ₃ : ℝ)
    (q : Fin m → Poly 8) (lam : Fin 8 → Poly 8)
    (hμ₁ : 0 < μ₁) (hμ₃ : 0 ≤ μ₃)
    (hid : Identity (Eight.h8 Eight.tStar) (coulombEnergy (Eight.candidate Eight.tStar))
      μ₁ μ₃ q lam) :
    ∀ x : Fin 8 → R3, Admissible x →
      coulombEnergy (Eight.candidate Eight.tStar) ≤ coulombEnergy x ∧
      (coulombEnergy x = coulombEnergy (Eight.candidate Eight.tStar) →
        ∃ (σ : Equiv.Perm (Fin 8)) (U : R3 →ₗᵢ[ℝ] R3),
          ∀ i, U (Eight.candidate Eight.tStar i) = x (σ i)) := by
  intro x hx
  let S : Set ℝ := {u | u = Eight.a Eight.tStar ∨ u = Eight.b Eight.tStar ∨
    u = Eight.c Eight.tStar ∨ u = Eight.d Eight.tStar}
  have hm (u : ℝ) (h₀ : -1 ≤ u) (h₁ : u < 1) :=
    Eight.h8_strict_minorant Eight.tStar u Eight.tStar_bounds.1 Eight.tStar_bounds.2 h₀ h₁
  obtain ⟨hb,he⟩ := certificate_equality (Eight.h8 Eight.tStar) S
    (coulombEnergy (Eight.candidate Eight.tStar)) μ₁ μ₃ q lam hμ₁ hμ₃ hid
    (fun u h₀ h₁ => (hm u h₀ h₁).1) (fun u h₀ h₁ => (hm u h₀ h₁).2) x hx
  refine ⟨hb, fun hh => ?_⟩
  exact Eight.rigidity_isometry Eight.tStar Eight.tStar_bounds.1 Eight.tStar_bounds.2
    x (norm_configuration_unit_inner hx.1) (he hh).1 (he hh).2

end Thomson78.Coordinates

#print axioms Thomson78.Coordinates.seven_minimum
#print axioms Thomson78.Coordinates.eight_minimum
