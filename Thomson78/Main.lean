import Thomson78.Certificate
import Thomson78.SphereEnergy
import Thomson78.SevenRigidity
import Thomson78.SevenDimension
import Thomson78.SevenMinorantBound
import Thomson78.EightCandidate
import Thomson78.EightParameter
import Thomson78.AnalysisEightMinorant
import Thomson78.Harmonics
import Thomson78.SevenEnergy
import Thomson78.EightEnergy

/-! Main implications after evaluating the finite computer-assisted certificate.

`certificate_pairing` supplies the displayed identity from the finite coefficient
identity. Matrix positivity, the analytic minorants, the harmonic term and both
geometric classifications are mathematical theorems proved in this project.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix
namespace Thomson78

abbrev R3 := EuclideanSpace ℝ (Fin 3)

def harmonic3 {n : ℕ} (x : Fin n → R3) : ℝ :=
  ∑ i, ∑ j, Harmonics.P3 ⟪x i,x j⟫_ℝ

theorem seven_certificate_equality
    (x : Fin 7 → R3) (hx : Admissible x) (τ μ₁ μ₃ : ℝ)
    {J K L : Type*} [Fintype J] [Fintype K] [Fintype L]
    (B : J → Matrix K K ℝ) (F : J → Matrix K L ℝ)
    (hB : ∀ j, (B j).PosSemidef) (hμ₁ : 0 < μ₁) (hμ₃ : 0 ≤ μ₃)
    (hcertificate : pairEnergy Seven.h7.eval x - τ =
      μ₁ * ‖∑ i, x i‖^2 + μ₃ * harmonic3 x +
        ∑ j, Matrix.trace ((F j * (F j)ᴴ) * B j)) :
    τ ≤ coulombEnergy x ∧
      (coulombEnergy x = τ → Seven.Configuration x) := by
  have hp := energy_bound_and_equality x Analysis.coulomb Seven.h7.eval
    {u | Seven.Contact u} τ μ₁ μ₃ (harmonic3 x)
    (fun j => Matrix.trace ((F j * (F j)ᴴ) * B j)) hμ₁ hμ₃
    (Harmonics.P3_sum_nonneg x hx.1)
    (fun j => trace_factor_nonneg (B j) (F j) (hB j))
    (fun i j hij => Seven.h7_minorant (admissible_inner_interval hx hij).1
      (admissible_inner_interval hx hij).2)
    (fun i j hij => Seven.h7_equality_iff (admissible_inner_interval hx hij).1
      (admissible_inner_interval hx hij).2) hcertificate
  rw [← coulombEnergy_eq_pairEnergy x hx.1] at hp
  refine ⟨hp.1, fun he => ?_⟩
  obtain ⟨hc,hz⟩ := hp.2 he
  exact ⟨norm_configuration_unit_inner hx.1, hc, hz⟩

theorem seven_certificate_rigidity
    (x : Fin 7 → R3) (hx : Admissible x) (τ μ₁ μ₃ : ℝ)
    {J K L : Type*} [Fintype J] [Fintype K] [Fintype L]
    (B : J → Matrix K K ℝ) (F : J → Matrix K L ℝ)
    (hB : ∀ j, (B j).PosSemidef) (hμ₁ : 0 < μ₁) (hμ₃ : 0 ≤ μ₃)
    (hcertificate : pairEnergy Seven.h7.eval x - τ =
      μ₁ * ‖∑ i, x i‖^2 + μ₃ * harmonic3 x +
        ∑ j, Matrix.trace ((F j * (F j)ᴴ) * B j))
    (he : coulombEnergy x = τ) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range x)) = 3 ∧
    ∃ e₁ e₂ e₃ : R3,
      ⟪e₁,e₁⟫_ℝ=1 ∧ ⟪e₂,e₂⟫_ℝ=1 ∧ ⟪e₃,e₃⟫_ℝ=1 ∧
      ⟪e₁,e₂⟫_ℝ=0 ∧ ⟪e₁,e₃⟫_ℝ=0 ∧ ⟪e₂,e₃⟫_ℝ=0 ∧
      Set.range x = {e₃,-e₃} ∪ Set.range (fun k : Fin 5 =>
        Real.cos (2*Real.pi*k/5) • e₁ + Real.sin (2*Real.pi*k/5) • e₂) := by
  have h := (seven_certificate_equality x hx τ μ₁ μ₃ B F hB hμ₁ hμ₃ hcertificate).2 he
  exact ⟨Seven.rigidity_finrank h, Seven.rigidity h⟩

theorem eight_certificate_rigidity
    (x : Fin 8 → R3) (hx : Admissible x) (μ₁ μ₃ : ℝ)
    {J K L : Type*} [Fintype J] [Fintype K] [Fintype L]
    (B : J → Matrix K K ℝ) (F : J → Matrix K L ℝ)
    (hB : ∀ j, (B j).PosSemidef) (hμ₁ : 0 < μ₁) (hμ₃ : 0 ≤ μ₃)
    (hcertificate : pairEnergy (Eight.h8 Eight.tStar).eval x -
        coulombEnergy (Eight.candidate Eight.tStar) =
      μ₁ * ‖∑ i, x i‖^2 + μ₃ * harmonic3 x +
        ∑ j, Matrix.trace ((F j * (F j)ᴴ) * B j)) :
    coulombEnergy (Eight.candidate Eight.tStar) ≤ coulombEnergy x ∧
      (coulombEnergy x = coulombEnergy (Eight.candidate Eight.tStar) →
        ∃ (σ : Equiv.Perm (Fin 8)) (U : R3 →ₗᵢ[ℝ] R3),
          ∀ i, U (Eight.candidate Eight.tStar i) = x (σ i)) := by
  let S : Set ℝ := {u | u = Eight.a Eight.tStar ∨ u = Eight.b Eight.tStar ∨
    u = Eight.c Eight.tStar ∨ u = Eight.d Eight.tStar}
  have hm (i j : Fin 8) (hij : i ≠ j) := Eight.h8_strict_minorant
    Eight.tStar (gram x i j) Eight.tStar_bounds.1 Eight.tStar_bounds.2
      (admissible_inner_interval hx hij).1 (admissible_inner_interval hx hij).2
  have hp := energy_bound_and_equality x Analysis.coulomb (Eight.h8 Eight.tStar).eval
    S (coulombEnergy (Eight.candidate Eight.tStar)) μ₁ μ₃ (harmonic3 x)
    (fun j => Matrix.trace ((F j * (F j)ᴴ) * B j)) hμ₁ hμ₃
    (Harmonics.P3_sum_nonneg x hx.1)
    (fun j => trace_factor_nonneg (B j) (F j) (hB j))
    (fun i j hij => (hm i j hij).1) (fun i j hij => (hm i j hij).2) hcertificate
  rw [← coulombEnergy_eq_pairEnergy x hx.1] at hp
  refine ⟨hp.1, fun he => ?_⟩
  obtain ⟨hc,hz⟩ := hp.2 he
  exact Eight.rigidity_isometry Eight.tStar Eight.tStar_bounds.1 Eight.tStar_bounds.2
    x (norm_configuration_unit_inner hx.1) hc hz

/-- The seven-point certificate with its target fixed to the candidate energy. -/
theorem seven_candidate_minimum
    (x : Fin 7 → R3) (hx : Admissible x) (μ₁ μ₃ : ℝ)
    {J K L : Type*} [Fintype J] [Fintype K] [Fintype L]
    (B : J → Matrix K K ℝ) (F : J → Matrix K L ℝ)
    (hB : ∀ j, (B j).PosSemidef) (hμ₁ : 0 < μ₁) (hμ₃ : 0 ≤ μ₃)
    (hcertificate : pairEnergy Seven.h7.eval x - coulombEnergy Seven.candidate =
      μ₁ * ‖∑ i, x i‖^2 + μ₃ * harmonic3 x +
        ∑ j, Matrix.trace ((F j * (F j)ᴴ) * B j)) :
    coulombEnergy Seven.candidate ≤ coulombEnergy x ∧
    (coulombEnergy x = coulombEnergy Seven.candidate → Seven.Configuration x) :=
  seven_certificate_equality x hx _ μ₁ μ₃ B F hB hμ₁ hμ₃ hcertificate

/-- The lower bound in the radical form used in the manuscript. -/
theorem seven_radical_lower_bound
    (x : Fin 7 → R3) (hx : Admissible x) (μ₁ μ₃ : ℝ)
    {J K L : Type*} [Fintype J] [Fintype K] [Fintype L]
    (B : J → Matrix K K ℝ) (F : J → Matrix K L ℝ)
    (hB : ∀ j, (B j).PosSemidef) (hμ₁ : 0 < μ₁) (hμ₃ : 0 ≤ μ₃)
    (hcertificate : pairEnergy Seven.h7.eval x - coulombEnergy Seven.candidate =
      μ₁ * ‖∑ i, x i‖^2 + μ₃ * harmonic3 x +
        ∑ j, Matrix.trace ((F j * (F j)ᴴ) * B j)) :
    1/2 + 5*Real.sqrt 2 + (1/2)*Real.sqrt (50-10*Real.sqrt 5) +
      (1/2)*Real.sqrt (50+10*Real.sqrt 5) ≤ coulombEnergy x := by
  rw [← Seven.candidate_energy_radical]
  exact (seven_candidate_minimum x hx μ₁ μ₃ B F hB hμ₁ hμ₃ hcertificate).1

end Thomson78

#print axioms Thomson78.seven_certificate_rigidity
#print axioms Thomson78.eight_certificate_rigidity
