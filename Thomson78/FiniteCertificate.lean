import Thomson78.Main

/-! Entry from a finite coefficient identity. The mathematical realization
equalities below are separate from the finite certificate identity `hid`.
In particular, positivity of an evaluated block is derived from its weighted
Gram representation, rather than assumed in the conclusion theorem. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix
namespace Thomson78

variable {D R J K L I : Type*} [Fintype D] [DecidableEq D]
  [Fintype R] [Fintype J] [Fintype K] [Fintype L] [Fintype I]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem realize_factorized_certificate
    {n : ℕ} (x : Fin n → R3) (h : ℝ → ℝ)
    (e : D) (c v₁ v₃ m : D → ℝ) (A : Matrix R D ℝ) (lam : R → ℝ)
    (B : J → D → Matrix K K ℝ) (F : J → Matrix K L ℝ)
    (w : J → I → ℝ) (v : J → I → K → W) (τ μ₁ μ₃ : ℝ)
    (hm : m e = 1) (hA : A *ᵥ m = 0)
    (hc : c ⬝ᵥ m = pairEnergy h x)
    (hv₁ : v₁ ⬝ᵥ m = ‖∑ i, x i‖^2) (hv₃ : v₃ ⬝ᵥ m = harmonic3 x)
    (hw : ∀ j i, 0 ≤ w j i)
    (hB : ∀ j, momentMatrix (B j) m = averagedGram (w j) (v j))
    (hid : c + Aᵀ *ᵥ lam = τ • Pi.single e 1 + μ₁ • v₁ + μ₃ • v₃ +
      ∑ j, traceCoefficient (F j * (F j)ᴴ) (B j)) :
    (∀ j, (momentMatrix (B j) m).PosSemidef) ∧
    pairEnergy h x - τ = μ₁ * ‖∑ i, x i‖^2 + μ₃ * harmonic3 x +
      ∑ j, Matrix.trace ((F j * (F j)ᴴ) * momentMatrix (B j) m) := by
  constructor
  · intro j
    rw [hB j]
    exact averagedGram_posSemidef (w j) (v j) (hw j)
  · have hp := certificate_pairing e c v₁ v₃ m A lam B
      (fun j => F j * (F j)ᴴ) τ μ₁ μ₃ hm hA hid
    simpa only [hc, hv₁, hv₃] using hp

theorem seven_finite_certificate
    (x : Fin 7 → R3) (hx : Admissible x)
    (e : D) (c v₁ v₃ m : D → ℝ) (A : Matrix R D ℝ) (lam : R → ℝ)
    (B : J → D → Matrix K K ℝ) (F : J → Matrix K L ℝ)
    (w : J → I → ℝ) (v : J → I → K → W) (μ₁ μ₃ : ℝ)
    (hm : m e = 1) (hA : A *ᵥ m = 0)
    (hc : c ⬝ᵥ m = pairEnergy Seven.h7.eval x)
    (hv₁ : v₁ ⬝ᵥ m = ‖∑ i, x i‖^2) (hv₃ : v₃ ⬝ᵥ m = harmonic3 x)
    (hw : ∀ j i, 0 ≤ w j i)
    (hB : ∀ j, momentMatrix (B j) m = averagedGram (w j) (v j))
    (hμ₁ : 0 < μ₁) (hμ₃ : 0 ≤ μ₃)
    (hid : c + Aᵀ *ᵥ lam = coulombEnergy Seven.candidate • Pi.single e 1 +
      μ₁ • v₁ + μ₃ • v₃ + ∑ j, traceCoefficient (F j * (F j)ᴴ) (B j)) :
    coulombEnergy Seven.candidate ≤ coulombEnergy x ∧
    (coulombEnergy x = coulombEnergy Seven.candidate → Seven.Configuration x) := by
  obtain ⟨hpos,he⟩ := realize_factorized_certificate x Seven.h7.eval e c v₁ v₃ m A lam
    B F w v (coulombEnergy Seven.candidate) μ₁ μ₃ hm hA hc hv₁ hv₃ hw hB hid
  exact seven_candidate_minimum x hx μ₁ μ₃ (fun j => momentMatrix (B j) m)
    F hpos hμ₁ hμ₃ he

theorem eight_finite_certificate
    (x : Fin 8 → R3) (hx : Admissible x)
    (e : D) (c v₁ v₃ m : D → ℝ) (A : Matrix R D ℝ) (lam : R → ℝ)
    (B : J → D → Matrix K K ℝ) (F : J → Matrix K L ℝ)
    (w : J → I → ℝ) (v : J → I → K → W) (μ₁ μ₃ : ℝ)
    (hm : m e = 1) (hA : A *ᵥ m = 0)
    (hc : c ⬝ᵥ m = pairEnergy (Eight.h8 Eight.tStar).eval x)
    (hv₁ : v₁ ⬝ᵥ m = ‖∑ i, x i‖^2) (hv₃ : v₃ ⬝ᵥ m = harmonic3 x)
    (hw : ∀ j i, 0 ≤ w j i)
    (hB : ∀ j, momentMatrix (B j) m = averagedGram (w j) (v j))
    (hμ₁ : 0 < μ₁) (hμ₃ : 0 ≤ μ₃)
    (hid : c + Aᵀ *ᵥ lam = coulombEnergy (Eight.candidate Eight.tStar) • Pi.single e 1 +
      μ₁ • v₁ + μ₃ • v₃ + ∑ j, traceCoefficient (F j * (F j)ᴴ) (B j)) :
    coulombEnergy (Eight.candidate Eight.tStar) ≤ coulombEnergy x ∧
    (coulombEnergy x = coulombEnergy (Eight.candidate Eight.tStar) →
      ∃ (σ : Equiv.Perm (Fin 8)) (U : R3 →ₗᵢ[ℝ] R3),
        ∀ i, U (Eight.candidate Eight.tStar i) = x (σ i)) := by
  obtain ⟨hpos,he⟩ := realize_factorized_certificate x (Eight.h8 Eight.tStar).eval
    e c v₁ v₃ m A lam B F w v (coulombEnergy (Eight.candidate Eight.tStar))
    μ₁ μ₃ hm hA hc hv₁ hv₃ hw hB hid
  exact eight_certificate_rigidity x hx μ₁ μ₃ (fun j => momentMatrix (B j) m)
    F hpos hμ₁ hμ₃ he

end Thomson78

#print axioms Thomson78.seven_finite_certificate
#print axioms Thomson78.eight_finite_certificate
