import Thomson78.AnalysisCoulomb
import Mathlib.Tactic.FinCases

/-! Differentiation of the auxiliary energy along the antiprism family. -/
noncomputable section
open scoped BigOperators
namespace Thomson78.Analysis

def contactSlope : Fin 4 → ℝ := ![1,2,-1-Real.sqrt 2/2,-1+Real.sqrt 2/2]
def contactOffset : Fin 4 → ℝ := ![0,-1,Real.sqrt 2/2,-Real.sqrt 2/2]

theorem contact_affine (t : ℝ) (i : Fin 4) :
    antiprismContacts t i = contactOffset i + contactSlope i*t := by
  fin_cases i <;> norm_num [antiprismContacts,contactOffset,contactSlope] <;> ring

theorem contact_hasDerivAt (t : ℝ) (i : Fin 4) :
    HasDerivAt (fun u => antiprismContacts u i) (contactSlope i) t := by
  convert ((hasDerivAt_id t).const_mul (contactSlope i)).const_add (contactOffset i) using 1
  · ext u
    rw [contact_affine]
    rfl
  · simp

def antiprismEnergy (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ i, antiprismWeights i * f (antiprismContacts t i)

def antiprismSlope (f' : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ i, antiprismWeights i * f' (antiprismContacts t i) * contactSlope i

theorem antiprismEnergy_hasDerivAt (f f' : ℝ → ℝ) (t : ℝ)
    (hf : ∀ i, HasDerivAt f (f' (antiprismContacts t i)) (antiprismContacts t i)) :
    HasDerivAt (antiprismEnergy f) (antiprismSlope f' t) t := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      HasDerivAt (fun u => antiprismWeights i*f (antiprismContacts u i))
        (antiprismWeights i*(f' (antiprismContacts t i)*contactSlope i)) t := by
    intro i hi
    exact ((hf i).comp t (contact_hasDerivAt t i)).const_mul (antiprismWeights i)
  convert HasDerivAt.fun_sum h using 1
  · rfl
  · simp only [antiprismSlope, mul_assoc]

theorem polynomial_antiprism_hasDerivAt (p : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (antiprismEnergy p.eval) (antiprismSlope p.derivative.eval t) t :=
  antiprismEnergy_hasDerivAt _ _ t (fun i => p.hasDerivAt _)

theorem coulomb_antiprism_hasDerivAt (t : ℝ) (ht : ∀ i, antiprismContacts t i < 1) :
    HasDerivAt (antiprismEnergy coulomb) (antiprismSlope (coulombDerivative 1) t) t := by
  apply antiprismEnergy_hasDerivAt
  intro i
  simpa only [coulombDerivative_zero] using coulombDerivative_hasDerivAt 0 _ (ht i)

/-- Interpolation at the four contacts preserves the value and derivative of
the energy at the candidate parameter. -/
theorem antiprism_interpolation_value_derivative (p : Polynomial ℝ) (t : ℝ)
    (ht : ∀ i, antiprismContacts t i < 1)
    (hv : ∀ i, p.eval (antiprismContacts t i) = coulomb (antiprismContacts t i))
    (hd : ∀ i, p.derivative.eval (antiprismContacts t i) =
      coulombDerivative 1 (antiprismContacts t i)) :
    antiprismEnergy p.eval t = antiprismEnergy coulomb t ∧
      deriv (antiprismEnergy p.eval) t = deriv (antiprismEnergy coulomb) t := by
  constructor
  · simp only [antiprismEnergy, hv]
  · rw [(polynomial_antiprism_hasDerivAt p t).deriv,
      (coulomb_antiprism_hasDerivAt t ht).deriv]
    simp only [antiprismSlope, hd]

end Thomson78.Analysis
