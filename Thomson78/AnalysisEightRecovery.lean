import Thomson78.AnalysisEightMinorant
import Thomson78.AnalysisFamily
import Thomson78.AnalysisRecovery
import Thomson78.EightParameter

/-! Complete value-and-stationarity recovery for the eight-point auxiliary
polynomial. The certificate blocks enter through their nonnegative trace sum. -/
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace Thomson78.Eight

/-- The auxiliary polynomial is fixed at parameter `t`; `u` varies along the
whole antiprism family. -/
def auxiliaryEnergy (t u : ℝ) : ℝ := Analysis.antiprismEnergy (h8 t).eval u

theorem contacts_lt_one (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25) :
    ∀ i, Analysis.antiprismContacts t i < 1 := by
  have hm : ∀ i, minorantNodes t i < 1 := by
    intro i
    have h := (minorantNodes_strictMono t hL hU).monotone (Fin.le_last i)
    have hlast : minorantNodes t (Fin.last 3) < 1 := by norm_num [minorantNodes,a]; linarith
    exact h.trans_lt hlast
  intro i
  fin_cases i
  · simpa [Analysis.antiprismContacts,minorantNodes,a] using hm 3
  · simpa [Analysis.antiprismContacts,minorantNodes,b] using hm 1
  · simpa [Analysis.antiprismContacts,minorantNodes,c] using hm 2
  · simpa [Analysis.antiprismContacts,minorantNodes,d] using hm 0

theorem h8_values_all_contacts (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25) :
    ∀ i, (h8 t).eval (Analysis.antiprismContacts t i) =
      Analysis.coulomb (Analysis.antiprismContacts t i) := by
  intro i
  fin_cases i
  · simpa [Analysis.antiprismContacts,minorantNodes,a] using h8_contact t hL hU 3
  · simpa [Analysis.antiprismContacts,minorantNodes,b] using h8_contact t hL hU 1
  · simpa [Analysis.antiprismContacts,minorantNodes,c] using h8_contact t hL hU 2
  · simpa [Analysis.antiprismContacts,minorantNodes,d] using h8_contact t hL hU 0

theorem h8_slopes_all_contacts (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25) :
    ∀ i, (h8 t).derivative.eval (Analysis.antiprismContacts t i) =
      Analysis.coulombDerivative 1 (Analysis.antiprismContacts t i) := by
  intro i
  fin_cases i
  · simpa [Analysis.antiprismContacts,minorantNodes,a] using h8_derivative_contact t hL hU 3
  · simpa [Analysis.antiprismContacts,minorantNodes,b] using h8_derivative_contact t hL hU 1
  · simpa [Analysis.antiprismContacts,minorantNodes,c] using h8_derivative_contact t hL hU 2
  · simpa [Analysis.antiprismContacts,minorantNodes,d] using h8_derivative_contact t hL hU 0

theorem antiprismEnergy_coulomb_eq_phi (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    Analysis.antiprismEnergy Analysis.coulomb t = phi t := by
  rw [phi_eq_weighted_coulomb t ht ht1]
  norm_num [Analysis.antiprismEnergy,Analysis.antiprismContacts,Analysis.antiprismWeights,
    Fin.sum_univ_succ,a,b,c,d]
  ring

theorem auxiliaryEnergy_value_derivative (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25) :
    auxiliaryEnergy t t = phi t ∧ HasDerivAt (auxiliaryEnergy t) (phiPrime t) t := by
  have ht : t ∈ Ioo (0:ℝ) 1 := by constructor <;> linarith
  have h := Analysis.antiprism_interpolation_value_derivative (h8 t) t
    (contacts_lt_one t hL hU) (h8_values_all_contacts t hL hU) (h8_slopes_all_contacts t hL hU)
  have hevent : Analysis.antiprismEnergy Analysis.coulomb =ᶠ[nhds t] phi :=
    (show ∀ᶠ u in nhds t, u ∈ Ioo (0:ℝ) 1 from isOpen_Ioo.mem_nhds ht).mono
      (fun u hu => antiprismEnergy_coulomb_eq_phi u hu.1 hu.2)
  have hw := (phi_hasDerivAt t ht).congr_of_eventuallyEq hevent
  constructor
  · exact h.1.trans (antiprismEnergy_coulomb_eq_phi t ht.1 ht.2)
  · have hh := (Analysis.polynomial_antiprism_hasDerivAt (h8 t) t).differentiableAt.hasDerivAt
    have he : deriv (Analysis.antiprismEnergy (h8 t).eval) t = phiPrime t := h.2.trans hw.deriv
    convert hh using 1
    · rfl
    · exact he.symm

/-- The two-coordinate recovery lemma at the uniquely defined stationary
parameter, with the value and derivative hypotheses discharged analytically. -/
theorem certificate_two_coordinates_zero (r₀ r₆ : ℝ) (G : ℝ → ℝ)
    (hidentity : ∀ u ∈ Ioo (0:ℝ) 1,
      r₀ + Analysis.sixthMoment u * r₆ = auxiliaryEnergy tStar u - phi tStar - G u)
    (hGnonneg : ∀ u ∈ Ioo (0:ℝ) 1, 0 ≤ G u)
    (hGvalue : G tStar = 0) (hGdiff : DifferentiableAt ℝ G tStar) :
    r₀ = 0 ∧ r₆ = 0 := by
  have h := auxiliaryEnergy_value_derivative tStar tStar_bounds.1 tStar_bounds.2
  apply Analysis.recover_certificate_residual tStar r₀ r₆ (phi tStar)
    (auxiliaryEnergy tStar) G tStar_bounds.1.le tStar_bounds.2 hidentity h.1
  · simpa only [phiPrime_tStar] using h.2
  · exact hGnonneg
  · exact hGvalue
  · exact hGdiff

end Thomson78.Eight
