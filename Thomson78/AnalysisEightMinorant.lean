import Thomson78.AnalysisMinorants
import Thomson78.EightGeometry
import Mathlib.Tactic.Tauto

/-! The strict Hermite minorant at the four square-antiprism contacts. -/
noncomputable section
open Polynomial
namespace Thomson78.Eight

def minorantNodes (t : ℝ) : Fin 4 → ℝ := ![d t, b t, c t, a t]

def h8 (t : ℝ) : ℝ[X] := Analysis.correctedHermite (minorantNodes t)

theorem minorantNodes_strictMono (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25) :
    StrictMono (minorantNodes t) := by
  obtain ⟨hdb,hbc,hcm,hma,_,_⟩ := contact_inequalities t hL hU
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [minorantNodes] at * <;> linarith

theorem minorantNodes_lower (t : ℝ) (hU : t < 8/25) : -1 < minorantNodes t 0 := by
  obtain ⟨hsL,hsU⟩ := sqrt_bounds
  have ht : 0 < 1-t := by linarith
  have hp := mul_pos ht (show 0 < (3:ℝ)/2-s by linarith)
  norm_num [minorantNodes, d]
  nlinarith

theorem h8_strict_minorant (t u : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (hu₀ : -1 ≤ u) (hu₁ : u < 1) :
    (h8 t).eval u ≤ Analysis.coulomb u ∧
      ((h8 t).eval u = Analysis.coulomb u ↔
        u = a t ∨ u = b t ∨ u = c t ∨ u = d t) := by
  have h := Analysis.correctedHermite_strict_minorant (minorantNodes t)
    (minorantNodes_strictMono t hL hU) (minorantNodes_lower t hU).le
    (by norm_num [minorantNodes, a]; linarith) u hu₀ hu₁
  refine ⟨h.1, ?_⟩
  change (Analysis.correctedHermite (minorantNodes t)).eval u = _ ↔ _
  rw [h.2]
  norm_num [minorantNodes]
  tauto

theorem h8_degree (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25) :
    (h8 t).natDegree ≤ 8 :=
  Analysis.correctedHermite_degree _ (minorantNodes_strictMono t hL hU).injective

theorem h8_degree_exact (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25) :
    (h8 t).natDegree = 8 :=
  Analysis.correctedHermite_degree_exact _ (minorantNodes_strictMono t hL hU).injective

theorem h8_contact (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25) (i : Fin 4) :
    (h8 t).eval (minorantNodes t i) = Analysis.coulomb (minorantNodes t i) :=
  Analysis.correctedHermite_eval _ (minorantNodes_strictMono t hL hU).injective i

theorem h8_derivative_contact (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25) (i : Fin 4) :
    (h8 t).derivative.eval (minorantNodes t i) =
      Analysis.coulombDerivative 1 (minorantNodes t i) :=
  Analysis.correctedHermite_derivative_eval _ (minorantNodes_strictMono t hL hU).injective i

end Thomson78.Eight
