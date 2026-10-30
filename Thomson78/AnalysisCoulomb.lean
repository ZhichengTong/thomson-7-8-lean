import Thomson78.Analysis
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Positive derivative sequence of the Coulomb kernel. -/
noncomputable section

open Filter
open scoped Topology

namespace Thomson78.Analysis

/-- The positive-argument square-root derivative, obtained from the inverse
of the square map using Mathlib's one-dimensional inverse derivative theorem. -/
theorem sqrt_hasDerivAt_of_pos (x : ℝ) (hx : 0 < x) :
    HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := by
  have hs : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hpow : HasDerivAt (fun y : ℝ => y^2) (2*Real.sqrt x) (Real.sqrt x) := by
    simpa using hasDerivAt_pow 2 (Real.sqrt x)
  have hne : 2*Real.sqrt x ≠ 0 := mul_ne_zero (by norm_num) hs
  have hlocal : ∀ᶠ y in nhds x, (Real.sqrt y)^2 = y :=
    (eventually_gt_nhds hx).mono (fun y hy => Real.sq_sqrt hy.le)
  simpa [one_div] using hpow.of_local_left_inverse Real.continuous_sqrt.continuousAt hne hlocal

def oddFactor : ℕ → ℝ
  | 0 => 1
  | n+1 => (2*n+1) * oddFactor n

def coulombDerivative (n : ℕ) (t : ℝ) : ℝ :=
  oddFactor n * (Real.sqrt (2-2*t))⁻¹ ^ (2*n+1)

def coulomb (t : ℝ) : ℝ := (Real.sqrt (2-2*t))⁻¹

theorem coulombDerivative_zero : coulombDerivative 0 = coulomb := by
  funext t
  simp [coulombDerivative, oddFactor, coulomb]

theorem oddFactor_pos (n : ℕ) : 0 < oddFactor n := by
  induction n with
  | zero => norm_num [oddFactor]
  | succ n ih => simp only [oddFactor]; positivity

theorem coulombDerivative_pos (n : ℕ) (t : ℝ) (ht : t < 1) :
    0 < coulombDerivative n t := by
  unfold coulombDerivative
  have hh : 0 < 2-2*t := by linarith
  have hs : 0 < Real.sqrt (2-2*t) := Real.sqrt_pos.2 hh
  exact mul_pos (oddFactor_pos n) (pow_pos (inv_pos.2 hs) _)

theorem coulomb_hasDerivAt (t : ℝ) (ht : t < 1) :
    HasDerivAt coulomb ((Real.sqrt (2-2*t))⁻¹ ^ 3) t := by
  have hh : 0 < 2-2*t := by linarith
  have hs : Real.sqrt (2-2*t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hh)
  have hbase : HasDerivAt (fun x : ℝ => 2-2*x) (-2) t := by
    convert (hasDerivAt_const t (2 : ℝ)).sub ((hasDerivAt_id t).const_mul 2) using 1
    · rfl
    · norm_num
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (2-2*x))
      ((-2)/(2*Real.sqrt (2-2*t))) t := by
    convert (sqrt_hasDerivAt_of_pos (2-2*t) hh).comp t hbase using 1
    · rfl
    · ring
  have h := hsqrt.inv hs
  convert h using 1
  · rfl
  · field_simp

theorem coulombDerivative_hasDerivAt (n : ℕ) (t : ℝ) (ht : t < 1) :
    HasDerivAt (coulombDerivative n) (coulombDerivative (n+1) t) t := by
  have h := ((coulomb_hasDerivAt t ht).pow (2*n+1)).const_mul (oddFactor n)
  convert h using 1
  · rfl
  · simp only [coulombDerivative, oddFactor, coulomb, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, Nat.add_sub_cancel]
    have hpow : 2*(n+1)+1 = 2*n+3 := by omega
    rw [hpow, pow_add]
    ring

theorem coulombDerivative_strictMono (n : ℕ) (x y : ℝ) (hxy : x < y) (hy : y < 1) :
    coulombDerivative n x < coulombDerivative n y := by
  have hx : x < 1 := hxy.trans hy
  have hsx : 0 < Real.sqrt (2-2*x) := Real.sqrt_pos.2 (by linarith)
  have hsy : 0 < Real.sqrt (2-2*y) := Real.sqrt_pos.2 (by linarith)
  have hs : Real.sqrt (2-2*y) < Real.sqrt (2-2*x) :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hi : (Real.sqrt (2-2*x))⁻¹ < (Real.sqrt (2-2*y))⁻¹ :=
    (inv_lt_inv₀ hsx hsy).2 hs
  unfold coulombDerivative
  apply mul_lt_mul_of_pos_left _ (oddFactor_pos n)
  exact pow_lt_pow_left₀ hi (inv_nonneg.2 hsx.le) (by omega)

theorem coulombDerivative_eight_endpoint :
    coulombDerivative 8 (-1) / (Nat.factorial 8) = (6435/16777216 : ℝ) := by
  norm_num [coulombDerivative, oddFactor, Nat.factorial]

end Thomson78.Analysis

