import Thomson78.Harmonics
import Mathlib.Tactic.FinCases

/-! Positive semidefiniteness of every Legendre kernel used in the manuscript.
The degrees zero through eight are verified using real harmonic polynomials.
All addition identities are polynomial identities checked by the Lean kernel.
The rational weights are 1 for m=0 and 2(l-m)!/(l+m)! for m>0. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Matrix
namespace Thomson78.LegendreKernel

abbrev R3 := EuclideanSpace ℝ (Fin 3)

def squareNorm (u : Fin 3 → ℝ) : ℝ := ∑ i, (u i)^2

def homogeneousKernel (l : Fin 9) (t r : ℝ) : ℝ :=
  match l.val with
  | 0 => 1
  | 1 => t
  | 2 => (((-1/2 : ℝ) * r) + ((3/2 : ℝ) * (t^2)))
  | 3 => (((5/2 : ℝ) * (t^3)) + ((-3/2 : ℝ) * r * t))
  | 4 => (((3/8 : ℝ) * (r^2)) + ((35/8 : ℝ) * (t^4)) + ((-15/4 : ℝ) * r * (t^2)))
  | 5 => (((63/8 : ℝ) * (t^5)) + ((-35/4 : ℝ) * r * (t^3)) + ((15/8 : ℝ) * t * (r^2)))
  | 6 => (((-5/16 : ℝ) * (r^3)) + ((231/16 : ℝ) * (t^6)) + ((-315/16 : ℝ) * r * (t^4)) + ((105/16 : ℝ) * (r^2) * (t^2)))
  | 7 => (((429/16 : ℝ) * (t^7)) + ((-693/16 : ℝ) * r * (t^5)) + ((-35/16 : ℝ) * t * (r^3)) + ((315/16 : ℝ) * (r^2) * (t^3)))
  | 8 => (((35/128 : ℝ) * (r^4)) + ((6435/128 : ℝ) * (t^8)) + ((-3003/32 : ℝ) * r * (t^6)) + ((-315/32 : ℝ) * (r^3) * (t^2)) + ((3465/64 : ℝ) * (r^2) * (t^4)))
  | _ => 0

def legendre (l : Fin 9) (t : ℝ) : ℝ := homogeneousKernel l t 1

def homogeneousDerivative (l m : Fin 9) (z r : ℝ) : ℝ :=
  match l.val, m.val with
  | 0, 0 => 1
  | 1, 0 => z
  | 1, 1 => 1
  | 2, 0 => (((-1/2 : ℝ) * r) + ((3/2 : ℝ) * (z^2)))
  | 2, 1 => (3 * z)
  | 2, 2 => 3
  | 3, 0 => (((5/2 : ℝ) * (z^3)) + ((-3/2 : ℝ) * r * z))
  | 3, 1 => (((-3/2 : ℝ) * r) + ((15/2 : ℝ) * (z^2)))
  | 3, 2 => (15 * z)
  | 3, 3 => 15
  | 4, 0 => (((3/8 : ℝ) * (r^2)) + ((35/8 : ℝ) * (z^4)) + ((-15/4 : ℝ) * r * (z^2)))
  | 4, 1 => (((35/2 : ℝ) * (z^3)) + ((-15/2 : ℝ) * r * z))
  | 4, 2 => (((-15/2 : ℝ) * r) + ((105/2 : ℝ) * (z^2)))
  | 4, 3 => (105 * z)
  | 4, 4 => 105
  | 5, 0 => (((63/8 : ℝ) * (z^5)) + ((-35/4 : ℝ) * r * (z^3)) + ((15/8 : ℝ) * z * (r^2)))
  | 5, 1 => (((15/8 : ℝ) * (r^2)) + ((315/8 : ℝ) * (z^4)) + ((-105/4 : ℝ) * r * (z^2)))
  | 5, 2 => (((315/2 : ℝ) * (z^3)) + ((-105/2 : ℝ) * r * z))
  | 5, 3 => (((-105/2 : ℝ) * r) + ((945/2 : ℝ) * (z^2)))
  | 5, 4 => (945 * z)
  | 5, 5 => 945
  | 6, 0 => (((-5/16 : ℝ) * (r^3)) + ((231/16 : ℝ) * (z^6)) + ((-315/16 : ℝ) * r * (z^4)) + ((105/16 : ℝ) * (r^2) * (z^2)))
  | 6, 1 => (((693/8 : ℝ) * (z^5)) + ((-315/4 : ℝ) * r * (z^3)) + ((105/8 : ℝ) * z * (r^2)))
  | 6, 2 => (((105/8 : ℝ) * (r^2)) + ((3465/8 : ℝ) * (z^4)) + ((-945/4 : ℝ) * r * (z^2)))
  | 6, 3 => (((3465/2 : ℝ) * (z^3)) + ((-945/2 : ℝ) * r * z))
  | 6, 4 => (((-945/2 : ℝ) * r) + ((10395/2 : ℝ) * (z^2)))
  | 6, 5 => (10395 * z)
  | 6, 6 => 10395
  | 7, 0 => (((429/16 : ℝ) * (z^7)) + ((-693/16 : ℝ) * r * (z^5)) + ((-35/16 : ℝ) * z * (r^3)) + ((315/16 : ℝ) * (r^2) * (z^3)))
  | 7, 1 => (((-35/16 : ℝ) * (r^3)) + ((3003/16 : ℝ) * (z^6)) + ((-3465/16 : ℝ) * r * (z^4)) + ((945/16 : ℝ) * (r^2) * (z^2)))
  | 7, 2 => (((9009/8 : ℝ) * (z^5)) + ((-3465/4 : ℝ) * r * (z^3)) + ((945/8 : ℝ) * z * (r^2)))
  | 7, 3 => (((945/8 : ℝ) * (r^2)) + ((45045/8 : ℝ) * (z^4)) + ((-10395/4 : ℝ) * r * (z^2)))
  | 7, 4 => (((45045/2 : ℝ) * (z^3)) + ((-10395/2 : ℝ) * r * z))
  | 7, 5 => (((-10395/2 : ℝ) * r) + ((135135/2 : ℝ) * (z^2)))
  | 7, 6 => (135135 * z)
  | 7, 7 => 135135
  | 8, 0 => (((35/128 : ℝ) * (r^4)) + ((6435/128 : ℝ) * (z^8)) + ((-3003/32 : ℝ) * r * (z^6)) + ((-315/32 : ℝ) * (r^3) * (z^2)) + ((3465/64 : ℝ) * (r^2) * (z^4)))
  | 8, 1 => (((6435/16 : ℝ) * (z^7)) + ((-9009/16 : ℝ) * r * (z^5)) + ((-315/16 : ℝ) * z * (r^3)) + ((3465/16 : ℝ) * (r^2) * (z^3)))
  | 8, 2 => (((-315/16 : ℝ) * (r^3)) + ((45045/16 : ℝ) * (z^6)) + ((-45045/16 : ℝ) * r * (z^4)) + ((10395/16 : ℝ) * (r^2) * (z^2)))
  | 8, 3 => (((135135/8 : ℝ) * (z^5)) + ((-45045/4 : ℝ) * r * (z^3)) + ((10395/8 : ℝ) * z * (r^2)))
  | 8, 4 => (((10395/8 : ℝ) * (r^2)) + ((675675/8 : ℝ) * (z^4)) + ((-135135/4 : ℝ) * r * (z^2)))
  | 8, 5 => (((675675/2 : ℝ) * (z^3)) + ((-135135/2 : ℝ) * r * z))
  | 8, 6 => (((-135135/2 : ℝ) * r) + ((2027025/2 : ℝ) * (z^2)))
  | 8, 7 => (2027025 * z)
  | 8, 8 => 2027025
  | _, _ => 0

def realPower (m : Fin 9) (u v : ℝ) : ℝ :=
  match m.val with
  | 0 => 1
  | 1 => u
  | 2 => ((u^2) + ((-1) * (v^2)))
  | 3 => ((u^3) + ((-3) * u * (v^2)))
  | 4 => ((u^4) + (v^4) + ((-6) * (u^2) * (v^2)))
  | 5 => ((u^5) + ((-10) * (u^3) * (v^2)) + (5 * u * (v^4)))
  | 6 => ((u^6) + ((-1) * (v^6)) + ((-15) * (u^4) * (v^2)) + (15 * (u^2) * (v^4)))
  | 7 => ((u^7) + ((-21) * (u^5) * (v^2)) + ((-7) * u * (v^6)) + (35 * (u^3) * (v^4)))
  | 8 => ((u^8) + (v^8) + ((-28) * (u^2) * (v^6)) + ((-28) * (u^6) * (v^2)) + (70 * (u^4) * (v^4)))
  | _ => 0

def imagPower (m : Fin 9) (u v : ℝ) : ℝ :=
  match m.val with
  | 0 => 0
  | 1 => v
  | 2 => (2 * u * v)
  | 3 => (((-1) * (v^3)) + (3 * v * (u^2)))
  | 4 => (((-4) * u * (v^3)) + (4 * v * (u^3)))
  | 5 => ((v^5) + ((-10) * (u^2) * (v^3)) + (5 * v * (u^4)))
  | 6 => (((-20) * (u^3) * (v^3)) + (6 * u * (v^5)) + (6 * v * (u^5)))
  | 7 => (((-1) * (v^7)) + ((-35) * (u^4) * (v^3)) + (7 * v * (u^6)) + (21 * (u^2) * (v^5)))
  | 8 => (((-56) * (u^5) * (v^3)) + ((-8) * u * (v^7)) + (8 * v * (u^7)) + (56 * (u^3) * (v^5)))
  | _ => 0

def weight (l m : Fin 9) : ℝ :=
  if m.val ≤ l.val then
    if m.val = 0 then 1 else 2*(Nat.factorial (l.val-m.val) : ℝ)/(Nat.factorial (l.val+m.val))
  else 0

def realFeature (l m : Fin 9) (u : Fin 3 → ℝ) : ℝ :=
  homogeneousDerivative l m (u 2) (squareNorm u) * realPower m (u 0) (u 1)

def imagFeature (l m : Fin 9) (u : Fin 3 → ℝ) : ℝ :=
  homogeneousDerivative l m (u 2) (squareNorm u) * imagPower m (u 0) (u 1)

theorem weight_nonneg (l m : Fin 9) : 0 ≤ weight l m := by
  unfold weight
  split_ifs <;> positivity

theorem legendre_zero (t : ℝ) : legendre 0 t = 1 := rfl
theorem legendre_one (t : ℝ) : legendre 1 t = t := by simp [legendre,homogeneousKernel]

theorem legendre_normalized (l : Fin 9) : legendre l 1 = 1 := by
  fin_cases l <;> norm_num [legendre,homogeneousKernel]

/-- The defining three-term Legendre recurrence through degree eight. -/
theorem legendre_recurrence (n : Fin 7) (t : ℝ) :
    ((n.val+2 : ℕ) : ℝ) * legendre ⟨n.val+2,by omega⟩ t =
      ((2*n.val+3 : ℕ) : ℝ)*t*legendre ⟨n.val+1,by omega⟩ t -
      ((n.val+1 : ℕ) : ℝ)*legendre ⟨n.val,by omega⟩ t := by
  fin_cases n <;> norm_num [legendre,homogeneousKernel] <;> ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem addition_hom_0 (u v : Fin 3 → ℝ) :
    homogeneousKernel 0 (∑ i, u i*v i) (squareNorm u*squareNorm v) =
      ∑ m : Fin 9, weight 0 m *
        (realFeature 0 m u*realFeature 0 m v + imagFeature 0 m u*imagFeature 0 m v) := by
  norm_num [homogeneousKernel,weight,realFeature,imagFeature,homogeneousDerivative,
    squareNorm,realPower,imagPower,Fin.sum_univ_succ,Nat.factorial]
  all_goals ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem addition_hom_1 (u v : Fin 3 → ℝ) :
    homogeneousKernel 1 (∑ i, u i*v i) (squareNorm u*squareNorm v) =
      ∑ m : Fin 9, weight 1 m *
        (realFeature 1 m u*realFeature 1 m v + imagFeature 1 m u*imagFeature 1 m v) := by
  norm_num [homogeneousKernel,weight,realFeature,imagFeature,homogeneousDerivative,
    squareNorm,realPower,imagPower,Fin.sum_univ_succ,Nat.factorial]
  all_goals ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem addition_hom_2 (u v : Fin 3 → ℝ) :
    homogeneousKernel 2 (∑ i, u i*v i) (squareNorm u*squareNorm v) =
      ∑ m : Fin 9, weight 2 m *
        (realFeature 2 m u*realFeature 2 m v + imagFeature 2 m u*imagFeature 2 m v) := by
  norm_num [homogeneousKernel,weight,realFeature,imagFeature,homogeneousDerivative,
    squareNorm,realPower,imagPower,Fin.sum_univ_succ,Nat.factorial]
  all_goals ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem addition_hom_3 (u v : Fin 3 → ℝ) :
    homogeneousKernel 3 (∑ i, u i*v i) (squareNorm u*squareNorm v) =
      ∑ m : Fin 9, weight 3 m *
        (realFeature 3 m u*realFeature 3 m v + imagFeature 3 m u*imagFeature 3 m v) := by
  norm_num [homogeneousKernel,weight,realFeature,imagFeature,homogeneousDerivative,
    squareNorm,realPower,imagPower,Fin.sum_univ_succ,Nat.factorial]
  all_goals ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem addition_hom_4 (u v : Fin 3 → ℝ) :
    homogeneousKernel 4 (∑ i, u i*v i) (squareNorm u*squareNorm v) =
      ∑ m : Fin 9, weight 4 m *
        (realFeature 4 m u*realFeature 4 m v + imagFeature 4 m u*imagFeature 4 m v) := by
  norm_num [homogeneousKernel,weight,realFeature,imagFeature,homogeneousDerivative,
    squareNorm,realPower,imagPower,Fin.sum_univ_succ,Nat.factorial]
  all_goals ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem addition_hom_5 (u v : Fin 3 → ℝ) :
    homogeneousKernel 5 (∑ i, u i*v i) (squareNorm u*squareNorm v) =
      ∑ m : Fin 9, weight 5 m *
        (realFeature 5 m u*realFeature 5 m v + imagFeature 5 m u*imagFeature 5 m v) := by
  norm_num [homogeneousKernel,weight,realFeature,imagFeature,homogeneousDerivative,
    squareNorm,realPower,imagPower,Fin.sum_univ_succ,Nat.factorial]
  all_goals ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem addition_hom_6 (u v : Fin 3 → ℝ) :
    homogeneousKernel 6 (∑ i, u i*v i) (squareNorm u*squareNorm v) =
      ∑ m : Fin 9, weight 6 m *
        (realFeature 6 m u*realFeature 6 m v + imagFeature 6 m u*imagFeature 6 m v) := by
  norm_num [homogeneousKernel,weight,realFeature,imagFeature,homogeneousDerivative,
    squareNorm,realPower,imagPower,Fin.sum_univ_succ,Nat.factorial]
  all_goals ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem addition_hom_7 (u v : Fin 3 → ℝ) :
    homogeneousKernel 7 (∑ i, u i*v i) (squareNorm u*squareNorm v) =
      ∑ m : Fin 9, weight 7 m *
        (realFeature 7 m u*realFeature 7 m v + imagFeature 7 m u*imagFeature 7 m v) := by
  norm_num [homogeneousKernel,weight,realFeature,imagFeature,homogeneousDerivative,
    squareNorm,realPower,imagPower,Fin.sum_univ_succ,Nat.factorial]
  all_goals ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem addition_hom_8 (u v : Fin 3 → ℝ) :
    homogeneousKernel 8 (∑ i, u i*v i) (squareNorm u*squareNorm v) =
      ∑ m : Fin 9, weight 8 m *
        (realFeature 8 m u*realFeature 8 m v + imagFeature 8 m u*imagFeature 8 m v) := by
  norm_num [homogeneousKernel,weight,realFeature,imagFeature,homogeneousDerivative,
    squareNorm,realPower,imagPower,Fin.sum_univ_succ,Nat.factorial]
  all_goals ring

theorem homogeneous_addition (l : Fin 9) (u v : Fin 3 → ℝ) :
    homogeneousKernel l (∑ i, u i*v i) (squareNorm u*squareNorm v) =
      ∑ m : Fin 9, weight l m *
        (realFeature l m u*realFeature l m v + imagFeature l m u*imagFeature l m v) := by
  fin_cases l
  · exact addition_hom_0 u v
  · exact addition_hom_1 u v
  · exact addition_hom_2 u v
  · exact addition_hom_3 u v
  · exact addition_hom_4 u v
  · exact addition_hom_5 u v
  · exact addition_hom_6 u v
  · exact addition_hom_7 u v
  · exact addition_hom_8 u v

end Thomson78.LegendreKernel
