import Thomson78.SevenPentagon
import Thomson78.SphereEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Thomson78.Seven

abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- The pentagon is listed in the recurrence order, followed by its two poles. -/
def candidate : Fin 7 → R3 :=
  let s := Real.sin theta
  ![!₂[1,0,0], !₂[b,s,0], !₂[a,2*b*s,0], !₂[a,-2*b*s,0], !₂[b,-s,0],
    !₂[0,0,1], !₂[0,0,-1]]

def candidateGram : Fin 7 → Fin 7 → ℝ :=
  ![![1,b,a,a,b,0,0], ![b,1,b,a,a,0,0], ![a,b,1,b,a,0,0],
    ![a,a,b,1,b,0,0], ![b,a,a,b,1,0,0], ![0,0,0,0,0,1,-1], ![0,0,0,0,0,-1,1]]

theorem candidate_gram (i j : Fin 7) :
    ⟪candidate i, candidate j⟫_ℝ = candidateGram i j := by
  have hb := contact_arithmetic.2.2.2
  have hab : a = -1/2-b := by linarith [contact_arithmetic.1]
  have hs : Real.sin theta ^ 2 = 1-b^2 := by
    have hh := Real.sin_sq_add_cos_sq theta
    rw [theta_cos] at hh
    linarith
  have hb3 : 8*b^3 = 4*b-1 := by nlinarith [sq_nonneg (2*b+1)]
  have hb4 : 16*b^4 = 2-6*b := by nlinarith [sq_nonneg (2*b+1)]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  fin_cases i <;> fin_cases j <;>
    norm_num [candidate, candidateGram, Fin.sum_univ_succ, hab] <;>
    ring_nf <;> (try rw [hs]) <;> (try ring_nf) <;> nlinarith

theorem candidate_unit (i : Fin 7) : ‖candidate i‖ = 1 := by
  have hh := candidate_gram i i
  have hd : candidateGram i i = 1 := by fin_cases i <;> rfl
  rw [hd, real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (candidate i)]

theorem candidate_contact (i j : Fin 7) (hij : i ≠ j) :
    Contact ⟪candidate i, candidate j⟫_ℝ := by
  rw [candidate_gram]
  fin_cases i <;> fin_cases j <;> norm_num [candidateGram, Contact] at * <;>
    first | contradiction | tauto

theorem candidate_centroid : ∑ i, candidate i = 0 := by
  have hab := contact_arithmetic.1
  ext j
  fin_cases j <;> simp [candidate, Fin.sum_univ_succ] <;> linarith

theorem candidate_configuration : Configuration candidate :=
  ⟨fun i => by rw [real_inner_self_eq_norm_sq, candidate_unit]; norm_num,
    candidate_contact, candidate_centroid⟩

theorem candidate_admissible : Admissible candidate :=
  ⟨candidate_unit, candidate_configuration.injective⟩

private theorem pairs_seven : pairs 7 =
    {(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),
      (1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),
      (3,4),(3,5),(3,6),(4,5),(4,6),(5,6)} := by decide

/-- The contact multiplicities are (1,10,5,5) for (-1,0,a,b). -/
theorem candidate_pair_sum (f : ℝ → ℝ) :
    pairEnergy f candidate = f (-1) + 10*f 0 + 5*f a + 5*f b := by
  unfold pairEnergy gram
  simp_rw [candidate_gram]
  rw [pairs_seven]
  norm_num [candidateGram]
  ring

theorem candidate_energy : coulombEnergy candidate =
    1/2 + 10*Analysis.coulomb 0 + 5*Analysis.coulomb a + 5*Analysis.coulomb b := by
  rw [coulombEnergy_eq_pairEnergy candidate candidate_unit, candidate_pair_sum]
  norm_num [Analysis.coulomb]

private theorem five_inverse_sqrt (q r : ℝ) (hq : 0 < q) (hr : 0 < r)
    (hqr : q*r = 100) : 5 * (Real.sqrt q)⁻¹ = Real.sqrt r / 2 := by
  have hs : (Real.sqrt q * Real.sqrt r)^2 = 100 := by
    rw [mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hr.le, hqr]
  have hp : Real.sqrt q * Real.sqrt r = 10 := by
    have hn := mul_nonneg (Real.sqrt_nonneg q) (Real.sqrt_nonneg r)
    nlinarith
  have hnq : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  field_simp
  nlinarith

theorem candidate_energy_radical : coulombEnergy candidate =
    1/2 + 5*Real.sqrt 2 + (1/2)*Real.sqrt (50-10*Real.sqrt 5) +
      (1/2)*Real.sqrt (50+10*Real.sqrt 5) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hb := sqrt_five_bounds
  have h0 : 10*Analysis.coulomb 0 = 5*Real.sqrt 2 := by
    norm_num [Analysis.coulomb]
    have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    nlinarith
  have ha : 5*Analysis.coulomb a = Real.sqrt (50+10*Real.sqrt 5)/2 := by
    apply five_inverse_sqrt
    · linarith [contact_bounds.2.2.2]
    · linarith
    · dsimp [a]; nlinarith
  have hbb : 5*Analysis.coulomb b = Real.sqrt (50-10*Real.sqrt 5)/2 := by
    apply five_inverse_sqrt
    · linarith [contact_bounds.2.1]
    · linarith
    · dsimp [b]; nlinarith
  rw [candidate_energy, h0, ha, hbb]
  ring

#print axioms candidate_pair_sum
#print axioms candidate_energy
#print axioms candidate_energy_radical

end Thomson78.Seven
