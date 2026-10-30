import Thomson78.AnalysisRolle
import Thomson78.Analysis
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FieldSimp

/-! Hermite's remainder theorem from the repeated-node version of Rolle.
The ordered list contains all interpolation nodes with their multiplicities,
and one additional evaluation node, indexed by `u`. -/
noncomputable section
open scoped BigOperators
open Polynomial Set

namespace Thomson78.Analysis

def nodalPolynomial {n : ℕ} (x : Fin (n+1) → ℝ) (u : Fin (n+1)) : ℝ[X] :=
  ∏ i ∈ Finset.univ.erase u, (X-C (x i))

theorem nodalPolynomial_monic {n : ℕ} (x : Fin (n+1) → ℝ) (u : Fin (n+1)) :
    (nodalPolynomial x u).Monic := by
  apply monic_prod_of_monic
  intro i hi
  exact monic_X_sub_C _

theorem nodalPolynomial_degree {n : ℕ} (x : Fin (n+1) → ℝ) (u : Fin (n+1)) :
    (nodalPolynomial x u).natDegree = n := by
  unfold nodalPolynomial
  rw [natDegree_prod_of_monic _ _ (fun i hi => monic_X_sub_C _)]
  simp

theorem monic_top_derivative (p : ℝ[X]) (n : ℕ) (hp : p.Monic)
    (hn : p.natDegree = n) : derivative^[n] p = C (Nat.factorial n : ℝ) := by
  ext k
  rw [coeff_iterate_derivative]
  by_cases hk : k = 0
  · subst k
    simp [← hn, hp.coeff_natDegree, Nat.descFactorial_self]
  · have hkn : p.natDegree < k+n := by omega
    rw [coeff_eq_zero_of_natDegree_lt hkn]
    simp [hk]

/-- A block of repeated nodes contributes the corresponding power of a linear
factor to the nodal polynomial. -/
theorem repeated_block_dvd {n : ℕ} (x : Fin (n+1) → ℝ) (u : Fin (n+1))
    (hx : Monotone x) (hu : ∀ i, x i = x u → i = u)
    (i j : Fin (n+1)) (hij : i ≤ j) (heq : x i = x j) (hiu : i ≠ u) :
    (X-C (x i))^(j.val-i.val+1) ∣ nodalPolynomial x u := by
  have hsub : Finset.Icc i j ⊆ Finset.univ.erase u := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hki : x k = x i := le_antisymm
      ((hx hk'.2).trans_eq heq.symm) (hx hk'.1)
    have hku : k ≠ u := by
      intro h
      subst k
      exact hiu (hu i hki.symm)
    simp [hku]
  have hprod : (∏ k ∈ Finset.Icc i j, (X-C (x k) : ℝ[X])) =
      (X-C (x i))^(j.val-i.val+1) := by
    have hc : (Finset.Icc i j).card = j.val-i.val+1 := by
      rw [Fin.card_Icc]
      have hh : i.val ≤ j.val := hij
      omega
    calc
      _ = ∏ k ∈ Finset.Icc i j, (X-C (x i) : ℝ[X]) := by
        apply Finset.prod_congr rfl
        intro k hk
        have hk' := Finset.mem_Icc.mp hk
        have hki : x k = x i := le_antisymm
          ((hx hk'.2).trans_eq heq.symm) (hx hk'.1)
        rw [hki]
      _ = _ := by simp [hc]
  rw [← hprod]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

theorem nodalPolynomial_vanishing_jets {n : ℕ} (x : Fin (n+1) → ℝ)
    (u : Fin (n+1)) (hx : Monotone x) (hu : ∀ i, x i = x u → i = u)
    (i j : Fin (n+1)) (hij : i ≤ j) (heq : x i = x j) (hiu : i ≠ u) :
    (derivative^[j.val-i.val] (nodalPolynomial x u)).eval (x i) = 0 := by
  have h := pow_sub_dvd_iterate_derivative_of_pow_dvd (j.val-i.val)
    (repeated_block_dvd x u hx hu i j hij heq hiu)
  have hpow : j.val-i.val+1-(j.val-i.val) = 1 := by omega
  rw [hpow, pow_one] at h
  exact (dvd_iff_isRoot.mp h)

theorem nodalPolynomial_eval_ne_zero {n : ℕ} (x : Fin (n+1) → ℝ)
    (u : Fin (n+1)) (hu : ∀ i, x i = x u → i = u) :
    (nodalPolynomial x u).eval (x u) ≠ 0 := by
  simp only [nodalPolynomial, eval_prod, eval_sub, eval_X, eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply sub_ne_zero.mpr
  intro heq
  exact (Finset.mem_erase.mp hi).1 (hu i heq.symm)

/-- General Hermite remainder, with explicit multiplicities and an interior
remainder point. Every hypothesis concerns differentiability or interpolation
data; the remainder identity is proved here. -/
theorem hermite_remainder (n : ℕ) (f : ℕ → ℝ → ℝ) (a b : ℝ)
    (x : Fin (n+1) → ℝ) (u : Fin (n+1)) (p : ℝ[X])
    (hx : Monotone x) (hmem : ∀ i, x i ∈ Icc a b)
    (hspan : x 0 < x (Fin.last n))
    (hu : ∀ i, x i = x u → i = u) (hp : p.natDegree < n)
    (hinterp : ∀ i j, i ≤ j → x i = x j → i ≠ u →
      f (j.val-i.val) (x i) = (derivative^[j.val-i.val] p).eval (x i))
    (hd : ∀ k < n, ∀ t ∈ Icc a b, HasDerivAt (f k) (f (k+1) t) t) :
    ∃ ξ ∈ Ioo (x 0) (x (Fin.last n)),
      f 0 (x u) - p.eval (x u) =
        f n ξ / (Nat.factorial n) * (nodalPolynomial x u).eval (x u) := by
  let w := nodalPolynomial x u
  let A := (f 0 (x u) - p.eval (x u)) / w.eval (x u)
  let F : ℕ → ℝ → ℝ := fun k t =>
    f k t - (derivative^[k] p).eval t - A*(derivative^[k] w).eval t
  have hw : w.eval (x u) ≠ 0 := nodalPolynomial_eval_ne_zero x u hu
  have hFjets : VanishingJets F x := by
    intro i j hij heq
    by_cases hi : i = u
    · subst i
      have hj : j = u := hu j heq.symm
      subst j
      simp only [F, Nat.sub_self, Function.iterate_zero, id_eq]
      dsimp [A]
      field_simp
      ring
    · have hh := hinterp i j hij heq hi
      have hz := nodalPolynomial_vanishing_jets x u hx hu i j hij heq hi
      dsimp only [F]
      rw [hh]
      change _ - _ - A*(derivative^[j.val-i.val] (nodalPolynomial x u)).eval (x i) = 0
      rw [hz]
      ring
  have hFd : ∀ k < n, ∀ t ∈ Icc a b, HasDerivAt (F k) (F (k+1) t) t := by
    intro k hk t ht
    convert ((hd k hk t ht).sub ((derivative^[k] p).hasDerivAt t)).sub
      (((derivative^[k] w).hasDerivAt t).const_mul A) using 1 <;>
      simp only [F, Function.iterate_succ_apply']
  obtain ⟨ξ, hξ, hzero, hξstrict⟩ := repeated_rolle_strong n F a b x hx hmem hFjets hFd
  refine ⟨ξ, hξstrict hspan, ?_⟩
  have hpzero : derivative^[n] p = 0 := iterate_derivative_eq_zero hp
  have hwtop : derivative^[n] w = C (Nat.factorial n : ℝ) :=
    monic_top_derivative w n (nodalPolynomial_monic x u) (nodalPolynomial_degree x u)
  dsimp only [F] at hzero
  rw [hpzero, hwtop] at hzero
  simp only [eval_zero, eval_C, sub_zero] at hzero
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  dsimp only [A] at hzero
  change f 0 (x u) - p.eval (x u) = f n ξ / ↑n.factorial * w.eval (x u)
  field_simp [hw, hfac] at hzero ⊢
  nlinarith

end Thomson78.Analysis
