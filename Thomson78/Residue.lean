import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! The algebraic implication behind the reduction modulo 23 argument.

`no_root_of_reduction` proves the integrality-and-reduction step for any
integrally closed subring. `reduced23_no_root` checks all 23 residue classes
using kernel-checked arithmetic. No trusted computational axiom is used.
-/
noncomputable section
open Polynomial
namespace Thomson78

theorem no_root_of_reduction
    {R K F : Type*} [CommRing R] [CommRing K] [CommRing F]
    [Algebra R K] [IsIntegrallyClosedIn R K]
    (ρ : R →+* F) (p : R[X]) (hp : p.Monic)
    (hinj : Function.Injective (algebraMap R K))
    (hred : ∀ z : F, (p.map ρ).eval z ≠ 0) :
    ∀ x : K, p.aeval x ≠ 0 := by
  intro x hx
  have hi : IsIntegral R x := ⟨p, hp, hx⟩
  obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hi
  have he : p.eval r = 0 := by
    apply hinj
    rw [map_zero]
    rw [← Polynomial.eval₂_at_apply]
    change p.aeval (algebraMap R K r) = 0
    rw [hr]
    exact hx
  apply hred (ρ r)
  rw [Polynomial.eval_map_apply, he, map_zero]

def reduced23 (z : ZMod 23) : ZMod 23 :=
  z^12 + 8*z^11 + 22*z^10 + 9*z^9 + 17*z^8 + 7*z^7 + 20*z^6 +
    17*z^5 + 14*z^4 + 6*z^3 + 22*z^2 + 7*z + 18

theorem reduced23_no_root : ∀ z : ZMod 23, reduced23 z ≠ 0 := by
  decide

theorem residue_sqrt_two : (18 : ZMod 23)^2 = 2 := by decide

theorem residue_leading_coefficient : (1201 + 328 * 18 : ZMod 23) = 21 := by
  decide

end Thomson78

#print axioms Thomson78.no_root_of_reduction
#print axioms Thomson78.reduced23_no_root
