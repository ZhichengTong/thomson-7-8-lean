import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith

/-! Rolle's theorem for repeated nodes, expressed using a derivative sequence.
Repeated-node conditions encode the usual vanishing jets. -/
noncomputable section
open Set

namespace Thomson78.Analysis

/-- Vanishing values and jets at an ordered list of nodes. For repeated entries
at positions `i ≤ j`, the derivative of order `j-i` vanishes there. -/
def VanishingJets (F : ℕ → ℝ → ℝ) {m : ℕ} (x : Fin m → ℝ) : Prop :=
  ∀ i j, i ≤ j → x i = x j → F (j.val-i.val) (x i) = 0

/-- Rolle's theorem with multiplicities. The statement keeps the entire
interval explicit, so it applies to derivatives defined on a bounded interval. -/
theorem repeated_rolle_strong (n : ℕ) (F : ℕ → ℝ → ℝ) (a b : ℝ)
    (x : Fin (n+1) → ℝ) (hx : Monotone x)
    (hmem : ∀ i, x i ∈ Icc a b)
    (hjets : VanishingJets F x)
    (hd : ∀ k < n, ∀ t ∈ Icc a b, HasDerivAt (F k) (F (k+1) t) t) :
    ∃ c ∈ Icc (x 0) (x (Fin.last n)), F n c = 0 ∧
      (x 0 < x (Fin.last n) → c ∈ Ioo (x 0) (x (Fin.last n))) := by
  induction n generalizing F with
  | zero =>
      refine ⟨x 0, ⟨le_rfl, le_rfl⟩, ?_, ?_⟩
      · simpa [VanishingJets] using hjets 0 0 le_rfl rfl
      · intro h
        exact (lt_irrefl _ h).elim
  | succ n ih =>
      have hpair : ∀ i : Fin (n+1), ∃ y : ℝ,
          x i.castSucc ≤ y ∧ y ≤ x i.succ ∧
          (x i.castSucc < x i.succ → x i.castSucc < y ∧ y < x i.succ) ∧
          F 1 y = 0 := by
        intro i
        have hle : x i.castSucc ≤ x i.succ := hx (by change i.val ≤ i.val+1; omega)
        by_cases heq : x i.castSucc = x i.succ
        · refine ⟨x i.castSucc, le_rfl, hle, ?_, ?_⟩
          · intro hlt
            exact (lt_irrefl _ (heq ▸ hlt)).elim
          · have hh := hjets i.castSucc i.succ (by change i.val ≤ i.val+1; omega) heq
            simpa using hh
        · have hlt := lt_of_le_of_ne hle heq
          have hc : ContinuousOn (F 0) (Icc (x i.castSucc) (x i.succ)) := by
            intro t ht
            apply (hd 0 (by omega) t ?_).continuousAt.continuousWithinAt
            exact ⟨(hmem i.castSucc).1.trans ht.1, ht.2.trans (hmem i.succ).2⟩
          have hz0 : F 0 (x i.castSucc) = 0 := by
            simpa using hjets i.castSucc i.castSucc le_rfl rfl
          have hz1 : F 0 (x i.succ) = 0 := by
            simpa using hjets i.succ i.succ le_rfl rfl
          obtain ⟨y, hy, hy0⟩ := exists_hasDerivAt_eq_zero hlt hc (hz0.trans hz1.symm)
            (fun t ht => hd 0 (by omega) t
              ⟨(hmem i.castSucc).1.trans ht.1.le, ht.2.le.trans (hmem i.succ).2⟩)
          exact ⟨y, hy.1.le, hy.2.le, fun _ => hy, hy0⟩
      choose y hyL hyR hyStrict hy0 using hpair
      have hymem : ∀ i, y i ∈ Icc a b := fun i =>
        ⟨(hmem i.castSucc).1.trans (hyL i), (hyR i).trans (hmem i.succ).2⟩
      have hmono : Monotone y := by
        intro i j hij
        rcases eq_or_lt_of_le hij with h | h
        · exact le_of_eq (congrArg y h)
        · exact (hyR i).trans ((hx (show i.succ ≤ j.castSucc by
            simpa using h)).trans (hyL j))
      have hyjets : VanishingJets (fun k => F (k+1)) y := by
        intro i j hij heq
        rcases eq_or_lt_of_le hij with he | hlt
        · subst j
          simpa using hy0 i
        · have hmid : x i.succ ≤ x j.castSucc := hx (by simpa using hlt)
          have hiR : y i = x i.succ := by linarith [hyR i, hyL j]
          have hjL : y j = x j.castSucc := by linarith [hyR i, hyL j]
          have hi : x i.castSucc = x i.succ := by
            by_contra hn
            have hh := hyStrict i (lt_of_le_of_ne (hx (by change i.val ≤ i.val+1; omega)) hn)
            linarith
          have hj : x j.castSucc = x j.succ := by
            by_contra hn
            have hh := hyStrict j (lt_of_le_of_ne (hx (by change j.val ≤ j.val+1; omega)) hn)
            linarith
          have hends : x i.castSucc = x j.succ := by linarith
          have hh := hjets i.castSucc j.succ (by change i.val ≤ j.val+1; have hh : i.val ≤ j.val := hij; omega) hends
          have hindex : j.succ.val - i.castSucc.val = (j.val-i.val)+1 := by
            simp only [Fin.val_succ, Fin.val_castSucc]
            omega
          rw [hindex] at hh
          have hpoint : y i = x i.castSucc := hiR.trans hi.symm
          simpa only [hpoint] using hh
      obtain ⟨c, hc, hz, hstrict⟩ := ih (fun k => F (k+1)) y hmono hymem hyjets
        (fun k hk t ht => hd (k+1) (by omega) t ht)
      have hfirst : x 0 ≤ y 0 := by simpa using hyL 0
      have hlast : y (Fin.last n) ≤ x (Fin.last (n+1)) := by simpa using hyR (Fin.last n)
      refine ⟨c, ⟨hfirst.trans hc.1, hc.2.trans hlast⟩, hz, ?_⟩
      intro hspan
      by_cases hn : n = 0
      · subst n
        have hc0 : c = y 0 := le_antisymm hc.2 hc.1
        have hs := hyStrict 0 (by simpa using hspan)
        simpa [hc0] using hs
      · have hm : x (Fin.succ (0 : Fin (n+1))) ≤ x (Fin.last n).castSucc := by
          apply hx
          change 1 ≤ n
          omega
        have hys : y 0 < y (Fin.last n) := by
          by_contra h
          have hyEq : y 0 = y (Fin.last n) :=
            le_antisymm (hmono (Fin.zero_le _)) (le_of_not_gt h)
          have he0 : x (0 : Fin (n+1)).castSucc = x (0 : Fin (n+1)).succ := by
            by_contra he
            have hs := hyStrict 0 (lt_of_le_of_ne (hx (by change (0 : ℕ) ≤ 1; omega)) he)
            linarith [hyL (Fin.last n)]
          have hen : x (Fin.last n).castSucc = x (Fin.last n).succ := by
            by_contra he
            have hs := hyStrict (Fin.last n)
              (lt_of_le_of_ne (hx (by change n ≤ n+1; omega)) he)
            linarith [hyR 0]
          have hspan' : x (0 : Fin (n+1)).castSucc < x (Fin.last n).succ := by
            simpa using hspan
          linarith [hyR 0, hyL (Fin.last n)]
        have hcs := hstrict hys
        exact ⟨lt_of_le_of_lt hfirst hcs.1, lt_of_lt_of_le hcs.2 hlast⟩

/-- Closed-interval version of Rolle's theorem with multiplicities. -/
theorem repeated_rolle (n : ℕ) (F : ℕ → ℝ → ℝ) (a b : ℝ)
    (x : Fin (n+1) → ℝ) (hx : Monotone x)
    (hmem : ∀ i, x i ∈ Icc a b)
    (hjets : VanishingJets F x)
    (hd : ∀ k < n, ∀ t ∈ Icc a b, HasDerivAt (F k) (F (k+1) t) t) :
    ∃ c ∈ Icc a b, F n c = 0 := by
  obtain ⟨c, hc, hz, _⟩ := repeated_rolle_strong n F a b x hx hmem hjets hd
  exact ⟨c, ⟨(hmem 0).1.trans hc.1, hc.2.trans (hmem (Fin.last n)).2⟩, hz⟩

end Thomson78.Analysis

