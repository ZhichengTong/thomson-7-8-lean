import Thomson78.Energy
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Nat.Choose.Basic

/-! Uniform injection averages and the finite-population coefficients. -/
noncomputable section
open scoped BigOperators
namespace Thomson78.FivePoint

abbrev Injection (k N : ℕ) := Fin k ↪ Fin N

abbrev Remaining {k N : ℕ} (e : Injection k N) := ↥(Set.range e)ᶜ

def splitInjection (k l N : ℕ) :
    Injection (k+l) N ≃ Σ e : Injection k N, Fin l ↪ Remaining e :=
  ((finSumFinEquiv : Fin k ⊕ Fin l ≃ Fin (k+l)).symm.embeddingCongr
    (Equiv.refl (Fin N))).trans Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted

def restrict (k l N : ℕ) (e : Injection (k+l) N) : Injection k N :=
  (splitInjection k l N e).1

theorem restrict_apply (k l N : ℕ) (e : Injection (k+l) N) (i : Fin k) :
    restrict k l N e i = e (Fin.castAdd l i) := rfl

theorem splitInjection_right_apply (k l N : ℕ) (e : Injection (k+l) N) (i : Fin l) :
    ((splitInjection k l N e).2 i).1 = e (Fin.natAdd k i) := rfl

theorem remaining_card {k N : ℕ} (e : Injection k N) :
    Fintype.card (Remaining e) = N-k := by
  classical
  change Fintype.card ↥(Set.range e)ᶜ = N-k
  rw [Fintype.card_compl_set, Fintype.card_range]
  simp

def average (k N : ℕ) (f : Injection k N → ℝ) : ℝ :=
  (∑ e, f e) / N.descFactorial k

theorem average_const (k N : ℕ) (h : k ≤ N) (c : ℝ) : average k N (fun _ => c) = c := by
  classical
  have hn : (N.descFactorial k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr h))
  simp only [average, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_embedding_eq, Fintype.card_fin]
  field_simp

theorem average_relabel (k N : ℕ) (σ : Equiv.Perm (Fin k)) (f : Injection k N → ℝ) :
    average k N (fun e => f (σ.toEmbedding.trans e)) = average k N f := by
  classical
  unfold average
  congr 1
  exact Fintype.sum_equiv (σ.symm.embeddingCongr (Equiv.refl (Fin N))) _ _ (fun _ => rfl)

theorem injection_sum_split (k l N : ℕ) (f : Injection (k+l) N → ℝ) :
    ∑ e, f e = ∑ e : Injection k N, ∑ g : Fin l ↪ Remaining e,
      f ((splitInjection k l N).symm ⟨e,g⟩) := by
  classical
  calc
    _ = ∑ p : Σ e : Injection k N, Fin l ↪ Remaining e,
        f ((splitInjection k l N).symm p) :=
      Fintype.sum_equiv (splitInjection k l N) _ _ (fun e => by simp)
    _ = _ := Fintype.sum_sigma _

theorem sum_restrict (k l N : ℕ) (f : Injection k N → ℝ) :
    (∑ e : Injection (k+l) N, f (restrict k l N e)) =
      ((N-k).descFactorial l : ℝ) * ∑ e, f e := by
  classical
  rw [injection_sum_split]
  simp only [restrict, Equiv.apply_symm_apply]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_embedding_eq, Fintype.card_fin, remaining_card]
  rw [Finset.mul_sum]

theorem average_restrict (k l N : ℕ) (h : k+l ≤ N) (f : Injection k N → ℝ) :
    average (k+l) N (fun e => f (restrict k l N e)) = average k N f := by
  classical
  have he : (N-k).descFactorial l * N.descFactorial k = N.descFactorial (k+l) := by
    simpa using (Nat.descFactorial_mul_descFactorial (n:=N) (k:=k) (m:=k+l) (by omega))
  have ha : ((N-k).descFactorial l : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega : l ≤ N-k)))
  unfold average
  rw [sum_restrict, ← he, Nat.cast_mul]
  exact mul_div_mul_left _ _ ha

theorem five_average_two (N : ℕ) (h : 5 ≤ N) (f : Injection 2 N → ℝ) :
    average 5 N (fun e => f (restrict 2 3 N e)) = average 2 N f :=
  average_restrict 2 3 N h f

theorem five_average_three (N : ℕ) (h : 5 ≤ N) (f : Injection 3 N → ℝ) :
    average 5 N (fun e => f (restrict 3 2 N e)) = average 3 N f :=
  average_restrict 3 2 N h f

theorem five_average_four (N : ℕ) (h : 5 ≤ N) (f : Injection 4 N → ℝ) :
    average 5 N (fun e => f (restrict 4 1 N e)) = average 4 N f :=
  average_restrict 4 1 N h f

def pairEmbeddingEquiv (R : Type*) : (Fin 2 ↪ R) ≃ Σ j : R, {k : R // k ≠ j} where
  toFun e := ⟨e 0, e 1, fun h => by have := e.injective h; norm_num at this⟩
  invFun p := ⟨![p.1,p.2.1], by
    have hn := p.2.property
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩
  left_inv e := by ext i; fin_cases i <;> rfl
  right_inv p := by rfl

theorem double_sum_split {R : Type*} [Fintype R] (H : R → R → ℝ) :
    (∑ j, ∑ k, H j k) = (∑ j, H j j) + ∑ e : Fin 2 ↪ R, H (e 0) (e 1) := by
  classical
  have hp : (∑ e : Fin 2 ↪ R, H (e 0) (e 1)) =
      ∑ j : R, ∑ k : {k : R // k ≠ j}, H j k := by
    calc
      _ = ∑ p : Σ j : R, {k : R // k ≠ j}, H p.1 p.2 :=
        Fintype.sum_equiv (pairEmbeddingEquiv R) _ _ (fun _ => rfl)
      _ = _ := Fintype.sum_sigma _
  rw [hp, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∑ k : {k : R // k ≠ j}, H j k) = ∑ k ∈ Finset.univ.erase j, H j k := by
    exact (Finset.sum_subtype _ (by simp [ne_comm]) (H j)).symm
  rw [he, add_comm]
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm

theorem five_edge_average (N : ℕ) (hN : 5 ≤ N) (f : Fin N → Fin N → ℝ) :
    average 5 N (fun e => f (e 0) (e 1)) =
      (∑ i : Fin N, ∑ j : {j : Fin N // j ≠ i}, f i j) / ((N:ℝ)*(N-1 : ℕ)) := by
  classical
  have hr := five_average_two N hN (fun e => f (e 0) (e 1))
  change average 5 N (fun e => f (e 0) (e 1)) = _ at hr
  rw [hr, average]
  have hp : (∑ e : Injection 2 N, f (e 0) (e 1)) =
      ∑ i : Fin N, ∑ j : {j : Fin N // j ≠ i}, f i j := by
    calc
      _ = ∑ p : Σ i : Fin N, {j : Fin N // j ≠ i}, f p.1 p.2 :=
        Fintype.sum_equiv (pairEmbeddingEquiv (Fin N)) _ _ (fun _ => rfl)
      _ = _ := Fintype.sum_sigma _
  rw [hp]
  congr 1
  simp [Nat.descFactorial_succ, mul_comm]

theorem sum_symmetric_offDiagonal (N : ℕ) (f : Fin N → Fin N → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    (∑ i : Fin N, ∑ j : {j : Fin N // j ≠ i}, f i j) =
      2 * ∑ p ∈ pairs N, f p.1 p.2 := by
  classical
  have hr (i : Fin N) : (∑ j : {j : Fin N // j ≠ i}, f i j) =
      ∑ j : Fin N, if i ≠ j then f i j else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp [ne_comm]) (f i)).symm
  simp_rw [hr]
  have hp (i j : Fin N) : (if i ≠ j then f i j else 0) =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le]
    · subst j; simp
    · simp [h,Ne.symm (ne_of_lt h),not_lt_of_ge h.le,hf i j]
  simp_rw [hp,Finset.sum_add_distrib]
  have hswap : (∑ i : Fin N, ∑ j : Fin N, if j < i then f j i else 0) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then f i j else 0 := Finset.sum_comm
  rw [hswap]
  have he : (∑ p ∈ pairs N, f p.1 p.2) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then f i j else 0 := by
    simp only [pairs,Finset.sum_filter]
    exact Fintype.sum_prod_type _
  rw [he]
  ring

theorem five_edge_average_unordered (N : ℕ) (hN : 5 ≤ N) (f : Fin N → Fin N → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    average 5 N (fun e => f (e 0) (e 1)) =
      (∑ p ∈ pairs N, f p.1 p.2) / (N.choose 2 : ℝ) := by
  rw [five_edge_average N hN f, sum_symmetric_offDiagonal N f hf]
  have hc : (N:ℝ) * (N-1 : ℕ) = 2 * (N.choose 2 : ℝ) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose N 2
    norm_num [Nat.descFactorial_succ] at h
    rw [mul_comm]
    exact_mod_cast h
  rw [hc]
  exact mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)

theorem five_edge_moment {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (N : ℕ) (hN : 5 ≤ N) (x : Fin N → V) (r : ℕ) :
    average 5 N (fun e => (gram x (e 0) (e 1))^r) =
      (∑ p ∈ pairs N, (gram x p.1 p.2)^r) / (N.choose 2 : ℝ) := by
  apply five_edge_average_unordered N hN (fun i j => (gram x i j)^r)
  intro i j
  rw [gram_symmetric]

theorem polynomial_energy_average {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (N : ℕ) (hN : 5 ≤ N) (x : Fin N → V) (h : ℝ → ℝ) :
    (N.choose 2 : ℝ) * average 5 N (fun e => h (gram x (e 0) (e 1))) = pairEnergy h x := by
  have hs := five_edge_average_unordered N hN (fun i j => h (gram x i j))
    (by intro i j; rw [gram_symmetric])
  have hc : (N.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : 2 ≤ N)))
  rw [hs,pairEnergy]
  field_simp

def diagonal {N : ℕ} (H : (e : Injection 3 N) → Remaining e → Remaining e → ℝ)
    (q : Injection 4 N) : ℝ :=
  let p := splitInjection 3 1 N q
  H p.1 (p.2 0) (p.2 0)

def offDiagonal {N : ℕ} (H : (e : Injection 3 N) → Remaining e → Remaining e → ℝ)
    (q : Injection 5 N) : ℝ :=
  let p := splitInjection 3 2 N q
  H p.1 (p.2 0) (p.2 1)

theorem sum_diagonal {N : ℕ}
    (H : (e : Injection 3 N) → Remaining e → Remaining e → ℝ) :
    (∑ q : Injection 4 N, diagonal H q) =
      ∑ e : Injection 3 N, ∑ j : Remaining e, H e j j := by
  classical
  rw [injection_sum_split 3 1 N]
  apply Finset.sum_congr rfl
  intro e _
  exact Fintype.sum_equiv (Equiv.uniqueEmbeddingEquivResult (α:=Fin 1) (β:=Remaining e))
    _ _ (fun g => by
      change (fun p : Σ e : Injection 3 N, Fin 1 ↪ Remaining e =>
        H p.1 (p.2 0) (p.2 0))
        ((splitInjection 3 1 N) ((splitInjection 3 1 N).symm ⟨e,g⟩)) = _
      rw [Equiv.apply_symm_apply]
      rfl)

theorem sum_offDiagonal {N : ℕ}
    (H : (e : Injection 3 N) → Remaining e → Remaining e → ℝ) :
    (∑ q : Injection 5 N, offDiagonal H q) =
      ∑ e : Injection 3 N, ∑ g : Fin 2 ↪ Remaining e, H e (g 0) (g 1) := by
  classical
  rw [injection_sum_split 3 2 N]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro g _
  change (fun p : Σ e : Injection 3 N, Fin 2 ↪ Remaining e =>
    H p.1 (p.2 0) (p.2 1))
    ((splitInjection 3 2 N) ((splitInjection 3 2 N).symm ⟨e,g⟩)) = _
  rw [Equiv.apply_symm_apply]

/-- Exact diagonal/off-diagonal factors before specializing the kernel. -/
theorem finite_population (N : ℕ) (hN : 5 ≤ N)
    (H : (e : Injection 3 N) → Remaining e → Remaining e → ℝ) :
    average 3 N (fun e => ∑ j : Remaining e, ∑ k : Remaining e, H e j k) =
      (N-3 : ℕ) * average 5 N (fun q => diagonal H (restrict 4 1 N q)) +
      ((N-3 : ℕ) : ℝ) * (N-4 : ℕ) * average 5 N (offDiagonal H) := by
  classical
  rw [five_average_four N hN]
  have hs : (∑ e : Injection 3 N, ∑ j : Remaining e, ∑ k : Remaining e, H e j k) =
      (∑ q : Injection 4 N, diagonal H q) + ∑ q : Injection 5 N, offDiagonal H q := by
    rw [sum_diagonal, sum_offDiagonal, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    exact double_sum_split (H e)
  have h3 : (N.descFactorial 3 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega : 3 ≤ N)))
  have h43 : ((N-3 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N-3 ≠ 0)
  have h54 : ((N-4 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N-4 ≠ 0)
  unfold average
  rw [hs]
  have h4 : N.descFactorial 4 = (N-3) * N.descFactorial 3 := Nat.descFactorial_succ N 3
  have h5 : N.descFactorial 5 = (N-4) * N.descFactorial 4 := Nat.descFactorial_succ N 4
  rw [h5,h4]
  push_cast
  field_simp [h3,h43,h54]

/-- The manuscript's finite-population identity for any normalized kernel. -/
theorem kernel_finite_population (N : ℕ) (hN : 5 ≤ N)
    (p q : Injection 3 N → Fin N → ℝ) (K : Fin N → Fin N → ℝ)
    (hK : ∀ j, K j j = 1) :
    average 3 N (fun e => ∑ j : Remaining e, ∑ k : Remaining e,
      p e j * q e k * K j k) =
      (N-3 : ℕ) * average 5 N (fun e =>
        p (restrict 3 2 N e) (e 3) * q (restrict 3 2 N e) (e 3)) +
      ((N-3 : ℕ) : ℝ) * (N-4 : ℕ) * average 5 N (fun e =>
        p (restrict 3 2 N e) (e 3) * q (restrict 3 2 N e) (e 4) * K (e 3) (e 4)) := by
  let H : (e : Injection 3 N) → Remaining e → Remaining e → ℝ :=
    fun e j k => p e j * q e k * K j k
  rw [finite_population N hN H]
  have hd : (fun e : Injection 5 N => diagonal H (restrict 4 1 N e)) =
      (fun e => p (restrict 3 2 N e) (e 3) * q (restrict 3 2 N e) (e 3)) := by
    funext e
    have hr : restrict 3 1 N (restrict 4 1 N e) = restrict 3 2 N e := by ext i; rfl
    change p (restrict 3 1 N (restrict 4 1 N e)) (e 3) *
      q (restrict 3 1 N (restrict 4 1 N e)) (e 3) * K (e 3) (e 3) = _
    rw [hr,hK,mul_one]
  have ho : offDiagonal H = (fun e : Injection 5 N =>
      p (restrict 3 2 N e) (e 3) * q (restrict 3 2 N e) (e 4) * K (e 3) (e 4)) := by
    funext e
    rfl
  rw [hd,ho]

end Thomson78.FivePoint

#print axioms Thomson78.FivePoint.average_restrict
#print axioms Thomson78.FivePoint.kernel_finite_population
