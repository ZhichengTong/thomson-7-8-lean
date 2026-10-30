import Thomson78.Seven
import Thomson78.Parity

noncomputable section
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace Thomson78.Seven

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

structure Configuration (x : Fin 7 → V) : Prop where
  unit : ∀ i, ⟪x i, x i⟫_ℝ = 1
  contacts : ∀ i j, i ≠ j → Contact ⟪x i, x j⟫_ℝ
  centroid : ∑ i, x i = 0

theorem Configuration.injective {x : Fin 7 → V} (h : Configuration x) :
    Function.Injective x := by
  intro i j heq
  by_contra hne
  have hc := contact_lt_one (h.contacts i j hne)
  rw [heq, h.unit j] at hc
  exact lt_irrefl _ hc

def neighbors (x : Fin 7 → V) (i : Fin 7) (c : ℝ) : Finset (Fin 7) := by
  classical
  exact Finset.univ.filter fun j => ⟪x i, x j⟫_ℝ = c

@[simp] theorem mem_neighbors (x : Fin 7 → V) (i j : Fin 7) (c : ℝ) :
    j ∈ neighbors x i c ↔ ⟪x i, x j⟫_ℝ = c := by
  classical
  simp [neighbors]

theorem antipodal_card_le_one {x : Fin 7 → V} (h : Configuration x) (i : Fin 7) :
    (neighbors x i (-1)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro j hj k hk
  apply h.injective
  have hj' := antipodal_of_inner (x i) (x j) (h.unit i) (h.unit j)
    ((mem_neighbors x i j (-1)).mp hj)
  have hk' := antipodal_of_inner (x i) (x k) (h.unit i) (h.unit k)
    ((mem_neighbors x i k (-1)).mp hk)
  exact hj'.trans hk'.symm

private theorem four_indicators (u : ℝ) (hu : Contact u) :
    (if u = -1 then 1 else 0 : ℕ) + (if u = 0 then 1 else 0) +
    (if u = a then 1 else 0) + (if u = b then 1 else 0) = 1 := by
  classical
  have ha := contact_bounds
  rcases hu with rfl | rfl | rfl | rfl <;> split_ifs <;>
    first | contradiction | solve | norm_num | solve | exfalso; linarith

private theorem four_weighted_indicators (u : ℝ) (hu : Contact u) :
    -(if u = -1 then 1 else 0 : ℝ) +
    a * (if u = a then 1 else 0) + b * (if u = b then 1 else 0) = u := by
  classical
  have ha := contact_bounds
  rcases hu with rfl | rfl | rfl | rfl <;> split_ifs <;>
    first | contradiction | solve | ring | solve | exfalso; linarith

theorem configuration_count_sum {x : Fin 7 → V} (h : Configuration x) (i : Fin 7) :
    (neighbors x i (-1)).card + (neighbors x i 0).card +
      (neighbors x i a).card + (neighbors x i b).card = 6 := by
  classical
  simp only [neighbors, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hh : ∀ j : Fin 7,
      (if ⟪x i, x j⟫_ℝ = -1 then 1 else 0 : ℕ) +
      (if ⟪x i, x j⟫_ℝ = 0 then 1 else 0) +
      (if ⟪x i, x j⟫_ℝ = a then 1 else 0) +
      (if ⟪x i, x j⟫_ℝ = b then 1 else 0) = if j = i then 0 else 1 := by
    intro j
    by_cases hj : j = i
    · subst j
      have ha := contact_bounds
      rw [h.unit i]
      norm_num [show (1 : ℝ) ≠ a by linarith, show (1 : ℝ) ≠ b by linarith]
    · rw [ite_eq_right hj]
      exact four_indicators _ (h.contacts i j (Ne.symm hj))
  simp_rw [hh]
  simp [Finset.sum_ite, Finset.filter_ne']

theorem configuration_row_sum {x : Fin 7 → V} (h : Configuration x) (i : Fin 7) :
    (1 : ℝ) - (neighbors x i (-1)).card +
      a * (neighbors x i a).card + b * (neighbors x i b).card = 0 := by
  classical
  have hr := zero_centroid_row x h.centroid i
  have hh : ∀ j : Fin 7, ⟪x i, x j⟫_ℝ =
      (if j = i then 1 else 0) -
      (if ⟪x i, x j⟫_ℝ = -1 then 1 else 0 : ℝ) +
      a * (if ⟪x i, x j⟫_ℝ = a then 1 else 0) +
      b * (if ⟪x i, x j⟫_ℝ = b then 1 else 0) := by
    intro j
    by_cases hj : j = i
    · subst j
      have ha := contact_bounds
      rw [h.unit i]
      norm_num [show (1 : ℝ) ≠ a by linarith, show (1 : ℝ) ≠ b by linarith]
    · rw [ite_eq_right hj]
      have hw := four_weighted_indicators _ (h.contacts i j (Ne.symm hj))
      linarith
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hh j)
  rw [hr] at hsum
  symm at hsum
  have hcast (c : ℝ) : ((neighbors x i c).card : ℝ) =
      ∑ j : Fin 7, (if ⟪x i, x j⟫_ℝ = c then 1 else 0 : ℝ) := by
    simp only [neighbors, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← hcast, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
  exact hsum

theorem configuration_counts {x : Fin 7 → V} (h : Configuration x) (i : Fin 7) :
    (neighbors x i a).card = 2 * (1 - (neighbors x i (-1)).card) ∧
    (neighbors x i b).card = 2 * (1 - (neighbors x i (-1)).card) ∧
    (neighbors x i 0).card = 2 + 3 * (neighbors x i (-1)).card :=
  row_counts _ _ _ _ (antipodal_card_le_one h i)
    (configuration_count_sum h i) (configuration_row_sum h i)

theorem two_neighbors_of_edge {x : Fin 7 → V} (h : Configuration x)
    (i j : Fin 7) (hij : ⟪x i, x j⟫_ℝ = b) :
    (neighbors x i b).card = 2 := by
  have hj : j ∈ neighbors x i b := (mem_neighbors _ _ _ _).mpr hij
  have hpos := Finset.card_pos.mpr ⟨j, hj⟩
  have hc := (configuration_counts h i).2.1
  have hm := antipodal_card_le_one h i
  omega

theorem next_vertex {x : Fin 7 → V} (h : Configuration x)
    (i j : Fin 7) (hij : ⟪x i, x j⟫_ℝ = b) :
    ∃ k : Fin 7, k ≠ i ∧ ⟪x j, x k⟫_ℝ = b ∧
      x k = (2 * b) • x j - x i := by
  classical
  have hji : ⟪x j, x i⟫_ℝ = b := by rw [real_inner_comm, hij]
  have hi : i ∈ neighbors x j b := (mem_neighbors _ _ _ _).mpr hji
  have hc := two_neighbors_of_edge h j i hji
  have hnonempty : ((neighbors x j b).erase i).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hi, hc]
    norm_num
  obtain ⟨k, hk⟩ := hnonempty
  obtain ⟨hki, hkmem⟩ := Finset.mem_erase.mp hk
  have hjk := (mem_neighbors x j k b).mp hkmem
  refine ⟨k, hki, hjk, ?_⟩
  have hrec := (neighbor_recurrence (x j) (x i) (x k) (h.unit j)
    (h.unit i) (h.unit k) hji hjk (h.contacts i k hki.symm)).2
  calc
    x k = (x i + x k) - x i := by module
    _ = (2 * b) • x j - x i := by rw [hrec]

def nextIndex {x : Fin 7 → V} (h : Configuration x) (i j : Fin 7) : Fin 7 := by
  classical
  exact if hij : ⟪x i, x j⟫_ℝ = b then (next_vertex h i j hij).choose else 0

theorem nextIndex_spec {x : Fin 7 → V} (h : Configuration x)
    (i j : Fin 7) (hij : ⟪x i, x j⟫_ℝ = b) :
    nextIndex h i j ≠ i ∧ ⟪x j, x (nextIndex h i j)⟫_ℝ = b ∧
      x (nextIndex h i j) = (2 * b) • x j - x i := by
  classical
  simp only [nextIndex, dite_eq_left hij]
  exact (next_vertex h i j hij).choose_spec

def walk {x : Fin 7 → V} (h : Configuration x) (i j : Fin 7) : ℕ → Fin 7
  | 0 => i
  | 1 => j
  | k + 2 => nextIndex h (walk h i j k) (walk h i j (k + 1))

theorem walk_edge {x : Fin 7 → V} (h : Configuration x) (i j : Fin 7)
    (hij : ⟪x i, x j⟫_ℝ = b) :
    ∀ k, ⟪x (walk h i j k), x (walk h i j (k + 1))⟫_ℝ = b := by
  intro k
  induction k with
  | zero => exact hij
  | succ k hk =>
      exact (nextIndex_spec h _ _ hk).2.1

theorem walk_recurrence {x : Fin 7 → V} (h : Configuration x) (i j : Fin 7)
    (hij : ⟪x i, x j⟫_ℝ = b) :
    ∀ k, x (walk h i j (k + 2)) =
      (2 * b) • x (walk h i j (k + 1)) - x (walk h i j k) := by
  intro k
  exact (nextIndex_spec h _ _ (walk_edge h i j hij k)).2.2

theorem walk_periodic {x : Fin 7 → V} (h : Configuration x) (i j : Fin 7)
    (hij : ⟪x i, x j⟫_ℝ = b) : ∀ k, walk h i j (k + 5) = walk h i j k := by
  intro k
  apply h.injective
  exact recurrence_periodic (fun k => x (walk h i j k)) (walk_recurrence h i j hij) k

theorem exists_edge {x : Fin 7 → V} (h : Configuration x) :
    ∃ i j, ⟪x i, x j⟫_ℝ = b := by
  classical
  by_contra he
  have hb : ∀ i j, ⟪x i, x j⟫_ℝ ≠ b := by
    intro i j hij
    exact he ⟨i, j, hij⟩
  have hn (i : Fin 7) : (neighbors x i b).card = 0 := by
    apply Finset.card_eq_zero.mpr
    ext j
    simp [hb i j]
  have ha (i : Fin 7) : ∃ j, ⟪x i, x j⟫_ℝ = -1 := by
    have hc := (configuration_counts h i).2.1
    have hm := antipodal_card_le_one h i
    have hm1 : (neighbors x i (-1)).card = 1 := by rw [hn i] at hc; omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < (neighbors x i (-1)).card by omega)
    exact ⟨j, (mem_neighbors _ _ _ _).mp hj⟩
  let f : Fin 7 → Fin 7 := fun i => (ha i).choose
  have hf (i : Fin 7) : x (f i) = -x i :=
    antipodal_of_inner (x i) (x (f i)) (h.unit i) (h.unit (f i)) (ha i).choose_spec
  apply no_fixedPointFree_involution_fin7 f
  · intro i
    apply h.injective
    rw [hf, hf, neg_neg]
  · intro i hi
    have hh := (ha i).choose_spec
    change ⟪x i, x (f i)⟫_ℝ = -1 at hh
    rw [hi, h.unit i] at hh
    norm_num at hh

theorem walk_inner_two {x : Fin 7 → V} (h : Configuration x) (i j : Fin 7)
    (hij : ⟪x i, x j⟫_ℝ = b) (k : ℕ) :
    ⟪x (walk h i j k), x (walk h i j (k + 2))⟫_ℝ = a := by
  rw [walk_recurrence h i j hij k, inner_sub_right, real_inner_smul_right,
    walk_edge h i j hij k, h.unit]
  nlinarith [contact_arithmetic.2.2.1]

theorem walk_inner_three {x : Fin 7 → V} (h : Configuration x) (i j : Fin 7)
    (hij : ⟪x i, x j⟫_ℝ = b) (k : ℕ) :
    ⟪x (walk h i j k), x (walk h i j (k + 3))⟫_ℝ = a := by
  have hrec := walk_recurrence h i j hij (k + 1)
  rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at hrec
  rw [hrec, inner_sub_right, real_inner_smul_right,
    walk_inner_two h i j hij k, walk_edge h i j hij k]
  nlinarith [contact_arithmetic.1, contact_arithmetic.2.1]

theorem walk_inner_four {x : Fin 7 → V} (h : Configuration x) (i j : Fin 7)
    (hij : ⟪x i, x j⟫_ℝ = b) (k : ℕ) :
    ⟪x (walk h i j k), x (walk h i j (k + 4))⟫_ℝ = b := by
  have he := walk_edge h i j hij (k + 4)
  rw [show k + 4 + 1 = k + 5 by omega, walk_periodic h i j hij k] at he
  rw [real_inner_comm]
  exact he

theorem walk_distinct_of_gap {x : Fin 7 → V} (h : Configuration x) (i j : Fin 7)
    (hij : ⟪x i, x j⟫_ℝ = b) (k d : ℕ) (hd : 1 ≤ d) (hd' : d < 5) :
    walk h i j k ≠ walk h i j (k + d) := by
  intro he
  have ha := contact_bounds
  interval_cases d
  · have ht := walk_edge h i j hij k
    rw [← he, h.unit] at ht
    linarith
  · have ht := walk_inner_two h i j hij k
    rw [← he, h.unit] at ht
    linarith
  · have ht := walk_inner_three h i j hij k
    rw [← he, h.unit] at ht
    linarith
  · have ht := walk_inner_four h i j hij k
    rw [← he, h.unit] at ht
    linarith

theorem walk_first_five_injective {x : Fin 7 → V} (h : Configuration x) (i j : Fin 7)
    (hij : ⟪x i, x j⟫_ℝ = b) :
    Function.Injective (fun k : Fin 5 => walk h i j k) := by
  intro k l he
  by_contra hne
  have hneq : k.val ≠ l.val := by exact fun hh => hne (Fin.ext hh)
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · apply walk_distinct_of_gap h i j hij k (l - k) (by omega) (by omega)
    simpa only [Nat.add_sub_of_le hlt.le] using he
  · apply walk_distinct_of_gap h i j hij l (k - l) (by omega) (by omega)
    simpa only [Nat.add_sub_of_le hgt.le] using he.symm

end Thomson78.Seven
