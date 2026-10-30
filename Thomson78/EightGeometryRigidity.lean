import Thomson78.EightGeometry
import Thomson78.EightGeometryGraph

/-! Assembly of the eight-point Gram classification from row sums and
local positive-semidefinite constraints. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace InnerProductSpace
namespace Thomson78.Eight
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def contactCount (x : Fin 8 → V) (i : Fin 8) (v : ℝ) : ℕ :=
  ((Finset.univ.erase i).filter (fun j => ⟪x i,x j⟫_ℝ=v)).card

/-- The centroid identity gives the integer row identities used above. -/
theorem row_count_identities (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (x : Fin 8 → V) (hu : ∀ i, ⟪x i,x i⟫_ℝ=1)
    (hc : ∀ i j, i ≠ j →
      ⟪x i,x j⟫_ℝ=a t ∨ ⟪x i,x j⟫_ℝ=b t ∨ ⟪x i,x j⟫_ℝ=c t ∨ ⟪x i,x j⟫_ℝ=d t)
    (hz : ∑ i, x i=0) (i : Fin 8) :
    contactCount x i (a t)+contactCount x i (b t)+contactCount x i (c t)+contactCount x i (d t)=7 ∧
    1+(contactCount x i (a t):ℝ)*a t+(contactCount x i (b t):ℝ)*b t+
      (contactCount x i (c t):ℝ)*c t+(contactCount x i (d t):ℝ)*d t=0 := by
  classical
  obtain ⟨hdb,hbc,hcq,hqa,_,_⟩ := contact_inequalities t hL hU
  have hba : b t < a t := by linarith
  have hca : c t < a t := by linarith
  have hda : d t < a t := by linarith
  have hdc : d t < c t := by linarith
  have hab : a t ≠ b t := ne_of_gt hba
  have hac : a t ≠ c t := ne_of_gt hca
  have had : a t ≠ d t := ne_of_gt hda
  have hbd : b t ≠ d t := ne_of_gt hdb
  have hcb : c t ≠ b t := ne_of_gt hbc
  have hcd : c t ≠ d t := ne_of_gt hdc
  have hpart (j : Fin 8) (hj : j ∈ Finset.univ.erase i) :
      (if ⟪x i,x j⟫_ℝ=a t then 1 else 0) +
      (if ⟪x i,x j⟫_ℝ=b t then 1 else 0) +
      (if ⟪x i,x j⟫_ℝ=c t then 1 else 0) +
      (if ⟪x i,x j⟫_ℝ=d t then 1 else 0) = (1:ℕ) := by
    have hne : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    rcases hc i j hne with hh|hh|hh|hh <;>
      simp [hh,hab,hac,had,hbd,hcb,hcd,Ne.symm hab,Ne.symm hac,Ne.symm had,
        Ne.symm hbd,Ne.symm hcb,Ne.symm hcd]
  have hweighted (j : Fin 8) (hj : j ∈ Finset.univ.erase i) :
      (if ⟪x i,x j⟫_ℝ=a t then 1 else 0)*a t +
      (if ⟪x i,x j⟫_ℝ=b t then 1 else 0)*b t +
      (if ⟪x i,x j⟫_ℝ=c t then 1 else 0)*c t +
      (if ⟪x i,x j⟫_ℝ=d t then 1 else 0)*d t = ⟪x i,x j⟫_ℝ := by
    have hne : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    rcases hc i j hne with hh|hh|hh|hh <;>
      simp [hh,hab,hac,had,hbd,hcb,hcd,Ne.symm hab,Ne.symm hac,Ne.symm had,
        Ne.symm hbd,Ne.symm hcb,Ne.symm hcd]
  have hcount (v : ℝ) : contactCount x i v =
      ∑ j ∈ Finset.univ.erase i, if ⟪x i,x j⟫_ℝ=v then 1 else 0 := by
    simp only [contactCount,Finset.card_eq_sum_ones,Finset.sum_filter]
  have hcountR (v : ℝ) : (contactCount x i v:ℝ) =
      ∑ j ∈ Finset.univ.erase i, if ⟪x i,x j⟫_ℝ=v then 1 else 0 := by
    rw [hcount]
    simp
  constructor
  · simp only [hcount,← Finset.sum_add_distrib]
    calc
      _ = ∑ j ∈ Finset.univ.erase i, (1:ℕ) := Finset.sum_congr rfl hpart
      _ = 7 := by simp
  · have hsum : (∑ j : Fin 8, ⟪x i,x j⟫_ℝ)=0 := by
      rw [← inner_sum,hz,inner_zero_right]
    have herase := Finset.sum_erase_add Finset.univ (fun j => ⟪x i,x j⟫_ℝ) (Finset.mem_univ i)
    rw [hu i,hsum] at herase
    simp only [hcountR,Finset.sum_mul]
    have hw : (∑ j ∈ Finset.univ.erase i, if ⟪x i,x j⟫_ℝ=a t then 1 else 0)*a t +
        (∑ j ∈ Finset.univ.erase i, if ⟪x i,x j⟫_ℝ=b t then 1 else 0)*b t +
        (∑ j ∈ Finset.univ.erase i, if ⟪x i,x j⟫_ℝ=c t then 1 else 0)*c t +
        (∑ j ∈ Finset.univ.erase i, if ⟪x i,x j⟫_ℝ=d t then 1 else 0)*d t =
        ∑ j ∈ Finset.univ.erase i, ⟪x i,x j⟫_ℝ := by
      simp only [Finset.sum_mul,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hweighted
    simp only [Finset.sum_mul] at hw
    linarith

/-- Actual contact counts in every row, without an additional algebraic hypothesis. -/
theorem row_counts (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (x : Fin 8 → V) (hu : ∀ i, ⟪x i,x i⟫_ℝ=1)
    (hc : ∀ i j, i ≠ j →
      ⟪x i,x j⟫_ℝ=a t ∨ ⟪x i,x j⟫_ℝ=b t ∨ ⟪x i,x j⟫_ℝ=c t ∨ ⟪x i,x j⟫_ℝ=d t)
    (hz : ∑ i, x i=0) (i : Fin 8) :
    contactCount x i (a t)=2 ∧ contactCount x i (b t)=1 ∧
    contactCount x i (c t)=2 ∧ contactCount x i (d t)=2 := by
  obtain ⟨hn,hr⟩ := row_count_identities t hL hU x hu hc hz i
  exact multiplicities_from_interval t hL hU _ _ _ _ hn hr



def contactGraph (t : ℝ) (x : Fin 8 → V) : SimpleGraph (Fin 8) where
  Adj i j := i ≠ j ∧ ⟪x i,x j⟫_ℝ=d t
  symm.symm i j hij := ⟨hij.1.symm,(real_inner_comm (x i) (x j)).trans hij.2⟩
  loopless.irrefl _i hii := hii.1 rfl

theorem contactGraph_neighbor_card (t : ℝ) (x : Fin 8 → V) (i : Fin 8) :
    ((contactGraph t x).neighborSet i).ncard=contactCount x i (d t) := by
  classical
  have he : (contactGraph t x).neighborSet i =
      ↑((Finset.univ.erase i).filter (fun j => ⟪x i,x j⟫_ℝ=d t)) := by
    ext j
    simp [contactGraph,SimpleGraph.mem_neighborSet,ne_comm]
  rw [he,Set.ncard_coe_finset]
  rfl

/-- The contacts of type `d` can be numbered consecutively by `Fin 8`. -/
theorem cycle_numbering (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (x : Fin 8 → V) (hu : ∀ i, ⟪x i,x i⟫_ℝ=1)
    (hc : ∀ i j, i ≠ j →
      ⟪x i,x j⟫_ℝ=a t ∨ ⟪x i,x j⟫_ℝ=b t ∨ ⟪x i,x j⟫_ℝ=c t ∨ ⟪x i,x j⟫_ℝ=d t)
    (hz : ∑ i, x i=0) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ i, ⟪x (σ i),x (σ (i+1))⟫_ℝ=d t := by
  classical
  let G := contactGraph t x
  have hcard (i : Fin 8) : (G.neighborSet i).ncard=2 := by
    rw [contactGraph_neighbor_card]
    exact (row_counts t hL hU x hu hc hz i).2.2.2
  have hcyc : G.IsCycles := fun {i} _ => hcard i
  have hn (i : Fin 8) : (G.neighborSet i).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hcard]; norm_num)
  have had : a t ≠ d t := by
    obtain ⟨hdb,hbc,hcq,hqa,_,_⟩ := contact_inequalities t hL hU
    linarith
  have h3 (i j k : Fin 8) (hij : G.Adj i j) (hjk : G.Adj j k) (hki : G.Adj k i) : False := by
    have ha := neighbors_contact t hL hU (x j) (x i) (x k) (hu j) (hu i) (hu k)
      hij.symm.2 hjk.2 (hc i k hki.1.symm)
    exact had (ha.symm.trans hki.symm.2)
  have h4 (i j k l : Fin 8) (hik : i ≠ k) (hjl : j ≠ l)
      (hij : G.Adj i j) (hjk : G.Adj j k) (hkl : G.Adj k l) (hli : G.Adj l i) : False := by
    have ha := neighbors_contact t hL hU (x j) (x i) (x k) (hu j) (hu i) (hu k)
      hij.symm.2 hjk.2 (hc i k hik)
    have hb := neighbors_contact t hL hU (x k) (x j) (x l) (hu k) (hu j) (hu l)
      hjk.symm.2 hkl.2 (hc j l hjl)
    exact exclude_four_cycle t hL hU (x i) (x j) (x k) (x l)
      (hu i) (hu j) (hu k) (hu l) hij.2 hjk.2 hkl.2 hli.symm.2 ha hb
  obtain ⟨p,hp,hlen,hspan⟩ := exists_eight_cycle hcyc hn h3 h4
  have hinj : Function.Injective (fun i : Fin 8 => p.getVert i.val) := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val ≤ p.length-1; omega)
      (by change j.val ≤ p.length-1; omega) hij
  let σ : Equiv.Perm (Fin 8) := Equiv.ofBijective (fun i : Fin 8 => p.getVert i.val)
    ⟨hinj,Finite.surjective_of_injective hinj⟩
  refine ⟨σ,fun i => ?_⟩
  have he (k : ℕ) (hk : k < 8) : G.Adj (p.getVert k) (p.getVert (k+1)) :=
    p.adj_getVert_succ (by omega)
  fin_cases i
  all_goals try { exact (he _ (by norm_num)).2 }
  have helast := he 7 (by norm_num)
  have hp0 : p.getVert 8=p.getVert 0 := by simpa [hlen] using p.getVert_length
  change ⟪x (p.getVert 7),x (p.getVert 0)⟫_ℝ=d t
  exact hp0 ▸ helast.2



/-- Two known contacts exhaust a row entry whose multiplicity is two. -/
theorem contact_count_two (x : Fin 8 → V) (i j k l : Fin 8) (v : ℝ)
    (hn : contactCount x i v=2) (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hj : ⟪x i,x j⟫_ℝ=v) (hk : ⟪x i,x k⟫_ℝ=v)
    (hl : ⟪x i,x l⟫_ℝ=v) : l=j ∨ l=k := by
  classical
  let S := (Finset.univ.erase i).filter (fun z => ⟪x i,x z⟫_ℝ=v)
  have hjm : j ∈ S := by simp [S,hij.symm,hj]
  have hkm : k ∈ S := by simp [S,hik.symm,hk]
  have hlm : l ∈ S := by simp [S,hil.symm,hl]
  have hsub : {j,k} ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl
    · exact hjm
    · exact hkm
  have hS : S={j,k} := (Finset.eq_of_subset_of_card_le hsub (by
    change contactCount x i v ≤ ({j,k}:Finset (Fin 8)).card
    simp [hn,hjk])).symm
  simpa [hS] using hlm

/-- With consecutive `d`-contacts, cyclic distances determine every Gram entry. -/
theorem labeled_gram (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (x : Fin 8 → V) (hu : ∀ i, ⟪x i,x i⟫_ℝ=1)
    (hc : ∀ i j, i ≠ j →
      ⟪x i,x j⟫_ℝ=a t ∨ ⟪x i,x j⟫_ℝ=b t ∨ ⟪x i,x j⟫_ℝ=c t ∨ ⟪x i,x j⟫_ℝ=d t)
    (hz : ∑ i, x i=0) (he : ∀ i, ⟪x i,x (i+1)⟫_ℝ=d t) :
    (∀ i, ⟪x i,x (i+2)⟫_ℝ=a t) ∧
    (∀ i, ⟪x i,x (i+3)⟫_ℝ=c t) ∧
    (∀ i, ⟪x i,x (i+4)⟫_ℝ=b t) := by
  classical
  have hcnt := row_counts t hL hU x hu hc hz
  have htwo (i : Fin 8) : ⟪x i,x (i+2)⟫_ℝ=a t := by
    apply neighbors_contact t hL hU (x (i+1)) (x i) (x (i+2))
      (hu _) (hu _) (hu _)
    · exact (real_inner_comm (x i) (x (i+1))).trans (he i)
    · simpa [add_assoc] using he (i+1)
    · apply hc
      fin_cases i <;> decide
  have htwo' (i : Fin 8) : ⟪x i,x (i+6)⟫_ℝ=a t := by
    have h := htwo (i+6)
    have ei : (i+6)+2=i := by fin_cases i <;> decide
    rw [ei] at h
    exact (real_inner_comm (x (i+6)) (x i)).trans h
  have hone' (i : Fin 8) : ⟪x i,x (i+7)⟫_ℝ=d t := by
    have h := he (i+7)
    have ei : (i+7)+1=i := by fin_cases i <;> decide
    rw [ei] at h
    exact (real_inner_comm (x (i+7)) (x i)).trans h
  have hnotA (i : Fin 8) (k : Fin 8) (hk : k=3 ∨ k=4) : ⟪x i,x (i+k)⟫_ℝ ≠ a t := by
    intro hh
    have h := contact_count_two x i (i+2) (i+6) (i+k) (a t) (hcnt i).1
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by rcases hk with rfl|rfl <;> fin_cases i <;> decide)
      (by fin_cases i <;> decide) (htwo i) (htwo' i) hh
    rcases hk with rfl|rfl <;> fin_cases i <;> norm_num at h
  have hnotD (i : Fin 8) (k : Fin 8) (hk : k=3 ∨ k=4) : ⟪x i,x (i+k)⟫_ℝ ≠ d t := by
    intro hh
    have h := contact_count_two x i (i+1) (i+7) (i+k) (d t) (hcnt i).2.2.2
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by rcases hk with rfl|rfl <;> fin_cases i <;> decide)
      (by fin_cases i <;> decide) (he i) (hone' i) hh
    rcases hk with rfl|rfl <;> fin_cases i <;> norm_num at h
  have hthree (i : Fin 8) : ⟪x i,x (i+3)⟫_ℝ=c t := by
    rcases hc i (i+3) (by fin_cases i <;> decide) with hh|hh|hh|hh
    · exact False.elim (hnotA i 3 (Or.inl rfl) hh)
    · apply False.elim
      exact exclude_path_three_b t hL hU (x i) (x (i+1)) (x (i+2)) (x (i+3))
        (hu _) (hu _) (hu _) (hu _) (he i)
        (by simpa [add_assoc] using he (i+1))
        (by simpa [add_assoc] using he (i+2)) hh (htwo i)
        (by simpa [add_assoc] using htwo (i+1))
    · exact hh
    · exact False.elim (hnotD i 3 (Or.inl rfl) hh)
  have hthree' (i : Fin 8) : ⟪x i,x (i+5)⟫_ℝ=c t := by
    have h := hthree (i+5)
    have ei : (i+5)+3=i := by fin_cases i <;> decide
    rw [ei] at h
    exact (real_inner_comm (x (i+5)) (x i)).trans h
  refine ⟨htwo,hthree,fun i => ?_⟩
  rcases hc i (i+4) (by fin_cases i <;> decide) with hh|hh|hh|hh
  · exact False.elim (hnotA i 4 (Or.inr rfl) hh)
  · exact hh
  · have h := contact_count_two x i (i+3) (i+5) (i+4) (c t) (hcnt i).2.2.1
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (hthree i) (hthree' i) hh
    fin_cases i <;> norm_num at h
  · exact False.elim (hnotD i 4 (Or.inr rfl) hh)

/-- The full cyclic Gram pattern of the eight-point theorem. -/
theorem gram_classification (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (x : Fin 8 → V) (hu : ∀ i, ⟪x i,x i⟫_ℝ=1)
    (hc : ∀ i j, i ≠ j →
      ⟪x i,x j⟫_ℝ=a t ∨ ⟪x i,x j⟫_ℝ=b t ∨ ⟪x i,x j⟫_ℝ=c t ∨ ⟪x i,x j⟫_ℝ=d t)
    (hz : ∑ i, x i=0) :
    ∃ σ : Equiv.Perm (Fin 8),
      (∀ i, ⟪x (σ i),x (σ (i+1))⟫_ℝ=d t) ∧
      (∀ i, ⟪x (σ i),x (σ (i+2))⟫_ℝ=a t) ∧
      (∀ i, ⟪x (σ i),x (σ (i+3))⟫_ℝ=c t) ∧
      (∀ i, ⟪x (σ i),x (σ (i+4))⟫_ℝ=b t) := by
  obtain ⟨σ,hσ⟩ := cycle_numbering t hL hU x hu hc hz
  have hc' (i j : Fin 8) (hij : i ≠ j) := hc (σ i) (σ j) (σ.injective.ne hij)
  have hz' : ∑ i, x (σ i)=0 := by rw [Equiv.sum_comp,hz]
  obtain ⟨h₂,h₃,h₄⟩ := labeled_gram t hL hU (fun i => x (σ i)) (fun i => hu (σ i)) hc' hz' hσ
  exact ⟨σ,hσ,h₂,h₃,h₄⟩



/-- The first row of the classified circulant Gram matrix. -/
def gramEntry (t : ℝ) (k : Fin 8) : ℝ := ![1,d t,a t,c t,b t,c t,a t,d t] k

/-- Entrywise version convenient for comparison with standard antiprism coordinates. -/
theorem gram_classification_entrywise (t : ℝ) (hL : (39:ℝ)/125 < t) (hU : t < 8/25)
    (x : Fin 8 → V) (hu : ∀ i, ⟪x i,x i⟫_ℝ=1)
    (hc : ∀ i j, i ≠ j →
      ⟪x i,x j⟫_ℝ=a t ∨ ⟪x i,x j⟫_ℝ=b t ∨ ⟪x i,x j⟫_ℝ=c t ∨ ⟪x i,x j⟫_ℝ=d t)
    (hz : ∑ i, x i=0) :
    ∃ σ : Equiv.Perm (Fin 8), ∀ i j,
      ⟪x (σ i),x (σ j)⟫_ℝ=gramEntry t (j-i) := by
  obtain ⟨σ,h₁,h₂,h₃,h₄⟩ := gram_classification t hL hU x hu hc hz
  have h₅ (i : Fin 8) : ⟪x (σ i),x (σ (i+5))⟫_ℝ=c t := by
    have h := h₃ (i+5)
    have ei : (i+5)+3=i := by fin_cases i <;> decide
    rw [ei] at h
    exact (real_inner_comm (x (σ (i+5))) (x (σ i))).trans h
  have h₆ (i : Fin 8) : ⟪x (σ i),x (σ (i+6))⟫_ℝ=a t := by
    have h := h₂ (i+6)
    have ei : (i+6)+2=i := by fin_cases i <;> decide
    rw [ei] at h
    exact (real_inner_comm (x (σ (i+6))) (x (σ i))).trans h
  have h₇ (i : Fin 8) : ⟪x (σ i),x (σ (i+7))⟫_ℝ=d t := by
    have h := h₁ (i+7)
    have ei : (i+7)+1=i := by fin_cases i <;> decide
    rw [ei] at h
    exact (real_inner_comm (x (σ (i+7))) (x (σ i))).trans h
  refine ⟨σ,fun i j => ?_⟩
  generalize hk : j-i=k
  have hij : j=i+k := by simpa [add_comm] using (sub_eq_iff_eq_add.mp hk)
  subst j
  fin_cases k
  · change ⟪x (σ i),x (σ (i+0))⟫_ℝ=1
    simpa only [add_zero] using hu (σ i)
  all_goals simp [gramEntry,h₁,h₂,h₃,h₄,h₅,h₆,h₇]

end Thomson78.Eight

