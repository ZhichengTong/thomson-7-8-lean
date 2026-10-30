import Thomson78.Basic
import Mathlib.Combinatorics.SimpleGraph.Matching

/-! The finite graph step: a two-regular graph on eight vertices with no
three- or four-cycles is one eight-cycle. -/
noncomputable section
open scoped BigOperators
namespace Thomson78.Eight

variable {G : SimpleGraph (Fin 8)}

theorem cycle_length_at_least_five
    (h3 : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False)
    (h4 : ∀ u v w z, u ≠ w → v ≠ z →
      G.Adj u v → G.Adj v w → G.Adj w z → G.Adj z u → False)
    {u : Fin 8} (p : G.Walk u u) (hp : p.IsCycle) : 5 ≤ p.length := by
  have hlen := hp.three_le_length
  have hadj (k : ℕ) (hk : k < p.length) := p.adj_getVert_succ hk
  by_contra h
  have he : p.length=3 ∨ p.length=4 := by omega
  rcases he with he|he
  · apply h3 (p.getVert 0) (p.getVert 1) (p.getVert 2)
    · exact hadj 0 (by omega)
    · exact hadj 1 (by omega)
    · simpa [← he] using hadj 2 (by omega)
  · apply h4 (p.getVert 0) (p.getVert 1) (p.getVert 2) (p.getVert 3)
    · intro hh
      have hh' := hp.getVert_injOn' (x₁:=0) (x₂:=2) (by change 0 ≤ p.length-1; omega)
        (by change 2 ≤ p.length-1; omega) hh
      omega
    · intro hh
      have hh' := hp.getVert_injOn' (x₁:=1) (x₂:=3) (by change 1 ≤ p.length-1; omega)
        (by change 3 ≤ p.length-1; omega) hh
      omega
    · exact hadj 0 (by omega)
    · exact hadj 1 (by omega)
    · exact hadj 2 (by omega)
    · simpa [← he] using hadj 3 (by omega)

theorem cycle_support_card {u : Fin 8} (p : G.Walk u u) (hp : p.IsCycle) :
    p.support.toFinset.card = p.length := by
  classical
  have he : p.support.toFinset = p.support.tail.toFinset := by
    rw [← p.cons_tail_eq hp.not_nil]
    simp only [SimpleGraph.Walk.support_cons,List.tail_cons,List.toFinset_cons]
    exact Finset.insert_eq_of_mem (List.mem_toFinset.mpr (p.tail.end_mem_support))
  rw [he,List.toFinset_card_of_nodup hp.support_nodup,List.length_tail,p.length_support]
  omega

/-- The purely graph theoretic extraction used in the manuscript. -/
theorem exists_eight_cycle
    (hcyc : G.IsCycles) (hn : ∀ v, (G.neighborSet v).Nonempty)
    (h3 : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False)
    (h4 : ∀ u v w z, u ≠ w → v ≠ z →
      G.Adj u v → G.Adj v w → G.Adj w z → G.Adj z u → False) :
    ∃ p : G.Walk 0 0, p.IsCycle ∧ p.length=8 ∧ ∀ v, v ∈ p.support := by
  classical
  obtain ⟨p,hp,hpc⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c:=G.connectedComponentMk 0) (v:=0) (by rfl) (hn 0)
  have hp5 := cycle_length_at_least_five h3 h4 p hp
  have hspan : ∀ v, v ∈ p.support := by
    intro v
    by_contra hv
    obtain ⟨q,hq,hqc⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c:=G.connectedComponentMk v) (v:=v) (by rfl) (hn v)
    have hq5 := cycle_length_at_least_five h3 h4 q hq
    have hne : G.connectedComponentMk 0 ≠ G.connectedComponentMk v := by
      intro hh
      apply hv
      rw [← p.mem_verts_toSubgraph,hpc,hh]
      rfl
    have hdset := G.pairwise_disjoint_supp_connectedComponent hne
    have hd : Disjoint p.support.toFinset q.support.toFinset := by
      apply Finset.disjoint_left.mpr
      intro w hwp hwq
      apply Set.disjoint_left.mp hdset
      · rw [← hpc,p.mem_verts_toSubgraph]
        exact List.mem_toFinset.mp hwp
      · rw [← hqc,q.mem_verts_toSubgraph]
        exact List.mem_toFinset.mp hwq
    have hc := Finset.card_le_univ (p.support.toFinset ∪ q.support.toFinset)
    rw [Finset.card_union_of_disjoint hd,cycle_support_card p hp,cycle_support_card q hq] at hc
    norm_num at hc
    omega
  refine ⟨p,hp,?_,hspan⟩
  have hu : p.support.toFinset=Finset.univ := by
    ext v
    simp [hspan v]
  have hc := cycle_support_card p hp
  rw [hu] at hc
  norm_num at hc
  omega

end Thomson78.Eight

