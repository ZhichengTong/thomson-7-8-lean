import Thomson78.Analysis
import Thomson78.Moments

/-! The analytic step in the two-coordinate certificate recovery.
The trace pairing is treated as a nonnegative scalar function, so Fermat's
lemma gives its vanishing first derivative at a tight certificate block. -/
noncomputable section
open Set Filter Matrix
open scoped BigOperators Topology
namespace Thomson78.Analysis

theorem derivative_eq_zero_of_nonneg_on_interval (g : ℝ → ℝ)
    (a b t d : ℝ) (ht : t ∈ Ioo a b)
    (hnonneg : ∀ s ∈ Ioo a b, 0 ≤ g s) (hzero : g t = 0)
    (hd : HasDerivAt g d t) : d = 0 := by
  have hmin : IsMinOn g (Ioo a b) t := by
    intro s hs
    rw [hzero]
    exact hnonneg s hs
  exact (hmin.isLocalMin (isOpen_Ioo.mem_nhds ht)).hasDerivAt_eq_zero hd

/-- A tight positive semidefinite block has zero trace derivative along any
smooth family of feasible moment matrices. -/
theorem trace_derivative_eq_zero {J K : Type*} [Fintype J] [Fintype K] [DecidableEq J]
    (M : ℝ → Matrix J J ℝ) (R : Matrix J K ℝ) (a b t d : ℝ)
    (ht : t ∈ Ioo a b) (hM : ∀ s ∈ Ioo a b, (M s).PosSemidef)
    (hkernel : M t * (R * Rᴴ) = 0)
    (hd : HasDerivAt (fun s => Matrix.trace ((R * Rᴴ) * M s)) d t) : d = 0 := by
  apply derivative_eq_zero_of_nonneg_on_interval _ a b t d ht
  · intro s hs
    exact Thomson78.trace_factor_nonneg (M s) R (hM s hs)
  · rw [Matrix.trace_mul_comm, hkernel, Matrix.trace_zero]
  · exact hd

/-- The value and stationarity equations recover the two residual coordinates.
`H` is the auxiliary polynomial energy on the antiprism family and `G` is the
sum of the trace pairings. The other constraint terms vanish along that family. -/
theorem recover_certificate_residual
    (t r₀ r₆ τ : ℝ) (H G : ℝ → ℝ)
    (hL : 39/125 ≤ t) (hU : t < 8/25)
    (hidentity : ∀ s ∈ Ioo (0 : ℝ) 1,
      r₀ + sixthMoment s * r₆ = H s - τ - G s)
    (hHvalue : H t = τ) (hHderiv : HasDerivAt H 0 t)
    (hGnonneg : ∀ s ∈ Ioo (0 : ℝ) 1, 0 ≤ G s)
    (hGvalue : G t = 0) (hGdiff : DifferentiableAt ℝ G t) :
    r₀ = 0 ∧ r₆ = 0 := by
  have ht : t ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
  have hGzero : deriv G t = 0 := derivative_eq_zero_of_nonneg_on_interval G 0 1 t
    (deriv G t) ht hGnonneg hGvalue hGdiff.hasDerivAt
  have hGderiv : HasDerivAt G 0 t := by simpa [hGzero] using hGdiff.hasDerivAt
  have hrvalue : r₀ + sixthMoment t * r₆ = 0 := by
    simpa [hHvalue, hGvalue] using hidentity t ht
  have hbase : HasDerivAt (fun s => H s - τ - G s) 0 t := by
    convert (hHderiv.sub_const τ).sub hGderiv using 1 <;> norm_num
  have hevent : (fun s => r₀ + sixthMoment s * r₆) =ᶠ[nhds t]
      (fun s => H s - τ - G s) :=
    (show ∀ᶠ s in nhds t, s ∈ Ioo (0 : ℝ) 1 from
      isOpen_Ioo.mem_nhds ht).mono (fun s hs => hidentity s hs)
  have hrzero := hbase.congr_of_eventuallyEq hevent
  have hrslope := ((sixthMoment_hasDerivAt t).mul_const r₆).const_add r₀
  have heq := hrslope.unique hrzero
  apply recover_two_coordinates t r₀ r₆ hL hU hrvalue
  simpa [sixthMoment_deriv] using heq

end Thomson78.Analysis
