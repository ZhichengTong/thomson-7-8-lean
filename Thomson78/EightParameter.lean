import Thomson78.EightGeometry
import Thomson78.AnalysisCoulomb
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp

/-! Existence, uniqueness and localization of the square-antiprism parameter.
The elementary inverse-square-root derivative and monotonicity calculations
were cross-checked against J. Tooby-Smith and A. Zughaid,
Thomson-N-8-Warrant, commit 2c35d62e07d72686931da4bc3e062d668e858eda,
Thomson/Antiprism/Derivative.lean. The interval estimates below use the
manuscript's endpoints and newly checked short rational bounds. -/
noncomputable section
open scoped Topology
namespace Thomson78.Eight

/-- Energy of the square-antiprism family. -/
def phi (t : ℝ) : ℝ :=
  (2+4*s) / Real.sqrt (1-t) +
  8 / Real.sqrt (2-s+(2+s)*t) +
  8 / Real.sqrt (2+s+(2-s)*t)

/-- Its explicit derivative. -/
def phiPrime (t : ℝ) : ℝ :=
  (1+2*s) / (Real.sqrt (1-t))^3 -
  4*(2+s) / (Real.sqrt (2-s+(2+s)*t))^3 -
  4*(2-s) / (Real.sqrt (2+s+(2-s)*t))^3

theorem sqrt_tight_bounds : (7071:ℝ)/5000 < s ∧ s < (14143:ℝ)/10000 := by
  have hs : s^2=2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  constructor <;> nlinarith


/-- The square-root derivative from the common analysis module. -/
theorem sqrt_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt Real.sqrt (1/(2*Real.sqrt u)) u :=
  Thomson78.Analysis.sqrt_hasDerivAt_of_pos u hu

/-- Chain rule for one term of the family energy. -/
theorem derivative_inv_sqrt_affine (A B C t : ℝ) (hpos : 0 < B+C*t) :
    HasDerivAt (fun u => A / Real.sqrt (B+C*u))
      (-(A*C/2) / (Real.sqrt (B+C*t))^3) t := by
  have hlin : HasDerivAt (fun u => B+C*u) C t := by
    simpa using ((hasDerivAt_id t).const_mul C).const_add B
  have h := (((sqrt_hasDerivAt hpos).comp t hlin).inv (Real.sqrt_pos.2 hpos).ne').const_mul A
  have hs : Real.sqrt (B+C*t) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  convert h using 1
  · ext u
    exact div_eq_mul_inv A _
  · dsimp only [Function.comp_apply]
    field_simp

theorem phi_hasDerivAt (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt phi (phiPrime t) t := by
  obtain ⟨hsL,hsU⟩ := sqrt_bounds
  have h₁ := derivative_inv_sqrt_affine (2+4*s) 1 (-1) t (by linarith [ht.2])
  have h₂ := derivative_inv_sqrt_affine 8 (2-s) (2+s) t (by nlinarith [ht.1])
  have h₃ := derivative_inv_sqrt_affine 8 (2+s) (2-s) t (by nlinarith [ht.1])
  convert (h₁.add h₂).add h₃ using 1
  · ext u
    simp only [phi,Pi.add_apply]
    simp only [show ∀ u : ℝ, 1+(-1)*u=1-u by intro u; ring]
  · simp only [phiPrime,show (1:ℝ)+(-1)*t=1-t by ring]
    ring

theorem inverse_cube_sqrt_strictAnti {A u v : ℝ}
    (hA : 0 < A) (hu : 0 < u) (huv : u < v) :
    A / (Real.sqrt v)^3 < A / (Real.sqrt u)^3 := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hlt : Real.sqrt u < Real.sqrt v := Real.sqrt_lt_sqrt hu.le huv
  have hpow := pow_lt_pow_left₀ hlt hs.le (show (3:ℕ) ≠ 0 by decide)
  exact div_lt_div_of_pos_left hA (by positivity) hpow

theorem phiPrime_strictMonoOn : StrictMonoOn phiPrime (Set.Ioo (0:ℝ) 1) := by
  intro t ht u hu htu
  obtain ⟨hsL,hsU⟩ := sqrt_bounds
  have h₁ := inverse_cube_sqrt_strictAnti (A:=1+2*s)
    (by linarith) (show 0 < 1-u by linarith [hu.2]) (show 1-u < 1-t by linarith)
  have h₂ := inverse_cube_sqrt_strictAnti (A:=4*(2+s))
    (by linarith) (show 0 < 2-s+(2+s)*t by nlinarith [ht.1])
    (show 2-s+(2+s)*t < 2-s+(2+s)*u by nlinarith)
  have h₃ := inverse_cube_sqrt_strictAnti (A:=4*(2-s))
    (by linarith) (show 0 < 2+s+(2-s)*t by nlinarith [ht.1])
    (show 2+s+(2-s)*t < 2+s+(2-s)*u by nlinarith)
  dsimp [phiPrime]
  linarith

/-- Rational upper enclosure of an inverse-cube square-root term. -/
theorem cube_term_upper {A U v y : ℝ}
    (hA : A ≤ U) (hU : 0 < U) (hy : 0 < y) (hv : y^2 < v) :
    A/(Real.sqrt v)^3 < U/y^3 := by
  have hys : y < Real.sqrt v := (Real.lt_sqrt hy.le).2 hv
  have hsp : 0 < Real.sqrt v := hy.trans hys
  have hpow := pow_lt_pow_left₀ hys hy.le (show (3:ℕ) ≠ 0 by decide)
  calc
    A/(Real.sqrt v)^3 ≤ U/(Real.sqrt v)^3 := div_le_div_of_nonneg_right hA (by positivity)
    _ < U/y^3 := div_lt_div_of_pos_left hU (by positivity) hpow

/-- Rational lower enclosure of an inverse-cube square-root term. -/
theorem cube_term_lower {A L v z : ℝ}
    (hA : L ≤ A) (hL : 0 < L) (hv : 0 < v) (hz : 0 < z) (hvz : v < z^2) :
    L/z^3 < A/(Real.sqrt v)^3 := by
  have hsz : Real.sqrt v < z := (Real.sqrt_lt' hz).2 hvz
  have hsp : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hpow := pow_lt_pow_left₀ hsz hsp.le (show (3:ℕ) ≠ 0 by decide)
  calc
    L/z^3 < L/(Real.sqrt v)^3 := div_lt_div_of_pos_left hL (by positivity) hpow
    _ ≤ A/(Real.sqrt v)^3 := div_le_div_of_nonneg_right hA (by positivity)

theorem phiPrime_left_bound : phiPrime ((39:ℝ)/125) < -(3:ℝ)/50 := by
  obtain ⟨hsL,hsU⟩ := sqrt_tight_bounds
  have h₁ := cube_term_upper (A:=1+2*s) (U:=19143/5000)
    (v:=1-39/125) (y:=4147/5000) (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have h₂ := cube_term_lower (A:=4*(2+s)) (L:=17071/1250)
    (v:=2-s+(2+s)*(39/125)) (z:=257/200)
    (by linarith) (by norm_num) (by nlinarith) (by norm_num) (by nlinarith)
  have h₃ := cube_term_lower (A:=4*(2-s)) (L:=5857/2500)
    (v:=2+s+(2-s)*(39/125)) (z:=1897/1000)
    (by linarith) (by norm_num) (by nlinarith) (by norm_num) (by nlinarith)
  have hn : (19143/5000:ℝ)/(4147/5000)^3 -
      (17071/1250)/(257/200)^3 - (5857/2500)/(1897/1000)^3 < -(3:ℝ)/50 := by norm_num
  dsimp [phiPrime]
  linarith

theorem phiPrime_right_bound : (9:ℝ)/50 < phiPrime ((8:ℝ)/25) := by
  obtain ⟨hsL,hsU⟩ := sqrt_tight_bounds
  have h₁ := cube_term_lower (A:=1+2*s) (L:=9571/2500)
    (v:=1-8/25) (z:=33/40)
    (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h₂ := cube_term_upper (A:=4*(2+s)) (U:=34143/2500)
    (v:=2-s+(2+s)*(8/25)) (y:=259/200)
    (by linarith) (by norm_num) (by norm_num) (by nlinarith)
  have h₃ := cube_term_upper (A:=4*(2-s)) (U:=2929/1250)
    (v:=2+s+(2-s)*(8/25)) (y:=1897/1000)
    (by linarith) (by norm_num) (by norm_num) (by nlinarith)
  have hn : (9:ℝ)/50 < (9571/2500)/(33/40)^3 -
      (34143/2500)/(259/200)^3 - (2929/1250)/(1897/1000)^3 := by norm_num
  dsimp [phiPrime]
  linarith

theorem phiPrime_left_negative : phiPrime ((39:ℝ)/125) < 0 := by
  linarith [phiPrime_left_bound]

theorem phiPrime_right_positive : 0 < phiPrime ((8:ℝ)/25) := by
  linarith [phiPrime_right_bound]

theorem phiPrime_continuousOn : ContinuousOn phiPrime (Set.Ioo (0:ℝ) 1) := by
  intro t ht
  obtain ⟨hsL,hsU⟩ := sqrt_bounds
  have h₁ : 0 < 1-t := by linarith [ht.2]
  have h₂ : 0 < 2-s+(2+s)*t := by nlinarith [ht.1]
  have h₃ : 0 < 2+s+(2-s)*t := by nlinarith [ht.1]
  apply ContinuousAt.continuousWithinAt
  unfold phiPrime
  fun_prop (disch := positivity)

theorem exists_stationary : ∃ t ∈ Set.Ioo ((39:ℝ)/125) (8/25), phiPrime t=0 := by
  have hsub : Set.Icc ((39:ℝ)/125) (8/25) ⊆ Set.Ioo (0:ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (show (39:ℝ)/125 ≤ 8/25 by norm_num)
    (phiPrime_continuousOn.mono hsub)
    (show (0:ℝ) ∈ Set.Icc (phiPrime (39/125)) (phiPrime (8/25)) from
      ⟨phiPrime_left_negative.le,phiPrime_right_positive.le⟩)
  refine ⟨t,⟨?_,?_⟩,he⟩
  · exact lt_of_le_of_ne ht.1 (by intro hh; rw [← hh] at he; linarith [phiPrime_left_negative])
  · exact lt_of_le_of_ne ht.2 (by intro hh; rw [hh] at he; linarith [phiPrime_right_positive])

def tStar : ℝ := Classical.choose exists_stationary

theorem tStar_bounds : (39:ℝ)/125 < tStar ∧ tStar < 8/25 :=
  (Classical.choose_spec exists_stationary).1

theorem phiPrime_tStar : phiPrime tStar=0 := (Classical.choose_spec exists_stationary).2

theorem tStar_mem : tStar ∈ Set.Ioo (0:ℝ) 1 := by
  constructor <;> linarith [tStar_bounds.1,tStar_bounds.2]

theorem stationary_unique (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) (he : phiPrime t=0) :
    t=tStar := phiPrime_strictMonoOn.injOn ht tStar_mem (he.trans phiPrime_tStar.symm)



/-- Strict minimality follows from the sign change of the increasing derivative. -/
theorem phi_strict_minimum (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) (hne : t ≠ tStar) :
    phi tStar < phi t := by
  rcases lt_or_gt_of_ne hne with hlt|hlt
  · have hanti : StrictAntiOn phi (Set.Icc t tStar) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · intro u hu
        apply (phi_hasDerivAt u ?_).continuousAt.continuousWithinAt
        constructor <;> linarith [ht.1,ht.2,tStar_mem.1,tStar_mem.2,hu.1,hu.2]
      · intro u hu
        rw [interior_Icc] at hu
        have hu' : u ∈ Set.Ioo (0:ℝ) 1 := by
          constructor <;> linarith [ht.1,tStar_mem.2,hu.1,hu.2]
        rw [(phi_hasDerivAt u hu').deriv]
        have hh := phiPrime_strictMonoOn hu' tStar_mem hu.2
        rwa [phiPrime_tStar] at hh
    exact hanti ⟨le_rfl,hlt.le⟩ ⟨hlt.le,le_rfl⟩ hlt
  · have hmono : StrictMonoOn phi (Set.Icc tStar t) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · intro u hu
        apply (phi_hasDerivAt u ?_).continuousAt.continuousWithinAt
        constructor <;> linarith [ht.1,ht.2,tStar_mem.1,tStar_mem.2,hu.1,hu.2]
      · intro u hu
        rw [interior_Icc] at hu
        have hu' : u ∈ Set.Ioo (0:ℝ) 1 := by
          constructor <;> linarith [tStar_mem.1,ht.2,hu.1,hu.2]
        rw [(phi_hasDerivAt u hu').deriv]
        have hh := phiPrime_strictMonoOn tStar_mem hu' hu.1
        rwa [phiPrime_tStar] at hh
    exact hmono ⟨le_rfl,hlt.le⟩ ⟨hlt.le,le_rfl⟩ hlt

theorem phi_minimum (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) : phi tStar ≤ phi t := by
  by_cases he : t=tStar
  · subst t
    rfl
  · exact (phi_strict_minimum t ht he).le

theorem phi_minimum_unique (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    phi t=phi tStar ↔ t=tStar := by
  constructor
  · intro he
    by_contra hn
    exact (ne_of_gt (phi_strict_minimum t ht hn)) he
  · intro he
    rw [he]

theorem phi_deriv_tStar : deriv phi tStar=0 := by
  rw [(phi_hasDerivAt tStar tStar_mem).deriv,phiPrime_tStar]

theorem phi_deriv_zero_unique (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1)
    (he : deriv phi t=0) : t=tStar := by
  apply stationary_unique t ht
  rwa [(phi_hasDerivAt t ht).deriv] at he



/-- The explicit energy formula equals the weighted Coulomb contact sum. -/
theorem phi_eq_weighted_coulomb (t : ℝ) (_ht : 0 < t) (ht1 : t < 1) :
    phi t=8*Thomson78.Analysis.coulomb (a t)+4*Thomson78.Analysis.coulomb (b t)+
      8*Thomson78.Analysis.coulomb (c t)+8*Thomson78.Analysis.coulomb (d t) := by
  have hr : Real.sqrt (1-t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hs : s ≠ 0 := (Real.sqrt_pos.2 (show (0:ℝ)<2 by norm_num)).ne'
  have hs2 : s^2=2 := Real.sq_sqrt (by norm_num)
  have ha : Real.sqrt (2-2*a t)=s*Real.sqrt (1-t) := by
    rw [show 2-2*a t=2*(1-t) by dsimp [a]; ring,Real.sqrt_mul (by norm_num)]
  have hb : Real.sqrt (2-2*b t)=2*Real.sqrt (1-t) := by
    rw [show 2-2*b t=4*(1-t) by dsimp [b]; ring,Real.sqrt_mul (by norm_num)]
    norm_num
  have hc : Real.sqrt (2-2*c t)=Real.sqrt (2-s+(2+s)*t) := by
    congr 1
    dsimp [c]
    ring
  have hd : Real.sqrt (2-2*d t)=Real.sqrt (2+s+(2-s)*t) := by
    congr 1
    dsimp [d]
    ring
  have hab : (2+4*s)/Real.sqrt (1-t)=
      8*(s*Real.sqrt (1-t))⁻¹+4*(2*Real.sqrt (1-t))⁻¹ := by
    field_simp
    nlinarith [hs2]
  unfold phi Thomson78.Analysis.coulomb
  rw [ha,hb,hc,hd,hab]
  ring

end Thomson78.Eight
