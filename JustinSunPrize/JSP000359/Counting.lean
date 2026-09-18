import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

/-!
# JSP-000359 / Erdős problem 440: the square-root counting estimate

This file formalizes the elementary order-bound part of the historical
Erdős--Szemerédi result.  The mathematical result is not new.  The Lean source
is an AI-assisted reimplementation in a current Mathlib release.
-/

set_option autoImplicit false

namespace JustinSunPrize.JSP000359

/-- An enumeration of an infinite set of positive integers. -/
structure PositiveIncreasingSequence where
  term : ℕ → ℕ
  positive : ∀ i, 0 < term i
  strictlyIncreasing : StrictMono term

namespace PositiveIncreasingSequence

instance : CoeFun PositiveIncreasingSequence (fun _ => ℕ → ℕ) :=
  ⟨PositiveIncreasingSequence.term⟩

/-- Least common multiple associated to the edge from `i` to `i + 1`. -/
def edgeLcm (A : PositiveIncreasingSequence) (i : ℕ) : ℕ :=
  Nat.lcm (A i) (A (i + 1))

/-- All indices whose adjacent LCM is at most `x`.

The ambient range is exact rather than an arbitrary computational cutoff.
-/
def goodEdges (A : PositiveIncreasingSequence) (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun i => A.edgeLcm i ≤ x

/-- The counting function in Erdős problem 440. -/
def count (A : PositiveIncreasingSequence) (x : ℕ) : ℕ :=
  (A.goodEdges x).card

lemma index_succ_le_term (A : PositiveIncreasingSequence) (i : ℕ) : i + 1 ≤ A i := by
  induction i with
  | zero => exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (A.positive 0))
  | succ i ih =>
      have hstep := A.strictlyIncreasing (Nat.lt_succ_self i)
      simp only [Nat.succ_eq_add_one] at hstep ⊢
      omega

lemma edge_index_lt_threshold {A : PositiveIncreasingSequence} {i x : ℕ}
    (hix : A.edgeLcm i ≤ x) : i < x := by
  have hright : A (i + 1) ≤ A.edgeLcm i := by
    exact Nat.le_of_dvd (Nat.lcm_pos (A.positive i) (A.positive (i + 1)))
      (Nat.dvd_lcm_right _ _)
  have hindex : i + 2 ≤ A (i + 1) := by
    simpa [Nat.add_assoc] using A.index_succ_le_term (i + 1)
  omega

lemma mem_goodEdges_iff {A : PositiveIncreasingSequence} {i x : ℕ} :
    i ∈ A.goodEdges x ↔ A.edgeLcm i ≤ x := by
  simp only [goodEdges, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    exact ⟨edge_index_lt_threshold h, h⟩

lemma gcd_le_positive_gap (A : PositiveIncreasingSequence) (i : ℕ) :
    Nat.gcd (A i) (A (i + 1)) ≤ A (i + 1) - A i := by
  have hlt := A.strictlyIncreasing (Nat.lt_succ_self i)
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hlt)
    (Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _))

/-- On a good edge, division by the right endpoint is strictly smaller than
division by the left endpoint. -/
lemma quotient_strictly_drops (A : PositiveIncreasingSequence) {i x : ℕ}
    (hi : A.edgeLcm i ≤ x) : x / A (i + 1) < x / A i := by
  have hmono := A.strictlyIncreasing (Nat.lt_succ_self i)
  have hright : 0 < A (i + 1) := A.positive (i + 1)
  have hgcd := A.gcd_le_positive_gap i
  have hquot : A.edgeLcm i / A (i + 1) ≤ x / A (i + 1) :=
    Nat.div_le_div_right hi
  have hlcmMul : A.edgeLcm i / A (i + 1) * A (i + 1) = A.edgeLcm i :=
    Nat.div_mul_cancel (Nat.dvd_lcm_right _ _)
  have hfactor : Nat.gcd (A i) (A (i + 1)) * (A.edgeLcm i / A (i + 1)) = A i := by
    apply Nat.eq_of_mul_eq_mul_right hright
    calc
      (Nat.gcd (A i) (A (i + 1)) * (A.edgeLcm i / A (i + 1))) * A (i + 1) =
          Nat.gcd (A i) (A (i + 1)) * A.edgeLcm i := by
            rw [Nat.mul_assoc, hlcmMul]
      _ = A i * A (i + 1) := by
        simp [edgeLcm, Nat.gcd_mul_lcm]
  have hmulGcd := Nat.mul_le_mul_left (Nat.gcd (A i) (A (i + 1))) hquot
  have hmulGap := Nat.mul_le_mul_right (x / A (i + 1)) hgcd
  have hfloor := Nat.div_mul_le_self x (A (i + 1))
  have htarget : (x / A (i + 1) + 1) * A i ≤ x := by
    have hsub : A (i + 1) - A i + A i = A (i + 1) :=
      Nat.sub_add_cancel hmono.le
    nlinarith
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    ((Nat.le_div_iff_mul_le (A.positive i)).2 htarget)

/-- Distinct good indices give distinct quotients `x / A i`. -/
lemma quotient_injective_on_good (A : PositiveIncreasingSequence) (x : ℕ) :
    Set.InjOn (fun i => x / A i) (A.goodEdges x : Set ℕ) := by
  intro i hi j hj heq
  change x / A i = x / A j at heq
  rcases lt_trichotomy i j with hij | hij | hji
  · have hterms : A (i + 1) ≤ A j := A.strictlyIncreasing.monotone (by omega)
    have hdiv : x / A j ≤ x / A (i + 1) :=
      Nat.div_le_div_left hterms (A.positive (i + 1))
    have hdrop := A.quotient_strictly_drops
      ((mem_goodEdges_iff.mp hi) : A.edgeLcm i ≤ x)
    omega
  · exact hij
  · have hterms : A (j + 1) ≤ A i := A.strictlyIncreasing.monotone (by omega)
    have hdiv : x / A i ≤ x / A (j + 1) :=
      Nat.div_le_div_left hterms (A.positive (j + 1))
    have hdrop := A.quotient_strictly_drops
      ((mem_goodEdges_iff.mp hj) : A.edgeLcm j ≤ x)
    omega

/-- Split at `t`: at most `t` small terms, and at most `x/(t+1)` distinct
positive quotients from the remaining terms. -/
theorem count_le_split (A : PositiveIncreasingSequence) (x t : ℕ) :
    A.count x ≤ t + x / (t + 1) := by
  let G := A.goodEdges x
  have hsmall : (G.filter fun i => A i ≤ t).card ≤ t := by
    calc
      _ ≤ (Finset.Icc 1 t).card := by
        apply Finset.card_le_card_of_injOn A.term
        · intro i hi
          exact Finset.mem_Icc.mpr ⟨A.positive i, (Finset.mem_filter.mp hi).2⟩
        · intro i _ j _ hij
          exact A.strictlyIncreasing.injective hij
      _ = t := by simp
  have hlarge : (G.filter fun i => ¬ A i ≤ t).card ≤ x / (t + 1) := by
    calc
      _ ≤ (Finset.Icc 1 (x / (t + 1))).card := by
        apply Finset.card_le_card_of_injOn (fun i => x / A i)
        · intro i hi
          obtain ⟨hiGood, hiLarge⟩ := Finset.mem_filter.mp hi
          have hAi : A i ≤ x := by
            have hdiv : A i ∣ A.edgeLcm i := Nat.dvd_lcm_left _ _
            exact (Nat.le_of_dvd (Nat.lcm_pos (A.positive i) (A.positive (i + 1))) hdiv).trans
              (mem_goodEdges_iff.mp hiGood)
          exact Finset.mem_Icc.mpr ⟨Nat.div_pos hAi (A.positive i),
            Nat.div_le_div_left (by omega) (by omega)⟩
        · intro i hi j hj hij
          exact A.quotient_injective_on_good x
            (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
      _ = x / (t + 1) := by simp
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := G) (fun i => A i ≤ t)
  change G.card ≤ _
  change (G.filter fun i => A i ≤ t).card +
      (G.filter fun i => ¬ A i ≤ t).card = G.card at hpartition
  omega

/-- An explicit global bound implying the requested `O(sqrt x)` estimate. -/
theorem count_le_two_sqrt (A : PositiveIncreasingSequence) (x : ℕ) :
    A.count x ≤ 2 * Nat.sqrt x := by
  have hsplit := A.count_le_split x (Nat.sqrt x)
  have hdivision : x / (Nat.sqrt x + 1) < Nat.sqrt x + 1 :=
    (Nat.div_lt_iff_lt_mul (by omega)).2 (Nat.lt_succ_sqrt x)
  omega

/-- Literal asymptotic form of the first question in Erdős problem 440. -/
theorem count_isBigO_sqrt (A : PositiveIncreasingSequence) :
    (fun x : ℕ => (A.count x : ℝ)) =O[Filter.atTop]
      (fun x : ℕ => Real.sqrt x) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards with x
  have hcount : (A.count x : ℝ) ≤ 2 * Nat.sqrt x := by
    exact_mod_cast A.count_le_two_sqrt x
  have hsqrt : (Nat.sqrt x : ℝ) ≤ Real.sqrt x := Real.nat_sqrt_le_real_sqrt
  have hcountNonnegative : (0 : ℝ) ≤ (A.count x : ℝ) := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hcountNonnegative,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  linarith

end PositiveIncreasingSequence

end JustinSunPrize.JSP000359
