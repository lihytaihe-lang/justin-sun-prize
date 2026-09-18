import JustinSunPrize.JSP000359.Counting

/-!
# JSP-000359 / Erdős problem 440: the sharp normalized lower limit

For the counting function defined in `Counting.lean`, every increasing positive
integer sequence has normalized liminf at most one.  Consecutive positive
integers attain one, so one is the greatest attainable value.

The mathematics is due to Erdős and Szemerédi (1980).  This source is an
AI-assisted Lean reimplementation and makes no claim of mathematical novelty
or first-formalization priority.
-/

set_option autoImplicit false

namespace JustinSunPrize.JSP000359

open Finset Filter
open scoped Topology

namespace PositiveIncreasingSequence

/-- The reciprocal LCM is bounded by the drop between reciprocal endpoints. -/
lemma reciprocal_edgeLcm_le_drop (A : PositiveIncreasingSequence) (i : ℕ) :
    (1 : ℝ) / A.edgeLcm i ≤ 1 / (A i : ℝ) - 1 / (A (i + 1) : ℝ) := by
  have hAi : (0 : ℝ) < A i := by exact_mod_cast A.positive i
  have hAj : (0 : ℝ) < A (i + 1) := by exact_mod_cast A.positive (i + 1)
  have hLcm : (0 : ℝ) < A.edgeLcm i := by
    exact_mod_cast Nat.lcm_pos (A.positive i) (A.positive (i + 1))
  have hgap :
      (Nat.gcd (A i) (A (i + 1)) : ℝ) ≤ (A (i + 1) : ℝ) - A i := by
    have hnat := A.gcd_le_positive_gap i
    rw [← Nat.cast_sub (A.strictlyIncreasing (Nat.lt_succ_self i)).le]
    exact_mod_cast hnat
  calc
    (1 : ℝ) / A.edgeLcm i =
        (Nat.gcd (A i) (A (i + 1)) : ℝ) / ((A i : ℝ) * A (i + 1)) := by
      field_simp
      unfold edgeLcm
      exact_mod_cast (by
        calc
          A i * A (i + 1) = Nat.gcd (A i) (A (i + 1)) * Nat.lcm (A i) (A (i + 1)) :=
            (Nat.gcd_mul_lcm _ _).symm
          _ = Nat.lcm (A i) (A (i + 1)) * Nat.gcd (A i) (A (i + 1)) :=
            Nat.mul_comm _ _)
    _ ≤ ((A (i + 1) : ℝ) - A i) / ((A i : ℝ) * A (i + 1)) := by
      exact div_le_div_of_nonneg_right hgap (mul_nonneg hAi.le hAj.le)
    _ = 1 / (A i : ℝ) - 1 / (A (i + 1) : ℝ) := by field_simp

lemma reciprocal_sum_on_interval (A : PositiveIncreasingSequence) {n m : ℕ}
    (hnm : n ≤ m) :
    (∑ i ∈ Ico n m, (1 : ℝ) / A.edgeLcm i) ≤
      1 / (A n : ℝ) - 1 / (A m : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Ico n m, (1 / (A i : ℝ) - 1 / (A (i + 1) : ℝ)) := by
      exact sum_le_sum fun i _ => A.reciprocal_edgeLcm_le_drop i
    _ = _ := by
      have htel := sum_Ico_sub (fun i => (1 : ℝ) / A i) hnm
      simp only [sum_sub_distrib] at htel ⊢
      linarith

/-- Any finite collection of edges with index at least `n` has total reciprocal
LCM mass at most `1/(n+1)`. -/
lemma reciprocal_mass_of_tail (A : PositiveIncreasingSequence) (s : Finset ℕ) (n : ℕ)
    (hs : ∀ i ∈ s, n ≤ i) :
    (∑ i ∈ s, (1 : ℝ) / A.edgeLcm i) ≤ 1 / ((n : ℝ) + 1) := by
  let m := max n (s.sup id + 1)
  have hnm : n ≤ m := le_max_left _ _
  have hsubset : s ⊆ Ico n m := by
    intro i hi
    have hisup : i ≤ s.sup id := le_sup (f := id) hi
    exact mem_Ico.mpr ⟨hs i hi, lt_of_le_of_lt hisup (by omega)⟩
  have hindex : n + 1 ≤ A n := by
    simpa using A.index_succ_le_term n
  calc
    _ ≤ ∑ i ∈ Ico n m, (1 : ℝ) / A.edgeLcm i :=
      sum_le_sum_of_subset_of_nonneg hsubset (by intros; positivity)
    _ ≤ 1 / (A n : ℝ) - 1 / (A m : ℝ) := A.reciprocal_sum_on_interval hnm
    _ ≤ 1 / (A n : ℝ) := sub_le_self _ (by positivity)
    _ ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast hindex

/-- Under an eventually-too-large counting hypothesis, greedily choose many
distinct tail edges with controlled LCMs. -/
lemma choose_many_tail_edges (A : PositiveIncreasingSequence) (n : ℕ)
    (hlarge : ∀ k ≥ n, k < A.count (k ^ 2)) (m : ℕ) :
    ∃ s : Finset ℕ, s.card = m ∧ (∀ i ∈ s, n ≤ i) ∧
      (∑ j ∈ range m, (1 : ℝ) / ((n + j : ℕ) : ℝ) ^ 2) ≤
        ∑ i ∈ s, (1 : ℝ) / A.edgeLcm i := by
  induction m with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨s, hcard, htail, hweight⟩ := ih
    have hused : (range n ∪ s).card ≤ n + m := by
      calc
        _ ≤ (range n).card + s.card := card_union_le _ _
        _ = n + m := by simp [hcard]
    have hcount : n + m < (A.goodEdges ((n + m) ^ 2)).card := by
      simpa [count] using hlarge (n + m) (by omega)
    obtain ⟨i, hiGood, hiFresh⟩ := exists_mem_not_mem_of_card_lt_card
      (lt_of_le_of_lt hused hcount)
    have hiNotS : i ∉ s := fun hi => hiFresh (mem_union.mpr (Or.inr hi))
    have hiTail : n ≤ i := by
      have hiNotRange : i ∉ range n := fun hi => hiFresh (mem_union.mpr (Or.inl hi))
      simpa using hiNotRange
    have hiLcm : A.edgeLcm i ≤ (n + m) ^ 2 := mem_goodEdges_iff.mp hiGood
    have hiLcmReal : (A.edgeLcm i : ℝ) ≤ ((n + m : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hiLcm
    have hiLcmPos : (0 : ℝ) < A.edgeLcm i := by
      exact_mod_cast Nat.lcm_pos (A.positive i) (A.positive (i + 1))
    have hiReciprocal := one_div_le_one_div_of_le hiLcmPos hiLcmReal
    refine ⟨insert i s, by simp [hiNotS, hcard], ?_, ?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact hiTail
      · exact htail j hj
    · rw [sum_insert hiNotS, sum_range_succ]
      linarith

lemma reciprocal_drop_le_inverse_square (t : ℝ) (ht : 0 < t) :
    1 / t - 1 / (t + 1) ≤ 1 / t ^ 2 := by
  have ht1 : 0 < t + 1 := by linarith
  calc
    _ = 1 / (t * (t + 1)) := by field_simp [ne_of_gt ht, ne_of_gt ht1]
    _ ≤ 1 / t ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos ht) (by nlinarith)

lemma reciprocal_square_sum_lower (n m : ℕ) (hn : 0 < n) :
    (1 : ℝ) / n - 1 / ((n + m : ℕ) : ℝ) ≤
      ∑ j ∈ range m, (1 : ℝ) / ((n + j : ℕ) : ℝ) ^ 2 := by
  calc
    _ = ∑ j ∈ range m, ((1 : ℝ) / (n + j : ℕ) - 1 / (n + (j + 1) : ℕ)) := by
      have htel := sum_range_sub (fun j => (1 : ℝ) / (n + j : ℕ)) m
      simp only [Nat.add_zero, sum_sub_distrib] at htel ⊢
      linarith
    _ ≤ _ := by
      apply sum_le_sum
      intro j _
      have hpos : (0 : ℝ) < (n + j : ℕ) := by
        exact_mod_cast (show 0 < n + j by omega)
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
        reciprocal_drop_le_inverse_square _ hpos

/-- Arbitrarily large square thresholds have count at most their square root. -/
theorem exists_large_square_with_small_count (A : PositiveIncreasingSequence) (N : ℕ) :
    ∃ k ≥ N, A.count (k ^ 2) ≤ k := by
  by_contra hcontra
  push_neg at hcontra
  let n := max N 1
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < 1) (le_max_right _ _)
  have hlarge : ∀ k ≥ n, k < A.count (k ^ 2) := by
    intro k hk
    exact hcontra k ((le_max_left _ _).trans hk)
  obtain ⟨s, _, htail, hsum⟩ :=
    A.choose_many_tail_edges n hlarge (n * n + 1)
  have hupper := A.reciprocal_mass_of_tail s n htail
  have hlower := reciprocal_square_sum_lower n (n * n + 1) hn
  have hcombined := hlower.trans (hsum.trans hupper)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hcombined
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnPlus : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hgap : (1 : ℝ) / n - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * (n + 1)) := by
    field_simp [ne_of_gt hnReal, ne_of_gt hnPlus]
  have hstrict :
      (1 : ℝ) / ((n : ℝ) + (n * n + 1)) < 1 / ((n : ℝ) * (n + 1)) :=
    one_div_lt_one_div_of_lt (mul_pos hnReal hnPlus) (by nlinarith)
  linarith

end PositiveIncreasingSequence

/-- The positive integers in their natural order. -/
def naturalsSequence : PositiveIncreasingSequence where
  term i := i + 1
  positive i := Nat.succ_pos i
  strictlyIncreasing := fun _ _ h => Nat.add_lt_add_right h 1

namespace naturalsSequence

lemma edgeLcm_eq (i : ℕ) :
    naturalsSequence.edgeLcm i = (i + 1) * (i + 2) := by
  have hcoprime : Nat.Coprime (i + 1) ((i + 1) + 1) := by simp
  simpa [naturalsSequence, PositiveIncreasingSequence.edgeLcm, Nat.add_assoc] using
    hcoprime.lcm_eq_mul

lemma count_between_sqrts (x : ℕ) :
    Nat.sqrt x - 1 ≤ naturalsSequence.count x ∧
      naturalsSequence.count x ≤ Nat.sqrt x := by
  constructor
  · calc
      _ = (range (Nat.sqrt x - 1)).card := by simp
      _ ≤ _ := card_le_card (by
        intro i hi
        have hiRange := mem_range.mp hi
        apply PositiveIncreasingSequence.mem_goodEdges_iff.mpr
        rw [edgeLcm_eq]
        have hsquare := Nat.sqrt_le' x
        have hibound : i + 2 ≤ Nat.sqrt x := by omega
        nlinarith)
  · calc
      _ ≤ (range (Nat.sqrt x)).card := card_le_card (by
        intro i hi
        have hiLcm := PositiveIncreasingSequence.mem_goodEdges_iff.mp hi
        rw [edgeLcm_eq] at hiLcm
        apply mem_range.mpr
        have hsquare := Nat.lt_succ_sqrt' x
        nlinarith)
      _ = _ := by simp

end naturalsSequence

/-- Real-threshold count, obtained by flooring a nonnegative threshold. -/
noncomputable def realCount (A : PositiveIncreasingSequence) (x : ℝ) : ℕ :=
  A.count ⌊x⌋₊

/-- Normalized counting function used in the original liminf question. -/
noncomputable def normalizedCount (A : PositiveIncreasingSequence) (x : ℝ) : ℝ :=
  realCount A x / Real.sqrt x

lemma mem_realCount_iff (A : PositiveIncreasingSequence) (i : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    i ∈ A.goodEdges ⌊x⌋₊ ↔ (A.edgeLcm i : ℝ) ≤ x := by
  rw [PositiveIncreasingSequence.mem_goodEdges_iff, Nat.le_floor_iff hx]

lemma realCount_le_two_sqrt (A : PositiveIncreasingSequence) (x : ℝ) (hx : 0 ≤ x) :
    (realCount A x : ℝ) ≤ 2 * Real.sqrt x := by
  have hnat : (realCount A x : ℝ) ≤ 2 * (Nat.sqrt ⌊x⌋₊ : ℝ) := by
    exact_mod_cast A.count_le_two_sqrt ⌊x⌋₊
  have hsqrt : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ Real.sqrt x :=
    Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (Nat.floor_le hx))
  linarith

/-- Universal upper bound for the normalized liminf. -/
theorem normalized_liminf_le_one (A : PositiveIncreasingSequence) :
    Filter.liminf (normalizedCount A) atTop ≤ 1 := by
  have hfrequent : ∃ᶠ x : ℝ in atTop, normalizedCount A x ≤ 1 := by
    apply frequently_atTop.mpr
    intro lower
    obtain ⟨n, hn⟩ := exists_nat_gt lower
    obtain ⟨k, hkN, hkCount⟩ := A.exists_large_square_with_small_count (max n 1)
    have hkPositive : 0 < k := by omega
    have hkn : n ≤ k := (le_max_left _ _).trans hkN
    refine ⟨((k ^ 2 : ℕ) : ℝ), ?_, ?_⟩
    · have hnr : (n : ℝ) ≤ k := by exact_mod_cast hkn
      push_cast
      nlinarith
    · unfold normalizedCount realCount
      rw [Nat.floor_natCast, Nat.cast_pow, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ k)]
      apply (div_le_iff₀ (by exact_mod_cast hkPositive : (0 : ℝ) < k)).2
      exact_mod_cast hkCount
  refine liminf_le_of_frequently_le hfrequent ?_
  refine ⟨0, ?_⟩
  exact Filter.Eventually.of_forall fun x => by
    unfold normalizedCount
    positivity

lemma naturals_realCount_bounds (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt x - 2 ≤ (realCount naturalsSequence x : ℝ) ∧
      (realCount naturalsSequence x : ℝ) ≤ Real.sqrt x := by
  obtain ⟨hlowNat, hhighNat⟩ := naturalsSequence.count_between_sqrts ⌊x⌋₊
  have hfloorSqrt : Nat.sqrt ⌊x⌋₊ ≤ realCount naturalsSequence x + 1 := by
    unfold realCount
    omega
  have hfloorSqrtReal :
      (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ (realCount naturalsSequence x : ℝ) + 1 := by
    exact_mod_cast hfloorSqrt
  have hnextSquare : x < ((Nat.sqrt ⌊x⌋₊ : ℝ) + 1) ^ 2 := by
    have hfloor := (Nat.floor_lt hx).mp (Nat.lt_succ_sqrt' ⌊x⌋₊)
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] using hfloor
  have hsqrtUpper : Real.sqrt x < (Nat.sqrt ⌊x⌋₊ : ℝ) + 1 :=
    (Real.sqrt_lt hx (by positivity)).mpr hnextSquare
  constructor
  · linarith
  · have hcast : (realCount naturalsSequence x : ℝ) ≤ (Nat.sqrt ⌊x⌋₊ : ℝ) := by
      exact_mod_cast hhighNat
    exact hcast.trans
      (Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (Nat.floor_le hx)))

lemma naturals_normalized_bounds (x : ℝ) (hx : 0 < x) :
    1 - 2 / Real.sqrt x ≤ normalizedCount naturalsSequence x ∧
      normalizedCount naturalsSequence x ≤ 1 := by
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  obtain ⟨hlow, hhigh⟩ := naturals_realCount_bounds x hx.le
  unfold normalizedCount
  constructor
  · apply (le_div_iff₀ hsqrt).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hsqrt)]
    exact hlow
  · exact (div_le_one hsqrt).mpr hhigh

lemma real_sqrt_tendsto_atTop : Tendsto Real.sqrt atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨(max b 0) ^ 2, ?_⟩
  intro x hx
  have hxNonnegative : 0 ≤ x := (sq_nonneg _).trans hx
  exact (le_max_left _ _).trans
    ((Real.le_sqrt (le_max_right _ _) hxNonnegative).mpr hx)

theorem naturals_normalized_tendsto_one :
    Tendsto (normalizedCount naturalsSequence) atTop (𝓝 1) := by
  have hvanish : Tendsto (fun x : ℝ => 2 / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp real_sqrt_tendsto_atTop))
  have hlower : Tendsto (fun x : ℝ => 1 - 2 / Real.sqrt x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hvanish
  have hbounds : ∀ᶠ x : ℝ in atTop,
      1 - 2 / Real.sqrt x ≤ normalizedCount naturalsSequence x ∧
        normalizedCount naturalsSequence x ≤ 1 :=
    (eventually_gt_atTop (0 : ℝ)).mono fun x hx => naturals_normalized_bounds x hx
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

/-- The greatest attainable normalized liminf is exactly one. -/
theorem sharp_liminf :
    IsGreatest {c : ℝ | ∃ A : PositiveIncreasingSequence,
      Filter.liminf (normalizedCount A) atTop = c} 1 := by
  constructor
  · exact ⟨naturalsSequence, naturals_normalized_tendsto_one.liminf_eq⟩
  · intro c hc
    obtain ⟨A, rfl⟩ := hc
    exact normalized_liminf_le_one A

/-- Both displayed questions in the original problem: an explicit square-root
bound for every real threshold, and the sharp greatest attainable liminf. -/
theorem original_problem :
    (∀ (A : PositiveIncreasingSequence) (x : ℝ), 0 ≤ x →
      (realCount A x : ℝ) ≤ 2 * Real.sqrt x) ∧
    IsGreatest {c : ℝ | ∃ A : PositiveIncreasingSequence,
      Filter.liminf (normalizedCount A) atTop = c} 1 := by
  exact ⟨realCount_le_two_sqrt, sharp_liminf⟩

#print axioms PositiveIncreasingSequence.count_isBigO_sqrt
#print axioms mem_realCount_iff
#print axioms sharp_liminf
#print axioms original_problem

end JustinSunPrize.JSP000359
