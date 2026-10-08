import FCAppendix.Game.UniformRoutes

namespace FCAppendix
namespace ExactCapacity

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def fractional (p : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => 0 < p i ∧ p i < 1)

noncomputable def shift (p : ι → ℝ) (i j : ι) (t : ℝ) : ι → ℝ := by
  classical
  exact fun a => p a + (if a = i then t else 0) - (if a = j then t else 0)

omit [Fintype ι] in
theorem shift_apply_left (p : ι → ℝ) (i j : ι) (t : ℝ) (hij : i ≠ j) :
    shift p i j t i = p i + t := by
  unfold shift
  rw [if_pos rfl, if_neg hij]
  ring

omit [Fintype ι] in
theorem shift_apply_right (p : ι → ℝ) (i j : ι) (t : ℝ) (hij : i ≠ j) :
    shift p i j t j = p j - t := by
  unfold shift
  rw [if_neg (Ne.symm hij), if_pos rfl]
  ring

omit [Fintype ι] in
theorem shift_apply_other (p : ι → ℝ) (i j : ι) (t : ℝ) (a : ι)
    (hai : a ≠ i) (haj : a ≠ j) : shift p i j t a = p a := by
  unfold shift
  rw [if_neg hai, if_neg haj]
  ring

theorem sum_shift (p : ι → ℝ) (i j : ι) (t : ℝ) :
    (∑ a, shift p i j t a) = ∑ a, p a := by
  classical
  simp only [shift, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

omit [Fintype ι] in
theorem shift_box (p : ι → ℝ) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1)
    (i j : ι) (hij : i ≠ j) (t : ℝ)
    (hti : -p i ≤ t) (htI : t ≤ 1 - p i)
    (htj : p j - 1 ≤ t) (htJ : t ≤ p j) :
    (∀ a, 0 ≤ shift p i j t a) ∧ (∀ a, shift p i j t a ≤ 1) := by
  classical
  have hji : j ≠ i := Ne.symm hij
  constructor <;> intro a <;> by_cases hai : a = i
  · rw [hai, shift_apply_left p i j t hij]
    linarith
  · by_cases haj : a = j
    · rw [haj, shift_apply_right p i j t hij]
      linarith
    · rw [shift_apply_other p i j t a hai haj]
      exact hp0 a
  · rw [hai, shift_apply_left p i j t hij]
    linarith
  · by_cases haj : a = j
    · rw [haj, shift_apply_right p i j t hij]
      linarith
    · rw [shift_apply_other p i j t a hai haj]
      exact hp1 a

theorem fractional_shift_subset (p : ι → ℝ) (i j : ι) (t : ℝ)
    (hi : 0 < p i ∧ p i < 1) (hj : 0 < p j ∧ p j < 1) :
    fractional (shift p i j t) ⊆ fractional p := by
  classical
  intro a ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_cases hai : a = i
  · simpa [hai] using hi
  by_cases haj : a = j
  · simpa [haj] using hj
  have h := (Finset.mem_filter.mp ha).2
  simpa [shift, hai, haj] using h

theorem another_fractional (p : ι → ℝ) (c : ℕ)
    (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1) (hsum : ∑ a, p a = c)
    (i : ι) (hi : 0 < p i ∧ p i < 1) :
    ∃ j, j ≠ i ∧ 0 < p j ∧ p j < 1 := by
  classical
  by_contra hnone
  have endpoints : ∀ j, j ≠ i → p j = 0 ∨ p j = 1 := by
    intro j hji
    by_cases hz : p j = 0
    · exact Or.inl hz
    · right
      have hpos : 0 < p j := lt_of_le_of_ne (hp0 j) (Ne.symm hz)
      have hnot : ¬ p j < 1 := fun hlt => hnone ⟨j, hji, hpos, hlt⟩
      exact le_antisymm (hp1 j) (le_of_not_gt hnot)
  let T : Finset ι := Finset.univ.filter (fun j => j ≠ i ∧ p j = 1)
  have he : ∀ j, p j = (if j = i then p i else 0) + (if j ∈ T then 1 else 0) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [T]
    · rcases endpoints j hji with hz | ho
      · simp [T, hji, hz]
      · simp [T, hji, ho]
  have hs : (∑ j, p j) = p i + (T.card : ℝ) := by
    calc
      _ = ∑ j, ((if j = i then p i else 0) + (if j ∈ T then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact he j
      _ = _ := by rw [Finset.sum_add_distrib, Game.sum_membership_real]; simp
  have hlo : (T.card : ℝ) < (c : ℝ) := by linarith [hi.1]
  have hhi : (c : ℝ) < ((T.card + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [hi.2]
  have hloN : T.card < c := by exact_mod_cast hlo
  have hhiN : c < T.card + 1 := by exact_mod_cast hhi
  omega

theorem fractional_card_drop (p : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (hi : 0 < p i ∧ p i < 1) (hj : 0 < p j ∧ p j < 1) :
    (fractional (shift p i j (min (1 - p i) (p j)))).card < (fractional p).card ∧
    (fractional (shift p i j (-(min (p i) (1 - p j))))).card < (fractional p).card := by
  classical
  have hji : j ≠ i := Ne.symm hij
  have oldi : i ∈ fractional p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  have oldj : j ∈ fractional p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  constructor
  · have hs := fractional_shift_subset p i j (min (1 - p i) (p j)) hi hj
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hs, ?_⟩
    intro heq
    by_cases h : 1 - p i ≤ p j
    · have hmem : i ∈ fractional (shift p i j (min (1 - p i) (p j))) := by
        rw [heq]
        exact oldi
      have hx := (Finset.mem_filter.mp hmem).2.2
      simp [shift, hij, min_eq_left h] at hx
    · have hmem : j ∈ fractional (shift p i j (min (1 - p i) (p j))) := by
        rw [heq]
        exact oldj
      have hx := (Finset.mem_filter.mp hmem).2.1
      simp [shift, hji, min_eq_right (le_of_not_ge h)] at hx
  · have hs := fractional_shift_subset p i j (-(min (p i) (1 - p j))) hi hj
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hs, ?_⟩
    intro heq
    by_cases h : p i ≤ 1 - p j
    · have hmem : i ∈ fractional (shift p i j (-(min (p i) (1 - p j)))) := by
        rw [heq]
        exact oldi
      have hx := (Finset.mem_filter.mp hmem).2.1
      simp [shift, hij, min_eq_left h] at hx
    · have hmem : j ∈ fractional (shift p i j (-(min (p i) (1 - p j)))) := by
        rw [heq]
        exact oldj
      have hx := (Finset.mem_filter.mp hmem).2.2
      simp [shift, hji, min_eq_right (le_of_not_ge h)] at hx

omit [Fintype ι] in
theorem shift_mixture (p : ι → ℝ) (i j : ι) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (a : ι) :
    (y / (x + y)) * shift p i j x a +
      (1 - y / (x + y)) * shift p i j (-y) a = p a := by
  classical
  have hxy : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  unfold shift
  split_ifs <;> field_simp [hxy] <;> ring

theorem exists_lottery (p : ι → ℝ) (c : ℕ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = c) :
    ∃ μ : FiniteLaw (Finset ι),
      (∀ S, μ.mass S ≠ 0 → S.card = c) ∧
      (∀ i, μ.prob (fun S => i ∈ S) = p i) := by
  classical
  have main : ∀ d : ℕ, ∀ q : ι → ℝ, (fractional q).card = d →
      (∀ i, 0 ≤ q i) → (∀ i, q i ≤ 1) → (∑ i, q i = c) →
      ∃ μ : FiniteLaw (Finset ι),
        (∀ S, μ.mass S ≠ 0 → S.card = c) ∧
        (∀ i, μ.prob (fun S => i ∈ S) = q i) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro q hd hq0 hq1 hqsum
      by_cases hf : fractional q = ∅
      · have endpoints : ∀ i, q i = 0 ∨ q i = 1 := by
          intro i
          have hnot : ¬ (0 < q i ∧ q i < 1) := by
            intro hi
            have hm : i ∈ fractional q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
            rw [hf] at hm
            exact Finset.notMem_empty i hm
          by_cases hz : q i = 0
          · exact Or.inl hz
          · right
            have hpos : 0 < q i := lt_of_le_of_ne (hq0 i) (Ne.symm hz)
            have hn : ¬ q i < 1 := fun hlt => hnot ⟨hpos, hlt⟩
            exact le_antisymm (hq1 i) (le_of_not_gt hn)
        let S : Finset ι := Finset.univ.filter (fun i => q i = 1)
        have hmarg : ∀ i, (if i ∈ S then (1 : ℝ) else 0) = q i := by
          intro i
          rcases endpoints i with hz | ho
          · simp [S, hz]
          · simp [S, ho]
        have hcard : S.card = c := by
          have he : (S.card : ℝ) = (c : ℝ) := by
            rw [← Game.sum_membership_real]
            simp_rw [hmarg]
            exact hqsum
          exact_mod_cast he
        refine ⟨FiniteLaw.dirac S, ?_, ?_⟩
        · intro T hT
          have ht : T = S := by
            by_contra hne
            exact hT (by simp [FiniteLaw.dirac, hne])
          simpa [ht] using hcard
        · intro i
          rw [FiniteLaw.prob_eq_expect, FiniteLaw.expect_dirac]
          exact hmarg i
      · obtain ⟨i, hiF⟩ := Finset.nonempty_iff_ne_empty.mpr hf
        have hi := (Finset.mem_filter.mp hiF).2
        obtain ⟨j, hji, hj0, hj1⟩ := another_fractional q c hq0 hq1 hqsum i hi
        have hij : i ≠ j := Ne.symm hji
        have hj : 0 < q j ∧ q j < 1 := ⟨hj0, hj1⟩
        let x : ℝ := min (1 - q i) (q j)
        let y : ℝ := min (q i) (1 - q j)
        have hx : 0 < x := lt_min (sub_pos.mpr hi.2) hj.1
        have hy : 0 < y := lt_min hi.1 (sub_pos.mpr hj.2)
        have hxI : x ≤ 1 - q i := min_le_left _ _
        have hxJ : x ≤ q j := min_le_right _ _
        have hyI : y ≤ q i := min_le_left _ _
        have hyJ : y ≤ 1 - q j := min_le_right _ _
        have hplus := shift_box q hq0 hq1 i j hij x
          (by linarith [hq0 i]) hxI (by linarith [hq1 j]) hxJ
        have hminus := shift_box q hq0 hq1 i j hij (-y)
          (by linarith) (by linarith [hq1 i]) (by linarith) (by linarith [hq0 j])
        have hdrop := fractional_card_drop q i j hij hi hj
        have hdplus : (fractional (shift q i j x)).card < d := by
          simpa only [x, hd] using hdrop.1
        have hdminus : (fractional (shift q i j (-y))).card < d := by
          simpa only [y, hd] using hdrop.2
        obtain ⟨μ, hμcap, hμmarg⟩ := ih _ hdplus (shift q i j x) rfl
          hplus.1 hplus.2 (by rw [sum_shift]; exact hqsum)
        obtain ⟨ν, hνcap, hνmarg⟩ := ih _ hdminus (shift q i j (-y)) rfl
          hminus.1 hminus.2 (by rw [sum_shift]; exact hqsum)
        let t : ℝ := y / (x + y)
        have ht0 : 0 ≤ t := le_of_lt (div_pos hy (add_pos hx hy))
        have ht1 : t ≤ 1 := (div_le_one (add_pos hx hy)).mpr (by linarith)
        refine ⟨FiniteLaw.mixture μ ν t ht0 ht1, ?_, ?_⟩
        · intro S hS
          by_cases hm : μ.mass S = 0
          · have hn : ν.mass S ≠ 0 := by
              intro hn
              exact hS (by simp [FiniteLaw.mixture, hm, hn])
            exact hνcap S hn
          · exact hμcap S hm
        · intro i'
          rw [FiniteLaw.prob_eq_expect, FiniteLaw.expect_mixture,
            ← FiniteLaw.prob_eq_expect, ← FiniteLaw.prob_eq_expect, hμmarg, hνmarg]
          exact shift_mixture q i j x y hx hy i'
  exact main _ p rfl hp0 hp1 hsum

end ExactCapacity
end FCAppendix
