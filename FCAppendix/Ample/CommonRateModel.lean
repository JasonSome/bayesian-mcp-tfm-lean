import FCAppendix.Ample.RateSystem

namespace FCAppendix
namespace Ample

open Finset
open scoped BigOperators

structure ValidLaw (n : ℕ) (lam : ℕ → ℝ) : Prop where
  nonneg : ∀ j ∈ Icc 1 n, 0 ≤ lam j
  total_le : ∑ j ∈ Icc 1 n, lam j ≤ 1

noncomputable def contactWeight (n : ℕ) (lam : ℕ → ℝ) (T : Finset (Fin n)) : ℝ :=
  if T = ∅ then 1 - ∑ j ∈ Icc 1 n, lam j else lam T.card / (n.choose T.card : ℝ)

def contacts {N n : ℕ} (x : Fin N → Finset (Fin n)) (j : Fin n) : ℕ :=
  (univ.filter fun l => j ∈ x l).card

def selected (n k : ℕ) : Finset (Fin n) := univ.filter fun j => j.val < k

noncomputable def congestProbAt (n N c : ℕ) (lam : ℕ → ℝ) (S : Finset (Fin n)) : ℝ := by
  classical
  exact ∑ x : Fin N → Finset (Fin n), (∏ l, contactWeight n lam (x l)) *
    (if ∀ j ∈ S, c ≤ contacts x j then 1 else 0)

noncomputable def congestProb (n N c k : ℕ) (lam : ℕ → ℝ) : ℝ :=
  congestProbAt n N c lam (selected n k)

theorem card_selected {n k : ℕ} (hk : k ≤ n) : (selected n k).card = k := by
  classical
  have : selected n k = (Finset.range k).attachFin (fun r hr => by
      have := Finset.mem_range.mp hr
      omega) := by
    ext r
    simp [selected]
  rw [this, Finset.card_attachFin, Finset.card_range]

theorem selected_mono {n k k' : ℕ} (h : k ≤ k') : selected n k ⊆ selected n k' := by
  intro j hj
  simp only [selected, mem_filter, mem_univ, true_and] at hj ⊢
  omega

theorem selected_self (n : ℕ) : selected n n = univ := by
  ext j
  simp [selected]

theorem contactWeight_empty (n : ℕ) (lam : ℕ → ℝ) :
    contactWeight n lam ∅ = 1 - ∑ j ∈ Icc 1 n, lam j := by
  simp [contactWeight]

theorem contactWeight_of_ne {n : ℕ} (lam : ℕ → ℝ) {T : Finset (Fin n)} (hT : T ≠ ∅) :
    contactWeight n lam T = lam T.card / (n.choose T.card : ℝ) := by
  simp [contactWeight, hT]

theorem card_mem_Icc_of_ne {n : ℕ} {T : Finset (Fin n)} (hT : T ≠ ∅) : T.card ∈ Icc 1 n := by
  have h1 : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
  have h2 : T.card ≤ n := by simpa using Finset.card_le_univ T
  exact mem_Icc.mpr ⟨h1, h2⟩

theorem contactWeight_nonneg {n : ℕ} {lam : ℕ → ℝ} (hlam : ValidLaw n lam)
    (T : Finset (Fin n)) : 0 ≤ contactWeight n lam T := by
  by_cases hT : T = ∅
  · rw [hT, contactWeight_empty]
    linarith [hlam.total_le]
  · rw [contactWeight_of_ne lam hT]
    exact div_nonneg (hlam.nonneg _ (card_mem_Icc_of_ne hT)) (Nat.cast_nonneg _)

theorem sum_finset_card_eq (n : ℕ) (g : ℕ → ℝ) :
    ∑ T : Finset (Fin n), g T.card = ∑ m ∈ range (n + 1), (n.choose m : ℝ) * g m := by
  have h := Finset.sum_powerset_apply_card (f := g) (x := (univ : Finset (Fin n)))
  rw [Finset.powerset_univ] at h
  simpa [nsmul_eq_mul] using h

theorem sum_contactWeight (n : ℕ) (lam : ℕ → ℝ) :
    ∑ T : Finset (Fin n), contactWeight n lam T = 1 := by
  let g : ℕ → ℝ := fun m => if m = 0 then 1 - ∑ j ∈ Icc 1 n, lam j
    else lam m / (n.choose m : ℝ)
  have hg : ∀ T : Finset (Fin n), contactWeight n lam T = g T.card := by
    intro T
    by_cases hT : T = ∅
    · simp [hT, contactWeight, g]
    · have hc : T.card ≠ 0 := by
        simpa [Finset.card_eq_zero] using hT
      simp [contactWeight, hT, g, hc]
  rw [Finset.sum_congr rfl (fun T _ => hg T), sum_finset_card_eq, Finset.sum_range_succ']
  have hrest : ∑ m ∈ range n, (n.choose (m + 1) : ℝ) * g (m + 1) =
      ∑ j ∈ Icc 1 n, lam j := by
    rw [sum_Icc_one_eq_sum_range (fun j => lam j) n]
    apply Finset.sum_congr rfl
    intro m hm
    have hmn : m + 1 ≤ n := by simpa using Finset.mem_range.mp hm
    have hC : (n.choose (m + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hmn).ne'
    simp only [g, Nat.succ_ne_zero, if_false]
    field_simp
  rw [hrest]
  simp [g]

theorem sum_prod_eq_pow {N : ℕ} {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) :
    ∑ x : Fin N → α, ∏ l, f (x l) = (∑ a, f a) ^ N := by
  have h := Fintype.prod_sum (fun (_ : Fin N) (a : α) => f a)
  rw [← h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem congestProbAt_nonneg {n N c : ℕ} {lam : ℕ → ℝ} (hlam : ValidLaw n lam)
    (S : Finset (Fin n)) : 0 ≤ congestProbAt n N c lam S := by
  classical
  unfold congestProbAt
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (Finset.prod_nonneg fun l _ => contactWeight_nonneg hlam _)
  split_ifs <;> norm_num

theorem congestProbAt_le_one {n N c : ℕ} {lam : ℕ → ℝ} (hlam : ValidLaw n lam)
    (S : Finset (Fin n)) : congestProbAt n N c lam S ≤ 1 := by
  classical
  unfold congestProbAt
  calc _ ≤ ∑ x : Fin N → Finset (Fin n), ∏ l, contactWeight n lam (x l) := by
        apply Finset.sum_le_sum
        intro x _
        have hp : 0 ≤ ∏ l, contactWeight n lam (x l) :=
          Finset.prod_nonneg fun l _ => contactWeight_nonneg hlam _
        split_ifs
        · rw [mul_one]
        · rw [mul_zero]; exact hp
    _ = 1 := by rw [sum_prod_eq_pow, sum_contactWeight, one_pow]

theorem congestProbAt_anti {n N c : ℕ} {lam : ℕ → ℝ} (hlam : ValidLaw n lam)
    {S S' : Finset (Fin n)} (hSS : S ⊆ S') :
    congestProbAt n N c lam S' ≤ congestProbAt n N c lam S := by
  classical
  unfold congestProbAt
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun l _ => contactWeight_nonneg hlam _)
  by_cases h' : ∀ j ∈ S', c ≤ contacts x j
  · rw [if_pos h', if_pos (fun j hj => h' j (hSS hj))]
  · rw [if_neg h']
    split_ifs <;> norm_num

theorem congestProb_anti {n N c : ℕ} {lam : ℕ → ℝ} (hlam : ValidLaw n lam) {k k' : ℕ}
    (hkk : k ≤ k') : congestProb n N c k' lam ≤ congestProb n N c k lam :=
  congestProbAt_anti hlam (selected_mono hkk)

theorem congestProbAt_map {n N c : ℕ} (lam : ℕ → ℝ) (e : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) :
    congestProbAt n N c lam (S.map e.toEmbedding) = congestProbAt n N c lam S := by
  classical
  unfold congestProbAt
  let E : (Fin N → Finset (Fin n)) ≃ (Fin N → Finset (Fin n)) :=
    Equiv.piCongrRight fun _ =>
      { toFun := fun T => T.map e.toEmbedding
        invFun := fun T => T.map e.symm.toEmbedding
        left_inv := fun T => by ext j; simp
        right_inv := fun T => by ext j; simp }
  rw [← Equiv.sum_comp E]
  apply Finset.sum_congr rfl
  intro x _
  have hw : ∀ l, contactWeight n lam (E x l) = contactWeight n lam (x l) := by
    intro l
    change contactWeight n lam ((x l).map e.toEmbedding) = _
    by_cases hT : x l = ∅
    · simp [hT]
    · have hT' : (x l).map e.toEmbedding ≠ ∅ := by
        intro h
        apply hT
        simpa using h
      rw [contactWeight_of_ne lam hT, contactWeight_of_ne lam hT', Finset.card_map]
  have hc : ∀ j, contacts (E x) (e j) = contacts x j := by
    intro j
    unfold contacts
    congr 1
    ext l
    simp [E]
  rw [Finset.prod_congr rfl (fun l _ => hw l)]
  congr 1
  apply if_congr _ rfl rfl
  constructor
  · intro h j hj
    have := h (e j) (by simpa using hj)
    rwa [hc] at this
  · intro h j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    rw [Equiv.toEmbedding_apply, hc]
    exact h i hi

theorem exists_perm_map_eq {n : ℕ} (A S : Finset (Fin n)) (hcard : A.card = S.card) :
    ∃ e : Equiv.Perm (Fin n), A.map e.toEmbedding = S := by
  classical
  have hc : Fintype.card {x // x ∈ A} = Fintype.card {x // x ∈ S} := by
    simp [hcard]
  let e0 : {x // x ∈ A} ≃ {x // x ∈ S} := Fintype.equivOfCardEq hc
  refine ⟨e0.extendSubtype, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    rw [Equiv.toEmbedding_apply, Equiv.extendSubtype_apply_of_mem e0 x hx]
    exact (e0 ⟨x, hx⟩).2
  · rw [Finset.card_map, hcard]

theorem congestProbAt_eq_congestProb {n N c : ℕ} (lam : ℕ → ℝ) (S : Finset (Fin n)) :
    congestProbAt n N c lam S = congestProb n N c S.card lam := by
  have hk : S.card ≤ n := by simpa using Finset.card_le_univ S
  obtain ⟨e, he⟩ := exists_perm_map_eq (selected n S.card) S (card_selected hk)
  rw [congestProb]
  conv_lhs => rw [← he]
  rw [congestProbAt_map]

theorem sum_split_inter_sdiff {n : ℕ} (S : Finset (Fin n)) (F : Finset (Fin n) → Finset (Fin n) → ℝ) :
    ∑ T : Finset (Fin n), F (T ∩ S) (T \ S) =
      ∑ A ∈ S.powerset, ∑ B ∈ (univ \ S).powerset, F A B := by
  classical
  rw [← Finset.sum_product' (f := F)]
  apply Finset.sum_nbij' (fun T => (T ∩ S, T \ S)) (fun p => p.1 ∪ p.2)
  · intro T _
    simp only [mem_product, mem_powerset]
    exact ⟨Finset.inter_subset_right, fun x hx => by
      simp only [mem_sdiff] at hx ⊢; exact ⟨mem_univ _, hx.2⟩⟩
  · intro p _
    exact mem_univ _
  · intro T _
    ext x
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  · intro p hp
    simp only [mem_product, mem_powerset] at hp
    have h1 : (p.1 ∪ p.2) ∩ S = p.1 := by
      ext x
      simp only [mem_union, mem_inter]
      constructor
      · rintro ⟨hx | hx, hxS⟩
        · exact hx
        · exact absurd hxS (mem_sdiff.mp (hp.2 hx)).2
      · intro hx
        exact ⟨Or.inl hx, hp.1 hx⟩
    have h2 : (p.1 ∪ p.2) \ S = p.2 := by
      ext x
      simp only [mem_union, mem_sdiff]
      constructor
      · rintro ⟨hx | hx, hxS⟩
        · exact absurd (hp.1 hx) hxS
        · exact hx
      · intro hx
        exact ⟨Or.inr hx, (mem_sdiff.mp (hp.2 hx)).2⟩
    simp [h1, h2]
  · intro T _
    rfl

theorem sum_choose_indicator (N a j : ℕ) :
    ∑ m ∈ range (N + 1), (N.choose m : ℝ) * (if a + m = j then 1 else 0) =
      if a ≤ j then (N.choose (j - a) : ℝ) else 0 := by
  by_cases haj : a ≤ j
  · rw [if_pos haj]
    by_cases hjN : j - a ≤ N
    · rw [Finset.sum_eq_single (j - a)]
      · rw [if_pos (by omega), mul_one]
      · intro m _ hm
        rw [if_neg (by omega), mul_zero]
      · intro hm
        exact absurd (Finset.mem_range.mpr (by omega)) hm
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
      apply Finset.sum_eq_zero
      intro m hm
      have := Finset.mem_range.mp hm
      rw [if_neg (by omega), mul_zero]
  · rw [if_neg haj]
    apply Finset.sum_eq_zero
    intro m _
    rw [if_neg (by omega), mul_zero]

theorem sum_card_eq_pow_inter {n : ℕ} (S : Finset (Fin n)) (j : ℕ) (z : ℝ) :
    ∑ T : Finset (Fin n), (if T.card = j then z ^ (T ∩ S).card else 0) =
      hyperNum n S.card j z := by
  classical
  have hsplit := sum_split_inter_sdiff S
    (fun A B => if A.card + B.card = j then z ^ A.card else 0)
  have hcard : ∀ T : Finset (Fin n), T.card = (T ∩ S).card + (T \ S).card := by
    intro T
    rw [add_comm, Finset.card_sdiff_add_card_inter]
  simp only [← hcard] at hsplit
  rw [hsplit]
  have hinner : ∀ A ∈ S.powerset, ∑ B ∈ (univ \ S).powerset,
      (if A.card + B.card = j then z ^ A.card else 0) =
      z ^ A.card * (if A.card ≤ j then ((n - S.card).choose (j - A.card) : ℝ) else 0) := by
    intro A _
    have h := Finset.sum_powerset_apply_card
      (f := fun m => z ^ A.card * (if A.card + m = j then (1 : ℝ) else 0)) (x := univ \ S)
    have hc : (univ \ S).card = n - S.card := by
      rw [Finset.card_sdiff_of_subset (subset_univ S), card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul] at h
    rw [show (∑ B ∈ (univ \ S).powerset, (if A.card + B.card = j then z ^ A.card else 0)) =
        ∑ B ∈ (univ \ S).powerset, z ^ A.card * (if A.card + B.card = j then (1 : ℝ) else 0) by
      apply Finset.sum_congr rfl; intro B _; split_ifs <;> simp, h, hc]
    rw [← sum_choose_indicator (n - S.card) A.card j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [Finset.sum_congr rfl hinner]
  have h := Finset.sum_powerset_apply_card
    (f := fun a => z ^ a * (if a ≤ j then ((n - S.card).choose (j - a) : ℝ) else 0)) (x := S)
  simp only [nsmul_eq_mul] at h
  rw [h, hyperNum_eq_paper]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem sum_contactWeight_pow (n : ℕ) (lam : ℕ → ℝ) (S : Finset (Fin n)) (z : ℝ) :
    ∑ T : Finset (Fin n), contactWeight n lam T * z ^ (T ∩ S).card =
      1 + ∑ j ∈ Icc 1 n, lam j * (hyperPGF n S.card j z - 1) := by
  classical
  have hsplit : ∀ T : Finset (Fin n), contactWeight n lam T * z ^ (T ∩ S).card =
      (if T.card = 0 then 1 - ∑ j ∈ Icc 1 n, lam j else 0) +
        ∑ j ∈ Icc 1 n, lam j / (n.choose j : ℝ) *
          (if T.card = j then z ^ (T ∩ S).card else 0) := by
    intro T
    by_cases hT : T = ∅
    · subst hT
      have hz : ∀ j ∈ Icc 1 n, (if (∅ : Finset (Fin n)).card = j then
          z ^ ((∅ : Finset (Fin n)) ∩ S).card else 0) = 0 := by
        intro j hj
        rw [if_neg (by simp; have := (mem_Icc.mp hj).1; omega)]
      have hs : ∑ j ∈ Icc 1 n, lam j / (n.choose j : ℝ) *
          (if (∅ : Finset (Fin n)).card = j then z ^ ((∅ : Finset (Fin n)) ∩ S).card else 0) =
          0 := Finset.sum_eq_zero (fun j hj => by rw [hz j hj, mul_zero])
      rw [hs]
      simp [contactWeight]
    · have hc : T.card ≠ 0 := by simpa [Finset.card_eq_zero] using hT
      rw [if_neg hc, zero_add, contactWeight_of_ne lam hT,
        Finset.sum_eq_single T.card]
      · rw [if_pos rfl]
      · intro j _ hj
        rw [if_neg (Ne.symm hj), mul_zero]
      · intro hj
        exact absurd (card_mem_Icc_of_ne hT) hj
  rw [Finset.sum_congr rfl (fun T _ => hsplit T), Finset.sum_add_distrib, Finset.sum_comm]
  have h0 : ∑ T : Finset (Fin n), (if T.card = 0 then 1 - ∑ j ∈ Icc 1 n, lam j else 0) =
      1 - ∑ j ∈ Icc 1 n, lam j := by
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro T _ hT
      rw [if_neg (by simpa [Finset.card_eq_zero] using hT)]
    · intro h
      exact absurd (mem_univ _) h
  rw [h0]
  have h1 : ∀ j ∈ Icc 1 n, ∑ T : Finset (Fin n), lam j / (n.choose j : ℝ) *
      (if T.card = j then z ^ (T ∩ S).card else 0) = lam j * hyperPGF n S.card j z := by
    intro j _
    rw [← Finset.mul_sum, sum_card_eq_pow_inter, hyperPGF]
    ring
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ j ∈ Icc 1 n, lam j * (hyperPGF n S.card j z - 1) =
      ∑ j ∈ Icc 1 n, lam j * hyperPGF n S.card j z - ∑ j ∈ Icc 1 n, lam j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h2]
  ring

theorem sum_contactWeight_exp (n : ℕ) (lam : ℕ → ℝ) (S : Finset (Fin n)) (θ : ℝ) :
    ∑ T : Finset (Fin n), contactWeight n lam T * Real.exp θ ^ (T ∩ S).card =
      rivalMGF n S.card lam θ := by
  rw [sum_contactWeight_pow]
  rfl

theorem sum_contacts_eq {N n : ℕ} (x : Fin N → Finset (Fin n)) (S : Finset (Fin n)) :
    ∑ j ∈ S, contacts x j = ∑ l, (x l ∩ S).card := by
  classical
  unfold contacts
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]

theorem congestProbAt_le_chernoff {n N c : ℕ} {lam : ℕ → ℝ} (hlam : ValidLaw n lam)
    (S : Finset (Fin n)) {θ : ℝ} (hθ : 0 ≤ θ) :
    congestProbAt n N c lam S ≤
      Real.exp (-(θ * ((S.card : ℝ) * c))) * rivalMGF n S.card lam θ ^ N := by
  classical
  unfold congestProbAt
  have hind : ∀ x : Fin N → Finset (Fin n),
      (if ∀ j ∈ S, c ≤ contacts x j then (1 : ℝ) else 0) ≤
        Real.exp (-(θ * ((S.card : ℝ) * c))) * ∏ l, Real.exp θ ^ (x l ∩ S).card := by
    intro x
    have hprod : Real.exp (-(θ * ((S.card : ℝ) * c))) * ∏ l, Real.exp θ ^ (x l ∩ S).card =
        Real.exp (θ * ((∑ j ∈ S, contacts x j : ℕ) - (S.card : ℝ) * c)) := by
      rw [sum_contacts_eq]
      simp_rw [← Real.exp_nat_mul]
      rw [← Real.exp_sum, ← Real.exp_add]
      congr 1
      push_cast
      rw [← Finset.sum_mul]
      ring
    rw [hprod]
    split_ifs with h
    · apply Real.one_le_exp
      apply mul_nonneg hθ
      have hsum : (S.card : ℝ) * c ≤ ((∑ j ∈ S, contacts x j : ℕ) : ℝ) := by
        have : S.card * c ≤ ∑ j ∈ S, contacts x j := by
          have := Finset.sum_le_sum (s := S) (f := fun _ => c) (g := fun j => contacts x j)
            (fun j hj => h j hj)
          simpa [Finset.sum_const, smul_eq_mul] using this
        exact_mod_cast this
      linarith
    · exact (Real.exp_pos _).le
  calc _ ≤ ∑ x : Fin N → Finset (Fin n), (∏ l, contactWeight n lam (x l)) *
        (Real.exp (-(θ * ((S.card : ℝ) * c))) * ∏ l, Real.exp θ ^ (x l ∩ S).card) := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hind x)
          (Finset.prod_nonneg fun l _ => contactWeight_nonneg hlam _)
    _ = Real.exp (-(θ * ((S.card : ℝ) * c))) *
        ∑ x : Fin N → Finset (Fin n), ∏ l, (contactWeight n lam (x l) *
          Real.exp θ ^ (x l ∩ S).card) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.prod_mul_distrib]
        ring
    _ = _ := by
        rw [sum_prod_eq_pow (fun T => contactWeight n lam T * Real.exp θ ^ (T ∩ S).card),
          sum_contactWeight_exp]

theorem congestProb_le_chernoff {n N c k : ℕ} (hk : k ≤ n) {lam : ℕ → ℝ}
    (hlam : ValidLaw n lam) {θ : ℝ} (hθ : 0 ≤ θ) :
    congestProb n N c k lam ≤ Real.exp (-(θ * ((k : ℝ) * c))) * rivalMGF n k lam θ ^ N := by
  have h := congestProbAt_le_chernoff (N := N) (c := c) hlam (selected n k) hθ
  rwa [card_selected hk] at h

end Ample
end FCAppendix
