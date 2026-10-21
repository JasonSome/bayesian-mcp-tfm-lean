import FCAppendix.Affine.Tail04.TopSelection

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set Filter Topology Classical
open scoped BigOperators

namespace AtypicalUnequal

def EitherSlack (N H0 H1 c : ℕ) : Prop := N + min H0 H1 < c

theorem eitherSlack_iff (N H0 H1 c : ℕ) :
    EitherSlack N H0 H1 c ↔ N + H0 < c ∨ N + H1 < c := by
  unfold EitherSlack
  omega

theorem nonslack_both (N H0 H1 c : ℕ) (h : ¬ EitherSlack N H0 H1 c) :
    c ≤ N + H0 ∧ c ≤ N + H1 := by
  rw [eitherSlack_iff] at h
  omega

def overloadOwnerLeft (N H0 c : ℕ) : ℕ := max (c - H0) (N - c)

def overloadOwnerRight (N H0 c : ℕ) : ℕ := N - overloadOwnerLeft N H0 c

theorem overload_owner_counts (N H0 H1 c : ℕ)
    (h0 : c ≤ N + H0) (h1 : c ≤ N + H1) (hN : N ≤ 2 * c)
    (hover : 2 * c ≤ N + H0 + H1) :
    overloadOwnerLeft N H0 c + overloadOwnerRight N H0 c = N ∧
    c - H0 ≤ overloadOwnerLeft N H0 c ∧ overloadOwnerLeft N H0 c ≤ c ∧
    c - H1 ≤ overloadOwnerRight N H0 c ∧ overloadOwnerRight N H0 c ≤ c := by
  simp only [overloadOwnerLeft,overloadOwnerRight]
  omega

theorem fitting_residual_counts (N H0 H1 c : ℕ)
    (h0 : c ≤ N + H0) (h1 : c ≤ N + H1)
    (hfit : N + H0 + H1 ≤ 2 * c) :
    H0 ≤ c ∧ H1 ≤ c ∧ c - H0 ≤ N ∧ c - H1 ≤ N ∧
      N ≤ (c - H0) + (c - H1) := by
  omega

section Fitting
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open LowBody.CompleteInformation

theorem fitting_active_receipt_optimal
    (r0 r1 : ℕ) (hr0 : r0 ≤ Fintype.card ι) (hr1 : r1 ≤ Fintype.card ι)
    (kappa : ℝ) (hk : 0 ≤ kappa) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    let p := selector r0 r1 hr0 hr1 kappa b
    Finite.Optimal r0 (fun i => if i ∈ p.2.1 then kappa * b i else b i) p.1.1 ∧
    Finite.Optimal r1 (fun i => if i ∈ p.1.1 then kappa * b i else b i) p.2.1 := by
  dsimp only
  have hn := selector_nash_all_feasible r0 r1 hr0 hr1 kappa hk b hb
  exact ⟨⟨(selector r0 r1 hr0 hr1 kappa b).1.2.le, hn.1⟩,
    ⟨(selector r0 r1 hr0 hr1 kappa b).2.2.le, hn.2⟩⟩

theorem fitting_covers_all
    (r0 r1 : ℕ) (hr0 : r0 ≤ Fintype.card ι) (hr1 : r1 ≤ Fintype.card ι)
    (hslots : Fintype.card ι ≤ r0 + r1)
    (kappa : ℝ) (hk : 0 ≤ kappa) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hfirst : ∀ i j, kappa * b j < b i) :
    let p := selector r0 r1 hr0 hr1 kappa b
    p.1.1 ∪ p.2.1 = Finset.univ := by
  dsimp only
  let p := selector r0 r1 hr0 hr1 kappa b
  have hopt := fitting_active_receipt_optimal r0 r1 hr0 hr1 kappa hk b hb
  change Finite.Optimal r0 _ p.1.1 ∧ Finite.Optimal r1 _ p.2.1 at hopt
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hi
  have hi0 : i ∉ p.1.1 := fun h => hi (Finset.mem_union_left _ h)
  have hi1 : i ∉ p.2.1 := fun h => hi (Finset.mem_union_right _ h)
  have hsub : p.1.1 ∪ p.2.1 ⊆ (Finset.univ : Finset ι).erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨fun he => hi (he ▸ hj), Finset.mem_univ j⟩
  have hu := Finset.card_le_card hsub
  have hsum := Finset.card_union_add_card_inter p.1.1 p.2.1
  have hc0 : p.1.1.card = r0 := p.1.2
  have hc1 : p.2.1.card = r1 := p.2.2
  have hN : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] at hu
  have hd : 0 < (p.1.1 ∩ p.2.1).card := by omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hd
  obtain ⟨hj0, hj1⟩ := Finset.mem_inter.mp hj
  have hswap := Finite.optimal_swap r0 _ _ hopt.1 j i hj0 hi0
  change (if i∈p.2.1 then kappa*b i else b i) ≤
    (if j∈p.2.1 then kappa*b j else b j) at hswap
  rw [if_neg hi1,if_pos hj1] at hswap
  exact (not_le_of_gt (hfirst i j)) hswap

theorem fitting_duplicates_highest
    (r0 r1 : ℕ) (hr0 : r0 ≤ Fintype.card ι) (hr1 : r1 ≤ Fintype.card ι)
    (hslots : Fintype.card ι ≤ r0 + r1)
    (kappa : ℝ) (hk : 0 < kappa) (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hfirst : ∀ i j, kappa * b j < b i) :
    let p := selector r0 r1 hr0 hr1 kappa b
    ∀ i ∈ p.1.1 ∩ p.2.1, ∀ j ∉ p.1.1 ∩ p.2.1, b j ≤ b i := by
  dsimp only
  let p := selector r0 r1 hr0 hr1 kappa b
  have hopt := fitting_active_receipt_optimal r0 r1 hr0 hr1 kappa hk.le b hb
  have hcover := fitting_covers_all r0 r1 hr0 hr1 hslots kappa hk.le b hb hfirst
  change p.1.1 ∪ p.2.1 = Finset.univ at hcover
  change Finite.Optimal r0 _ p.1.1 ∧ Finite.Optimal r1 _ p.2.1 at hopt
  intro i hi j hj
  obtain ⟨hi0, hi1⟩ := Finset.mem_inter.mp hi
  have hjcov : j ∈ p.1.1 ∪ p.2.1 := by rw [hcover]; exact Finset.mem_univ j
  by_cases hj0 : j ∈ p.1.1
  · have hj1 : j ∉ p.2.1 := fun h => hj (Finset.mem_inter.mpr ⟨hj0, h⟩)
    have hs := Finite.optimal_swap r1 _ _ hopt.2 i j hi1 hj1
    change (if j∈p.1.1 then kappa*b j else b j) ≤
      (if i∈p.1.1 then kappa*b i else b i) at hs
    rw [if_pos hi0,if_pos hj0] at hs
    exact (mul_le_mul_iff_right₀ hk).mp hs
  · have hj1 : j ∈ p.2.1 := (Finset.mem_union.mp hjcov).resolve_left hj0
    have hs := Finite.optimal_swap r0 _ _ hopt.1 i j hi0 hj0
    change (if j∈p.2.1 then kappa*b j else b j) ≤
      (if i∈p.2.1 then kappa*b i else b i) at hs
    rw [if_pos hi1,if_pos hj1] at hs
    exact (mul_le_mul_iff_right₀ hk).mp hs

end Fitting

section Owners
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def splitLeft (A : Finset ι) (r : ℕ) : Finset ι :=
  topSelection A r (fun _ => 1)

def splitRight (A : Finset ι) (r : ℕ) : Finset ι := A \ splitLeft A r

theorem split_partition (A : Finset ι) (r : ℕ) (hr : r ≤ A.card) :
    Disjoint (splitLeft A r) (splitRight A r) ∧
    splitLeft A r ∪ splitRight A r = A ∧
    (splitLeft A r).card = r ∧ (splitRight A r).card = A.card - r := by
  have hs : splitLeft A r ⊆ A := (topSelection_feasible A r (fun _ => 1)).2
  have hc : (splitLeft A r).card = r := by
    rw [splitLeft, topSelection_card A r (fun _ => 1) (by intro i hi; norm_num),
      min_eq_left hr]
  refine ⟨?_, ?_, hc, ?_⟩
  · exact Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)
  · exact Finset.union_sdiff_of_subset hs
  · simp only [splitRight, Finset.card_sdiff, Finset.inter_eq_left.mpr hs, hc]

theorem overload_owner_partition
    (H0 H1 c : ℕ)
    (h0 : c ≤ Fintype.card ι + H0) (h1 : c ≤ Fintype.card ι + H1)
    (hN : Fintype.card ι ≤ 2 * c) (hover : 2 * c ≤ Fintype.card ι + H0 + H1) :
    let a0 := overloadOwnerLeft (Fintype.card ι) H0 c
    let O0 := splitLeft (Finset.univ : Finset ι) a0
    let O1 := splitRight (Finset.univ : Finset ι) a0
    Disjoint O0 O1 ∧ O0 ∪ O1 = Finset.univ ∧
    c - H0 ≤ O0.card ∧ O0.card ≤ c ∧ c - H1 ≤ O1.card ∧ O1.card ≤ c := by
  dsimp only
  have hc := overload_owner_counts (Fintype.card ι) H0 H1 c h0 h1 hN hover
  have ha : overloadOwnerLeft (Fintype.card ι) H0 c ≤ (Finset.univ : Finset ι).card := by
    rw [Finset.card_univ]
    omega
  have hs := split_partition (Finset.univ : Finset ι)
    (overloadOwnerLeft (Fintype.card ι) H0 c) ha
  refine ⟨hs.1, hs.2.1, ?_, ?_, ?_, ?_⟩
  · rw [hs.2.2.1]
    exact hc.2.1
  · rw [hs.2.2.1]
    exact hc.2.2.1
  · rw [hs.2.2.2, Finset.card_univ]
    exact hc.2.2.2.1
  · rw [hs.2.2.2, Finset.card_univ]
    exact hc.2.2.2.2

theorem top_two_capacity_owners (c : ℕ) (hc : 2 * c ≤ Fintype.card ι)
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) :
    let A := topSelection (Finset.univ : Finset ι) (2 * c) b
    let O0 := splitLeft A c
    let O1 := splitRight A c
    A.card = 2 * c ∧ Disjoint O0 O1 ∧ O0 ∪ O1 = A ∧
      O0.card = c ∧ O1.card = c ∧
      ∀ i ∈ A, ∀ j ∉ A, b j ≤ b i := by
  dsimp only
  let A := topSelection (Finset.univ : Finset ι) (2 * c) b
  have hA : A.card = 2 * c := by
    rw [topSelection_card _ _ _ (fun i _ => hb i), Finset.card_univ,
      min_eq_left hc]
  have hs := split_partition A c (by omega)
  refine ⟨hA, hs.1, hs.2.1, hs.2.2.1, ?_, ?_⟩
  · rw [hs.2.2.2, hA]
    omega
  · intro i hi j hj
    exact topSelection_order (Finset.univ : Finset ι) (2 * c) b
      (fun i _ => (hb i).le) i j hi (Finset.mem_univ j) hj

end Owners

section LocalPolicies
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ownerPrioritySelection (O U P : Finset ι) (c : ℕ) (b : ι → ℝ) : Finset ι :=
  topSelection (O ∪ (U ∪ P)) c b

def ownerPriorityLaw (O U P : Finset ι) (c : ℕ) (b : ι → ℝ) :
    FiniteLaw (Finset ι) := FiniteLaw.dirac (ownerPrioritySelection O U P c b)

theorem ownerPriority_capacity (O U P : Finset ι) (c : ℕ) (b : ι → ℝ) :
    (ownerPrioritySelection O U P c b).card ≤ c ∧
    ownerPrioritySelection O U P c b ⊆ O ∪ (U ∪ P) :=
  topSelection_feasible (O ∪ (U ∪ P)) c b

theorem ownerPriority_nonowner_excluded (O U P : Finset ι) (c : ℕ) (b : ι → ℝ)
    (i : ι) (hiO : i ∉ O) (hiU : i ∉ U) (hiP : i ∉ P) :
    i ∉ ownerPrioritySelection O U P c b := by
  intro hi
  have hh := (ownerPriority_capacity O U P c b).2 hi
  simp only [Finset.mem_union, hiO, hiU, hiP, false_or] at hh

omit [Fintype ι] in
theorem ownerPriority_available (O U P : Finset ι) (H c : ℕ)
    (hdis : Disjoint O (U ∪ P)) (hUP : Disjoint U P)
    (hH : U.card + P.card = H) (howners : c - H ≤ O.card) :
    c ≤ (O ∪ (U ∪ P)).card := by
  rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint hUP, hH]
  omega

theorem ownerPriority_no_upper_accepts_owners
    (O P : Finset ι) (c : ℕ) (b : ι → ℝ)
    (hOc : O.card ≤ c) (hO : ∀ i ∈ O, 1 ≤ b i)
    (hP : ∀ j ∈ P, b j < 1) :
    O ⊆ ownerPrioritySelection O ∅ P c b := by
  dsimp only [ownerPrioritySelection]
  simp only [Finset.empty_union]
  apply topSelection_contains_priority (O ∪ P) O c b Finset.subset_union_left hOc
  · intro i hi
    linarith [hO i hi]
  · intro i hi j hj hjO
    have hjP : j ∈ P := (Finset.mem_union.mp hj).resolve_left hjO
    exact (hP j hjP).trans_le (hO i hi)

theorem ownerPriority_receipt_optimal
    (O U P : Finset ι) (c : ℕ) (b rho : ι → ℝ) (R : ℝ)
    (hR : 0 < R) (havailable : c ≤ (O ∪ (U ∪ P)).card)
    (hbid : ∀ i ∈ O ∪ (U ∪ P), R ≤ b i)
    (hrho0 : ∀ i, 0 ≤ rho i)
    (hreceipts : ∀ i ∈ O ∪ (U ∪ P), rho i = b i)
    (houtside : ∀ j ∉ O ∪ (U ∪ P), rho j ≤ R) :
    Finite.Optimal c rho (ownerPrioritySelection O U P c b) := by
  apply topSelection_receipt_optimal (O ∪ (U ∪ P)) c b rho havailable
    (fun i hi => hR.trans_le (hbid i hi)) hrho0 hreceipts
  intro i hi j hj
  exact (houtside j hj).trans (hbid i hi)

theorem ownerPriority_all_compositions
    {D : Type*} (O : Finset ι) (U P : D → Finset ι) (c : ℕ)
    (b rho : D → ι → ℝ) (R : ℝ) (hR : 0 < R)
    (havailable : ∀ d, c ≤ (O ∪ (U d ∪ P d)).card)
    (hbid : ∀ d i, i ∈ O ∪ (U d ∪ P d) → R ≤ b d i)
    (hrho0 : ∀ d i, 0 ≤ rho d i)
    (hreceipts : ∀ d i, i ∈ O ∪ (U d ∪ P d) → rho d i = b d i)
    (houtside : ∀ d j, j ∉ O ∪ (U d ∪ P d) → rho d j ≤ R) :
    ∀ d, Finite.Optimal c (rho d) (ownerPrioritySelection O (U d) (P d) c (b d)) := by
  intro d
  exact ownerPriority_receipt_optimal O (U d) (P d) c (b d) (rho d) R hR
    (havailable d) (hbid d) (hrho0 d) (hreceipts d) (houtside d)

theorem top_two_local_receipt_optimal
    (A T O U : Finset ι) (c : ℕ) (b rho : ι → ℝ)
    (_hTA : T ⊆ A) (hOT : O ⊆ T) (hOc : O.card = c)
    (howner : ∀ i ∈ O, 1 ≤ b i) (hupper : ∀ i ∈ U, 1 ≤ b i)
    (hpool : ∀ i ∈ T, ∀ j ∈ A, j ∉ T → b j ≤ b i)
    (hupperOrder : ∀ i ∈ U, ∀ j ∈ A, b j ≤ b i)
    (hrho0 : ∀ i, 0 ≤ rho i)
    (hreceipts : ∀ i ∈ O ∪ U, rho i = b i)
    (hotherOwned : ∀ j ∈ T, j ∉ O → rho j ≤ 1)
    (hfirst : ∀ j ∈ A, j ∉ T → rho j ≤ b j)
    (hprivateLow : ∀ j ∉ A ∪ U, rho j ≤ 1) :
    Finite.Optimal c rho (ownerPrioritySelection O U ∅ c b) := by
  simp only [ownerPrioritySelection, Finset.union_empty]
  have hcap : c ≤ (O ∪ U).card := by
    rw [← hOc]
    exact Finset.card_le_card Finset.subset_union_left
  have hbid : ∀ i ∈ O ∪ U, 1 ≤ b i := by
    intro i hi
    exact (Finset.mem_union.mp hi).elim (howner i) (hupper i)
  apply topSelection_receipt_optimal (O ∪ U) c b rho hcap
    (fun i hi => lt_of_lt_of_le (by norm_num) (hbid i hi)) hrho0 hreceipts
  intro i hi j hj
  have hjO : j ∉ O := fun h => hj (Finset.mem_union_left _ h)
  have hjU : j ∉ U := fun h => hj (Finset.mem_union_right _ h)
  by_cases hjA : j ∈ A
  · by_cases hjT : j ∈ T
    · exact (hotherOwned j hjT hjO).trans (hbid i hi)
    · apply (hfirst j hjA hjT).trans
      rcases Finset.mem_union.mp hi with hiO | hiU
      · exact hpool i (hOT hiO) j hjA hjT
      · exact hupperOrder i hiU j hjA
  · exact (hprivateLow j (by simp [Finset.mem_union, hjA, hjU])).trans (hbid i hi)

omit [Fintype ι] in
theorem fitting_private_union_optimal
    (A H S : Finset ι) (r c : ℕ) (rho : ι → ℝ) (R d0 : ℝ)
    (hSA : S ⊆ A) (hAH : Disjoint A H)
    (hcard : S.card = r) (hcap : r + H.card = c)
    (hactive : Finite.Optimal r (fun i => if i ∈ A then rho i else 0) S)
    (hrho0 : ∀ i, 0 ≤ rho i) (hdR : d0 ≤ R)
    (hselected : ∀ i ∈ S, d0 ≤ rho i)
    (hprivate : ∀ i ∈ H, R ≤ rho i)
    (hduplicate : ∀ j ∈ A, j ∉ S → rho j ≤ R)
    (hlow : ∀ j ∉ A ∪ H, rho j ≤ d0) :
    Finite.Optimal c rho (S ∪ H) := by
  have hdis : Disjoint S H := hAH.mono_left hSA
  have hc : (S ∪ H).card = c := by
    rw [Finset.card_union_of_disjoint hdis, hcard, hcap]
  apply Hybrid.optimal_of_order_slack c rho (S ∪ H) hc.le (fun i _ => hrho0 i)
  · intro i hi j hj
    have hjS : j ∉ S := fun h => hj (Finset.mem_union_left _ h)
    have hjH : j ∉ H := fun h => hj (Finset.mem_union_right _ h)
    by_cases hjA : j ∈ A
    · rcases Finset.mem_union.mp hi with hiS | hiH
      · simpa only [if_pos (hSA hiS), if_pos hjA] using
          Finite.optimal_swap r _ S hactive i j hiS hjS
      · exact (hduplicate j hjA hjS).trans (hprivate i hiH)
    · have hlowj : rho j ≤ d0 := hlow j (by simp only [Finset.mem_union, hjA, hjH, false_or, not_false_eq_true])
      rcases Finset.mem_union.mp hi with hiS | hiH
      · exact hlowj.trans (hselected i hiS)
      · exact hlowj.trans (hdR.trans (hprivate i hiH))
  · intro h
    omega

omit [Fintype ι] in
theorem slack_high_then_low_optimal
    (H L : Finset ι) (c : ℕ) (rho : ι → ℝ)
    (hH : H.card ≤ c) (hdis : Disjoint H L) (hrho0 : ∀ i, 0 ≤ rho i)
    (hpriority : ∀ i ∈ H, ∀ j ∉ H, rho j ≤ rho i)
    (hlow : Finite.Optimal (c - H.card) (fun i => if i ∈ H then 0 else rho i) L) :
    Finite.Optimal c rho (H ∪ L) :=
  Hybrid.priority_union_optimal c rho H L hH hdis hrho0 hpriority hlow

end LocalPolicies

section BayesBounds
variable {Ω J : Type*} [Fintype Ω] [Fintype J]

theorem prob_exists_le_sum (nu : FiniteLaw Ω) (mark : J → Ω → Prop) :
    nu.prob (fun omega => ∃ j, mark j omega) ≤ ∑ j, nu.prob (mark j) := by
  classical
  unfold FiniteLaw.prob
  rw [← nu.expect_finset_sum]
  apply nu.expect_mono
  intro omega
  by_cases h : ∃ j, mark j omega
  · obtain ⟨j, hj⟩ := h
    rw [if_pos ⟨j, hj⟩]
    have hs := Finset.single_le_sum
      (f := fun i => if mark i omega then (1 : ℝ) else 0)
      (fun i (_hi : i ∈ (Finset.univ : Finset J)) => by split <;> norm_num)
      (Finset.mem_univ j)
    simpa only [if_pos hj] using hs
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun j _ => by split <;> norm_num)

theorem owner_acceptance_lower (nu : FiniteLaw Ω)
    (mark : J → Ω → Prop) (accept : Ω → Prop) (pi : ℝ)
    (hmark : ∀ j, nu.prob (mark j) ≤ pi)
    (hnoUpper : ∀ omega, (∀ j, ¬ mark j omega) → accept omega) :
    1 - (Fintype.card J : ℝ) * pi ≤ nu.prob accept := by
  classical
  have hu := prob_exists_le_sum nu mark
  have hm : (∑ j, nu.prob (mark j)) ≤ (Fintype.card J : ℝ) * pi := by
    calc
      _ ≤ ∑ _j : J, pi := Finset.sum_le_sum (fun j _ => hmark j)
      _ = _ := by simp
  have ha := nu.prob_mono (E := fun omega => ¬ ∃ j, mark j omega)
    (F := accept) (fun omega ho => hnoUpper omega (by simpa only [not_exists] using ho))
  rw [nu.prob_compl] at ha
  linarith

theorem nonowner_receipt_bound (b B xi e p : ℝ)
    (hb0 : 0 ≤ b) (hbB : b ≤ B) (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (he : 0 ≤ e) (hp : 1 - e ≤ p) :
    b * (1 - xi * p) ≤ (1 - xi) * B + xi * B * e := by
  have hc : 0 ≤ 1 - xi + xi * e :=
    add_nonneg (sub_nonneg.mpr hxi1) (mul_nonneg hxi0 he)
  have hp' := mul_le_mul_of_nonneg_left hp hxi0
  have hb' := mul_le_mul_of_nonneg_left
    (show 1 - xi * p ≤ 1 - xi + xi * e by nlinarith) hb0
  have hB' := mul_le_mul_of_nonneg_right hbB hc
  nlinarith

end BayesBounds

end AtypicalUnequal
end FCAppendix.Affine.Tail04
