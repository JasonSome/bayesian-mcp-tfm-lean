import FCAppendix.Affine.Hybrid.NativeEqual
import FCAppendix.Affine.Uniform07Finishing.Native.StrictPolicy

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine
open FCAppendix.Affine.Hybrid (threshold_optimal)
open Existence.PayOnceBounded (listBids measurable_listBids positiveSupport mem_positiveSupport)
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def threshold (ξ : ℝ) (d : ℕ) (b : ι → ℝ) : ℝ :=
  max 0 (Finset.univ.sup' Finset.univ_nonempty (fun i =>
    if EqualCapacity.positiveMarginal ξ d b i < 1 then
      b i * (1-ξ*EqualCapacity.positiveMarginal ξ d b i) else 0))

lemma threshold_nonneg (ξ : ℝ) (d : ℕ) (b : ι → ℝ) :
    0 ≤ threshold ξ d b := le_max_left _ _

lemma measurable_threshold (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (d : ℕ) :
    Measurable (threshold (ι:=ι) ξ d) := by
  have hi (i : ι) : Measurable (fun b : ι→ℝ =>
      if EqualCapacity.positiveMarginal ξ d b i<1 then
        b i*(1-ξ*EqualCapacity.positiveMarginal ξ d b i) else 0) := by
    have hp := ((measurable_pi_apply i).comp
      (EqualCapacity.measurable_positiveMarginal ξ d hξ hξ1))
    exact Measurable.ite (measurableSet_lt hp measurable_const)
      ((measurable_pi_apply i).mul (measurable_const.sub (measurable_const.mul hp)))
      measurable_const
  have hs : Measurable (fun b : ι→ℝ => Finset.univ.sup' Finset.univ_nonempty
      (fun i=>if EqualCapacity.positiveMarginal ξ d b i<1 then
        b i*(1-ξ*EqualCapacity.positiveMarginal ξ d b i) else 0)) := by
    convert Finset.measurable_sup' (α:=ℝ) Finset.univ_nonempty (fun i _=>hi i) using 1
    ext b
    simp only [Finset.sup'_apply]
  exact measurable_const.max hs

theorem threshold_spec (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (d : ℕ) (b : ι→ℝ) :
    Proposer.Threshold (EqualCapacity.positiveMarginal ξ d b)
      (fun i=>b i*(1-ξ*EqualCapacity.positiveMarginal ξ d b i)) (threshold ξ d b) ∧
      threshold ξ d b * ((d:ℝ)-∑i,EqualCapacity.positiveMarginal ξ d b i)=0 := by
  let p := EqualCapacity.positiveMarginal ξ d b
  let r := fun i=>b i*(1-ξ*p i)
  have hp := EqualCapacity.positiveMarginal_spec ξ d hξ hξ1 b
  obtain ⟨z,hz,ht,hs⟩ := EqualCapacity.positiveMarginal_threshold hξ hξ1 d b
  change Proposer.Threshold p r z at ht
  have hentry (i : ι) (hi : p i<1) : r i≤ z := by
    by_cases hi0 : p i=0
    · exact ht.1 i hi0
    · exact (ht.2.2 i (lt_of_le_of_ne (hp.1 i) (Ne.symm hi0)) hi).le
  have htz : threshold ξ d b≤ z := by
    apply max_le hz
    apply Finset.sup'_le
    intro i _
    by_cases hi : p i<1
    · exact (if_pos hi).trans_le (hentry i hi)
    · simpa only [p,if_neg hi] using hz
  have hrt (i : ι) (hi : p i<1) : r i≤ threshold ξ d b := by
    apply le_trans _ (le_max_right _ _)
    have hh := Finset.le_sup' (fun j=>
      if p j<1 then r j else 0) (Finset.mem_univ i)
    simpa only [if_pos hi,p,r] using hh
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro i hi
      exact hrt i (by change EqualCapacity.positiveMarginal ξ d b i < 1; rw [hi]; norm_num)
    · intro i hi
      exact htz.trans (ht.2.1 i hi)
    · intro i hi0 hi1
      apply le_antisymm (hrt i hi1)
      rw [ht.2.2 i hi0 hi1]
      exact htz
  · have hslack : 0≤(d:ℝ)-∑i,p i := by
      have hm := hp.2.2.le.trans (Nat.cast_le.mpr (min_le_left d (positiveSupport b).card))
      exact sub_nonneg.mpr hm
    have hle := mul_le_mul_of_nonneg_right htz hslack
    change z*((d:ℝ)-∑i,p i)=0 at hs
    rw [hs] at hle
    exact le_antisymm hle (mul_nonneg (threshold_nonneg ξ d b) hslack)

def remainder {m : ℕ} (L : LocalList m) (E : Finset (Fin m)) : LocalList m :=
  fun i=>if i∈E then none else L i

lemma measurable_remainder {m : ℕ} :
    Measurable (fun x : LocalList m×Finset (Fin m)=>remainder x.1 x.2) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite
    ((measurable_snd (MeasurableSet.of_discrete :
      MeasurableSet {E : Finset (Fin m) | i∈E}))) measurable_const
    ((measurable_pi_apply i).comp measurable_fst)

lemma remainder_entry {m : ℕ} (L : LocalList m) (E : Finset (Fin m)) (i : Fin m) :
    entryBid (remainder L E i)=if i∈E then 0 else entryBid (L i) := by
  by_cases hi:i∈E <;> simp [remainder,hi,entryBid]

lemma listBids_eq_entry {m : ℕ} (L : LocalList m) (i : Fin m) :
    listBids L i=entryBid (L i) := by unfold listBids; cases L i <;> rfl

lemma remainder_bid {m : ℕ} (L : LocalList m) (E : Finset (Fin m)) (i : Fin m) :
    listBids (remainder L E) i=if i∈E then 0 else listBids L i := by
  simp only [listBids_eq_entry,remainder_entry]

lemma remainder_present {m : ℕ} (L : LocalList m) (E : Finset (Fin m)) (i : Fin m) :
    remainder L E i≠none ↔ i∉E ∧ L i≠none := by
  by_cases hi:i∈E <;> simp [remainder,hi]

lemma remainder_nonnegative {m : ℕ} (L : LocalList m) (hL : NonnegativeList L)
    (E : Finset (Fin m)) : NonnegativeList (remainder L E) := by
  intro i
  rw [remainder_entry]
  split_ifs
  · exact le_rfl
  · exact hL i

lemma remainder_marginal_zero {m : ℕ} (ξ : ℝ) (d : ℕ) (L : LocalList m)
    (E : Finset (Fin m)) (i : Fin m) (hi : i∈E) :
    EqualCapacity.positiveMarginal ξ d (listBids (remainder L E)) i=0 := by
  apply EqualCapacity.onSupport_outside
  rw [mem_positiveSupport,remainder_bid,if_pos hi]
  exact lt_irrefl 0

lemma sample_card {m : ℕ} (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (d : ℕ)
    (L : LocalList m) (s : unitInterval)
    (hfill : d≤(positiveSupport (listBids L)).card) :
    (Hybrid.NativeEqual.sample m ξ hξ hξ1 d L s).card=d := by
  have hh := (EqualCapacity.canonicalLottery_implements hξ hξ1 d (listBids L)).1
    (Hybrid.NativeEqual.sample m ξ hξ hξ1 d L s)
    (Hybrid.NativeEqual.sample_support m ξ hξ hξ1 d L s).ne'
  simpa only [min_eq_left hfill] using hh

lemma sample_selected_receipt {m : ℕ} [Nonempty (Fin m)]
    (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (d : ℕ) (L : LocalList m)
    (s : unitInterval) (i : Fin m) (hi:i∈Hybrid.NativeEqual.sample m ξ hξ hξ1 d L s) :
    threshold ξ d (listBids L)≤
      listBids L i*(1-ξ*EqualCapacity.positiveMarginal ξ d (listBids L) i) := by
  let p := EqualCapacity.positiveMarginal ξ d (listBids L)
  have hp := EqualCapacity.positiveMarginal_spec ξ d hξ hξ1 (listBids L)
  have ht := (threshold_spec ξ hξ hξ1 d (listBids L)).1
  have hpos : 0< p i := by
    have hh := FiniteLaw.marginal_pos_of_support_mem
      (EqualCapacity.canonicalLottery ξ d (listBids L)) _
      (Hybrid.NativeEqual.sample_support m ξ hξ hξ1 d L s).ne' i hi
    rw [(EqualCapacity.canonicalLottery_implements hξ hξ1 d (listBids L)).2] at hh
    exact hh
  by_cases h1:p i=1
  · exact ht.2.1 i h1
  · exact (ht.2.2 i hpos (lt_of_le_of_ne (hp.2.1 i) h1)).ge

lemma sample_unselected_receipt {m : ℕ} [Nonempty (Fin m)]
    (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (d : ℕ) (L : LocalList m)
    (s : unitInterval) (i : Fin m) (hi:i∉Hybrid.NativeEqual.sample m ξ hξ hξ1 d L s) :
    listBids L i*(1-ξ*EqualCapacity.positiveMarginal ξ d (listBids L) i)≤
      threshold ξ d (listBids L) := by
  let p := EqualCapacity.positiveMarginal ξ d (listBids L)
  have hp := EqualCapacity.positiveMarginal_spec ξ d hξ hξ1 (listBids L)
  have ht := (threshold_spec ξ hξ hξ1 d (listBids L)).1
  have hne : p i≠1 := by
    intro h1
    have hm := (EqualCapacity.canonicalLottery_implements hξ hξ1 d (listBids L)).2 i
    have hin := Hybrid.GuardedData.support_mem_of_marginal_one
      (EqualCapacity.canonicalLottery ξ d (listBids L)) i (hm.trans h1)
      (Hybrid.NativeEqual.sample m ξ hξ hξ1 d L s)
      (Hybrid.NativeEqual.sample_support m ξ hξ hξ1 d L s).ne'
    exact hi hin
  by_cases h0:p i=0
  · exact ht.1 i h0
  · exact (ht.2.2 i (lt_of_le_of_ne (hp.1 i) (Ne.symm h0))
      (lt_of_le_of_ne (hp.2.1 i) hne)).le

def ValidExclusive {m : ℕ} [Nonempty (Fin m)] (ξ : ℝ) (L : LocalList m)
    (d₀ d₁ : ℕ) (E : Finset (Fin m)) : Prop :=
  E.card=max d₀ d₁-min d₀ d₁ ∧
  (∀i∈E,L i≠none) ∧
  min d₀ d₁≤(positiveSupport (listBids (remainder L E))).card ∧
  ∀i∈E,(1-ξ)*entryBid (L i)≤ threshold ξ (min d₀ d₁) (listBids (remainder L E)) ∧
    threshold ξ (min d₀ d₁) (listBids (remainder L E))≤ entryBid (L i)

theorem exclusive_large_optimal {m : ℕ} [Nonempty (Fin m)]
    (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (L : LocalList m) (_hL : NonnegativeList L)
    (d₀ d₁ : ℕ) (E : Finset (Fin m)) (hE:ValidExclusive ξ L d₀ d₁ E)
    (s : unitInterval) :
    let d:=min d₀ d₁
    let p:=EqualCapacity.positiveMarginal ξ d (listBids (remainder L E))
    let S:=Hybrid.NativeEqual.sample m ξ hξ hξ1 d (remainder L E) s
    Finite.Optimal (max d₀ d₁) (fun i=>entryBid (L i)*(1-ξ*p i)) (E∪S) := by
  dsimp only
  let d:=min d₀ d₁
  let B:=remainder L E
  let S:=Hybrid.NativeEqual.sample m ξ hξ hξ1 d B s
  let z:=threshold ξ d (listBids B)
  have hS:=Hybrid.NativeEqual.sample_feasible m ξ hξ hξ1 d B s
  have hd:Disjoint E S := Finset.disjoint_left.mpr (by
    intro i hi hsi
    exact ((remainder_present L E i).mp (hS.2 i hsi)).1 hi)
  have hc:S.card=d := sample_card ξ hξ hξ1 d B s hE.2.2.1
  have hec:(E∪S).card=max d₀ d₁ := by
    rw [Finset.card_union_of_disjoint hd,hE.1,hc]
    dsimp only [d]
    omega
  refine ⟨hec.le,?_⟩
  intro T hT
  apply threshold_optimal _ (E∪S) T z (threshold_nonneg ξ d (listBids B))
    (hT.trans_eq hec.symm)
  · intro i hi
    rcases Finset.mem_union.mp hi with hie | his
    · rw [remainder_marginal_zero ξ d L E i hie]
      simpa only [mul_zero,sub_zero,mul_one] using (hE.2.2.2 i hie).2
    · have hn:=((remainder_present L E i).mp (hS.2 i his)).1
      have hh:=sample_selected_receipt ξ hξ hξ1 d B s i his
      simpa only [B,listBids_eq_entry,remainder_entry,if_neg hn] using hh
  · intro i hi
    have hn:i∉E := fun h=>hi (Finset.mem_union_left S h)
    have hs:i∉S := fun h=>hi (Finset.mem_union_right E h)
    have hh:=sample_unselected_receipt ξ hξ hξ1 d B s i hs
    simpa only [B,listBids_eq_entry,remainder_entry,if_neg hn] using hh

theorem exclusive_small_optimal {m : ℕ} [Nonempty (Fin m)]
    (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (L : LocalList m) (_hL : NonnegativeList L)
    (d₀ d₁ : ℕ) (E : Finset (Fin m)) (hE:ValidExclusive ξ L d₀ d₁ E)
    (s : unitInterval) :
    let d:=min d₀ d₁
    let p:=EqualCapacity.positiveMarginal ξ d (listBids (remainder L E))
    let S:=Hybrid.NativeEqual.sample m ξ hξ hξ1 d (remainder L E) s
    Finite.Optimal d (fun i=>entryBid (L i)*(1-ξ*(if i∈E then 1 else p i))) S := by
  dsimp only
  let d:=min d₀ d₁
  let B:=remainder L E
  let S:=Hybrid.NativeEqual.sample m ξ hξ hξ1 d B s
  let z:=threshold ξ d (listBids B)
  have hS:=Hybrid.NativeEqual.sample_feasible m ξ hξ hξ1 d B s
  have hc:S.card=d := sample_card ξ hξ hξ1 d B s hE.2.2.1
  refine ⟨hc.le,?_⟩
  intro T hT
  apply threshold_optimal _ S T z (threshold_nonneg ξ d (listBids B))
    (hT.trans_eq hc.symm)
  · intro i hi
    have hn:=((remainder_present L E i).mp (hS.2 i hi)).1
    have hh:=sample_selected_receipt ξ hξ hξ1 d B s i hi
    simpa only [B,listBids_eq_entry,remainder_entry,if_neg hn] using hh
  · intro i hi
    by_cases hie:i∈E
    · simp only [if_pos hie,mul_one]
      have hh:=(hE.2.2.2 i hie).1
      dsimp only [z,d,B] at hh ⊢
      nlinarith
    · have hh:=sample_unselected_receipt ξ hξ hξ1 d B s i hi
      simpa only [B,listBids_eq_entry,remainder_entry,if_neg hie] using hh

end FCAppendix.Affine.Uniform07Finishing.Weighted
