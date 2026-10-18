import FCAppendix.Exclusive.MarkerConstructionPolicy

namespace FCAppendix.Exclusive.Marker

open MeasureTheory ProbabilityTheory Game Bayes Set
open scoped BigOperators

variable {m n c : ℕ}

noncomputable def higher (P : Finset (Fin m)) (b : Fin m → ℝ) (i : Fin m) : Finset (Fin m) := by
  classical
  exact P.filter (fun j => b i<b j)

noncomputable def rank (P : Finset (Fin m)) (b : Fin m → ℝ) (i : Fin m) : ℕ :=
  (higher P b i).card

theorem rank_lt_card (P : Finset (Fin m)) (b : Fin m → ℝ) (i : Fin m) (hi : i ∈ P) :
    rank P b i<P.card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _,?_⟩
  intro he
  have hh : i ∈ higher P b i := he.symm ▸ hi
  simp only [higher,Finset.mem_filter,lt_self_iff_false,and_false] at hh

theorem rank_strict (P : Finset (Fin m)) (b : Fin m → ℝ)
    (i j : Fin m) (hj : j ∈ P) (hij : b i<b j) : rank P b j<rank P b i := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro l hl
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hl).1,hij.trans (Finset.mem_filter.mp hl).2⟩
  · intro he
    have hjmem : j ∈ higher P b i := Finset.mem_filter.mpr ⟨hj,hij⟩
    have hh : j ∈ higher P b j := he.symm ▸ hjmem
    simp only [higher,Finset.mem_filter,lt_self_iff_false,and_false] at hh

theorem rank_injective (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hdist : Set.InjOn b P) : Set.InjOn (rank P b) P := by
  intro i hi j hj he
  rcases lt_trichotomy (b i) (b j) with hlt | heq | hgt
  · have hh := rank_strict P b i j hj hlt
    omega
  · exact hdist hi hj heq
  · have hh := rank_strict P b j i hi hgt
    omega

noncomputable def rankLabel (hm : 0 < m) (P : Finset (Fin m))
    (b : Fin m → ℝ) (i : Fin m) : Fin m :=
  ⟨min (rank P b i) (m-1),by omega⟩

theorem rankLabel_val (hm : 0 < m) (P : Finset (Fin m)) (b : Fin m → ℝ)
    (i : Fin m) (hi : i ∈ P) : (rankLabel hm P b i).val=rank P b i := by
  have hcard : P.card ≤ m := by simpa using Finset.card_le_univ P
  have hr := rank_lt_card P b i hi
  exact min_eq_left (by omega)

theorem rankLabel_injective (hm : 0 < m) (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hdist : Set.InjOn b P) : Set.InjOn (rankLabel hm P b) P := by
  intro i hi j hj he
  apply rank_injective P b hdist hi hj
  have hh := congrArg Fin.val he
  simpa only [rankLabel_val hm P b i hi,rankLabel_val hm P b j hj] using hh

noncomputable def rankLabels (N : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => i.val<N)

theorem rankLabels_card (N : ℕ) (hN : N ≤ m) : (rankLabels (m := m) N).card=N := by
  convert card_firstK (Equiv.refl (Fin m)) N hN using 1
  simp [rankLabels,firstK]

theorem rankLabel_mem (hm : 0 < m) (P : Finset (Fin m)) (b : Fin m → ℝ)
    (i : Fin m) (hi : i ∈ P) : rankLabel hm P b i ∈ rankLabels P.card := by
  classical
  simp only [rankLabels,Finset.mem_filter,Finset.mem_univ,true_and,rankLabel_val hm P b i hi]
  exact rank_lt_card P b i hi

noncomputable def sortedBlock (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (P : Finset (Fin m)) (target : Fin m) (b : Fin m → ℝ) (r : Fin n) : Finset (Fin m) := by
  classical
  exact P.filter (fun i => rankLabel hm P b i ∈
    blocks hn hc (rankLabels P.card) (rankLabel hm P b target) r)

theorem sortedBlock_subset (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (P : Finset (Fin m)) (target : Fin m) (b : Fin m → ℝ) (r : Fin n) :
    sortedBlock hm hn hc P target b r ⊆ P := Finset.filter_subset _ _

theorem sortedBlock_capacity (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (P : Finset (Fin m)) (target : Fin m) (b : Fin m → ℝ) (hdist : Set.InjOn b P) (r : Fin n) :
    (sortedBlock hm hn hc P target b r).card≤c := by
  classical
  let Q := blocks hn hc (rankLabels P.card) (rankLabel hm P b target) r
  let f : {i // i ∈ sortedBlock hm hn hc P target b r} → {i // i ∈ Q} :=
    fun i => ⟨rankLabel hm P b i.val,(Finset.mem_filter.mp i.property).2⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    exact rankLabel_injective hm P b hdist
      ((Finset.mem_filter.mp i.property).1) ((Finset.mem_filter.mp j.property).1)
        (congrArg Subtype.val he)
  have hcard := Fintype.card_le_of_injective f hf
  have hcap := blocks_capacity hn hc (rankLabels P.card) (rankLabel hm P b target) r
  have hsmall : (sortedBlock hm hn hc P target b r).card≤Q.card := by
    simpa only [Fintype.card_coe] using hcard
  exact hsmall.trans hcap

theorem sortedBlock_target_rejected (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (P : Finset (Fin m)) (target : Fin m) (b : Fin m → ℝ) :
    target ∉ sortedBlock hm hn hc P target b ⟨0,by omega⟩ := by
  classical
  intro hh
  exact blocks_target_rejected hn hc (rankLabels P.card) (rankLabel hm P b target)
    (Finset.mem_filter.mp hh).2

theorem exists_sorted_partition (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (P : Finset (Fin m)) (hP : P.card≤n*c) (target : Fin m) (htarget : target ∈ P)
    (b : Fin m → ℝ) (hdist : Set.InjOn b P) :
    ∃ Q : Partition P n c, ∀ r, Q.block r=sortedBlock hm hn hc P target b r := by
  classical
  have hcard : P.card ≤ m := by simpa using Finset.card_le_univ P
  have hlabels : (rankLabels (m := m) P.card).card≤n*c := by rw [rankLabels_card _ hcard]; exact hP
  have ht := rankLabel_mem hm P b target htarget
  let R := Classical.choose (exists_partition_target_role_one (rankLabels P.card) hn hc hlabels
    (rankLabel hm P b target) ht)
  have hguard : (rankLabels P.card).card≤n*c ∧ rankLabel hm P b target ∈ rankLabels P.card := ⟨hlabels,ht⟩
  have hblock : ∀ r, blocks hn hc (rankLabels P.card) (rankLabel hm P b target) r=R.block r := by
    intro r
    simp only [blocks,dif_pos hguard]
    rfl
  refine ⟨⟨sortedBlock hm hn hc P target b,sortedBlock_capacity hm hn hc P target b hdist,
    sortedBlock_subset hm hn hc P target b,?_⟩,fun _ => rfl⟩
  intro i hi
  obtain ⟨r,hr,hunique⟩ := R.member (rankLabel hm P b i) (rankLabel_mem hm P b i hi)
  refine ⟨r,?_,?_⟩
  · simp only [sortedBlock,Finset.mem_filter,hi,true_and,hblock]
    exact hr
  · intro s hs
    apply hunique s
    have hh := (Finset.mem_filter.mp hs).2
    simpa only [hblock] using hh

theorem rankLabel_relabel (hm : 0 < m) (e : Equiv.Perm (Fin m))
    (P : Finset (Fin m)) (b : Fin m → ℝ) (i : Fin m) :
    rankLabel hm (P.map e.toEmbedding) (fun j => b (e.symm j)) (e i)=rankLabel hm P b i := by
  classical
  have he : higher (P.map e.toEmbedding) (fun j => b (e.symm j)) (e i)=
      (higher P b i).map e.toEmbedding := by
    ext j
    simp [higher]
  apply Fin.ext
  simp only [rankLabel,rank,he,Finset.card_map]

theorem sortedBlock_relabel (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (e : Equiv.Perm (Fin m)) (P : Finset (Fin m)) (target : Fin m)
    (b : Fin m → ℝ) (r : Fin n) :
    sortedBlock hm hn hc (P.map e.toEmbedding) (e target) (fun j => b (e.symm j)) r=
      (sortedBlock hm hn hc P target b r).map e.toEmbedding := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hj).1
    apply Finset.mem_map.mpr
    refine ⟨i,Finset.mem_filter.mpr ⟨hi,?_⟩,rfl⟩
    simpa only [Finset.card_map,Equiv.toEmbedding_apply,rankLabel_relabel] using (Finset.mem_filter.mp hj).2
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_map.mpr ⟨i,(Finset.mem_filter.mp hi).1,rfl⟩,?_⟩
    simpa only [Finset.card_map,Equiv.toEmbedding_apply,rankLabel_relabel] using (Finset.mem_filter.mp hi).2

theorem rankLabel_injOn_iff (hm : 0 < m) (P : Finset (Fin m)) (b : Fin m → ℝ) :
    Set.InjOn (rankLabel hm P b) P ↔ Set.InjOn b P := by
  constructor
  · intro h i hi j hj he
    apply h hi hj
    apply Fin.ext
    simp only [rankLabel,rank,higher,he]
  · exact rankLabel_injective hm P b

theorem measurable_rankLabel {Ω : Type*} [MeasurableSpace Ω]
    (hm : 0 < m) (P : Finset (Fin m)) (b : Ω → Fin m → ℝ)
    (hb : ∀ i, Measurable (fun ω => b ω i)) (i : Fin m) :
    Measurable (fun ω => rankLabel hm P (b ω) i) := by
  classical
  have hh : Measurable (fun ω => higher P (b ω) i) :=
    measurable_filter P (fun ω j => b ω i<b ω j) (fun j => measurableSet_lt (hb i) (hb j))
  exact (measurable_of_countable (fun S : Finset (Fin m) =>
    (⟨min S.card (m-1),by omega⟩ : Fin m))).comp hh

noncomputable def rankVector (hm : 0 < m) (ℓ : LocalList m) : Fin m → Fin m :=
  rankLabel hm (positives ℓ) (fun i => (ℓ i).getD 0)

theorem measurable_rankVector (hm : 0 < m) : Measurable (rankVector hm : LocalList m → Fin m → Fin m) := by
  apply measurable_pi_iff.mpr
  intro i
  have ht : Measurable (fun z : Finset (Fin m) × LocalList m =>
      rankLabel hm z.1 (fun j => (z.2 j).getD 0) i) :=
    measurable_from_prod_countable_right (fun P => measurable_rankLabel hm P
      (fun (ℓ : LocalList m) j => (ℓ j).getD 0) (fun j => measurable_option_getD.comp (measurable_pi_apply j)) i)
  exact ht.comp (measurable_positives.prodMk measurable_id)

def SourceEligible (hm : 0 < m) (cutoff : ℝ) (ℓ : LocalList m) (n c : ℕ) : Prop :=
  Eligible cutoff ℓ n c ∧ Set.InjOn (rankVector hm ℓ) (positives ℓ)

theorem sourceEligible_iff (hm : 0 < m) (cutoff : ℝ) (ℓ : LocalList m) :
    SourceEligible hm cutoff ℓ n c ↔
      Eligible cutoff ℓ n c ∧ Set.InjOn (fun i => (ℓ i).getD 0) (positives ℓ) := by
  exact and_congr_right fun _ => rankLabel_injOn_iff hm (positives ℓ) (fun i => (ℓ i).getD 0)

theorem measurableSet_sourceEligible (hm : 0 < m) (cutoff : ℝ) :
    MeasurableSet {ℓ : LocalList m | SourceEligible hm cutoff ℓ n c} := by
  have hdistinct : MeasurableSet {ℓ : LocalList m | Set.InjOn (rankVector hm ℓ) (positives ℓ)} :=
    (measurable_positives.prodMk (measurable_rankVector hm))
      (MeasurableSet.of_discrete : MeasurableSet
        {z : Finset (Fin m) × (Fin m → Fin m) | Set.InjOn z.2 z.1})
  exact (measurableSet_eligible cutoff).inter hdistinct

noncomputable def rankSelected (hn : 2 ≤ n) (hc : 0 < c)
    (P T Z : Finset (Fin m)) (L : Fin m → Fin m) : Finset (Fin m) := by
  classical
  exact if h : EligibleCode P T Z n c then
    P.filter (fun i => L i ∈ blocks hn hc (rankLabels P.card)
      (L (targetOfSingleton T h.2.1)) ⟨Z.card,h.2.2⟩)
  else ∅

theorem rankSelected_subset (hn : 2 ≤ n) (hc : 0 < c)
    (P T Z : Finset (Fin m)) (L : Fin m → Fin m) : rankSelected hn hc P T Z L ⊆ P := by
  classical
  unfold rankSelected
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

theorem rankSelected_capacity (hn : 2 ≤ n) (hc : 0 < c)
    (P T Z : Finset (Fin m)) (L : Fin m → Fin m) (hL : Set.InjOn L P) :
    (rankSelected hn hc P T Z L).card≤c := by
  classical
  unfold rankSelected
  split_ifs with h
  · let Q := blocks hn hc (rankLabels P.card) (L (targetOfSingleton T h.2.1)) ⟨Z.card,h.2.2⟩
    let f : {i // i ∈ P.filter (fun i => L i ∈ Q)} → {i // i ∈ Q} :=
      fun i => ⟨L i.val,(Finset.mem_filter.mp i.property).2⟩
    have hf : Function.Injective f := by
      intro i j he
      apply Subtype.ext
      exact hL ((Finset.mem_filter.mp i.property).1) ((Finset.mem_filter.mp j.property).1)
        (congrArg Subtype.val he)
    have hcard := Fintype.card_le_of_injective f hf
    have hh : (P.filter (fun i => L i ∈ Q)).card≤Q.card := by simpa only [Fintype.card_coe] using hcard
    exact hh.trans (blocks_capacity _ _ _ _ _)
  · simp

noncomputable def sourceContinuation {Seed : Type*} (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (cutoff : ℝ) (fallback : LocalPolicy m c Seed) : LocalPolicy m c Seed := by
  classical
  intro ℓ s
  exact if h : SourceEligible hm cutoff ℓ n c then
    ⟨rankSelected hn hc (positives ℓ) (lows cutoff ℓ) (zeros ℓ) (rankVector hm ℓ),
      rankSelected_capacity _ _ _ _ _ _ h.2,
      fun _ hi => positive_visible ℓ (rankSelected_subset _ _ _ _ _ _ hi)⟩
  else fallback ℓ s

theorem measurable_sourceContinuation {Seed : Type*} [MeasurableSpace Seed]
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ) (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val)) :
    Measurable (fun p : LocalList m × Seed => (sourceContinuation hm hn hc cutoff fallback p.1 p.2).val) := by
  classical
  let f := fun z : Finset (Fin m) × Finset (Fin m) × Finset (Fin m) × (Fin m → Fin m) =>
    rankSelected hn hc z.1 z.2.1 z.2.2.1 z.2.2.2
  have hsel : Measurable (fun ℓ : LocalList m =>
      rankSelected hn hc (positives ℓ) (lows cutoff ℓ) (zeros ℓ) (rankVector hm ℓ)) :=
    (measurable_of_countable f).comp
      (measurable_positives.prodMk ((measurable_lows cutoff).prodMk
        (measurable_zeros.prodMk (measurable_rankVector hm))))
  have hh : Measurable (fun p : LocalList m × Seed => if SourceEligible hm cutoff p.1 n c then
      rankSelected hn hc (positives p.1) (lows cutoff p.1) (zeros p.1) (rankVector hm p.1) else
      (fallback p.1 p.2).val) :=
    (hsel.comp measurable_fst).ite
      ((measurableSet_sourceEligible (n := n) (c := c) hm cutoff).preimage measurable_fst) hfallback
  convert hh using 1
  funext p
  simp only [sourceContinuation]
  split_ifs <;> rfl

theorem sourceContinuation_fallback_of_no_low {Seed : Type*}
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ) (fallback : LocalPolicy m c Seed)
    (ℓ : LocalList m) (hzero : lows cutoff ℓ=∅) (s : Seed) :
    sourceContinuation hm hn hc cutoff fallback ℓ s=fallback ℓ s := by
  classical
  have hnot : ¬ SourceEligible hm cutoff ℓ n c := by simp [SourceEligible,Eligible,EligibleCode,hzero]
  simp [sourceContinuation,hnot]

theorem sourceContinuation_fallback_of_tie {Seed : Type*}
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ) (fallback : LocalPolicy m c Seed)
    (ℓ : LocalList m) (htie : ¬ Set.InjOn (fun i => (ℓ i).getD 0) (positives ℓ)) (s : Seed) :
    sourceContinuation hm hn hc cutoff fallback ℓ s=fallback ℓ s := by
  classical
  have hnot : ¬ SourceEligible hm cutoff ℓ n c := by
    rw [sourceEligible_iff]
    exact fun h => htie h.2
  simp [sourceContinuation,hnot]

theorem rankLabel_congr_on (hm : 0 < m) (P : Finset (Fin m)) (b d : Fin m → ℝ)
    (hbd : ∀ i ∈ P, b i=d i) (i : Fin m) (hi : i ∈ P) :
    rankLabel hm P b i=rankLabel hm P d i := by
  classical
  have he : higher P b i=higher P d i := by
    ext j
    by_cases hj : j ∈ P
    · simp [higher,hj,hbd i hi,hbd j hj]
    · simp [higher,hj]
  simp only [rankLabel,rank,he]

theorem sourceContinuation_roleList {Seed : Type*}
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ) (fallback : LocalPolicy m c Seed)
    (P : Finset (Fin m)) (hP : P.card≤n*c) (b : Fin m → ℝ)
    (hb : ∀ i ∈ P, 0 < b i) (hdist : Set.InjOn b P) (M : Markers P n) (r : Fin n)
    (target : Fin m) (htarget : target ∈ P)
    (hsmall : b target<cutoff) (hhigh : ∀ i ∈ P, i≠target → cutoff ≤ b i) (s : Seed) :
    (sourceContinuation hm hn hc cutoff fallback (roleList P b M r) s).val=
      sortedBlock hm hn hc P target b r := by
  classical
  let ℓ := roleList P b M r
  have hpos : positives ℓ=P := positives_roleList P b hb M r
  have hlow : lows cutoff ℓ={target} := lows_roleList P b hb M r cutoff target htarget hsmall hhigh
  have hzero : (zeros ℓ).card=r.val := zero_count_roleList P b hb M r
  have hget : ∀ i ∈ P, (ℓ i).getD 0=b i := by intro i hi; simp [ℓ,roleList,hi]
  have he : Eligible cutoff ℓ n c := by
    simp only [Eligible,EligibleCode,hpos,hlow,Finset.card_singleton,hzero]
    exact ⟨hP,trivial,r.isLt⟩
  have helig : SourceEligible hm cutoff ℓ n c := by
    apply (sourceEligible_iff hm cutoff ℓ).mpr
    refine ⟨he,?_⟩
    rw [hpos]
    intro i hi j hj hij
    apply hdist hi hj
    rw [← hget i hi,← hget j hj]
    exact hij
  have ht : targetOfSingleton (lows cutoff ℓ) he.2.1=target := by
    have hh := singleton_target (lows cutoff ℓ) he.2.1
    have hmem : target ∈ lows cutoff ℓ := by rw [hlow]; simp
    exact (Finset.mem_singleton.mp (hh ▸ hmem)).symm
  have hr : (⟨(zeros ℓ).card,he.2.2⟩ : Fin n)=r := Fin.ext hzero
  have hcongr (i : Fin m) (hi : i ∈ P) :
      rankLabel hm P (fun j => (ℓ j).getD 0) i=rankLabel hm P b i :=
    rankLabel_congr_on hm P _ b hget i hi
  change (sourceContinuation hm hn hc cutoff fallback ℓ s).val=_
  simp only [sourceContinuation,dif_pos helig]
  unfold rankSelected
  have he' : EligibleCode (positives ℓ) (lows cutoff ℓ) (zeros ℓ) n c := he
  rw [dif_pos he',ht,hr]
  ext i
  by_cases hi : i ∈ P
  · simp only [Finset.mem_filter,hpos,hi,true_and,sortedBlock,rankVector]
    simp only [hcongr i hi,hcongr target htarget]
  · simp only [Finset.mem_filter,hpos,hi,false_and,sortedBlock]

theorem sourceContinuation_rejects_role_zero {Seed : Type*}
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ) (fallback : LocalPolicy m c Seed)
    (ℓ : LocalList m) (he : SourceEligible hm cutoff ℓ n c)
    (target : Fin m) (hlow : lows cutoff ℓ={target}) (hZ : zeros ℓ=∅) (s : Seed) :
    target ∉ (sourceContinuation hm hn hc cutoff fallback ℓ s).val := by
  classical
  have ht : targetOfSingleton (lows cutoff ℓ) he.1.2.1=target := by
    have hh := singleton_target (lows cutoff ℓ) he.1.2.1
    have hmem : target ∈ lows cutoff ℓ := by rw [hlow]; simp
    exact (Finset.mem_singleton.mp (hh ▸ hmem)).symm
  have hr : (⟨(zeros ℓ).card,he.1.2.2⟩ : Fin n)=⟨0,by omega⟩ := by simp [hZ]
  change target ∉ (if h : SourceEligible hm cutoff ℓ n c then _ else fallback ℓ s).val
  rw [dif_pos he]
  change target ∉ rankSelected hn hc (positives ℓ) (lows cutoff ℓ) (zeros ℓ) (rankVector hm ℓ)
  unfold rankSelected
  have he' : EligibleCode (positives ℓ) (lows cutoff ℓ) (zeros ℓ) n c := he.1
  rw [dif_pos he',ht,hr]
  intro hh
  exact blocks_target_rejected hn hc (rankLabels (positives ℓ).card) (rankVector hm ℓ target)
    (Finset.mem_filter.mp hh).2

end FCAppendix.Exclusive.Marker
