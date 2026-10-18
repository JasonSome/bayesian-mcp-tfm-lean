import FCAppendix.Exclusive.MarkerConstruction

namespace FCAppendix.Exclusive.Marker

open MeasureTheory ProbabilityTheory Game Bayes Set
open scoped BigOperators

variable {m n c : ℕ}

theorem measurable_option_getD : Measurable (fun b : Option ℝ => b.getD 0) := by
  intro S hS
  change MeasurableSet S
  exact hS

noncomputable def positives (ℓ : LocalList m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => 0<(ℓ i).getD 0)

noncomputable def lows (cutoff : ℝ) (ℓ : LocalList m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => 0<(ℓ i).getD 0 ∧ (ℓ i).getD 0<cutoff)

theorem measurable_positives : Measurable (positives : LocalList m → Finset (Fin m)) := by
  classical
  exact measurable_filter Finset.univ (fun (ℓ : LocalList m) i => 0<(ℓ i).getD 0)
    (fun i => measurableSet_lt measurable_const (measurable_option_getD.comp (measurable_pi_apply i)))

theorem measurable_lows (cutoff : ℝ) : Measurable (lows cutoff : LocalList m → Finset (Fin m)) := by
  classical
  apply measurable_filter Finset.univ
  intro i
  exact (measurableSet_lt measurable_const
    (measurable_option_getD.comp (measurable_pi_apply i))).inter
      (measurableSet_lt (measurable_option_getD.comp (measurable_pi_apply i)) measurable_const)

theorem lows_subset_positives (cutoff : ℝ) (ℓ : LocalList m) :
    lows cutoff ℓ ⊆ positives ℓ := by
  classical
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.1⟩

theorem positive_visible (ℓ : LocalList m) {i : Fin m} (hi : i ∈ positives ℓ) : ℓ i≠none := by
  classical
  intro hn
  have hp := (Finset.mem_filter.mp hi).2
  simp [hn] at hp

noncomputable def blocks (hn : 2 ≤ n) (hc : 0 < c)
    (P : Finset (Fin m)) (target : Fin m) (r : Fin n) : Finset (Fin m) := by
  classical
  exact if h : P.card≤n*c ∧ target ∈ P then
    (Classical.choose (exists_partition_target_role_one P hn hc h.1 target h.2)).block r
  else ∅

theorem blocks_capacity (hn : 2 ≤ n) (hc : 0 < c)
    (P : Finset (Fin m)) (target : Fin m) (r : Fin n) :
    (blocks hn hc P target r).card≤c := by
  classical
  unfold blocks
  split_ifs with h
  · exact (Classical.choose (exists_partition_target_role_one P hn hc h.1 target h.2)).capacity r
  · simp

theorem blocks_subset (hn : 2 ≤ n) (hc : 0 < c)
    (P : Finset (Fin m)) (target : Fin m) (r : Fin n) :
    blocks hn hc P target r ⊆ P := by
  classical
  unfold blocks
  split_ifs with h
  · exact (Classical.choose (exists_partition_target_role_one P hn hc h.1 target h.2)).subset r
  · exact Finset.empty_subset _

theorem blocks_target_rejected (hn : 2 ≤ n) (hc : 0 < c)
    (P : Finset (Fin m)) (target : Fin m) :
    target ∉ blocks hn hc P target ⟨0,by omega⟩ := by
  classical
  unfold blocks
  split_ifs with h
  · exact (Classical.choose_spec (exists_partition_target_role_one P hn hc h.1 target h.2)).2
  · simp

def EligibleCode (P T Z : Finset (Fin m)) (n c : ℕ) : Prop :=
  P.card≤n*c ∧ T.card=1 ∧ Z.card<n

noncomputable def targetOfSingleton (T : Finset (Fin m)) (hT : T.card=1) : Fin m :=
  Classical.choose (Finset.card_eq_one.mp hT)

theorem singleton_target (T : Finset (Fin m)) (hT : T.card=1) :
    T={targetOfSingleton T hT} := Classical.choose_spec (Finset.card_eq_one.mp hT)

theorem targetOfSingleton_eq (target : Fin m) (hT : ({target} : Finset (Fin m)).card=1) :
    targetOfSingleton {target} hT=target := by
  have hh := singleton_target {target} hT
  simpa only [Finset.singleton_inj] using hh.symm

noncomputable def selectedBlock (hn : 2 ≤ n) (hc : 0 < c)
    (P T Z : Finset (Fin m)) : Finset (Fin m) := by
  classical
  exact if h : EligibleCode P T Z n c then
    blocks hn hc P (targetOfSingleton T h.2.1) ⟨Z.card,h.2.2⟩ else ∅

theorem selectedBlock_capacity (hn : 2 ≤ n) (hc : 0 < c)
    (P T Z : Finset (Fin m)) : (selectedBlock hn hc P T Z).card≤c := by
  classical
  unfold selectedBlock
  split_ifs
  · exact blocks_capacity _ _ _ _ _
  · simp

theorem selectedBlock_subset (hn : 2 ≤ n) (hc : 0 < c)
    (P T Z : Finset (Fin m)) : selectedBlock hn hc P T Z ⊆ P := by
  classical
  unfold selectedBlock
  split_ifs
  · exact blocks_subset _ _ _ _ _
  · exact Finset.empty_subset _

def Eligible (cutoff : ℝ) (ℓ : LocalList m) (n c : ℕ) : Prop :=
  EligibleCode (positives ℓ) (lows cutoff ℓ) (zeros ℓ) n c

theorem measurableSet_eligible (cutoff : ℝ) :
    MeasurableSet {ℓ : LocalList m | Eligible cutoff ℓ n c} := by
  have hm : Measurable (fun ℓ : LocalList m => (positives ℓ,(lows cutoff ℓ,zeros ℓ))) :=
    measurable_positives.prodMk ((measurable_lows cutoff).prodMk measurable_zeros)
  exact hm (MeasurableSet.of_discrete : MeasurableSet
    {z : Finset (Fin m) × Finset (Fin m) × Finset (Fin m) | EligibleCode z.1 z.2.1 z.2.2 n c})

noncomputable def continuation {Seed : Type*} (hn : 2 ≤ n) (hc : 0 < c)
    (cutoff : ℝ) (fallback : LocalPolicy m c Seed) : LocalPolicy m c Seed := by
  classical
  intro ℓ s
  exact if Eligible cutoff ℓ n c then
    ⟨selectedBlock hn hc (positives ℓ) (lows cutoff ℓ) (zeros ℓ),
      selectedBlock_capacity _ _ _ _ _,fun _ hi => positive_visible ℓ
        (selectedBlock_subset hn hc _ _ _ hi)⟩
  else fallback ℓ s

theorem measurable_continuation {Seed : Type*} [MeasurableSpace Seed]
    (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ) (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val)) :
    Measurable (fun p : LocalList m × Seed => (continuation hn hc cutoff fallback p.1 p.2).val) := by
  classical
  let f := fun z : Finset (Fin m) × Finset (Fin m) × Finset (Fin m) => selectedBlock hn hc z.1 z.2.1 z.2.2
  have hsel : Measurable (fun ℓ : LocalList m => selectedBlock hn hc
      (positives ℓ) (lows cutoff ℓ) (zeros ℓ)) :=
    (measurable_of_countable f).comp
      (measurable_positives.prodMk ((measurable_lows cutoff).prodMk measurable_zeros))
  have hh : Measurable (fun p : LocalList m × Seed => if Eligible cutoff p.1 n c then
      selectedBlock hn hc (positives p.1) (lows cutoff p.1) (zeros p.1) else
      (fallback p.1 p.2).val) :=
    (hsel.comp measurable_fst).ite
      ((measurableSet_eligible (n := n) (c := c) cutoff).preimage measurable_fst) hfallback
  convert hh using 1
  funext p
  simp only [continuation]
  split_ifs <;> rfl

theorem continuation_fallback_of_no_low {Seed : Type*} (hn : 2 ≤ n) (hc : 0 < c)
    (cutoff : ℝ) (fallback : LocalPolicy m c Seed) (ℓ : LocalList m)
    (hzero : lows cutoff ℓ=∅) (s : Seed) :
    continuation hn hc cutoff fallback ℓ s=fallback ℓ s := by
  classical
  have hnot : ¬ Eligible cutoff ℓ n c := by simp [Eligible,EligibleCode,hzero]
  simp [continuation,hnot]

theorem continuation_rejects_role_zero {Seed : Type*} (hn : 2 ≤ n) (hc : 0 < c)
    (cutoff : ℝ) (fallback : LocalPolicy m c Seed) (ℓ : LocalList m)
    (target : Fin m) (hlow : lows cutoff ℓ={target})
    (hP : (positives ℓ).card≤n*c) (hZ : zeros ℓ=∅) (s : Seed) :
    target ∉ (continuation hn hc cutoff fallback ℓ s).val := by
  classical
  have he : Eligible cutoff ℓ n c := by simp [Eligible,EligibleCode,hlow,hP,hZ]; omega
  have ht : targetOfSingleton (lows cutoff ℓ) he.2.1=target := by
    have hh := singleton_target (lows cutoff ℓ) he.2.1
    have hmem : target ∈ lows cutoff ℓ := by rw [hlow]; simp
    exact (Finset.mem_singleton.mp (hh ▸ hmem)).symm
  have hr : (⟨(zeros ℓ).card,he.2.2⟩ : Fin n)=⟨0,by omega⟩ := by simp [hZ]
  change target ∉ (if Eligible cutoff ℓ n c then _ else fallback ℓ s).val
  rw [if_pos he]
  change target ∉ selectedBlock hn hc (positives ℓ) (lows cutoff ℓ) (zeros ℓ)
  unfold selectedBlock
  have he' : EligibleCode (positives ℓ) (lows cutoff ℓ) (zeros ℓ) n c := he
  rw [dif_pos he',ht,hr]
  exact blocks_target_rejected hn hc (positives ℓ) target

theorem positives_roleList (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hb : ∀ i ∈ P, 0 < b i) (M : Markers P n) (r : Fin n) :
    positives (roleList P b M r)=P := by
  classical
  ext i
  by_cases hi : i ∈ P
  · simp [positives,roleList,hi,hb i hi]
  · simp only [positives,Finset.mem_filter,Finset.mem_univ,true_and,
      roleList,hi,if_false]
    split_ifs <;> simp

theorem lows_roleList (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hb : ∀ i ∈ P, 0 < b i) (M : Markers P n) (r : Fin n)
    (cutoff : ℝ) (target : Fin m) (htarget : target ∈ P)
    (hsmall : b target<cutoff) (hhigh : ∀ i ∈ P, i≠target → cutoff ≤ b i) :
    lows cutoff (roleList P b M r)={target} := by
  classical
  ext i
  by_cases hi : i ∈ P
  · by_cases he : i=target
    · subst i
      simp [lows,roleList,htarget,hb target htarget,hsmall]
    · have hh := hhigh i hi he
      simp [lows,roleList,hi,not_lt.mpr hh,he]
  · have hit : i≠target := fun h => hi (h ▸ htarget)
    simp only [lows,Finset.mem_filter,Finset.mem_univ,true_and,
      roleList,hi,if_false,Finset.mem_singleton]
    split_ifs <;> simp [hit]

theorem continuation_roleList {Seed : Type*} (hn : 2 ≤ n) (hc : 0 < c)
    (cutoff : ℝ) (fallback : LocalPolicy m c Seed)
    (P : Finset (Fin m)) (hP : P.card≤n*c) (b : Fin m → ℝ)
    (hb : ∀ i ∈ P, 0 < b i) (M : Markers P n) (r : Fin n)
    (target : Fin m) (htarget : target ∈ P)
    (hsmall : b target<cutoff) (hhigh : ∀ i ∈ P, i≠target → cutoff ≤ b i) (s : Seed) :
    (continuation hn hc cutoff fallback (roleList P b M r) s).val=
      blocks hn hc P target r := by
  classical
  have hpos := positives_roleList P b hb M r
  have hlow := lows_roleList P b hb M r cutoff target htarget hsmall hhigh
  have hzero := zero_count_roleList P b hb M r
  have helig : Eligible cutoff (roleList P b M r) n c := by
    simp only [Eligible,EligibleCode,hpos,hlow,Finset.card_singleton,hzero]
    exact ⟨hP,trivial,r.isLt⟩
  have ht : targetOfSingleton (lows cutoff (roleList P b M r)) helig.2.1=target := by
    have hh := singleton_target (lows cutoff (roleList P b M r)) helig.2.1
    have hmem : target ∈ lows cutoff (roleList P b M r) := by rw [hlow]; simp
    exact (Finset.mem_singleton.mp (hh ▸ hmem)).symm
  have hr : (⟨(zeros (roleList P b M r)).card,helig.2.2⟩ : Fin n)=r := Fin.ext hzero
  simp only [continuation,if_pos helig]
  unfold selectedBlock
  have he : EligibleCode (positives (roleList P b M r)) (lows cutoff (roleList P b M r))
      (zeros (roleList P b M r)) n c := helig
  rw [dif_pos he,ht,hr,hpos]

end FCAppendix.Exclusive.Marker
