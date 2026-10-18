import FCAppendix.Exclusive.OnceBayes
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Rev

namespace FCAppendix.Exclusive.Marker

open MeasureTheory ProbabilityTheory Game Bayes Finite Set
open scoped BigOperators

variable {m n c : ℕ}

structure Partition (P : Finset (Fin m)) (n c : ℕ) where
  block : Fin n → Finset (Fin m)
  capacity : ∀ r, (block r).card ≤ c
  subset : ∀ r, block r ⊆ P
  member : ∀ i ∈ P, ∃! r, i ∈ block r

theorem exists_partition_target_role_one (P : Finset (Fin m))
    (hn : 2 ≤ n) (hc : 0 < c) (hP : P.card ≤ n*c)
    (target : Fin m) (htarget : target ∈ P) :
    ∃ Q : Partition P n c,
      target ∈ Q.block ⟨1,hn⟩ ∧ target ∉ Q.block ⟨0,by omega⟩ := by
  classical
  have hcard : Fintype.card P ≤ Fintype.card (Fin n × Fin c) := by simpa using hP
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let t : P := ⟨target,htarget⟩
  let slot : Fin n × Fin c := (⟨1,hn⟩,⟨0,hc⟩)
  let f : P ↪ Fin n × Fin c := e.trans (Equiv.swap (e t) slot).toEmbedding
  have hf : f t = slot := by simp [f,slot]
  let owner := fun i : Fin m => if hi : i ∈ P then (f ⟨i,hi⟩).1 else ⟨0,by omega⟩
  let block := fun r : Fin n => P.filter (fun i => owner i = r)
  have hcap : ∀ r, (block r).card ≤ c := by
    intro r
    let g : {i // i ∈ block r} → Fin c := fun i => (f ⟨i.val,(Finset.mem_filter.mp i.property).1⟩).2
    have hg : Function.Injective g := by
      intro i j he
      have hi := (Finset.mem_filter.mp i.property).2
      have hj := (Finset.mem_filter.mp j.property).2
      simp only [owner,dif_pos (Finset.mem_filter.mp i.property).1] at hi
      simp only [owner,dif_pos (Finset.mem_filter.mp j.property).1] at hj
      have hpair : f ⟨i.val,(Finset.mem_filter.mp i.property).1⟩ =
          f ⟨j.val,(Finset.mem_filter.mp j.property).1⟩ :=
        Prod.ext (hi.trans hj.symm) he
      exact Subtype.ext (congrArg (fun z : P => (z : Fin m)) (f.injective hpair))
    have hh := Fintype.card_le_of_injective g hg
    simpa using hh
  have hmember : ∀ i ∈ P, ∃! r, i ∈ block r := by
    intro i hi
    refine ⟨owner i,by simp [block,hi],?_⟩
    intro r hr
    exact (Finset.mem_filter.mp hr).2.symm
  refine ⟨⟨block,hcap,fun _ => Finset.filter_subset _ _,hmember⟩,?_,?_⟩
  · change target ∈ block ⟨1,hn⟩
    simp only [block,Finset.mem_filter,htarget,true_and,owner]
    exact congrArg Prod.fst hf
  · change target ∉ block ⟨0,by omega⟩
    simp only [block,Finset.mem_filter,htarget,true_and,owner]
    intro hz
    have := (congrArg Prod.fst hf).symm.trans hz
    have := congrArg Fin.val this
    simp only [slot] at this
    omega

structure Markers (P : Finset (Fin m)) (n : ℕ) where
  identity : Fin (n-1) ↪ Fin m
  outside : ∀ l, identity l ∉ P

theorem exists_markers (P : Finset (Fin m)) (hroom : n-1 ≤ m-P.card) :
    Nonempty (Markers P n) := by
  classical
  have hcard : Fintype.card (Fin (n-1)) ≤ Fintype.card {i : Fin m // i ∉ P} := by
    simpa [Fintype.card_subtype_compl] using hroom
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨⟨e.trans (Function.Embedding.subtype _),fun l => (e l).property⟩⟩

theorem exists_markers_extending (P Z : Finset (Fin m))
    (hdis : Disjoint P Z) (hZ : Z.card<n) (hroom : n-1 ≤ m-P.card) :
    ∃ M : Markers P n,
      ∀ i, (∃ l : Fin (n-1), M.identity l=i ∧ l.val<Z.card) ↔ i ∈ Z := by
  classical
  let r := Z.card
  let s := n-1-r
  let R := (P ∪ Z)ᶜ
  have hR : R.card=m-(P.card+r) := by
    change ((P ∪ Z)ᶜ).card=m-(P.card+r)
    rw [Finset.card_compl,Finset.card_union_of_disjoint hdis]
    simp only [Fintype.card_fin,r]
  have hrest : Fintype.card (Fin s) ≤ Fintype.card R := by
    simp only [Fintype.card_fin,Fintype.card_coe,hR]
    dsimp only [s,r]
    omega
  obtain ⟨rest⟩ := Function.Embedding.nonempty_of_card_le hrest
  let seen : Fin r ≃ Z := (Fintype.equivFinOfCardEq (Fintype.card_coe Z)).symm
  let f : Fin (n-1) → Fin m := fun l =>
    if hl : l.val<r then (seen ⟨l.val,hl⟩).val
    else (rest ⟨l.val-r,by have := l.isLt; omega⟩).val
  have f_seen (l : Fin (n-1)) (hl : l.val<r) : f l ∈ Z := by
    simp only [f,dif_pos hl]
    exact (seen ⟨l.val,hl⟩).property
  have f_rest (l : Fin (n-1)) (hl : ¬l.val<r) : f l ∈ R := by
    simp only [f,dif_neg hl]
    exact (rest ⟨l.val-r,by have := l.isLt; omega⟩).property
  have hf : Function.Injective f := by
    intro l q he
    by_cases hl : l.val<r <;> by_cases hq : q.val<r
    · simp only [f,dif_pos hl,dif_pos hq] at he
      have hpair : seen ⟨l.val,hl⟩=seen ⟨q.val,hq⟩ := Subtype.ext he
      exact Fin.ext (congrArg (fun z : Fin r => z.val) (seen.injective hpair))
    · have hz := f_seen l hl
      have hr := f_rest q hq
      rw [← he] at hr
      exact ((Finset.mem_compl.mp hr) (Finset.mem_union.mpr (Or.inr hz))).elim
    · have hz := f_seen q hq
      have hr := f_rest l hl
      rw [he] at hr
      exact ((Finset.mem_compl.mp hr) (Finset.mem_union.mpr (Or.inr hz))).elim
    · simp only [f,dif_neg hl,dif_neg hq] at he
      have hpair : rest ⟨l.val-r,by have := l.isLt; omega⟩=
          rest ⟨q.val-r,by have := q.isLt; omega⟩ := Subtype.ext he
      have hh : l.val-r=q.val-r := congrArg (fun z : Fin s => z.val) (rest.injective hpair)
      apply Fin.ext
      omega
  have hout : ∀ l, f l ∉ P := by
    intro l
    by_cases hl : l.val<r
    · exact fun hi => Finset.disjoint_left.mp hdis hi (f_seen l hl)
    · have hr := f_rest l hl
      exact fun hi => (Finset.mem_compl.mp hr) (Finset.mem_union.mpr (Or.inl hi))
  refine ⟨⟨⟨f,hf⟩,hout⟩,?_⟩
  intro i
  constructor
  · rintro ⟨l,hl,hr⟩
    exact hl ▸ f_seen l hr
  · intro hi
    let l₀ : Fin r := seen.symm ⟨i,hi⟩
    let l : Fin (n-1) := ⟨l₀.val,by have := l₀.isLt; dsimp [r] at *; omega⟩
    refine ⟨l,?_,l₀.isLt⟩
    change f l=i
    have hl : l.val<r := l₀.isLt
    simp only [f,dif_pos hl]
    change (seen l₀).val=i
    exact congrArg Subtype.val (seen.apply_symm_apply ⟨i,hi⟩)

noncomputable def roleList (P : Finset (Fin m)) (b : Fin m → ℝ)
    (M : Markers P n) (r : Fin n) : LocalList m := by
  classical
  exact fun i => if i ∈ P then some (b i)
    else if ∃ l : Fin (n-1), M.identity l=i ∧ l.val<r.val then some 0 else none

noncomputable def world (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hb : ∀ i ∈ P, 0 ≤ b i) (M : Markers P n) (roles : Equiv.Perm (Fin n)) :
    UserProfile m n := by
  classical
  exact fun i => if hi : i ∈ P then
      ((0,⟨b i,hb i hi,n,le_rfl⟩),Equiv.refl _)
    else if hmarker : ∃ l, M.identity l=i then
      let l := Classical.choose hmarker
      ((0,⟨0,le_rfl,n-(l.val+1),Nat.sub_le _ _⟩),roles.trans Fin.revPerm)
    else ((0,⟨0,le_rfl,0,Nat.zero_le _⟩),Equiv.refl _)

theorem observe_world (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hb : ∀ i ∈ P, 0 ≤ b i) (M : Markers P n) (roles : Equiv.Perm (Fin n))
    (j : Fin n) :
    observe (drawsRealization (world P b hb M roles)) j=roleList P b M (roles j) := by
  classical
  funext i
  by_cases hi : i ∈ P
  · simp [world,hi,observe,drawsRealization,roleList,mem_firstK]
  · by_cases hm : ∃ l, M.identity l=i
    · let l := Classical.choose hm
      have hli : M.identity l=i := Classical.choose_spec hm
      have huniq : ∀ z, M.identity z=i ↔ z=l := by
        intro z
        exact ⟨fun hz => M.identity.injective (hz.trans hli.symm),fun hz => hz ▸ hli⟩
      have hroute : j ∈ firstK (roles.trans Fin.revPerm) (n-(l.val+1)) ↔ l.val<(roles j).val := by
        rw [mem_firstK]
        simp only [Equiv.trans_apply,Fin.revPerm_apply,Fin.val_rev]
        have hj := (roles j).isLt
        have hl := l.isLt
        omega
      simp only [observe,drawsRealization,world,hi,hm,dif_pos]
      change (if j ∈ firstK (roles.trans Fin.revPerm) (n-(l.val+1)) then some (0:ℝ) else none)=_
      simp [hroute,roleList,hi,huniq]
    · have hnone : ¬ ∃ l : Fin (n-1), M.identity l=i ∧ l.val<(roles j).val := by
        rintro ⟨l,hl,_⟩
        exact hm ⟨l,hl⟩
      simp [world,hi,hm,observe,drawsRealization,roleList,mem_firstK,hnone]

theorem roleList_feasible (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hb : ∀ i ∈ P, 0 ≤ b i) (M : Markers P n) (j r : Fin n) :
    FeasibleObservedList j (roleList P b M r) := by
  refine ⟨world P b hb M (Equiv.swap j r),?_⟩
  simpa using observe_world P b hb M (Equiv.swap j r) j

theorem exists_world_for_list (P Z : Finset (Fin m)) (b : Fin m → ℝ)
    (hb : ∀ i ∈ P, 0 ≤ b i) (hdis : Disjoint P Z) (hZ : Z.card<n)
    (hroom : n-1 ≤ m-P.card) (j : Fin n) (ℓ : LocalList m)
    (hℓ : ∀ i, ℓ i=if i ∈ P then some (b i) else if i ∈ Z then some 0 else none) :
    ∃ (M : Markers P n) (roles : Equiv.Perm (Fin n)),
      (roles j).val=Z.card ∧
      observe (drawsRealization (world P b hb M roles)) j=ℓ := by
  classical
  obtain ⟨M,hM⟩ := exists_markers_extending P Z hdis hZ hroom
  let r : Fin n := ⟨Z.card,hZ⟩
  have he : roleList P b M r=ℓ := by
    funext i
    rw [hℓ i]
    by_cases hi : i ∈ P
    · simp [roleList,hi]
    · simp only [roleList,hi,if_false]
      have hm : (∃ l : Fin (n-1), M.identity l=i ∧ l.val<r.val) ↔ i ∈ Z := hM i
      simp only [hm]
  refine ⟨M,Equiv.swap j r,by simp [r],?_⟩
  simpa only [observe_world,Equiv.swap_apply_left] using he

noncomputable def zeros (ℓ : LocalList m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => ℓ i=some 0)

theorem zeros_roleList (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hb : ∀ i ∈ P, 0 < b i) (M : Markers P n) (r : Fin n) :
    zeros (roleList P b M r)=
      (Finset.univ.filter (fun l : Fin (n-1) => l.val<r.val)).map M.identity := by
  classical
  ext i
  simp only [zeros,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
  by_cases hi : i ∈ P
  · have hnot : ¬∃ a : Fin (n-1), a.val<r.val ∧ M.identity a=i := by
      rintro ⟨a,_ha,hid⟩
      exact M.outside a (hid.symm ▸ hi)
    simp [roleList,hi,(hb i hi).ne',hnot]
  · simp [roleList,hi,and_comm]

theorem zero_count_roleList (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hb : ∀ i ∈ P, 0 < b i) (M : Markers P n) (r : Fin n) :
    (zeros (roleList P b M r)).card=r.val := by
  classical
  rw [zeros_roleList P b hb M r,Finset.card_map]
  convert card_firstK (Equiv.refl (Fin (n-1))) r.val (by have := r.isLt; omega) using 1
  simp [firstK]

theorem measurable_filter {Ω : Type*} [MeasurableSpace Ω]
    (s : Finset (Fin m)) (p : Ω → Fin m → Prop) [∀ ω, DecidablePred (p ω)]
    (hp : ∀ i, MeasurableSet {ω | p ω i}) :
    Measurable (fun ω => s.filter (p ω)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.filter_empty] using (measurable_const : Measurable (fun _ : Ω => (∅ : Finset (Fin m))))
  | @insert a s ha ih =>
    have hin : Measurable (fun ω => insert a (s.filter (p ω))) :=
      (measurable_of_countable (fun S : Finset (Fin m) => insert a S)).comp ih
    simpa only [Finset.filter_insert] using hin.ite (hp a) ih

theorem measurable_zeros : Measurable (zeros : LocalList m → Finset (Fin m)) := by
  classical
  exact measurable_filter Finset.univ (fun (ℓ : LocalList m) i => ℓ i=some (0:ℝ))
    (fun i => measurableSet_eq_fun (measurable_pi_apply i) measurable_const)

noncomputable def visible (ℓ : LocalList m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => ℓ i≠none)

theorem measurable_visible : Measurable (visible : LocalList m → Finset (Fin m)) := by
  classical
  exact measurable_filter Finset.univ (fun (ℓ : LocalList m) i => ℓ i≠none)
    (fun i => (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).compl)

noncomputable def rolePolicy (P : Finset (Fin m)) (Q : Partition P n c)
    (hn : 0 < n) : LocalPolicy m c Unit := by
  classical
  intro ℓ _
  let r : Fin n := ⟨min (zeros ℓ).card (n-1),by omega⟩
  exact ⟨(Q.block r).filter (fun i => ℓ i≠none),
    (Finset.card_filter_le _ _).trans (Q.capacity r),
    fun _ hi => (Finset.mem_filter.mp hi).2⟩

theorem measurable_rolePolicy (P : Finset (Fin m)) (Q : Partition P n c)
    (hn : 0 < n) :
    Measurable (fun p : LocalList m × Unit => (rolePolicy P Q hn p.1 p.2).val) := by
  classical
  let f := fun Z V : Finset (Fin m) =>
    (Q.block ⟨min Z.card (n-1),by omega⟩) ∩ V
  have hf : Measurable (Function.uncurry f) := measurable_of_countable _
  convert hf.comp ((measurable_zeros.comp measurable_fst).prodMk
    (measurable_visible.comp measurable_fst)) using 1
  funext p
  ext i
  simp [rolePolicy,f,visible]

theorem rolePolicy_roleList (P : Finset (Fin m)) (Q : Partition P n c)
    (b : Fin m → ℝ) (hb : ∀ i ∈ P, 0 < b i) (M : Markers P n)
    (hn : 0 < n) (r : Fin n) :
    (rolePolicy P Q hn (roleList P b M r) ()).val=Q.block r := by
  classical
  have hr : min (zeros (roleList P b M r)).card (n-1)=r.val := by
    rw [zero_count_roleList P b hb M r,min_eq_left (by have := r.isLt; omega)]
  change (Q.block ⟨min (zeros (roleList P b M r)).card (n-1),_⟩).filter _=Q.block r
  have he : (⟨min (zeros (roleList P b M r)).card (n-1),by omega⟩ : Fin n)=r := Fin.ext hr
  simp only [he]
  apply Finset.filter_eq_self.mpr
  intro i hi
  simp [roleList,Q.subset r hi]

theorem Partition.role_unique (P : Finset (Fin m)) (Q : Partition P n c)
    {i : Fin m} {r s : Fin n} (hr : i ∈ Q.block r) (hs : i ∈ Q.block s) : r=s := by
  obtain ⟨u,_hu,hunique⟩ := Q.member i (Q.subset r hr)
  exact (hunique r hr).trans (hunique s hs).symm

theorem rolePolicy_world_inclusion (P : Finset (Fin m)) (Q : Partition P n c)
    (b : Fin m → ℝ) (hb : ∀ i ∈ P, 0 < b i) (M : Markers P n)
    (hn : 0 < n) (roles : Equiv.Perm (Fin n)) (seed : Fin n → Unit)
    (j : Fin n) :
    allocation (drawsRealization (world P b (fun i hi => (hb i hi).le) M roles))
      (fun _ => rolePolicy P Q hn) seed j=Q.block (roles j) := by
  rw [allocation,observe_world]
  exact rolePolicy_roleList P Q b hb M hn (roles j)

theorem no_other_iff_assigned {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (P : Finset (Fin m)) (Q : Partition P n c)
    (b : Fin m → ℝ) (hb : ∀ i ∈ P, 0 < b i) (M : Markers P n)
    (roles : Equiv.Perm (Fin n))
    (hpolicy : ∀ j s, (Γ.policy j (roleList P b M (roles j)) s).val=Q.block (roles j))
    (j : Fin n) (i : Fin m) (hi : i ∈ P) (s : Fin n → Seed) :
    (otherInclusionCount Γ j i (world P b (fun i hi => (hb i hi).le) M roles,s)).val=0 ↔
      i ∈ Q.block (roles j) := by
  classical
  have halloc (l : Fin n) : allocation
      (drawsRealization (world P b (fun i hi => (hb i hi).le) M roles)) Γ.policy s l=Q.block (roles l) := by
    rw [allocation,observe_world]
    exact hpolicy l (s l)
  change ((Finset.univ.erase j).filter (fun l => i ∈ allocation
    (drawsRealization (world P b (fun i hi => (hb i hi).le) M roles)) Γ.policy s l)).card=0 ↔ _
  simp_rw [halloc]
  rw [Finset.card_eq_zero]
  constructor
  · intro hz
    obtain ⟨r,hr,_⟩ := Q.member i hi
    by_contra hnot
    have hne : roles.symm r ≠ j := by
      intro he
      have he' : r=roles j := by simpa using congrArg roles he
      exact hnot (he' ▸ hr)
    have hmem : roles.symm r ∈ (Finset.univ.erase j).filter (fun l => i ∈ Q.block (roles l)) := by
      simp [hne,hr]
    simp only [hz,Finset.notMem_empty] at hmem
  · intro hj
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    have hlj := (Finset.mem_erase.mp (Finset.mem_filter.mp hl).1).1
    have hir := (Finset.mem_filter.mp hl).2
    exact hlj (roles.injective (Partition.role_unique P Q hir hj))

theorem assigned_block_optimal (P : Finset (Fin m)) (Q : Partition P n c)
    (b : Fin m → ℝ) (hb : ∀ i ∈ P, 0 ≤ b i) (r : Fin n) :
    Optimal c (fun i => if i ∈ Q.block r then b i else 0) (Q.block r) := by
  classical
  refine ⟨Q.capacity r,?_⟩
  intro T _hT
  calc
    (∑ i ∈ T, if i ∈ Q.block r then b i else 0)=∑ i ∈ T ∩ Q.block r, b i := by
      simp only [Finset.sum_ite_mem]
    _ ≤ ∑ i ∈ Q.block r, b i := Finset.sum_le_sum_of_subset_of_nonneg
      Finset.inter_subset_right (fun i hi _ => hb i (Q.subset r hi))
    _ = ∑ i ∈ Q.block r, if i ∈ Q.block r then b i else 0 := by simp

theorem no_other_probability_at_world {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (P : Finset (Fin m)) (Q : Partition P n c)
    (b : Fin m → ℝ) (hb : ∀ i ∈ P, 0 < b i) (M : Markers P n)
    (roles : Equiv.Perm (Fin n))
    (hpolicy : ∀ j s, (Γ.policy j (roleList P b M (roles j)) s).val=Q.block (roles j))
    (j : Fin n)
    (hpost : B.posterior j (roleList P b M (roles j))=
      Measure.dirac (world P b (fun i hi => (hb i hi).le) M roles))
    (i : Fin m) (hi : i ∈ P) :
    noOtherProb Γ B j (roleList P b M (roles j)) i=
      if i ∈ Q.block (roles j) then 1 else 0 := by
  classical
  let f := fun ω : Background m n Seed =>
    if (otherInclusionCount Γ j i ω).val=0 then (1:ℝ) else 0
  have hf : Measurable f :=
    (measurable_of_countable (fun r : Fin n => if r.val=0 then (1:ℝ) else 0)).comp
      (measurable_otherInclusionCount Γ j i)
  rw [noOtherProb_eq_integral]
  change ∫ ω, f ω ∂posteriorBackground Γ B j (roleList P b M (roles j))=_
  rw [posteriorBackground,hpost,Measure.dirac_prod,
    integral_map_of_stronglyMeasurable measurable_prodMk_left hf.stronglyMeasurable]
  have he : ∀ s : Fin n → Seed,
      f (world P b (fun i hi => (hb i hi).le) M roles,s)=
        if i ∈ Q.block (roles j) then 1 else 0 := by
    intro s
    simp only [f,no_other_iff_assigned Γ P Q b hb M roles hpolicy j i hi s]
  simp_rw [he]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem receipts_at_world {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (P : Finset (Fin m)) (Q : Partition P n c)
    (b : Fin m → ℝ) (hb : ∀ i ∈ P, 0 < b i) (M : Markers P n)
    (roles : Equiv.Perm (Fin n))
    (hpolicy : ∀ j s, (Γ.policy j (roleList P b M (roles j)) s).val=Q.block (roles j))
    (j : Fin n)
    (hpost : B.posterior j (roleList P b M (roles j))=
      Measure.dirac (world P b (fun i hi => (hb i hi).le) M roles)) :
    exclusiveReceipts (posteriorCountBelief Γ B j (roleList P b M (roles j)))
      (roleList P b M (roles j))=
        fun i => if i ∈ Q.block (roles j) then b i else 0 := by
  classical
  funext i
  by_cases hi : i ∈ P
  · have hreceipt := no_other_probability_at_world Γ B P Q b hb M roles hpolicy j hpost i hi
    change (posteriorCountBelief Γ B j (roleList P b M (roles j)) i).prob (fun r => r.val=0)=_ at hreceipt
    simp only [exclusiveReceipts,roleList,hi,if_pos]
    rw [hreceipt]
    split_ifs <;> simp
  · have hnot : i ∉ Q.block (roles j) := fun h => hi (Q.subset (roles j) h)
    simp only [exclusiveReceipts,roleList,hi,if_false,hnot]
    split_ifs <;> simp

theorem optimal_at_world {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (P : Finset (Fin m)) (Q : Partition P n c)
    (b : Fin m → ℝ) (hb : ∀ i ∈ P, 0 < b i) (M : Markers P n)
    (roles : Equiv.Perm (Fin n))
    (hpolicy : ∀ j s, (Γ.policy j (roleList P b M (roles j)) s).val=Q.block (roles j))
    (j : Fin n)
    (hpost : B.posterior j (roleList P b M (roles j))=
      Measure.dirac (world P b (fun i hi => (hb i hi).le) M roles)) (s : Seed) :
    Optimal c (exclusiveReceipts (posteriorCountBelief Γ B j (roleList P b M (roles j)))
      (roleList P b M (roles j))) (Γ.policy j (roleList P b M (roles j)) s).val := by
  rw [hpolicy j s,receipts_at_world Γ B P Q b hb M roles hpolicy j hpost]
  exact assigned_block_optimal P Q b (fun i hi => (hb i hi).le) (roles j)

end FCAppendix.Exclusive.Marker
