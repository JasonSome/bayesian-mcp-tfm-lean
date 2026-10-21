import FCAppendix.Affine.Hybrid.NativeSeed
import FCAppendix.Affine.TaggedLocalInformation

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Bayes Game Set

def minOption : Option ℝ → Option ℝ → Option ℝ
  | none,b=>b
  | a,none=>a
  | some a,some b=>some (min a b)

lemma minOption_none (a b : Option ℝ) : minOption a b=none ↔ a=none ∧ b=none := by
  cases a <;> cases b <;> simp [minOption]

def allAbove (t : ℝ) : Option ℝ → Prop
  | none=>True
  | some b=>t<b

lemma minOption_allAbove (a b : Option ℝ) (t : ℝ) :
    allAbove t (minOption a b) ↔ allAbove t a ∧ allAbove t b := by
  cases a <;> cases b <;> simp [allAbove,minOption]

lemma measurable_isSome_real : Measurable (fun o : Option ℝ=>o.isSome) := by
  intro S hS
  change MeasurableSet ((fun _ : ℝ=>true) ⁻¹' S)
  exact measurable_const hS

lemma measurable_getD_zero : Measurable (fun o : Option ℝ=>o.getD 0) := by
  intro S hS
  change MeasurableSet S
  exact hS

lemma measurable_minOption : Measurable (Function.uncurry minOption) := by
  have he : Function.uncurry minOption=(fun x : Option ℝ × Option ℝ=>
      if x.1.isSome=true then
        if x.2.isSome=true then some (min (x.1.getD 0) (x.2.getD 0)) else x.1 else x.2) := by
    funext x
    rcases x with ⟨a,b⟩
    cases a <;> cases b <;> rfl
  rw [he]
  exact Measurable.ite
    (measurableSet_eq_fun (measurable_isSome_real.comp measurable_fst) measurable_const)
    (Measurable.ite
      (measurableSet_eq_fun (measurable_isSome_real.comp measurable_snd) measurable_const)
      (measurable_some.comp ((measurable_getD_zero.comp measurable_fst).min
        (measurable_getD_zero.comp measurable_snd))) measurable_fst) measurable_snd

def scanMinimum {ι : Type*} (ids : List ι) (L : ι → Option ℝ) : Option ℝ :=
  match ids with
  | []=>none
  | i::rest=>minOption (L i) (scanMinimum rest L)

lemma measurable_scanMinimum {ι : Type*} (ids : List ι) :
    Measurable (scanMinimum ids) := by
  induction ids with
  | nil=>exact measurable_const
  | cons i rest ih=>exact measurable_minOption.comp ((measurable_pi_apply i).prodMk ih)

lemma scanMinimum_none {ι : Type*} (ids : List ι) (L : ι → Option ℝ) :
    scanMinimum ids L=none ↔ ∀i∈ids,L i=none := by
  induction ids with
  | nil=>simp [scanMinimum]
  | cons i rest ih=>simp [scanMinimum,minOption_none,ih]

lemma scanMinimum_allAbove {ι : Type*} (ids : List ι) (L : ι → Option ℝ) (t : ℝ) :
    allAbove t (scanMinimum ids L) ↔ ∀i∈ids,allAbove t (L i) := by
  induction ids with
  | nil=>simp [scanMinimum,allAbove]
  | cons i rest ih=>simp [scanMinimum,minOption_allAbove,ih]

def localMinimum {m : ℕ} (L : LocalList m) : Option ℝ := scanMinimum (List.finRange m) L

lemma measurable_localMinimum {m : ℕ} : Measurable (localMinimum (m:=m)) :=
  measurable_scanMinimum _

def visibleCount {m : ℕ} (L : LocalList m) : ℕ :=
  (Finset.univ.filter (fun i=>L i≠none)).card

lemma measurable_visibleCount {m : ℕ} : Measurable (visibleCount (m:=m)) := by
  have he (L : LocalList m) : visibleCount L=∑i : Fin m,if L i≠none then 1 else 0 := by
    unfold visibleCount
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  have hm : Measurable (fun L : LocalList m=>∑i : Fin m,if L i≠none then (1:ℕ) else 0) := by
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).compl
      measurable_const measurable_const
  convert hm using 1
  funext L
  exact he L

def seedOnList {m : ℕ} (μ : Measure ℝ) (L : LocalList m) : Option unitInterval :=
  (localMinimum L).map (cdfUnit (minimumLaw μ (visibleCount L-1)))

lemma measurable_option_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α→β) (hf : Measurable f) : Measurable (Option.map f) := by
  intro S hS
  change MeasurableSet (f ⁻¹' (some ⁻¹' S))
  exact hf (measurable_some hS)

set_option maxHeartbeats 2000000 in
lemma measurable_seedOnList {m : ℕ} (μ : Measure ℝ) : Measurable (seedOnList (m:=m) μ) := by
  have hcount (n : ℕ) : Measurable (fun y : Option ℝ=>
      y.map (cdfUnit (minimumLaw μ (n-1)))) :=
    measurable_option_map _ (measurable_cdfUnit _)
  have hm : Measurable (fun x : ℕ × Option ℝ=>
      x.2.map (cdfUnit (minimumLaw μ (x.1-1)))) :=
    measurable_from_prod_countable_right hcount
  change Measurable ((fun x : ℕ × Option ℝ=>
    x.2.map (cdfUnit (minimumLaw μ (x.1-1)))) ∘
      (fun L : LocalList m=>(visibleCount L,localMinimum L)))
  exact hm.comp ((measurable_visibleCount (m:=m)).prodMk (measurable_localMinimum (m:=m)))

@[simp] lemma seedOnList_empty {m : ℕ} (μ : Measure ℝ) :
    seedOnList μ (fun _ : Fin m=>none)=none := by
  unfold seedOnList
  have hnone : localMinimum (fun _ : Fin m=>none)=none :=
    (scanMinimum_none _ _).mpr (by simp)
  rw [hnone]
  rfl

theorem localMinimum_enumeration {m n : ℕ} (p : Fin m → Prop) [DecidablePred p]
    (e : Fin (n+1) ≃ Subtype p) (b : Fin m → ℝ)
    (L : LocalList m) (hL : ∀i,L i=if p i then some (b i) else none) :
    localMinimum L=some (minBid n (fun j=>b (e j))) := by
  have hnotnone : localMinimum L≠none := by
    intro hn
    have h := (scanMinimum_none (List.finRange m) L).mp hn (e 0) (by simp)
    rw [hL (e 0),if_pos (e 0).property] at h
    exact Option.some_ne_none _ h
  cases hmin : localMinimum L with
  | none=>exact False.elim (hnotnone hmin)
  | some v=>
    have ht (t : ℝ) : t<v ↔ t < minBid n (fun j=>b (e j)) := by
      have hscan := scanMinimum_allAbove (List.finRange m) L t
      change allAbove t (localMinimum L) ↔ _ at hscan
      rw [hmin] at hscan
      change (t<v ↔ _) at hscan
      rw [lt_minBid_iff]
      constructor
      · intro hv j
        have hh := hscan.mp hv (e j) (by simp)
        simpa only [hL (e j),if_pos (e j).property,allAbove] using hh
      · intro hall
        apply hscan.mpr
        intro i _
        by_cases hi : p i
        · obtain ⟨j,hj⟩ := e.surjective ⟨i,hi⟩
          have hval : (e j).val=i := congrArg Subtype.val hj
          simpa only [hL i,if_pos hi,allAbove, hval] using hall j
        · simp only [hL i,if_neg hi,allAbove]
    have heq : v=minBid n (fun j=>b (e j)) := by
      rcases lt_trichotomy v (minBid n (fun j=>b (e j))) with hlt | heq | hgt
      · exact False.elim (lt_irrefl v ((ht v).mpr hlt))
      · exact heq
      · exact False.elim (lt_irrefl _ ((ht _).mp hgt))
    exact congrArg some heq

lemma visibleCount_enumeration {m n : ℕ} (p : Fin m → Prop) [DecidablePred p]
    (e : Fin (n+1) ≃ Subtype p) (b : Fin m → ℝ)
    (L : LocalList m) (hL : ∀i,L i=if p i then some (b i) else none) :
    visibleCount L=n+1 := by
  have hfilter : Finset.univ.filter (fun i=>L i≠none)=Finset.univ.filter p := by
    ext i
    by_cases hi : p i <;> simp [hL i,hi]
  have hc := Fintype.card_congr e
  simp only [Fintype.card_fin,Fintype.card_subtype] at hc
  simpa only [visibleCount,hfilter] using hc.symm

theorem seedOnList_enumeration {m n : ℕ} (μ : Measure ℝ)
    (p : Fin m → Prop) [DecidablePred p] (e : Fin (n+1) ≃ Subtype p) (b : Fin m → ℝ)
    (L : LocalList m) (hL : ∀i,L i=if p i then some (b i) else none) :
    seedOnList μ L=some (conditionalMinimumSeed μ n (fun j=>b (e j))) := by
  rw [seedOnList,localMinimum_enumeration p e b L hL,visibleCount_enumeration p e b L hL]
  simp only [Nat.add_sub_cancel,Option.map_some,conditionalMinimumSeed]

def observedLowSeed {m : ℕ} (d U : ℝ) (μ : Measure ℝ) (L : LocalList m) : Option unitInterval :=
  seedOnList μ (TaggedLocal.lowList d U L)

lemma measurable_observedLowSeed {m : ℕ} (d U : ℝ) (μ : Measure ℝ) :
    Measurable (observedLowSeed (m:=m) d U μ) :=
  (measurable_seedOnList μ).comp (TaggedLocal.measurable_lowList d U)

theorem observedLowSeed_actual {m n : ℕ} {d U : ℝ} (μ : Measure ℝ)
    (kind : Fin m → Fin 3) (x : Realization m 2) (hdU : d≤U)
    (hb : TaggedLocal.BidBoxes kind x d U) (hr : TaggedLocal.ClassRoutes kind x)
    (e : Fin (n+1) ≃ {i : Fin m // kind i=0}) (j : Fin 2) :
    observedLowSeed d U μ (observe x j)=
      some (conditionalMinimumSeed μ n (fun l=>(x.action (e l)).bid)) := by
  unfold observedLowSeed
  have hlow := TaggedLocal.lowList_observe kind x hdU hb hr j
  apply seedOnList_enumeration μ (fun i=>kind i=0) e (fun i=>(x.action i).bid)
  intro i
  exact congrFun hlow i

theorem observedLowSeed_native_joint {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : Bayes.FiniteGame m 2 c Seed)
    (tag : Bayes.UserDraw 2 → Fin 3) (htag : Measurable tag)
    (k : Fin m → Fin 3) (hmass : ∀i,Bayes.userLaw Γ (tag ⁻¹' {k i})≠0)
    (n : ℕ) (e : Fin (n+1) ≃ {i : Fin m // k i=0})
    (hnoatoms : ∀b : ℝ,
      ((cond (Bayes.userLaw Γ) (tag ⁻¹' {0})).map
        (fun u : Bayes.UserDraw 2=>u.1.2.bid)) {b}=0)
    {d U : ℝ} (hdU : d≤U)
    (hshape : ∀ᵐx ∂cond (Bayes.backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ),
      TaggedLocal.BidBoxes k (Bayes.drawsRealization x.1) d U ∧
        TaggedLocal.ClassRoutes k (Bayes.drawsRealization x.1)) (j : Fin 2) :
    (cond (Bayes.backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ)).map
      (fun x=>(observedLowSeed d U
          ((cond (Bayes.userLaw Γ) (tag ⁻¹' {0})).map
            (fun u : Bayes.UserDraw 2=>u.1.2.bid))
          (observe (Bayes.drawsRealization x.1) j),
        ((fun i : {i : Fin m // k i≠0}=>x.1 i),x.2))) =
      ((volume : Measure unitInterval).map some).prod
        ((Measure.pi (fun i : {i : Fin m // k i≠0}=>
          cond (Bayes.userLaw Γ) (tag ⁻¹' {k i}))).prod
            (Measure.pi (fun _ : Fin 2=>Γ.seedLaw))) := by
  let μB := (cond (Bayes.userLaw Γ) (tag ⁻¹' {0})).map
    (fun u : Bayes.UserDraw 2=>u.1.2.bid)
  let rest := (Measure.pi (fun i : {i : Fin m // k i≠0}=>
    cond (Bayes.userLaw Γ) (tag ⁻¹' {k i}))).prod
      (Measure.pi (fun _ : Fin 2=>Γ.seedLaw))
  let f : Bayes.Background m 2 Seed →
      unitInterval × (({i : Fin m // k i≠0}→Bayes.UserDraw 2) × (Fin 2→Seed)) :=
    fun x=>(conditionalMinimumSeed μB n (fun l=>(x.1 (e l)).1.2.bid),
      ((fun i=>x.1 i),x.2))
  have hf : Measurable f :=
    ((measurable_conditionalMinimumSeed μB n).comp (measurable_pi_lambda _
      (fun l=>((Game.measurable_bid 2).comp
        ((measurable_pi_apply ((e l):Fin m)).comp measurable_fst).fst.snd)))).prodMk
      ((measurable_pi_lambda _
        (fun i : {i : Fin m // k i≠0}=>(measurable_pi_apply (i:Fin m)).comp measurable_fst)).prodMk
          measurable_snd)
  have hlaw := native_background_minimum_seed Γ tag htag k 0 hmass n e hnoatoms
  change (cond (Bayes.backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ)).map _=
    ((volume : Measure unitInterval).map some).prod rest
  calc
    _ = (cond (Bayes.backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ)).map
        ((Prod.map some id) ∘ f) := by
      apply Measure.map_congr
      filter_upwards [hshape] with x hx
      apply Prod.ext
      · exact observedLowSeed_actual μB k (Bayes.drawsRealization x.1) hdU hx.1 hx.2 e j
      · rfl
    _ = ((cond (Bayes.backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ)).map f).map
        (Prod.map some id) :=
      (Measure.map_map (measurable_some.prodMap measurable_id) hf).symm
    _ = ((volume : Measure unitInterval).prod rest).map (Prod.map some id) := by rw [hlaw]
    _ = _ := by rw [←Measure.map_prod_map _ _ measurable_some measurable_id,Measure.map_id]

end FCAppendix.Affine.Hybrid
