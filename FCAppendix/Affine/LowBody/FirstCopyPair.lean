import FCAppendix.Affine.LowBody.PureTemplateCrossing
import FCAppendix.Affine.LowBody.RowServiceBounds

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace PureTemplate

lemma measurable_selection (T : PureTemplate ι) (κ : ℝ) : Measurable (T.selection κ) := by
  have hm:=FiniteSelector.measurable_select
    (fun (b : ι → ℝ) (P : T.Candidate)=>CompleteInformation.potential κ b P.val.1 P.val.2)
    (fun P=>(continuous_potential κ P.val).measurable)
  exact measurable_subtype_coe.comp hm

lemma left_optimal_of_right_zero (T : PureTemplate ι) (κ : ℝ) (b : ι → ℝ)
    (hzero : T.residual₁=0) (hz : ∀i,i∉T.support  →  b i=0) :
    Finite.Optimal T.residual₀ b (T.selection κ b).1 := by
  have hf:=T.selection_feasible κ b
  have he:=T.selection_empty_right κ b hzero
  refine ⟨hf.1,?_⟩
  intro A hA
  have hm:=(T.selection_nash κ b).1 (A∩T.support)
    ((Finset.card_le_card Finset.inter_subset_left).trans hA) Finset.inter_subset_right
  simp only [CompleteInformation.revenue,he,Finset.notMem_empty,if_false] at hm
  have hs : (∑i∈A∩T.support,b i)=∑i∈A,b i :=
    Finset.sum_subset Finset.inter_subset_left (fun i hi hni=>hz i
      (fun hs=>hni (Finset.mem_inter.mpr ⟨hi,hs⟩)))
  rwa [hs] at hm

end PureTemplate

def pairRestAbove (u : ℝ) (i j : ι) (b : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun k=>k≠i ∧ k≠j ∧ u < b k)

theorem lower_pair_excluded (T : PureTemplate ι) (κ : ℝ) (b : ι → ℝ)
    (hzero : T.residual₁=0) (hz : ∀k,k∉T.support  →  b k=0)
    (i j : ι) (_hij : i≠j) (u : ℝ) (hiu : b i ≤ u) (hijb : b i < b j)
    (hcount : T.residual₀-1 ≤ (pairRestAbove u i j b).card) :
    i∉(T.selection κ b).1 := by
  have hopt:=T.left_optimal_of_right_zero κ b hzero hz
  apply Finite.excluded_of_many_better T.residual₀ b _ hopt i
  have hjnot : j∉pairRestAbove u i j b := by simp [pairRestAbove]
  have hsub : insert j (pairRestAbove u i j b)⊆Finset.univ.filter (fun k=>b i < b k) := by
    intro k hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ k,?_⟩
    rcases Finset.mem_insert.mp hk with hkj | hkrest
    · exact hkj ▸ hijb
    · exact hiu.trans_lt (Finset.mem_filter.mp hkrest).2.2.2
  have hc:=Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hjnot] at hc
  omega

def pairBids (b : ι → ℝ) (i j : ι) (x y : ℝ) : ι → ℝ :=
  Function.update (Function.update b i x) j y

omit [Fintype ι] in
lemma continuous_pairBids (b : ι → ℝ) (i j : ι) :
    Continuous (fun p : ℝ×ℝ=>pairBids b i j p.1 p.2) := by
  apply continuous_pi
  intro k
  by_cases hkj : k=j
  · subst k
    simp only [pairBids,Function.update_self]
    fun_prop
  · by_cases hki : k=i
    · subst k
      simp only [pairBids,Function.update_of_ne hkj,Function.update_self]
      fun_prop
    · simp only [pairBids,Function.update_of_ne hkj,Function.update_of_ne hki]
      exact continuous_const

lemma pairRestAbove_pairBids (u : ℝ) (i j : ι) (b : ι → ℝ) (x y : ℝ) :
    pairRestAbove u i j (pairBids b i j x y)=pairRestAbove u i j b := by
  ext k
  by_cases hki : k=i  <;> by_cases hkj : k=j  <;>
    simp [pairRestAbove,pairBids,hki,hkj]

theorem cross_above_cluster_included (T : PureTemplate ι) (κ : ℝ) (b : ι → ℝ)
    (hzero : T.residual₁=0) (hz : ∀k,k∉T.support → b k=0)
    (i : ι) (hi : i∈T.support) (u x : ℝ) (hux : u < x) (hx : 0 < x)
    (hcount : (Finset.univ.filter (fun k=>k≠i ∧ u < b k)).card < T.residual₀) :
    i∈(T.selection κ (Function.update b i x)).1 := by
  have hz' (k : ι) (hk : k∉T.support) : Function.update b i x k=0 := by
    have hki : k≠i:=fun he=>hk (he ▸ hi)
    rw [Function.update_of_ne hki,hz k hk]
  have hopt:=T.left_optimal_of_right_zero κ (Function.update b i x) hzero hz'
  apply Finite.included_of_few_competitors T.residual₀ _ _ hopt i
    (by simpa only [Function.update_self] using hx)
  have hsub : Finset.univ.filter (fun k=>k≠i ∧
      Function.update b i x i ≤ Function.update b i x k) ⊆
      Finset.univ.filter (fun k=>k≠i ∧ u < b k) := by
    intro k hk
    obtain ⟨_,hki,hk⟩:=Finset.mem_filter.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ k,hki,?_⟩
    rw [Function.update_self,Function.update_of_ne hki] at hk
    exact hux.trans_le hk
  exact (Finset.card_le_card hsub).trans_lt hcount

theorem purePayoff_cross_above_cluster (T : PureTemplate ι) (κ w : ℝ) (b : ι → ℝ)
    (hzero : T.residual₁=0) (hz : ∀k,k∉T.support → b k=0)
    (i : ι) (hi : i∈T.support) (u x : ℝ) (hux : u < x) (hx : 0 < x)
    (hcount : (Finset.univ.filter (fun k=>k≠i ∧ u < b k)).card < T.residual₀) :
    purePayoff κ w (Function.update b i x) (T.selection κ (Function.update b i x)) i=w-x := by
  have hmem:=cross_above_cluster_included T κ b hzero hz i hi u x hux hx hcount
  have hempty:=T.selection_empty_right κ (Function.update b i x) hzero
  simp [purePayoff,focalCopy,hempty,hmem]

theorem firstCopy_crossing_gain (T : PureTemplate ι) (κ w : ℝ) (b : ι → ℝ)
    (hzero : T.residual₁=0) (hz : ∀k,k∉T.support → b k=0)
    (i : ι) (hi : i∈T.support) (l u x surplus : ℝ)
    (hl : l ≤ b i) (hux : u < x) (hx : 0 < x) (hsurplus : surplus ≤ w-b i)
    (hcount : (Finset.univ.filter (fun k=>k≠i ∧ u < b k)).card < T.residual₀) :
    (if i∉(T.selection κ b).1 then surplus else 0)-(x-l) ≤
      purePayoff κ w (Function.update b i x) (T.selection κ (Function.update b i x)) i-
        purePayoff κ w b (T.selection κ b) i := by
  classical
  rw [purePayoff_cross_above_cluster T κ w b hzero hz i hi u x hux hx hcount]
  have hempty:=T.selection_empty_right κ b hzero
  by_cases hmem : i∈(T.selection κ b).1
  · simp [purePayoff,focalCopy,hempty,hmem,Fin.ext_iff]; linarith
  · simp [purePayoff,focalCopy,hempty,hmem,Fin.ext_iff]; linarith

lemma iid_pair_strict_order_le_half (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (μ.prod μ).real {p : ℝ×ℝ | p.1 < p.2} ≤ 1/2 := by
  let A : Set (ℝ×ℝ):={p | p.1 < p.2}
  let B : Set (ℝ×ℝ):={p | p.2 < p.1}
  have hA : MeasurableSet A:=measurableSet_lt measurable_fst measurable_snd
  have hB : MeasurableSet B:=measurableSet_lt measurable_snd measurable_fst
  have he:=congrArg (fun ν : Measure (ℝ×ℝ)=>ν A) (Measure.prod_swap (μ:=μ) (ν:=μ))
  rw [Measure.map_apply measurable_swap hA] at he
  have hAB : (μ.prod μ).real A=(μ.prod μ).real B := by
    simpa only [Measure.real,A,B,preimage_setOf_eq,Prod.fst_swap,Prod.snd_swap] using
      (congrArg ENNReal.toReal he).symm
  have hd : Disjoint A B:=Set.disjoint_left.mpr (fun p ha hb=>lt_asymm (show p.1 < p.2 from ha) (show p.2 < p.1 from hb))
  have hh:=(measureReal_le_one (μ:=μ.prod μ) (s:=A∪B))
  rw [measureReal_union hd hB,hAB] at hh
  change (μ.prod μ).real A ≤ 1/2
  linarith

lemma iid_pair_weak_order_le_half (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : (μ.prod μ).real {p : ℝ×ℝ | p.1 ≤ p.2} ≤ 1/2 := by
  have hne : ∀ᵐp : ℝ×ℝ ∂μ.prod μ,p.1≠p.2 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun measurable_fst measurable_snd).compl)).mpr
    exact Eventually.of_forall (fun x=>(μ.ae_ne x).mono (fun _ h=>Ne.symm h))
  have he : {p : ℝ×ℝ | p.1 ≤ p.2}=ᵐ[μ.prod μ]{p : ℝ×ℝ | p.1 < p.2} := by
    filter_upwards [hne] with p hp
    exact propext (le_iff_lt_or_eq.trans (or_iff_left hp))
  rw [measureReal_congr he]
  exact iid_pair_strict_order_le_half μ

theorem pair_rejection_probability_ge_half (T : PureTemplate ι) (κ : ℝ)
    (b : ι → ℝ) (i j : ι) (hij : i≠j) (hi : i∈T.support) (hj : j∈T.support)
    (hzero : T.residual₁=0) (hz : ∀k,k∉T.support  →  b k=0)
    (u : ℝ) (hcount : T.residual₀-1 ≤ (pairRestAbove u i j b).card)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hμ : ∀ᵐx ∂μ,x ≤ u) :
    1/2 ≤ (μ.prod μ).real {p : ℝ×ℝ | i∉(T.selection κ (pairBids b i j p.1 p.2)).1} := by
  classical
  let A : Set (ℝ×ℝ):={p | i∈(T.selection κ (pairBids b i j p.1 p.2)).1}
  have hA : MeasurableSet A :=
    (((measurable_of_countable (fun P : Finset ι × Finset ι=>i∈P.1)).comp
      ((T.measurable_selection κ).comp (continuous_pairBids b i j).measurable))).setOf
  have hx : ∀ᵐp : ℝ×ℝ ∂μ.prod μ,p.1 ≤ u :=
    (measurePreserving_fst (μ:=μ) (ν:=μ)).quasiMeasurePreserving.ae hμ
  have hsub : A ≤ᵐ[μ.prod μ]{p : ℝ×ℝ | p.2 ≤ p.1} := by
    filter_upwards [hx] with p hp hmem
    by_contra hn
    have hlt : p.1 < p.2:=lt_of_not_ge hn
    have hzero' (k : ι) (hk : k∉T.support) : pairBids b i j p.1 p.2 k=0 := by
      have hki : k≠i:=fun he=>hk (he ▸ hi)
      have hkj : k≠j:=fun he=>hk (he ▸ hj)
      simp only [pairBids,Function.update_of_ne hkj,Function.update_of_ne hki,hz k hk]
    have he:=lower_pair_excluded T κ (pairBids b i j p.1 p.2) hzero hzero' i j hij u
      (by simpa [pairBids,Function.update_of_ne hij] using hp)
      (by simpa [pairBids,Function.update_of_ne hij] using hlt)
      (by simpa only [pairRestAbove_pairBids] using hcount)
    exact he hmem
  have hprob : (μ.prod μ).real A ≤ 1/2 := by
    apply (ENNReal.toReal_mono (measure_ne_top (μ.prod μ) _)
      (measure_mono_ae hsub)).trans
    have hh:=iid_pair_weak_order_le_half μ
    have he:=congrArg (fun ν : Measure (ℝ×ℝ)=>ν {p | p.1 ≤ p.2})
      (Measure.prod_swap (μ:=μ) (ν:=μ))
    rw [Measure.map_apply measurable_swap (measurableSet_le measurable_fst measurable_snd)] at he
    have heReal : (μ.prod μ).real {p : ℝ×ℝ | p.2 ≤ p.1}=
        (μ.prod μ).real {p : ℝ×ℝ | p.1 ≤ p.2} := congrArg ENNReal.toReal he
    change (μ.prod μ).real {p : ℝ×ℝ | p.2 ≤ p.1} ≤ 1/2
    rw [heReal]
    exact hh
  have hc:=measureReal_compl (μ:=μ.prod μ) hA
  change 1/2 ≤ (μ.prod μ).real Aᶜ
  rw [hc]
  simp only [probReal_univ]
  linarith

end FCAppendix.Affine.LowBody
