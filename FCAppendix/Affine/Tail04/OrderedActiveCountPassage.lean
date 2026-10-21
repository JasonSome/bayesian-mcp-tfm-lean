import FCAppendix.Affine.Tail04.OrderedSourceActiveSpecified
import FCAppendix.Affine.Tail04.FixedValueLimit

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedActiveCountPassage
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open OriginalValues SourceMenuIdentity ParametricMenuCount

variable (P : ValueParameters) (ξ B : ℝ)

theorem conditional_neighborhood (v : ℝ) (lam : ℝ×ℝ) (ls : ℕ→ℝ×ℝ)
    (hls : Tendsto ls atTop (𝓝 lam))
    (U : ℕ→ℝ) (_hU : ∀j,1≤ U j) (hUB : ∀j,U j≤ B)
    (σ : ℕ→ Measure (JointAction 2)) (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0))
    (b : Icc (1:ℝ) B)
    (hb : ∀a : Icc (1:ℝ) B,a≠b→ menuUtility P ξ lam.1 lam.2 v a< menuUtility P ξ lam.1 lam.2 v b)
    (hfeasible : ∀ᶠj in atTop,(b:ℝ)≤ U j)
    (hregret : ∀ᶠj in atTop,∀ᵐa ∂σ j,a.routeCount=2 ∧ a.bid∈Icc (1:ℝ) (U j) ∧
      ∀y : Icc (1:ℝ) (U j),menuUtility P ξ (ls j).1 (ls j).2 v y≤
        menuUtility P ξ (ls j).1 (ls j).2 v a.bid+e j)
    (δ : ℝ) (hδ : 0< δ) :
    ∀ᶠj in atTop,∀ᵐa ∂σ j,a.routeCount=2 ∧ a.bid∈Icc (1:ℝ) B ∧ |a.bid-(b:ℝ)|< δ := by
  let F:=utilityMap P ξ B v lam
  let Fs:=fun j=> utilityMap P ξ B v (ls j)
  let d:=fun j=>‖Fs j-F‖
  have hd : Tendsto d atTop (𝓝 0) := by
    have hh:=(((continuous_utilityMap P ξ B v).tendsto lam).comp hls).sub (tendsto_const_nhds (x:=F))
    simpa only [d,Fs,F,Function.comp_apply,sub_self,norm_zero] using hh.norm
  obtain ⟨γ,hγ,hgap⟩:=FixedValues.compact_strict_maximum_gap F F.continuous b hb δ hδ
  have hlim : Tendsto (fun j=>2*d j+e j) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using ((hd.const_mul 2).add he)
  have hsmall:=hlim.eventually_le_const hγ
  filter_upwards [hregret,hfeasible,hsmall] with j hj hf hjg
  filter_upwards [hj] with a ha
  let a' : Icc (1:ℝ) B:=⟨a.bid,ha.2.1.1,ha.2.1.2.trans (hUB j)⟩
  let b' : Icc (1:ℝ) (U j):=⟨b,b.2.1,hf⟩
  have hac : |Fs j a'-F a'|≤ d j := by
    simpa only [ContinuousMap.sub_apply,Real.norm_eq_abs,d] using
      (Fs j-F).norm_coe_le_norm a'
  have hbc : |Fs j b-F b|≤ d j := by
    simpa only [ContinuousMap.sub_apply,Real.norm_eq_abs,d] using
      (Fs j-F).norm_coe_le_norm b
  have hic:=ha.2.2 b'
  have hr : F b≤ F a'+γ := by
    change Fs j b≤ Fs j a'+e j at hic
    linarith [(abs_le.mp hac).2,(abs_le.mp hbc).1]
  exact ⟨ha.1,a'.2,by simpa only [Subtype.dist_eq,Real.dist_eq,a'] using hgap a' hr⟩

theorem native_count_tendsto
    (m c : ℕ→ℕ) (Seed : ℕ→ Type*) [∀j,MeasurableSpace (Seed j)]
    (G : ∀j,FiniteGame (m j) 2 (c j) (Seed j)) (hm : ∀j,0< m j)
    (v : ℝ) (lam : ℝ×ℝ) (ls : ℕ→ℝ×ℝ) (hls : Tendsto ls atTop (𝓝 lam))
    (b : Icc (1:ℝ) B) (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0))
    (hnear : ∀δ,0< δ→∀ᶠj in atTop,∀ᵐa ∂(G j).σ v,
      a.routeCount=2 ∧ a.bid∈Icc (1:ℝ) B ∧ |a.bid-(b:ℝ)|< δ)
    (r : Fin 3)
    (hcount : ∀ᶠj in atTop,∀i,∀ᵐa ∂(G j).σ v,
      |((problem (G j) i).outcome a).mass r-(law P ξ (ls j) a.bid).mass r|≤ e j) :
    Tendsto (fun j=>(conditionalTypeCountLaw (G j) (hm j) v).mass r)
      atTop (𝓝 ((law P ξ lam b).mass r)) := by
  let g:=massMap P ξ B r lam
  let gs:=fun j=> massMap P ξ B r (ls j)
  let d:=fun j=>‖gs j-g‖
  have hd : Tendsto d atTop (𝓝 0) := by
    have hh:=(((continuous_massMap P ξ B r).tendsto lam).comp hls).sub (tendsto_const_nhds (x:=g))
    simpa only [d,gs,g,Function.comp_apply,sub_self,norm_zero] using hh.norm
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδg⟩:=Metric.continuousAt_iff.mp g.continuous.continuousAt
    (ε/4) (by positivity)
  filter_upwards [hnear δ hδ,hcount,he.eventually_le_const (by positivity : 0< ε/4),
    hd.eventually_le_const (by positivity : 0< ε/4)] with j hj hc hej hdj
  have hall : ∀i,∀ᵐa ∂(G j).σ v,
      |((problem (G j) i).outcome a).mass r-(law P ξ lam b).mass r|≤5*ε/6 := by
    intro i
    filter_upwards [hj,hc i] with a ha hca
    let a' : Icc (1:ℝ) B:=⟨a.bid,ha.2.1⟩
    have h1 : |gs j a'-g a'|≤ ε/4 := by
      exact (show |gs j a'-g a'|≤ d j by
        simpa only [ContinuousMap.sub_apply,Real.norm_eq_abs,d] using
          (gs j-g).norm_coe_le_norm a').trans hdj
    have h2 : |g a'-g b|< ε/4 := by
      have hdist : dist a' b< δ := by
        simpa only [Subtype.dist_eq,Real.dist_eq,a'] using ha.2.2
      simpa only [Real.dist_eq] using hδg hdist
    have hs:=abs_add_le
      (((problem (G j) i).outcome a).mass r-(law P ξ (ls j) a.bid).mass r)
      ((law P ξ (ls j) a.bid).mass r-(law P ξ lam b).mass r)
    have ht:=abs_sub_le (gs j a') (g a') (g b)
    change |(law P ξ (ls j) a.bid).mass r-(law P ξ lam b).mass r|≤
      |gs j a'-g a'|+|g a'-g b| at ht
    rw [sub_add_sub_cancel] at hs

    linarith
  have hh:=PartialFixedValueVersions.conditional_mass_bound (G j) (hm j) v
    (law P ξ lam b) (5*ε/6) r hall
  simpa only [Real.dist_eq] using hh.trans_lt (by linarith : 5*ε/6< ε)

end FCAppendix.Affine.Tail04.OrderedActiveCountPassage
