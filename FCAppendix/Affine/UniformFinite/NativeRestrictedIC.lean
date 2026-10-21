import FCAppendix.Affine.UniformFinite.NativeIdentity

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Existence.Distributional
open Uniform05

namespace NativeIC
variable {i : Row} {N : ℕ}

lemma lowerAction_embedding (v : Value i) (hv : 0<(v:ℝ)) :
    MeasurableEmbedding (fun q : unitInterval=> OriginalPopulation.lowerAction i (v,q)) := by
  apply ((OriginalPopulation.measurable_lowerAction i).comp
    (measurable_const.prodMk measurable_id)).measurableEmbedding
  intro q r h
  have hb:=congrArg JointAction.bid h
  change (baseBid i (v,q):ℝ)=(baseBid i (v,r):ℝ) at hb
  rw [baseBid_val,baseBid_val] at hb
  apply Subtype.ext
  exact mul_left_cancel₀ (width_positive i v hv).ne' (by linarith)

lemma positive_comparison (E : ExactRestrictedLaw i (N+1))
    (p : Value i×unitInterval) (hinc : 0<(baseBid i p:ℝ))
    (hIC : ∀b : ℝ,b∈Icc (floorBid i p.1) (hiBid i p.1)→
      rawUtility i N E.law p.1 b≤ rawUtility i N E.law p.1 (baseBid i p))
    (a : Fin (N+1)) (b : Bid i) (hb : 0<(b:ℝ))
    (hf : (b:ℝ)∈Icc (floorBid i p.1) (hiBid i p.1)) :
    NativeIndexed.utility i E.law a p.1 b≤
      NativeIndexed.utility i E.law a p.1 (baseBid i p) := by
  rw [NativeIndexed.utility_positive_eq_raw i N E.law a _ b hb,
    NativeIndexed.utility_positive_eq_raw i N E.law a _ (baseBid i p) hinc]
  exact hIC b hf

lemma zero_comparison (E : ExactRestrictedLaw i (N+1))
    (p : Value i×unitInterval) (hv : 0<(p.1:ℝ)) (hinc : 0<(baseBid i p:ℝ))
    (hfloor : floorBid i p.1=0)
    (hIC : ∀b : ℝ,b∈Icc (floorBid i p.1) (hiBid i p.1)→
      rawUtility i N E.law p.1 b≤ rawUtility i N E.law p.1 (baseBid i p))
    (a : Fin (N+1)) :
    NativeIndexed.utility i E.law a p.1 (Noisy.zeroBid i)≤
      NativeIndexed.utility i E.law a p.1 (baseBid i p) := by
  let q : ℕ→ unitInterval:=noiseSchedule 1
  let b : ℕ→ Bid i:=fun n=> baseBid i (p.1,q n)
  have hq (n : ℕ) : 0<(q n:ℝ):=noiseSchedule_pos 1 (by norm_num) n
  have hb (n : ℕ) : 0<(b n:ℝ):=ExactIC.baseBid_pos_of_choice_pos i p.1 hv _ (hq n)
  have h0 : (baseBid i (p.1,0):ℝ)=0 := by simp [baseBid_val,hfloor]
  have ht : Tendsto (fun n=>(b n:ℝ)) atTop (𝓝 0) := by
    have hp : Tendsto (fun n=>(p.1,q n)) atTop (𝓝 (p.1,(0:unitInterval))) :=
      tendsto_const_nhds.prodMk_nhds (noiseSchedule_tendsto_zero 1)
    have h : Tendsto (fun n=>baseBid i (p.1,q n)) atTop
        (𝓝 (baseBid i (p.1,0))) :=
      (continuous_baseBid i).continuousAt.tendsto.comp hp
    convert! continuous_subtype_val.continuousAt.tendsto.comp h using 1
    exact congrArg nhds h0.symm
  have hpos (n : ℕ) : NativeIndexed.utility i E.law a p.1 (b n)≤
      NativeIndexed.utility i E.law a p.1 (baseBid i p) :=
    positive_comparison E p hinc hIC a (b n) (hb n) (baseBid_bounds i (p.1,q n))
  apply le_of_forall_pos_le_add
  intro err herr
  obtain ⟨r,hr,hbound⟩:=NativeIndexed.zero_right_bound (M:=N+1) i herr
  have he : ∀ᶠn in atTop,NativeIndexed.utility i E.law a p.1 (Noisy.zeroBid i)≤
      NativeIndexed.utility i E.law a p.1 (baseBid i p)+(1+eta i)*(b n:ℝ)+err := by
    filter_upwards [ht.eventually (Iio_mem_nhds hr)] with n hn
    exact (hbound E.law inferInstance a p.1 (b n) (hb n) hn).trans (by linarith [hpos n])
  have hlim : Tendsto (fun n=> NativeIndexed.utility i E.law a p.1 (baseBid i p)+
      (1+eta i)*(b n:ℝ)+err) atTop
      (𝓝 (NativeIndexed.utility i E.law a p.1 (baseBid i p)+err)) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_const_nhds.add (ht.const_mul (1+eta i))).add_const err
  exact ge_of_tendsto hlim he

lemma broadcast_eq (act : JointAction 2) (hroute : act.routeCount=2)
    (b : Bid i) (hbid : act.bid=(b:ℝ)) : act=Hybrid.lowBroadcast b := by
  cases act with
  | mk x hx k hk=>
    dsimp only at hroute hbid
    subst x
    subst k
    rfl

theorem common_broadcast_IC (E : ExactRestrictedLaw i (N+1)) {R : ℝ}
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) :
    ∀ᵐp∂(E.pi.1 : Measure (Value i×unitInterval)),
      0<(p.1:ℝ) ∧ 0<(baseBid i p:ℝ) ∧
      ∀a : Fin (N+1),∀act : JointAction 2,
        act.routeCount=2→ act.bid∈Icc (floorBid i p.1) (hiBid i p.1)→
        (problem (OriginalPopulation.game E H) a).payoff p.1 act≤
          (problem (OriginalPopulation.game E H) a).payoff p.1 (OriginalPopulation.lowerAction i p) := by
  filter_upwards [E.common_conull_contract] with p hp
  refine ⟨hp.1,hp.2.1,?_⟩
  intro a act hroute hbox
  have hIC : ∀b : ℝ,b∈Icc (floorBid i p.1) (hiBid i p.1)→
      rawUtility i N E.law p.1 b≤ rawUtility i N E.law p.1 (baseBid i p) := by
    simpa only [Nat.add_sub_cancel] using hp.2.2.2.2
  let b : Bid i:=⟨act.bid,act.bid_nonneg,hbox.2.trans (min_le_right _ _)⟩
  rw [broadcast_eq act hroute b rfl,OriginalPopulation.lowerAction,
    NativeIndexed.game_payoff E H hR a _ b,NativeIndexed.game_payoff E H hR a _ (baseBid i p)]
  by_cases hb : 0<(b:ℝ)
  · exact positive_comparison E p hp.2.1 hIC a b hb hbox
  · have hz : (b:ℝ)=0 := le_antisymm (le_of_not_gt hb) b.property.1
    have hb0 : b=Noisy.zeroBid i:=Subtype.ext hz
    have hf : floorBid i p.1=0 := le_antisymm (by
      have hact : act.bid=0 := hz
      simpa only [hact] using hbox.1)
      (floor_nonneg i p.1)
    rw [hb0]
    exact zero_comparison E p hp.1 hp.2.1 hf hIC a

theorem conditional_broadcast_IC (E : ExactRestrictedLaw i (N+1)) {R : ℝ}
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) :
    ∀ᵐ(v : Value i)∂lowerMeasure i,∀ᵐq∂E.sigma v,
      0<(v:ℝ) ∧ 0<(baseBid i (v,q):ℝ) ∧
      ∀a : Fin (N+1),∀act : JointAction 2,
        act.routeCount=2→ act.bid∈Icc (floorBid i v) (hiBid i v)→
        (problem (OriginalPopulation.game E H) a).payoff v act≤
          (problem (OriginalPopulation.game E H) a).payoff v
            (OriginalPopulation.lowerAction i (v,q)) := by
  have h:=common_broadcast_IC E H hR
  have hdis : lowerMeasure i⊗ₘE.sigma=(E.pi.1 : Measure (Value i×unitInterval)) := E.disintegration
  rw [← hdis] at h
  exact Measure.ae_ae_of_ae_compProd h

theorem native_kernel_broadcast_IC (E : ExactRestrictedLaw i (N+1)) {R : ℝ}
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) :
    ∀ᵐ(v : Value i)∂lowerMeasure i,∀ᵐinc∂(OriginalPopulation.game E H).σ v,
      inc.routeCount=2 ∧ inc.bid∈Icc (floorBid i v) (hiBid i v) ∧
      ∀a : Fin (N+1),∀act : JointAction 2,
        act.routeCount=2→ act.bid∈Icc (floorBid i v) (hiBid i v)→
        (problem (OriginalPopulation.game E H) a).payoff v act≤
          (problem (OriginalPopulation.game E H) a).payoff v inc := by
  have hv : ∀ᵐ(v : Value i)∂lowerMeasure i,0<(v:ℝ) := by
    have h:=original_value_positive i E.pi
    have hdis : lowerMeasure i⊗ₘE.sigma=(E.pi.1 : Measure (Value i×unitInterval)) := E.disintegration
    rw [← hdis] at h
    have hc:=Measure.ae_ae_of_ae_compProd h
    filter_upwards [hc] with v hq
    exact hq.exists.choose_spec
  filter_upwards [conditional_broadcast_IC E H hR,hv] with v hq hv
  rw [OriginalPopulation.game_lower_kernel,(lowerAction_embedding v hv).ae_map_iff]
  filter_upwards [hq] with q hq
  exact ⟨rfl,baseBid_bounds i (v,q),hq.2.2⟩

end NativeIC
end FCAppendix.Affine.UniformFinite
