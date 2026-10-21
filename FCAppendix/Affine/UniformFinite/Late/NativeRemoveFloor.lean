import FCAppendix.Affine.UniformFinite.NativeRoutes
import FCAppendix.Affine.UniformFinite.Late.RemoveFloor
import FCAppendix.Affine.UniformFinite.Late.OnPathConditional

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Late
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05

namespace NativeFloor
variable {i : Row} {N : ℕ}

lemma zero_top_bound (E : ExactRestrictedLaw i (N+1))
    (hmenu : SourceRawApprox i N E.pi (floorGap i/4)) (a : Fin (N+1)) :
    NativeIndexed.utility i E.law a (t i) (Noisy.zeroBid i)≤ floorGap i/4 := by
  let top : Value i:=⟨t i,(t_pos i).le,le_rfl⟩
  apply NativeIndexed.zero_le_of_positive_source_bound i N E.law a top
    (floorGap i/4) (lambda i) (lambda_pos i)
  intro b hb hbL
  have h:=hmenu (t i) ⟨(t_pos i).le,le_rfl⟩ b
  change |rawUtility i N E.law (t i) b-productPayoff (xi i) (t i) (lambda i) b|< _ at h
  rw [product_zero hbL.le,sub_zero] at h
  exact ((le_abs_self _).trans_lt h).le

lemma indexed_below_entry_bounds (E : ExactRestrictedLaw i (N+1))
    (hmenu : SourceRawApprox i N E.pi (floorGap i/4))
    (a : Fin (N+1)) (v : Value i) (own : Bid i) (hb : (own:ℝ)≤ floorTop i) :
    NativeIndexed.utility i E.law a v own< floorGap i/2 ∧
      t i*(NativeProfile.indexedLaw i E.law a own).success< floorGap i/2 := by
  have hg:=floorGap_pos i
  by_cases hpos : 0<(own:ℝ)
  · have hbL : (own:ℝ)≤ lambda i:=hb.trans (floorTop_lt_entry i).le
    have hpzero (w : ℝ) : productPayoff (xi i) w (lambda i) own=0 := product_zero hbL
    have hval:=hmenu v v.property own
    have ht:=hmenu (t i) ⟨(t_pos i).le,le_rfl⟩ own
    have hz:=hmenu 0 ⟨le_rfl,(t_pos i).le⟩ own
    change |rawUtility i N E.law v own-productPayoff (xi i) v (lambda i) own|< _ at hval
    change |rawUtility i N E.law (t i) own-productPayoff (xi i) (t i) (lambda i) own|< _ at ht
    change |rawUtility i N E.law 0 own-productPayoff (xi i) 0 (lambda i) own|< _ at hz
    rw [hpzero,sub_zero] at hval ht hz
    rw [NativeIndexed.utility_positive_eq_raw i N E.law a v own hpos,
      NativeIndexed.success_positive_eq_raw i N E.law a own hpos]
    have hid:=raw_value_difference i N E.law own (t i) 0
    simp only [sub_zero] at hid
    exact ⟨by linarith [(abs_lt.mp hval).2],by
      linarith [(abs_lt.mp ht).2,(abs_lt.mp hz).1]⟩
  · have hz : own=Noisy.zeroBid i:=Subtype.ext (le_antisymm (le_of_not_gt hpos) own.property.1)
    rw [hz]
    have ht:=zero_top_bound E hmenu a
    rw [NativeIndexed.utility_zero_bid] at ht ⊢
    have hs:=(NativeProfile.indexedLaw i E.law a (Noisy.zeroBid i)).success_nonneg
    have hv:=mul_le_mul_of_nonneg_right v.property.2 hs
    exact ⟨by linarith,by linarith⟩

theorem common_no_below_floor (E : ExactRestrictedLaw i (N+1)) {R : ℝ}
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (hmenu : SourceRawApprox i N E.pi (floorGap i/4)) :
    ∀ᵐp∂(E.pi.1 : Measure (Value i×unitInterval)),
      ∀a : Fin (N+1),∀act : JointAction 2,act.bid< floorBid i p.1→
        (problem (OriginalPopulation.game E H) a).payoff p.1 act<
          (problem (OriginalPopulation.game E H) a).payoff p.1 (OriginalPopulation.lowerAction i p) ∧
        ∀j : Fin 2,(NativeRoutes.namedOutcome (OriginalPopulation.game E H) a act.bid j).utility
          p.1 act.bid (OriginalPopulation.game E H).g
            (OriginalPopulation.game E H).A (OriginalPopulation.game E H).G<
          (problem (OriginalPopulation.game E H) a).payoff p.1 (OriginalPopulation.lowerAction i p) := by
  have hg:=floorGap_pos i
  filter_upwards [E.common_conull_contract] with p hp
  intro a act hbf
  have hf : 0< floorBid i p.1:=act.bid_nonneg.trans_lt hbf
  obtain ⟨_,target,htarget,hgap⟩:=floored_type_product_gap i p.1.property.1 p.1.property.2 hf
  let target' : Bid i:=⟨target,(floor_nonneg i p.1).trans htarget.1,
    htarget.2.trans (min_le_right _ _)⟩
  have hm:=hmenu p.1 p.1.property target'
  have hchosen : rawUtility i N E.law p.1 target≤ rawUtility i N E.law p.1 (baseBid i p) := by
    simpa only [Nat.add_sub_cancel] using hp.2.2.2.2 target htarget
  have hinc : 3*floorGap i/4≤
      (problem (OriginalPopulation.game E H) a).payoff p.1 (OriginalPopulation.lowerAction i p) := by
    rw [OriginalPopulation.lowerAction,NativeIndexed.game_payoff E H hR a,
      NativeIndexed.utility_positive_eq_raw i N E.law a p.1 (baseBid i p) hp.2.1]
    change floorGap i≤ productPayoff (xi i) p.1 (lambda i) target at hgap
    change |rawUtility i N E.law p.1 target-productPayoff (xi i) p.1 (lambda i) target|< _ at hm
    linarith [(abs_lt.mp hm).1]
  have hbtop : act.bid≤ floorTop i:=hbf.le.trans (floor_le_floorTop i p.1.property.2)
  let own : Bid i:=⟨act.bid,act.bid_nonneg,hbtop.trans (floorTop_lt_cap i).le⟩
  have hbounds:=indexed_below_entry_bounds E hmenu a p.1 own hbtop
  have hsuccess : t i*((problem (OriginalPopulation.game E H) a).outcome
      (Hybrid.lowBroadcast own)).success< floorGap i/2 := by
    rw [OriginalPopulation.game_broadcast_outcome E H hR a own]
    exact hbounds.2
  refine ⟨?_,?_⟩
  · by_cases hz : act.routeCount=0
    · rw [NativeRoutes.zero_route_payoff _ a p.1 act hz]
      linarith
    · by_cases hsingle : act.routeCount=1
      · have hs:=NativeRoutes.singleton_payoff_le_broadcast_success
          (OriginalPopulation.game E H) rfl a p.1 (t i) p.1.property.2 (t_pos i).le
          act (Hybrid.lowBroadcast own) hsingle rfl rfl
        linarith
      · have hfull : act.routeCount=2:=by have h:=act.routeCount_le;omega
        rw [NativeIC.broadcast_eq act hfull own rfl,NativeIndexed.game_payoff E H hR a]
        linarith [hbounds.1]
  · intro j
    have hn:=NativeRoutes.named_payoff_le_broadcast_success (OriginalPopulation.game E H)
      rfl a p.1 (t i) p.1.property.2 (t_pos i).le (Hybrid.lowBroadcast own) rfl j
    change (NativeRoutes.namedOutcome (OriginalPopulation.game E H) a act.bid j).utility
      p.1 act.bid (OriginalPopulation.game E H).g
        (OriginalPopulation.game E H).A (OriginalPopulation.game E H).G≤ _ at hn
    linarith

theorem eventually_common_no_below_floor (i : Row) :
    ∀ᶠN : ℕ in atTop,∀E : ExactRestrictedLaw i (N+1),∀R : ℝ,
      ∀H : OriginalPopulation.UpperPriorityLaw i R,cap i< R→
        ∀ᵐp∂(E.pi.1 : Measure (Value i×unitInterval)),
          ∀a : Fin (N+1),∀act : JointAction 2,act.bid< floorBid i p.1→
            (problem (OriginalPopulation.game E H) a).payoff p.1 act<
              (problem (OriginalPopulation.game E H) a).payoff p.1 (OriginalPopulation.lowerAction i p) := by
  filter_upwards [uniform_source_raw_menu i (div_pos (floorGap_pos i) (by norm_num : (0:ℝ)<4))]
    with N hN
  intro E R H hR
  have hIC : NoisyIC i N 0 E.pi := by
    change NoisyIC i N 0 E.cluster.pi0
    simpa only [Nat.add_sub_cancel] using E.IC
  have hm : SourceRawApprox i N E.pi (floorGap i/4):=fun v hv b=> hN E.pi hIC v b hv
  filter_upwards [common_no_below_floor E H hR hm] with p hp
  exact fun a act hb=>(hp a act hb).1

theorem eventually_strict_no_below_floor (i : Row) :
    ∀ᶠN : ℕ in atTop,∀E : ExactRestrictedLaw i (N+1),∀R : ℝ,
      ∀H : OriginalPopulation.UpperPriorityLaw i R,cap i< R→
        ∀ᵐp∂(E.pi.1 : Measure (Value i×unitInterval)),
          ∀a : Fin (N+1),∀act : JointAction 2,act.bid< floorBid i p.1→
            (problem (StrictOriginal.game E H) a).payoff p.1 act<
              (problem (StrictOriginal.game E H) a).payoff p.1 (OriginalPopulation.lowerAction i p) := by
  filter_upwards [eventually_common_no_below_floor i] with N hN
  intro E R H hR
  filter_upwards [hN E R H hR] with p hp
  intro a act hb
  have hcap : act.bid≤ cap i:=hb.le.trans ((floor_le_floorTop i p.1.property.2).trans
    (floorTop_lt_cap i).le)
  rw [StrictOriginal.payoff_below_cap E H hR a p.1 act hcap,
    StrictOriginal.payoff_below_cap E H hR a p.1 (OriginalPopulation.lowerAction i p)
      (baseBid i p).property.2]
  exact hp a act hb

end NativeFloor
end FCAppendix.Affine.UniformFinite.Late
