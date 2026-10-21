import FCAppendix.Affine.UniformFinite.Late.StrictOriginalGame
import FCAppendix.Affine.UniformFinite.NativeProfile

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late.StrictOriginal
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05
open scoped BigOperators

variable {i : Row} {M : ℕ} [NeZero M] {R : ℝ}

omit [NeZero M] in

theorem original_deviation_list (_E : ExactRestrictedLaw i M)
    (_H : OriginalPopulation.UpperPriorityLaw i R) (a : Fin M)
    (act : JointAction 2) (hbid : act.bid ≤ cap i)
    (ω : Bayes.Sample M 2 unitInterval)
    (hd : ω.1.1 ∈ Strict.strongProfiles M (cap i) R) (j : Fin 2) :
    Strict.OriginalList (cap i) R (observe (deviated a act ω) j) := by
  intro l b he
  have hj : j ∈ (deviated a act ω).recipients l := by
    by_contra hn
    simp only [observe,if_neg hn] at he
    cases he
  have hb : ((deviated a act ω).action l).bid=b := by
    apply Option.some.inj
    simpa only [observe,if_pos hj] using he
  by_cases hl : l=a
  · subst l
    rw [deviated_bid_self] at hb
    exact Or.inl (hb ▸ hbid)
  · rw [deviated_bid_other a l hl] at hb
    rcases hd l with h | h
    · exact Or.inl (hb ▸ h.1)
    · exact Or.inr (hb ▸ h.1)

theorem focalCount_below_cap (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (act : JointAction 2) (hbid : act.bid ≤ cap i)
    (ω : Bayes.Sample M 2 unitInterval)
    (hd : ω.1.1 ∈ Strict.strongProfiles M (cap i) R) :
    focalCount (game E H) a act ω=focalCount (OriginalPopulation.game E H) a act ω := by
  apply Fin.ext
  change inclusionCount (deviated a act ω) (game E H).policy ω.1.2 a=
    inclusionCount (deviated a act ω) (OriginalPopulation.game E H).policy ω.1.2 a
  rw [inclusionCount_eq_sum,inclusionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := policy_on_original_list E H hR j _
    (original_deviation_list E H a act hbid ω hd j) (ω.1.2 j)
  change (if a∈((game E H).policy j (observe (deviated a act ω) j) (ω.1.2 j)).val
    then 1 else 0)=_
  rw [h]
  rfl

theorem sample_original_support (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    ∀ᵐω ∂sampleLaw (game E H), ω.1.1∈Strict.strongProfiles M (cap i) R :=
  ((measurePreserving_fst (μ:=userProfileLaw (game E H))
    (ν:=Measure.pi (fun _ : Fin 2=>(game E H).seedLaw))).comp
      (measurePreserving_fst (μ:=backgroundLaw (game E H)) (ν:=permLaw 2))).quasiMeasurePreserving.ae
        (game_profile_support E H)

theorem outcome_below_cap (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (act : JointAction 2) (hbid : act.bid ≤ cap i) :
    (problem (game E H) a).outcome act=
      (problem (OriginalPopulation.game E H) a).outcome act := by
  apply FiniteLaw.ext_expect
  intro f
  simp only [problem_outcome,CountLaw.expect_ofMeasure]
  have hlaw : sampleLaw (OriginalPopulation.game E H)=sampleLaw (game E H) := rfl
  rw [hlaw]
  apply integral_congr_ae
  filter_upwards [sample_original_support E H] with ω hω
  rw [focalCount_below_cap E H hR a act hbid ω hω]

theorem payoff_below_cap (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (v : ℝ) (act : JointAction 2) (hbid : act.bid ≤ cap i) :
    (problem (game E H) a).payoff v act=
      (problem (OriginalPopulation.game E H) a).payoff v act := by
  change ((problem (game E H) a).outcome act).utility v act.bid
    (game E H).g (game E H).A (game E H).G=_
  rw [outcome_below_cap E H hR a act hbid]
  rfl

theorem game_broadcast_outcome (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (own : Bid i) :
    (problem (game E H) a).outcome (Hybrid.lowBroadcast own)=
      NativeProfile.indexedLaw i E.law a own := by
  rw [outcome_below_cap E H hR a _ own.property.2]
  exact OriginalPopulation.game_broadcast_outcome E H hR a own

theorem game_typeOutcome (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (a : Fin M) (v : Value i) :
    typeOutcome (game E H) a v=OriginalPopulation.indexedTypeLaw E a v := by
  apply FiniteLaw.ext_expect
  intro f
  rw [typeOutcome_expect,game_lower_kernel]
  have hm : Measurable (fun q : unitInterval=>OriginalPopulation.lowerAction i (v,q)) := by
    convert! (OriginalPopulation.measurable_lowerAction i).comp
      (measurable_const.prodMk measurable_id) using 1
  rw [integral_map (μ:=E.sigma v) hm.aemeasurable
    (measurable_outcome_expect (game E H) a f).aestronglyMeasurable,
    OriginalPopulation.indexedTypeLaw,FiniteLaw.expect_average]
  apply integral_congr_ae
  exact ae_of_all _ (fun q=> by
    change ((problem (game E H) a).outcome (OriginalPopulation.lowerAction i (v,q))).expect f=_
    rw [OriginalPopulation.lowerAction,game_broadcast_outcome E H hR a])

def averagedTypeLaw (E : ExactRestrictedLaw i M) (v : Value i) : CountLaw 2 :=
  FiniteLaw.uniformAverage (Nat.pos_of_ne_zero (NeZero.ne M))
    (fun a=> OriginalPopulation.indexedTypeLaw E a v)

theorem game_conditionalTypeCountLaw (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) (v : Value i) :
    conditionalTypeCountLaw (game E H) (Nat.pos_of_ne_zero (NeZero.ne M)) v=
      averagedTypeLaw E v := by
  unfold conditionalTypeCountLaw averagedTypeLaw
  congr 1
  funext a
  exact game_typeOutcome E H hR a v

theorem averagedTypeLaw_expect (E : ExactRestrictedLaw i M) (v : Value i) (f : Fin 3→ℝ) :
    (averagedTypeLaw E v).expect f=
      (∑a : Fin M,(OriginalPopulation.indexedTypeLaw E a v).expect f)/(M:ℝ) :=
  FiniteLaw.expect_uniformAverage _ _ _

theorem averagedTypeLaw_original_integral (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) (f : Fin 3→ℝ) :
    (∫v,(averagedTypeLaw E v).expect f ∂lowerMeasure i)=
      (∑a : Fin M,∫p,(NativeProfile.indexedLaw i E.law a (baseBid i p)).expect f
        ∂(E.pi.1 : Measure (Value i×unitInterval)))/(M:ℝ) := by
  have hint (a : Fin M) : Integrable
      (fun v : Value i=>(OriginalPopulation.indexedTypeLaw E a v).expect f) (lowerMeasure i) := by
    have he (v : Value i) := congrArg (fun P : CountLaw 2=> P.expect f)
      (game_typeOutcome E H hR a v)
    have hm : Measurable (fun v : Value i=> (typeOutcome (game E H) a v).expect f) :=
      (measurable_typeOutcome_expect (game E H) a f).comp measurable_subtype_coe
    have heq : (fun v : Value i=> (typeOutcome (game E H) a v).expect f)=
        (fun v : Value i=> (OriginalPopulation.indexedTypeLaw E a v).expect f) := funext he
    rw [heq] at hm
    apply Integrable.of_bound hm.aestronglyMeasurable (∑k,‖f k‖)
    exact ae_of_all _ (fun v=>(OriginalPopulation.indexedTypeLaw E a v).norm_expect_le_sum_norm f)
  simp_rw [averagedTypeLaw_expect]
  rw [integral_div,integral_finsetSum _ (fun a _=> hint a)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  exact OriginalPopulation.indexedTypeLaw_original_integral E a f

end FCAppendix.Affine.UniformFinite.Late.StrictOriginal
