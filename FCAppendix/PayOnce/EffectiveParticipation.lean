import FCAppendix.PayOnce.GeneralParticipation
import FCAppendix.PayOnce.BidScaling

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce.CompactifiedBidLaws
open scoped ProbabilityTheory
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem effectiveBid_nonneg {n : ℕ} (a : JointAction n) : 0 ≤ effectiveBid a := by
  unfold effectiveBid
  split_ifs
  · exact le_rfl
  · exact a.bid_nonneg

theorem ae_effectiveBid_participation (Γ : FiniteGame m (k+1) c Seed)
    (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      (0 < effectiveBid x.2 ↔ Γ.g < x.1) ∧
      effectiveBid x.2 ≤ max (x.1-Γ.g) 0 ∧
      (Γ.g < x.1 → x.2.routeCount = k+1) := by
  have hstrict := ae_positive_value_strict_surplus_broadcast Γ (by omega) hc hcm hA hG hu B hB hsym hatom
  have hfull : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), Γ.g < x.1 → 0 < x.2.bid ∧ x.2.routeCount = k+1 := by
    apply Measure.ae_compProd_of_ae_ae
    · have hv : MeasurableSet {x : ℝ × JointAction (k+1) | Γ.g < x.1} :=
        measurableSet_lt measurable_const measurable_fst
      have hb : MeasurableSet {x : ℝ × JointAction (k+1) | 0 < x.2.bid} :=
        measurableSet_lt measurable_const ((measurable_bid (k+1)).comp measurable_snd)
      have hr : MeasurableSet {x : ℝ × JointAction (k+1) | x.2.routeCount = k+1} :=
        measurableSet_eq_fun ((measurable_routeCount (k+1)).comp measurable_snd) measurable_const
      simpa only [imp_iff_not_or,Set.setOf_and,Set.setOf_or,Set.compl_setOf] using hv.compl.union (hb.inter hr)
    · filter_upwards [hstrict] with v hv
      exact hv.mono fun _ ha hpos => ⟨(ha hpos).1,(ha hpos).2.2⟩
  have hno := ae_no_overbid_compProd_onPath Γ (by omega) hc (posterior_isAEEquilibrium Γ hu B hB)
  filter_upwards [hfull,hno] with x hx hnx
  have hupper : effectiveBid x.2 ≤ max (x.1-Γ.g) 0 := by
    by_cases hz : x.2.routeCount = 0
    · simp only [effectiveBid,hz,if_pos]
      exact le_max_right _ _
    · simpa only [effectiveBid,hz,if_false] using hnx (Nat.pos_of_ne_zero hz)
  refine ⟨⟨?_,?_⟩,hupper,fun hv => (hx hv).2⟩
  · intro hb
    have hnet := hb.trans_le hupper
    rcases (lt_max_iff).mp hnet with hv | hv
    · linarith
    · exact (lt_irrefl _ hv).elim
  · intro hv
    have hh := hx hv
    simpa only [effectiveBid,hh.2,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false] using hh.1

theorem realEffectiveBidLaw_positive_mass (Γ : FiniteGame m (k+1) c Seed)
    (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) :
    (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ) (Ioi 0) = Γ.F (Ioi Γ.g) := by
  have he := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw (k+1))).quasiMeasurePreserving.ae
    (ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hatom)
  change (Measure.map (fun d : UserDraw (k+1) => effectiveBid d.1.2) (userLaw Γ)) (Ioi 0) = _
  have hm : Measurable (fun d : UserDraw (k+1) => effectiveBid d.1.2) :=
    (measurable_effectiveBid (k+1)).comp (measurable_snd.comp measurable_fst)
  rw [Measure.map_apply hm measurableSet_Ioi]
  have hm : userLaw Γ {d | 0 < effectiveBid d.1.2} = userLaw Γ {d | Γ.g < d.1.1} :=
    measure_congr (he.mono fun _ hd => propext hd.1)
  change userLaw Γ {d | 0 < effectiveBid d.1.2} = Γ.F (Ioi Γ.g)
  rw [hm]
  rw [← userLaw_value_map Γ,Measure.map_apply
    (show Measurable (fun d : UserDraw (k+1) => d.1.1) from measurable_fst.comp measurable_fst) measurableSet_Ioi]
  rfl

def InactiveAbstain (Γ : FiniteGame m (k+1) c Seed) : Prop :=
  ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.1 ≤ Γ.g → x.2.routeCount = 0

theorem ae_positive_broadcast_or_abstain (Γ : FiniteGame m (k+1) c Seed)
    (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ)
    (hinactive : InactiveAbstain Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k+1) := by
  filter_upwards [ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hatom,hinactive] with x hx hi
  by_cases hv : Γ.g < x.1
  · right
    have hr := hx.2.2 hv
    refine ⟨?_,hr⟩
    have hp := hx.1.mpr hv
    simpa only [effectiveBid,hr,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false] using hp
  · exact Or.inl (hi (le_of_not_gt hv))

end FCAppendix.Bayes
