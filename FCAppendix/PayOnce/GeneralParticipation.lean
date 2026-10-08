import FCAppendix.PayOnce.FullListAE

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_routed_positive_bids_broadcast (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid → 0 < x.2.routeCount → x.2.routeCount = n := by
  have hstrict := ae_positive_value_strict_surplus_broadcast Γ hn hc hcm hA hG hu B hB hsym hatom
  have hno := ae_no_overbid_onPath Γ (lt_trans hc hcm) hc (posterior_isAEEquilibrium Γ hu B hB)
  apply Measure.ae_compProd_of_ae_ae (p := fun x : ℝ × JointAction n =>
    0 < x.2.bid → 0 < x.2.routeCount → x.2.routeCount = n)
  · have hb : MeasurableSet {x : ℝ × JointAction n | 0 < x.2.bid} :=
      measurableSet_lt measurable_const ((measurable_bid n).comp measurable_snd)
    have hk : MeasurableSet {x : ℝ × JointAction n | 0 < x.2.routeCount} :=
      measurableSet_lt measurable_const ((measurable_routeCount n).comp measurable_snd)
    have he : MeasurableSet {x : ℝ × JointAction n | x.2.routeCount = n} :=
      measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd) measurable_const
    simpa only [imp_iff_not_or, Set.compl_setOf, Set.setOf_or] using hb.compl.union (hk.compl.union he)
  · filter_upwards [hstrict, hno] with v hs hn
    filter_upwards [hs, hn] with a hs hn hb hk
    have hle := hn hk
    have hv : Γ.g < v := by
      by_contra hnot
      rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt hnot))] at hle
      linarith
    exact (hs hv).2.2

def RoutedPositiveBroadcast (d : UserProfile m n) : Prop :=
  ∀ i, 0 < (d i).1.2.bid → 0 < (d i).1.2.routeCount → (d i).1.2.routeCount = n

theorem measurableSet_routedPositiveBroadcast :
    MeasurableSet {d : UserProfile m n | RoutedPositiveBroadcast d} := by
  have he : {d : UserProfile m n | RoutedPositiveBroadcast d} =
      ⋂ i, {d | 0 < (d i).1.2.bid → 0 < (d i).1.2.routeCount → (d i).1.2.routeCount = n} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_iInter, RoutedPositiveBroadcast]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  have hdraw : Measurable (fun d : UserProfile m n => d i) := measurable_pi_apply i
  have hact : Measurable (fun d : UserProfile m n => (d i).1.2) :=
    measurable_snd.comp (measurable_fst.comp hdraw)
  have hb : MeasurableSet {d : UserProfile m n | 0 < (d i).1.2.bid} :=
    measurableSet_lt measurable_const ((measurable_bid n).comp hact)
  have hk : MeasurableSet {d : UserProfile m n | 0 < (d i).1.2.routeCount} :=
    measurableSet_lt measurable_const ((measurable_routeCount n).comp hact)
  have heq : MeasurableSet {d : UserProfile m n | (d i).1.2.routeCount = n} :=
    measurableSet_eq_fun ((measurable_routeCount n).comp hact) measurable_const
  simpa only [imp_iff_not_or, Set.compl_setOf, Set.setOf_or] using hb.compl.union (hk.compl.union heq)

theorem common_list_of_full_positive_observation (d : UserProfile m n)
    (hd : RoutedPositiveBroadcast d) (j : Fin n) (ℓ : LocalList m)
    (ho : observe (drawsRealization d) j = ℓ) (b : Fin m → ℝ)
    (hb : ∀ i, 0 < b i) (hℓ : ∀ i, ℓ i = some (b i)) :
    ∀ l, observe (drawsRealization d) l = ℓ := by
  classical
  have hfull (i : Fin m) : (d i).1.2.routeCount = n := by
    have hi : observe (drawsRealization d) j i = some (b i) := by rw [ho, hℓ i]
    have hr : j ∈ firstK (d i).2 (d i).1.2.routeCount := by
      by_contra hn
      simp [observe, drawsRealization, hn] at hi
    have hbid : (d i).1.2.bid = b i := by
      simpa [observe, drawsRealization, hr] using hi
    have hpos : 0 < (d i).1.2.routeCount := by
      have hcard := Finset.card_pos.mpr ⟨j, hr⟩
      rwa [card_firstK _ _ (d i).1.2.routeCount_le] at hcard
    exact hd i (hbid ▸ hb i) hpos
  intro l
  exact (observe_eq_of_zero_or_full_routes d (fun i => Or.inr (hfull i)) l j).trans ho

theorem ae_equilibrium_on_full_positive_profiles (Γ : FiniteGame m (k + 1) c Seed)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid → 0 < x.2.routeCount → x.2.routeCount = k + 1)
    (j : Fin (k + 1)) : ∀ᵐ d ∂userProfileLaw Γ,
    (∀ i, 0 < (d i).1.2.bid ∧ (d i).1.2.routeCount = k + 1) →
      SymmetricAtList Γ (observe (drawsRealization d) j)
        (seedLottery Γ j (observe (drawsRealization d) j)) ∧
      CommonList.PayOnceEquilibrium (k + 1) c (fun i => (d i).1.2.bid)
        (seedLottery Γ j (observe (drawsRealization d) j)) := by
  have huser := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw (k + 1))).quasiMeasurePreserving.ae hroute
  have hdraw : ∀ᵐ d ∂userProfileLaw Γ, RoutedPositiveBroadcast d :=
    ae_all_iff.mpr fun i => (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae huser
  have hpost := B.ae_posterior_of_ae Γ j RoutedPositiveBroadcast measurableSet_routedPositiveBroadcast hdraw
  have hlist : ∀ᵐ ℓ ∂observedListLaw Γ j, SymmetricAtList Γ ℓ (seedLottery Γ j ℓ) ∧
      ∀ b : Fin m → ℝ, (∀ i, 0 < b i) → (∀ i, ℓ i = some (b i)) →
        CommonList.PayOnceEquilibrium (k + 1) c b (seedLottery Γ j ℓ) := by
    filter_upwards [hpost, B.ae_observation Γ j, hsym j] with ℓ hp ho hs
    refine ⟨hs, ?_⟩
    intro b hb hℓ
    have hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ := by
      filter_upwards [hp, ho] with d hd hdo
      exact common_list_of_full_positive_observation d hd j ℓ hdo b hb hℓ
    obtain ⟨d, hd⟩ := ho.exists
    exact full_payOnceEquilibrium_of_posterior_ae Γ hA B j ℓ (hB j ℓ ⟨d, hd⟩) b hℓ hcommon _ hs
  have hl := ae_of_ae_map (measurable_observe_draws j).aemeasurable hlist
  filter_upwards [hl] with d hd hfull
  refine ⟨hd.1, hd.2 _ (fun i => (hfull i).1) ?_⟩
  intro i
  simp [observe, drawsRealization, (hfull i).2, mem_firstK]
  exact Nat.le_of_lt_succ ((d i).2 j).isLt

theorem ae_positive_success_from_full_positive_profiles (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid → 0 < x.2.routeCount → x.2.routeCount = k + 1)
    (hfull : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), Γ.g < x.1 → 0 < x.2.bid ∧ x.2.routeCount = k + 1) (i : Fin m) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), Γ.g < x.1 → 0 < ((problem Γ i).outcome x.2).success := by
  classical
  let j : Fin (k + 1) := ⟨0, by omega⟩
  let P := fun x : ℝ × JointAction (k + 1) => Γ.g < x.1 ∧ ((problem Γ i).outcome x.2).success = 0
  have hP : MeasurableSet {x | P x} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_eq_fun ((measurable_success Γ i).comp measurable_snd) measurable_const)
  have hplayedzero : ∀ᵐ ω ∂backgroundLaw Γ, P (ω.1 i).1 → playedCount Γ i ω = 0 := by
    apply ae_played_of_ae_deviation Γ i (fun x r => P x → r = 0)
    · have hp : MeasurableSet {p : (ℝ × JointAction (k + 1)) × Fin (k + 2) | P p.1} :=
        measurable_fst hP
      have hz : MeasurableSet {p : (ℝ × JointAction (k + 1)) × Fin (k + 2) | p.2 = 0} :=
        measurableSet_eq_fun measurable_snd measurable_const
      simpa only [imp_iff_not_or, Set.compl_setOf, Set.setOf_or] using hp.compl.union hz
    · apply Filter.Eventually.of_forall
      intro x
      by_cases hx : P x
      · exact (ae_focalCount_zero_of_success_zero Γ i x.2 hx.2).mono fun _ h _ => h
      · exact Filter.Eventually.of_forall fun _ h => (hx h).elim
  have hdrawzero := Measure.ae_ae_of_ae_prod hplayedzero
  have huserfull := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw (k + 1))).quasiMeasurePreserving.ae hfull
  have hdrawfull : ∀ᵐ d ∂userProfileLaw Γ, ∀ l, Γ.g < (d l).1.1 →
      0 < (d l).1.2.bid ∧ (d l).1.2.routeCount = k + 1 :=
    ae_all_iff.mpr fun l => (measurePreserving_eval (fun _ : Fin m => userLaw Γ) l).quasiMeasurePreserving.ae huserfull
  have hdrawgame := ae_equilibrium_on_full_positive_profiles Γ hA B hB hsym hroute j
  have hnull : userLaw Γ {d | P d.1} = 0 := by
    by_contra hmass
    obtain ⟨D, hD, hmax⟩ := exists_positive_mass_maximal_profile (userLaw Γ) {d | P d.1} hmass
      (fun d => d.1.2.bid) ((measurable_bid (k + 1)).comp (measurable_snd.comp measurable_fst)) i
    obtain ⟨d, hdD, hdz, hdb, hdg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hD
      (ae_restrict_of_ae (hdrawzero.and (hdrawfull.and hdrawgame)))
    obtain ⟨hdP, hdmax⟩ := hmax d hdD
    have hfullD (l : Fin m) := hdb l (hdP l).1
    have hg := hdg hfullD
    let ℓ := observe (drawsRealization d) j
    let μ := seedLottery Γ j ℓ
    have hp : 0 < Proposer.marginal μ i := maximal_bid_marginal_pos (k + 1) (by omega)
      (fun l => (d l).1.2.bid) (fun l => (hfullD l).1) hc hcm μ hg.2 i hdmax
    obtain ⟨S, hS, hiS⟩ := CommonList.exists_mem_of_marginal_ne_zero μ i (ne_of_gt hp)
    let T : Set (Fin (k + 1) → Seed) := Set.univ.pi fun l => {s | (Γ.policy l ℓ s).val = S}
    have hmassS (l : Fin (k + 1)) : Γ.seedLaw {s | (Γ.policy l ℓ s).val = S} ≠ 0 := by
      intro hz
      apply hS
      change (seedLottery Γ j (observe (drawsRealization d) j)).mass S = 0
      rw [← hg.1 l]
      change (seedLottery Γ l ℓ).mass S = 0
      unfold seedLottery
      rw [FiniteLaw.ofMeasure_mass, hz, ENNReal.toReal_zero]
    have hT : (Measure.pi fun _ : Fin (k + 1) => Γ.seedLaw) T ≠ 0 := by
      rw [Measure.pi_pi]
      exact Finset.prod_ne_zero_iff.mpr fun l _ => hmassS l
    obtain ⟨s, hsT, hsz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hT (ae_restrict_of_ae hdz)
    have hz := hsz (hdP i)
    have hin : i ∈ allocation (drawsRealization d) Γ.policy s j := by
      change i ∈ (Γ.policy j ℓ (s j)).val
      rw [hsT j (Set.mem_univ j)]
      exact hiS
    have hcard : 0 < (accepted (drawsRealization d) Γ.policy s i).card :=
      Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hin⟩⟩
    have hzcard : (accepted (drawsRealization d) Γ.policy s i).card = 0 := congrArg Fin.val hz
    omega
  have hnot := Measure.ae_ae_of_ae_prod (measure_eq_zero_iff_ae_notMem.mp hnull)
  filter_upwards [hnot] with x hx hv
  have hne : ((problem Γ i).outcome x.2).success ≠ 0 := fun he => hx.exists.choose_spec ⟨hv, he⟩
  exact lt_of_le_of_ne (CountLaw.success_nonneg _) (Ne.symm hne)

theorem po_broadcast (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k + 1)) (hG : Γ.G = Schedule.once (k + 1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) :
    (∀ i : Fin m, ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, Γ.g < v →
      0 < a.bid ∧ a.bid < v - Γ.g ∧ 0 < (problem Γ i).payoff v a ∧ a.routeCount = k + 1) ∧
    (∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, 0 < a.bid → 0 < v - a.bid - Γ.g → a.routeCount = k + 1) := by
  have hstrict := ae_positive_value_strict_surplus_broadcast Γ
    (by omega) hc hcm hA hG hu B hB hsym hatom
  have hfull : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), Γ.g < x.1 → 0 < x.2.bid ∧ x.2.routeCount = k + 1 := by
    apply Measure.ae_compProd_of_ae_ae (p := fun x : ℝ × JointAction (k + 1) =>
      Γ.g < x.1 → 0 < x.2.bid ∧ x.2.routeCount = k + 1)
    · have hv : MeasurableSet {x : ℝ × JointAction (k + 1) | Γ.g < x.1} :=
        measurableSet_lt measurable_const measurable_fst
      have hb : MeasurableSet {x : ℝ × JointAction (k + 1) | 0 < x.2.bid} :=
        measurableSet_lt measurable_const ((measurable_bid (k + 1)).comp measurable_snd)
      have hr : MeasurableSet {x : ℝ × JointAction (k + 1) | x.2.routeCount = k + 1} :=
        measurableSet_eq_fun ((measurable_routeCount (k + 1)).comp measurable_snd) measurable_const
      simpa only [imp_iff_not_or, Set.setOf_and, Set.setOf_or, Set.compl_setOf] using hv.compl.union (hb.inter hr)
    · filter_upwards [hstrict] with v hv
      exact hv.mono fun _ ha hpos => ⟨(ha hpos).1, (ha hpos).2.2⟩
  have hroute := ae_routed_positive_bids_broadcast Γ (by omega) hc hcm hA hG hu B hB hsym hatom
  constructor
  · intro i
    have hsuccess := Measure.ae_ae_of_ae_compProd
      (ae_positive_success_from_full_positive_profiles Γ hk hc hcm.le hA B hB hsym hroute hfull i)
    filter_upwards [hstrict, hsuccess] with v hv hs
    filter_upwards [hv, hs] with a ha hs hv
    have hb := ha hv
    refine ⟨hb.1, hb.2.1, ?_, hb.2.2⟩
    rw [payoff_once Γ hA hG]
    apply mul_pos _ (hs hv)
    linarith [hb.2.1]
  · exact ae_positive_surplus_broadcast Γ hc hcm hA hG hu
      (posterior_rationalAtFeasibleLists Γ B hB) hsym

end FCAppendix.Bayes
