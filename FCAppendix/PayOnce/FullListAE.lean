import FCAppendix.PayOnce.StrictSurplus
import FCAppendix.Probability.UnitInterval

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m k c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem full_payOnceEquilibrium_of_posterior_ae (Γ : FiniteGame m (k + 1) c Seed)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (j : Fin (k + 1)) (ℓ : LocalList m)
    (hopt : ∀ᵐ s ∂Γ.seedLaw, Finite.Optimal c
      (beliefReceipts Γ.A (posteriorCountBelief Γ B j ℓ) ℓ) (Γ.policy j ℓ s).val)
    (b : Fin m → ℝ) (hℓ : ∀ i, ℓ i = some (b i))
    (hcommon : ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) :
    CommonList.PayOnceEquilibrium (k + 1) c b μ := by
  have hr : beliefReceipts Γ.A (posteriorCountBelief Γ B j ℓ) ℓ =
      fun i => b i * PayOnce.H (k + 1) (Proposer.marginal μ i) := by
    funext i
    simp only [beliefReceipts, hℓ i]
    exact posterior_payOnce_receipt Γ hA B j ℓ hcommon μ hμ i (b i)
  have hfeas : CommonList.Feasible c μ := by
    rw [← hμ j]
    exact seedLottery_feasible Γ j ℓ
  have hsupp : ∀ S, μ.mass S ≠ 0 →
      Finite.Optimal c (fun i => b i * PayOnce.H (k + 1) (Proposer.marginal μ i)) S := by
    intro S hS
    have hs : (seedLottery Γ j ℓ).mass S ≠ 0 := by rwa [hμ j]
    obtain ⟨s, hs, hoptS⟩ := seedLottery_support_exists_ae Γ j ℓ S hs _ hopt
    rw [← hs]
    simpa only [hr] using hoptS
  apply (CommonList.payOnceEquilibrium_iff (k + 1) (by omega) c b μ).mpr
  refine ⟨hfeas, ?_⟩
  intro ν hν
  unfold Proposer.revenue
  apply μ.const_le_expect_of_support
  intro S hS
  apply ν.expect_le_const_of_support
  intro T hT
  exact (hsupp S hS).2 T (hν T hT)

theorem ae_fullList_equilibrium_of_full_routes (Γ : FiniteGame m (k + 1) c Seed)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k + 1) (j : Fin (k + 1)) :
    ∀ᵐ d ∂userProfileLaw Γ,
      (∀ l, observe (drawsRealization d) l = observe (drawsRealization d) j) ∧
      SymmetricAtList Γ (observe (drawsRealization d) j)
        (seedLottery Γ j (observe (drawsRealization d) j)) ∧
      CommonList.PayOnceEquilibrium (k + 1) c (fun i => (d i).1.2.bid)
        (seedLottery Γ j (observe (drawsRealization d) j)) := by
  have hcommon := ae_commonLists_of_zero_or_full_routes Γ (hroute.mono fun _ h => Or.inr h) j
  have hpost := B.ae_commonLists Γ j hcommon
  have hlist : ∀ᵐ ℓ ∂observedListLaw Γ j,
      SymmetricAtList Γ ℓ (seedLottery Γ j ℓ) ∧
      ∀ b : Fin m → ℝ, (∀ i, ℓ i = some (b i)) →
        CommonList.PayOnceEquilibrium (k + 1) c b (seedLottery Γ j ℓ) := by
    filter_upwards [hpost, hsym j, B.ae_observation Γ j] with ℓ hp hs ho
    obtain ⟨d, hd⟩ := ho.exists
    exact ⟨hs, fun b hb => full_payOnceEquilibrium_of_posterior_ae Γ hA B j ℓ
      (hB j ℓ ⟨d, hd⟩) b hb hp _ hs⟩
  have hlist' := ae_of_ae_map (measurable_observe_draws j).aemeasurable hlist
  have huser := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw (k + 1))).quasiMeasurePreserving.ae hroute
  have hdrawroute : ∀ᵐ d ∂userProfileLaw Γ, ∀ i, (d i).1.2.routeCount = k + 1 :=
    ae_all_iff.mpr fun i => (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae huser
  filter_upwards [hcommon, hlist', hdrawroute] with d hc he hr
  refine ⟨hc, he.1, he.2 _ ?_⟩
  intro i
  simp [observe, drawsRealization, hr i, mem_firstK]
  exact Nat.le_of_lt_succ ((d i).2 j).isLt

theorem maximal_bid_marginal_pos (n : ℕ) (hn : 2 ≤ n) (b : Fin m → ℝ)
    (hb : ∀ i, 0 < b i) (hc : 0 < c) (hcm : c ≤ m)
    (μ : FiniteLaw (Finset (Fin m))) (heq : CommonList.PayOnceEquilibrium n c b μ)
    (i : Fin m) (hi : ∀ l, b l ≤ b i) : 0 < Proposer.marginal μ i := by
  obtain ⟨L, hL, hp, hsum⟩ := CommonList.equilibrium_kernel n hn b hb c (by simpa using hcm) μ heq
  by_contra hnot
  have hz : Proposer.marginal μ i = 0 := le_antisymm (le_of_not_gt hnot) (CommonList.marginal_nonneg μ i)
  have hbi : b i ≤ L := (CommonList.kernel_eq_zero_iff n hn (hb i) hL).mp ((hp i).symm.trans hz)
  have hall (l : Fin m) : CommonList.kernel n (b l) L = 0 :=
    (CommonList.kernel_eq_zero_iff n hn (hb l) hL).mpr ((hi l).trans hbi)
  simp only [hall, Finset.sum_const_zero] at hsum
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  linarith

theorem exists_positive_mass_maximal_profile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ] (E : Set Ω) (hE : μ E ≠ 0) (f : Ω → ℝ) (hf : Measurable f)
    (i : Fin m) : ∃ D : Set (Fin m → Ω),
      (Measure.pi fun _ : Fin m => μ) D ≠ 0 ∧
      ∀ d ∈ D, (∀ l, d l ∈ E) ∧ ∀ l, f (d l) ≤ f (d i) := by
  classical
  let ν := μ.restrict E
  by_cases hatom : ∃ r, ν {x | f x = r} ≠ 0
  · obtain ⟨r, hr⟩ := hatom
    let A := {x | f x = r} ∩ E
    have hA : μ A ≠ 0 := by
      simpa only [ν, Measure.restrict_apply (measurableSet_eq_fun hf measurable_const)] using hr
    refine ⟨Set.univ.pi fun _ => A, ?_, ?_⟩
    · rw [Measure.pi_pi]
      exact Finset.prod_ne_zero_iff.mpr fun _ _ => hA
    · intro d hd
      have h (l : Fin m) : f (d l) = r ∧ d l ∈ E := hd l (Set.mem_univ l)
      refine ⟨fun l => (h l).2, fun l => ?_⟩
      rw [(h l).1, (h i).1]
  · have hν : ν ≠ 0 := by
      intro hz
      have he := congrArg (fun ξ : Measure Ω => ξ Set.univ) hz
      exact hE (by simpa [ν] using he)
    push Not at hatom
    obtain ⟨q, hlo, hhi⟩ := exists_real_cut_of_null_fibers ν f hν hatom
    let A := {x | f x < (q : ℝ)} ∩ E
    let B := {x | (q : ℝ) < f x} ∩ E
    have hA : μ A ≠ 0 := by
      simpa only [ν, Measure.restrict_apply (measurableSet_lt hf measurable_const)] using hlo
    have hB : μ B ≠ 0 := by
      simpa only [ν, Measure.restrict_apply (measurableSet_lt measurable_const hf)] using hhi
    refine ⟨Set.univ.pi fun l => if l = i then B else A, ?_, ?_⟩
    · rw [Measure.pi_pi]
      apply Finset.prod_ne_zero_iff.mpr
      intro l _
      by_cases hli : l = i <;> simp only [hli, ↓reduceIte] <;> assumption
    · intro d hd
      have hi : (q : ℝ) < f (d i) ∧ d i ∈ E := by simpa only [↓reduceIte, B, Set.mem_inter_iff, Set.mem_setOf_eq] using hd i (Set.mem_univ i)
      have hl (l : Fin m) (hli : l ≠ i) : f (d l) < (q : ℝ) ∧ d l ∈ E := by
        simpa only [hli, ↓reduceIte, A, Set.mem_inter_iff, Set.mem_setOf_eq] using hd l (Set.mem_univ l)
      constructor
      · intro l
        by_cases hli : l = i
        · simpa only [hli] using hi.2
        · exact (hl l hli).2
      · intro l
        by_cases hli : l = i
        · simp only [hli, le_refl]
        · exact ((hl l hli).1.trans hi.1).le

theorem ae_fullList_success_pos (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k + 1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) (i : Fin m) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < ((problem Γ i).outcome x.2).success := by
  classical
  let j : Fin (k + 1) := ⟨0, by omega⟩
  let P := fun x : ℝ × JointAction (k + 1) => ((problem Γ i).outcome x.2).success = 0
  have hP : MeasurableSet {x | P x} :=
    measurableSet_eq_fun ((measurable_success Γ i).comp measurable_snd) measurable_const
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
      · exact (ae_focalCount_zero_of_success_zero Γ i x.2 hx).mono fun _ h _ => h
      · exact Filter.Eventually.of_forall fun _ h => (hx h).elim
  have hdrawzero := Measure.ae_ae_of_ae_prod hplayedzero
  have huserbid := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw (k + 1))).quasiMeasurePreserving.ae hbid
  have hdrawbid : ∀ᵐ d ∂userProfileLaw Γ, ∀ l, 0 < (d l).1.2.bid :=
    ae_all_iff.mpr fun l => (measurePreserving_eval (fun _ : Fin m => userLaw Γ) l).quasiMeasurePreserving.ae huserbid
  have hdrawgame := ae_fullList_equilibrium_of_full_routes Γ hA B hB hsym hroute j
  have hnull : userLaw Γ {d | P d.1} = 0 := by
    by_contra hmass
    obtain ⟨D, hD, hmax⟩ := exists_positive_mass_maximal_profile (userLaw Γ) {d | P d.1} hmass
      (fun d => d.1.2.bid) ((measurable_bid (k + 1)).comp (measurable_snd.comp measurable_fst)) i
    obtain ⟨d, hdD, hdz, hdb, hdg⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hD
      (ae_restrict_of_ae (hdrawzero.and (hdrawbid.and hdrawgame)))
    obtain ⟨hdP, hdmax⟩ := hmax d hdD
    let ℓ := observe (drawsRealization d) j
    let μ := seedLottery Γ j ℓ
    have hp : 0 < Proposer.marginal μ i := maximal_bid_marginal_pos (k + 1) (by omega)
      (fun l => (d l).1.2.bid) hdb hc hcm μ hdg.2.2 i hdmax
    obtain ⟨S, hS, hiS⟩ := CommonList.exists_mem_of_marginal_ne_zero μ i (ne_of_gt hp)
    let T : Set (Fin (k + 1) → Seed) := Set.univ.pi fun l => {s | (Γ.policy l ℓ s).val = S}
    have hmassS (l : Fin (k + 1)) : Γ.seedLaw {s | (Γ.policy l ℓ s).val = S} ≠ 0 := by
      intro hz
      apply hS
      change (seedLottery Γ j (observe (drawsRealization d) j)).mass S = 0
      rw [← hdg.2.1 l]
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
  filter_upwards [hnot] with x hx
  have hne : ((problem Γ i).outcome x.2).success ≠ 0 := hx.exists.choose_spec
  exact lt_of_le_of_ne (CountLaw.success_nonneg _) (Ne.symm hne)

theorem ae_full_routes_positive_bids_of_active (Γ : FiniteGame m (k + 1) c Seed)
    (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k + 1)) (hG : Γ.G = Schedule.once (k + 1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ)
    (hactive : ∀ᵐ v ∂Γ.F, Γ.g < v) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid ∧ x.2.routeCount = k + 1 := by
  apply Measure.ae_compProd_of_ae_ae (p := fun x : ℝ × JointAction (k + 1) =>
    0 < x.2.bid ∧ x.2.routeCount = k + 1)
  · exact (measurableSet_lt measurable_const ((measurable_bid (k + 1)).comp measurable_snd)).inter
      (measurableSet_eq_fun ((measurable_routeCount (k + 1)).comp measurable_snd) measurable_const)
  · filter_upwards [hactive, ae_positive_value_strict_surplus_broadcast Γ
      (by omega) hc hcm hA hG hu B hB hsym hatom] with v hv hs
    filter_upwards [hs] with a ha
    exact ⟨(ha hv).1, (ha hv).2.2⟩

theorem ae_active_payOnce_participation (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k + 1)) (hG : Γ.G = Schedule.once (k + 1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ)
    (hactive : ∀ᵐ v ∂Γ.F, Γ.g < v) (i : Fin m) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v,
      0 < a.bid ∧ a.bid < v - Γ.g ∧ a.routeCount = k + 1 ∧ 0 < (problem Γ i).payoff v a := by
  have hfull := ae_full_routes_positive_bids_of_active Γ hc hcm hA hG hu B hB hsym hatom hactive
  have hsuccess := Measure.ae_ae_of_ae_compProd
    (ae_fullList_success_pos Γ hk hc hcm.le hA B hB hsym
      (hfull.mono fun _ h => h.2) (hfull.mono fun _ h => h.1) i)
  filter_upwards [hactive, hsuccess, ae_positive_value_strict_surplus_broadcast Γ
    (by omega) hc hcm hA hG hu B hB hsym hatom] with v hv hs hb
  filter_upwards [hs, hb] with a hs hb
  have ha := hb hv
  refine ⟨ha.1, ha.2.1, ha.2.2, ?_⟩
  rw [payoff_once Γ hA hG]
  apply mul_pos _ hs
  linarith [ha.2.1]

end FCAppendix.Bayes
