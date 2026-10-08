import FCAppendix.Exclusive.OnceBayes

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
theorem presentDrawList_eq_singleton (d : UserProfile m n) (R : Finset (Fin n))
    (hd : ∀ l, firstK (d l).2 (d l).1.2.routeCount = R) (j : Fin n) (hj : j ∉ R)
    (i : Fin m) (b : ℝ) : presentDrawList d i b j = singletonList i b := by
  classical
  funext l
  by_cases hl : l = i
  · simp [presentDrawList, singletonList, hl]
  · simp [presentDrawList, singletonList, hl, observe, drawsRealization, hd l, hj]

theorem exclusive_outside_broadcast_positive (Γ : FiniteGame m n c Seed)
    (d : UserProfile m n) (R : Finset (Fin n))
    (hd : ∀ l, firstK (d l).2 (d l).1.2.routeCount = R) (j : Fin n) (hj : j ∉ R)
    (i : Fin m)
    (hacc : ∀ᵐ u ∂Γ.seedLaw, i ∈ (Γ.policy j (singletonList i (d i).1.2.bid) u).val) :
    ∀ᵐ s ∂(Measure.pi fun _ : Fin n => Γ.seedLaw),
      0 < (playedBroadcastCount Γ i (d, s)).val := by
  classical
  have hs' := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae
    hacc
  filter_upwards [hs'] with s hs
  have hroute : j ∈ firstK (d i).2 (broadcastAction (d i).1.2).routeCount := by
    simp [broadcastAction, mem_firstK]
  have hs2 : Accepts Γ i (d i).1.2.bid j (d, s) := by
    change i ∈ (Γ.policy j (presentDrawList d i (d i).1.2.bid j) (s j)).val
    rw [presentDrawList_eq_singleton d R hd j hj]
    exact hs
  have hacc' := (mem_allocation_deviated_iff Γ i (broadcastAction (d i).1.2)
    ((d, s), (d i).2) j).mpr ⟨hroute, hs2⟩
  change 0 < (accepted (deviated i (broadcastAction (d i).1.2)
    ((d, s), (d i).2)) Γ.policy s i).card
  apply Finset.card_pos.mpr
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hacc'⟩⟩

theorem exists_route_pair (R : Finset (Fin n)) (hR0 : R.Nonempty) (hR : R.card < n) :
    ∃ r j : Fin n, r ∈ R ∧ j ∉ R := by
  obtain ⟨r, hr⟩ := hR0
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ∉ R := by
    by_contra! h
    have he : R = Finset.univ := Finset.eq_univ_of_forall h
    rw [he, Finset.card_univ, Fintype.card_fin] at hR
    omega
  exact ⟨r, j, hr, hj⟩

theorem exclusive_broadcastViolationAt_zero (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalOnPath Γ B)
    (hsym : SymmetricProposersOnPath Γ) (R : Finset (Fin n)) (hR0 : R.Nonempty)
    (hR : R.card < n) :
    userLaw Γ (broadcastViolationAt Γ.g R) = 0 := by
  classical
  by_contra hmass
  obtain ⟨r, j, hr, hj⟩ := exists_route_pair R hR0 hR
  have hzero : ∀ᵐ ω ∂backgroundLaw Γ, ∀ i : Fin m,
      0 < (ω.1 i).1.1 - (ω.1 i).1.2.bid - Γ.g →
        playedCount Γ i ω = 0 → playedBroadcastCount Γ i ω = 0 :=
    ae_all_iff.mpr (ae_played_no_broadcast_rescue Γ hA hG hu)
  have hdrawzero := Measure.ae_ae_of_ae_prod hzero
  have hcore := ae_common_route_singleton_accepts Γ hc hcm B hB hsym R r j hr hj
  let D : Set (UserProfile m n) := Set.univ.pi fun _ : Fin m => broadcastViolationAt Γ.g R
  have hD : userProfileLaw Γ D ≠ 0 := by
    simp only [D, userProfileLaw, Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hmass
  obtain ⟨d, hdD, hdz, hdc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hD
    (ae_restrict_of_ae (hdrawzero.and hcore))
  have hd (i : Fin m) : 0 < (d i).1.2.bid ∧ 0 < (d i).1.1 - (d i).1.2.bid - Γ.g ∧
      firstK (d i).2 (d i).1.2.routeCount = R := hdD i (Set.mem_univ i)
  obtain ⟨i, ⟨E, hE, hfail⟩, hacc⟩ := hdc (fun l => (hd l).2.2) (fun l => (hd l).1)
  have hpos := exclusive_outside_broadcast_positive Γ d R (fun l => (hd l).2.2) j hj i hacc
  obtain ⟨s, hsE, hsz, hsp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hE
    (ae_restrict_of_ae (hdz.and hpos))
  have hz := hsz i (hd i).2.1 (hfail s hsE)
  have hzv : (playedBroadcastCount Γ i (d, s)).val = 0 := congrArg Fin.val hz
  omega

theorem exclusive_ae_positive_surplus_broadcast_userLaw (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalOnPath Γ B)
    (hsym : SymmetricProposersOnPath Γ) :
    ∀ᵐ d ∂userLaw Γ, 0 < d.1.2.bid → 0 < d.1.1 - d.1.2.bid - Γ.g →
      0 < d.1.2.routeCount → d.1.2.routeCount = n := by
  classical
  have hall : ∀ᵐ d ∂userLaw Γ, ∀ R : Finset (Fin n), R.Nonempty → R.card < n →
      d ∉ broadcastViolationAt Γ.g R :=
    ae_all_iff.mpr fun R => by
      by_cases hR : R.Nonempty ∧ R.card < n
      · exact (measure_eq_zero_iff_ae_notMem.mp
          (exclusive_broadcastViolationAt_zero Γ hc hcm hA hG hu B hB hsym R hR.1 hR.2)).mono
          fun _ h _ _ => h
      · exact Filter.Eventually.of_forall fun _ h1 h2 => (hR ⟨h1, h2⟩).elim
  filter_upwards [hall] with d hd hb hs hk
  by_contra hfull
  have hlt : d.1.2.routeCount < n := lt_of_le_of_ne d.1.2.routeCount_le hfull
  have hcard : (firstK d.2 d.1.2.routeCount).card = d.1.2.routeCount :=
    card_firstK _ _ d.1.2.routeCount_le
  have hne : (firstK d.2 d.1.2.routeCount).Nonempty := by
    apply Finset.card_pos.mp
    omega
  exact hd (firstK d.2 d.1.2.routeCount) hne (by omega) ⟨hb, hs, rfl⟩

theorem exclusive_ae_positive_surplus_broadcast (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalOnPath Γ B)
    (hsym : SymmetricProposersOnPath Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid → 0 < x.1 - x.2.bid - Γ.g →
      0 < x.2.routeCount → x.2.routeCount = n := by
  have h := Measure.ae_ae_of_ae_prod
    (exclusive_ae_positive_surplus_broadcast_userLaw Γ hc hcm hA hG hu B hB hsym)
  filter_upwards [h] with x hx
  obtain ⟨_, hτ⟩ := hx.exists
  exact hτ

theorem exclusive_zero_service_null (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalOnPath Γ B)
    (hsym : SymmetricProposersOnPath Γ)
    (P : ℝ × JointAction n → Prop) (hP : MeasurableSet {x | P x})
    (hbid : ∀ x, P x → 0 < x.2.bid)
    (hroute : ∀ x, P x → 0 < x.2.routeCount ∧ x.2.routeCount < n)
    (hzero : ∀ i, ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), P x → ((problem Γ i).outcome x.2).success = 0) :
    (Γ.F ⊗ₘ Γ.σ) {x | P x} = 0 := by
  classical

  have hplayed (i : Fin m) : ∀ᵐ ω ∂backgroundLaw Γ, P (ω.1 i).1 → playedCount Γ i ω = 0 := by
    apply ae_played_of_ae_deviation Γ i (fun x r => P x → r = 0)
    · have hp : MeasurableSet {p : (ℝ × JointAction n) × Fin (n + 1) | P p.1} :=
        measurable_fst hP
      have hcnt : MeasurableSet {p : (ℝ × JointAction n) × Fin (n + 1) | p.2 = 0} :=
        measurableSet_eq_fun measurable_snd measurable_const
      simpa only [imp_iff_not_or, Set.compl_setOf, Set.setOf_or] using hp.compl.union hcnt
    · filter_upwards [hzero i] with x hx
      by_cases hPx : P x
      · exact (ae_focalCount_zero_of_success_zero Γ i x.2 (hx hPx)).mono fun _ h _ => h
      · exact Filter.Eventually.of_forall fun _ h => (hPx h).elim
  have hnull (R : Finset (Fin n)) (hR0 : R.Nonempty) (hR : R.card < n) :
      userLaw Γ {d | P d.1 ∧ firstK d.2 d.1.2.routeCount = R} = 0 := by
    by_contra hmass
    obtain ⟨r, j, hr, hj⟩ := exists_route_pair R hR0 hR
    have hre : ∀ᵐ d ∂userProfileLaw Γ, ∀ i : Fin m,
        ∀ᵐ s ∂(Measure.pi fun _ : Fin n => Γ.seedLaw),
          P (d i).1 → playedCount Γ i (rerouteUser i (Equiv.swap r j) d, s) = 0 := by
      apply ae_all_iff.mpr
      intro i
      have h := Measure.ae_ae_of_ae_prod (hplayed i)
      have h' := (measurePreserving_rerouteUser Γ i (Equiv.swap r j)).quasiMeasurePreserving.ae h
      filter_upwards [h'] with d hd
      filter_upwards [hd] with s hs hPi
      apply hs
      simpa [rerouteUser, rerouteDraw] using hPi
    have hcore := ae_common_route_singleton_accepts Γ hc hcm B hB hsym R r j hr hj
    let D : Set (UserProfile m n) := Set.univ.pi fun _ : Fin m =>
      {d | P d.1 ∧ firstK d.2 d.1.2.routeCount = R}
    have hD : userProfileLaw Γ D ≠ 0 := by
      simp only [D, userProfileLaw, Measure.pi_pi]
      exact Finset.prod_ne_zero_iff.mpr fun _ _ => hmass
    obtain ⟨d, hdD, hdz, hdc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hD
      (ae_restrict_of_ae (hre.and hcore))
    have hd (i : Fin m) : P (d i).1 ∧ firstK (d i).2 (d i).1.2.routeCount = R :=
      hdD i (Set.mem_univ i)
    obtain ⟨i, _, hacc⟩ := hdc (fun l => (hd l).2) (fun l => hbid _ (hd l).1)
    have hs' := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae
      hacc
    obtain ⟨s, hsz, hsa⟩ := ((hdz i).and hs').exists
    have hz := hsz (hd i).1
    have hin : i ∈ allocation (drawsRealization (rerouteUser i (Equiv.swap r j) d))
        Γ.policy s j := by
      change i ∈ (Γ.policy j (observe (drawsRealization
        (rerouteUser i (Equiv.swap r j) d)) j) (s j)).val
      rw [observe_reroute_singleton d R (fun l => (hd l).2) r j hr hj i]
      exact hsa
    exact notMem_allocation_of_playedCount_zero Γ i _ hz j hin
  have hall : ∀ᵐ d ∂userLaw Γ, ∀ R : Finset (Fin n), R.Nonempty → R.card < n →
      ¬ (P d.1 ∧ firstK d.2 d.1.2.routeCount = R) :=
    ae_all_iff.mpr fun R => by
      by_cases hR : R.Nonempty ∧ R.card < n
      · exact (measure_eq_zero_iff_ae_notMem.mp (hnull R hR.1 hR.2)).mono fun _ h _ _ => h
      · exact Filter.Eventually.of_forall fun _ h1 h2 => (hR ⟨h1, h2⟩).elim
  have hnot : ∀ᵐ d ∂userLaw Γ, ¬ P d.1 := by
    filter_upwards [hall] with d hd hPd
    have hk := hroute d.1 hPd
    have hcard : (firstK d.2 d.1.2.routeCount).card = d.1.2.routeCount :=
      card_firstK _ _ d.1.2.routeCount_le
    have hne : (firstK d.2 d.1.2.routeCount).Nonempty := by
      apply Finset.card_pos.mp
      omega
    exact hd _ hne (by omega) ⟨hPd, rfl⟩
  apply measure_eq_zero_iff_ae_notMem.mpr
  have h := Measure.ae_ae_of_ae_prod hnot
  filter_upwards [h] with x hx
  exact hx.exists.choose_spec

theorem exclusive_ae_partial_surplus_nonneg (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalOnPath Γ B)
    (hsym : SymmetricProposersOnPath Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid → 0 < x.2.routeCount → x.2.routeCount < n →
      0 ≤ x.1 - x.2.bid - Γ.g := by
  classical
  let P : ℝ × JointAction n → Prop := fun x =>
    0 < x.2.bid ∧ (0 < x.2.routeCount ∧ x.2.routeCount < n) ∧ x.1 - x.2.bid - Γ.g < 0
  have hbm : Measurable (fun x : ℝ × JointAction n => x.2.bid) :=
    (measurable_bid n).comp measurable_snd
  have hkm : Measurable (fun x : ℝ × JointAction n => x.2.routeCount) :=
    (measurable_routeCount n).comp measurable_snd
  have hP : MeasurableSet {x | P x} :=
    (measurableSet_lt measurable_const hbm).inter
      (((measurableSet_lt measurable_const hkm).inter (measurableSet_lt hkm measurable_const)).inter
        (measurableSet_lt ((measurable_fst.sub hbm).sub_const Γ.g) measurable_const))
  have hzero (i : Fin m) : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), P x →
      ((problem Γ i).outcome x.2).success = 0 := by
    filter_upwards [ae_bestResponse_compProd Γ hu i] with x hx hPx
    have hpay : 0 ≤ (problem Γ i).payoff x.1 x.2 := by
      simpa only [(problem Γ i).payoff_abstain] using hx (Interim.abstain n)
    rw [payoff_once Γ hA hG] at hpay
    have hs0 := CountLaw.success_nonneg ((problem Γ i).outcome x.2)
    have hneg := hPx.2.2
    apply le_antisymm _ hs0
    nlinarith
  have hnull := exclusive_zero_service_null Γ hc hcm B hB hsym P hP (fun _ h => h.1)
    (fun _ h => h.2.1) hzero
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hb hk hkn
  by_contra hneg
  exact hx ⟨hb, ⟨hk, hkn⟩, lt_of_not_ge hneg⟩

def ZeroSurplusPartial (g : ℝ) (x : ℝ × JointAction n) : Prop :=
  0 < x.2.bid ∧ (0 < x.2.routeCount ∧ x.2.routeCount < n) ∧ x.2.bid = x.1 - g

theorem measurableSet_zeroSurplusPartial (g : ℝ) :
    MeasurableSet {x : ℝ × JointAction n | ZeroSurplusPartial g x} := by
  have hbm : Measurable (fun x : ℝ × JointAction n => x.2.bid) :=
    (measurable_bid n).comp measurable_snd
  have hkm : Measurable (fun x : ℝ × JointAction n => x.2.routeCount) :=
    (measurable_routeCount n).comp measurable_snd
  exact (measurableSet_lt measurable_const hbm).inter
    (((measurableSet_lt measurable_const hkm).inter (measurableSet_lt hkm measurable_const)).inter
      (measurableSet_eq_fun hbm (measurable_fst.sub_const g)))

theorem exclusive_zeroSurplusPartial_null (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalOnPath Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) :
    (Γ.F ⊗ₘ Γ.σ) {x | ZeroSurplusPartial Γ.g x} = 0 := by
  classical
  let E : Set (ℝ × JointAction n) := {x | ZeroSurplusPartial Γ.g x}
  have hE : MeasurableSet E := measurableSet_zeroSurplusPartial Γ.g
  let μ := (Γ.F ⊗ₘ Γ.σ).restrict E
  by_contra hmass
  have hμ : μ ≠ 0 := by
    intro hz
    have := congrArg (fun ν : Measure (ℝ × JointAction n) => ν Set.univ) hz
    exact hmass (by simpa [μ, E] using this)
  have hnull (v : ℝ) : μ {x | x.1 = v} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    by_cases hv : Γ.g < v
    · have hvnull : ∀ᵐ w ∂Γ.F, w ≠ v := measure_eq_zero_iff_ae_notMem.mp (hatom v hv)
      have hprod : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.1 ≠ v :=
        Measure.ae_compProd_of_ae_fst Γ.σ (by measurability) hvnull
      exact ae_restrict_of_ae hprod
    · filter_upwards [ae_restrict_mem hE] with x hx hxeq
      have hxpos : Γ.g < x.1 := by
        have h1 := hx.1
        have h2 := hx.2.2
        linarith
      exact hv (hxeq ▸ hxpos)
  obtain ⟨q, hlo, hhi⟩ := exists_real_cut_of_null_fibers μ Prod.fst hμ hnull
  have hqhi : MeasurableSet {x : ℝ × JointAction n | (q : ℝ) < x.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hqlo : MeasurableSet {x : ℝ × JointAction n | x.1 < (q : ℝ)} :=
    measurableSet_lt measurable_fst measurable_const
  have hupper : (Γ.F ⊗ₘ Γ.σ) ({x | (q : ℝ) < x.1} ∩ E) ≠ 0 := by
    simpa only [μ, Measure.restrict_apply hqhi] using hhi
  have hbest : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ∀ i, (problem Γ i).BestResponse x.1 x.2 :=
    ae_all_iff.mpr (ae_bestResponse_compProd Γ hu)
  obtain ⟨u, huE, hubest⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hupper
    (ae_restrict_of_ae hbest)
  let P := fun x : ℝ × JointAction n => ZeroSurplusPartial Γ.g x ∧ x.1 < q
  have hP : MeasurableSet {x | P x} := hE.inter hqlo
  have hzero (i : Fin m) (x : ℝ × JointAction n) (hx : P x) :
      ((problem Γ i).outcome x.2).success = 0 := by
    have hupay : (problem Γ i).payoff u.1 u.2 = 0 := by
      rw [payoff_once Γ hA hG, huE.2.2.2]
      have he : u.1 - (u.1 - Γ.g) - Γ.g = 0 := by ring
      rw [he, zero_mul]
    have hcompare := hubest i x.2
    rw [hupay, payoff_once Γ hA hG, hx.1.2.2] at hcompare
    have hlow : x.1 < (q : ℝ) := hx.2
    have hhigh : (q : ℝ) < u.1 := huE.1
    have hsurplus : 0 < u.1 - (x.1 - Γ.g) - Γ.g := by linarith
    have hnonneg := CountLaw.success_nonneg ((problem Γ i).outcome x.2)
    nlinarith
  have hlowerzero := exclusive_zero_service_null Γ hc hcm B hB hsym P hP
    (fun _ hx => hx.1.1) (fun _ hx => hx.1.2.1)
    (fun i => Filter.Eventually.of_forall fun x hx => hzero i x hx)
  apply hlo
  rw [Measure.restrict_apply hqlo]
  have hset : {x : ℝ × JointAction n | x.1 < (q : ℝ)} ∩ E = {x | P x} := by
    ext x
    exact and_comm
  rw [hset]
  exact hlowerzero

theorem exclusive_ae_partial_strict_surplus (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalOnPath Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid → 0 < x.2.routeCount → x.2.routeCount < n →
      0 < x.1 - x.2.bid - Γ.g := by
  filter_upwards [exclusive_ae_partial_surplus_nonneg Γ hc hcm hA hG hu B hB hsym,
    measure_eq_zero_iff_ae_notMem.mp
      (exclusive_zeroSurplusPartial_null Γ hc hcm hA hG hu B hB hsym hatom)]
    with x hnn hz hb hk hkn
  have h0 := hnn hb hk hkn
  refine lt_of_le_of_ne h0 (fun he => hz ⟨hb, ⟨hk, hkn⟩, ?_⟩)
  linarith

theorem exclusive_once_routing (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalOnPath Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, 0 < a.bid → 0 < a.routeCount → a.routeCount = n := by
  have h : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid → 0 < x.2.routeCount → x.2.routeCount = n := by
    filter_upwards [exclusive_ae_partial_strict_surplus Γ hc hcm hA hG hu B hB hsym hatom,
      exclusive_ae_positive_surplus_broadcast Γ hc hcm hA hG hu B hB hsym]
      with x hs hb hbid hk
    by_contra hfull
    have hlt : x.2.routeCount < n := lt_of_le_of_ne x.2.routeCount_le hfull
    exact hfull (hb hbid (hs hbid hk hlt) hk)
  exact Measure.ae_ae_of_ae_compProd h

theorem exclusive_once_routing_of_feasible_optimal (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, 0 < a.bid → 0 < a.routeCount → a.routeCount = n :=
  exclusive_once_routing Γ hc hcm hA hG hu B
    (ExclusivePosteriorOptimalAE.to_onPath Γ B hB) hsym hatom

end FCAppendix.Bayes
