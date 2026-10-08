import FCAppendix.Finite.ReceiptBoundsAE
import FCAppendix.Finite.NestedRouting

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def broadcastAction (a : JointAction n) : JointAction n :=
  ⟨a.bid, a.bid_nonneg, n, le_rfl⟩

theorem measurable_broadcastAction : Measurable (broadcastAction : JointAction n → JointAction n) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap broadcastAction
    (MeasurableSpace.comap (fun a : JointAction n => (a.bid, a.routeCount)) _) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact ((measurable_bid n).prodMk measurable_const).comap_le

theorem focalCount_le_broadcast (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) (ω : Sample m n Seed) :
    (focalCount Γ i a ω).val ≤ (focalCount Γ i (broadcastAction a) ω).val := by
  classical
  change (accepted (deviated i a ω) Γ.policy ω.1.2 i).card ≤
    (accepted (deviated i (broadcastAction a) ω) Γ.policy ω.1.2 i).card
  apply Finset.card_le_card
  intro j hj
  have ha : i ∈ allocation (deviated i a ω) Γ.policy ω.1.2 j := (Finset.mem_filter.mp hj).2
  obtain ⟨hroute, hacc⟩ := (mem_allocation_deviated_iff Γ i a ω j).mp ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, (mem_allocation_deviated_iff Γ i (broadcastAction a) ω j).mpr ?_⟩
  exact ⟨firstK_mono ω.2 a.routeCount_le hroute, hacc⟩

theorem successIndicator_mono_nat {a b : ℕ} (h : a ≤ b) :
    successIndicator a ≤ successIndicator b := by
  by_cases ha : a = 0
  · subst a
    exact successIndicator_nonneg b
  · have hb : b ≠ 0 := by omega
    simp [successIndicator, ha, hb]

theorem ae_no_broadcast_rescue_of_bestResponse (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (i : Fin m) (v : ℝ) (a : JointAction n) (hbr : (problem Γ i).BestResponse v a)
    (hs : 0 < v - a.bid - Γ.g) :
    ∀ᵐ ω ∂sampleLaw Γ, focalCount Γ i a ω = 0 →
      focalCount Γ i (broadcastAction a) ω = 0 := by
  have hbr' := hbr (broadcastAction a)
  have hpay (d : JointAction n) : (problem Γ i).payoff v d =
      (v - d.bid - Γ.g) * ((problem Γ i).outcome d).success := by
    change ((problem Γ i).outcome d).utility v d.bid Γ.g Γ.A Γ.G = _
    rw [hA, hG, CountLaw.once_utility]
  rw [hpay, hpay] at hbr'
  change (v - a.bid - Γ.g) * ((problem Γ i).outcome (broadcastAction a)).success ≤
    (v - a.bid - Γ.g) * ((problem Γ i).outcome a).success at hbr'
  have hle := le_of_mul_le_mul_left hbr' hs
  have hmono : ∀ ω : Sample m n Seed,
      0 ≤ successIndicator (focalCount Γ i (broadcastAction a) ω).val -
        successIndicator (focalCount Γ i a ω).val :=
    fun ω => sub_nonneg.mpr (successIndicator_mono_nat (focalCount_le_broadcast Γ i a ω))
  have hIfull := CountLaw.integrable_comp (sampleLaw Γ) _
    (measurable_focalCount Γ i (broadcastAction a)) (fun r => successIndicator r.val)
  have hIold := CountLaw.integrable_comp (sampleLaw Γ) _ (measurable_focalCount Γ i a)
    (fun r => successIndicator r.val)
  have hI := hIfull.sub hIold
  have hint : (∫ ω, successIndicator (focalCount Γ i (broadcastAction a) ω).val -
      successIndicator (focalCount Γ i a ω).val ∂sampleLaw Γ) = 0 := by
    apply le_antisymm _ (integral_nonneg hmono)
    rw [integral_sub hIfull hIold]
    simpa only [problem_outcome, CountLaw.success, CountLaw.expect_ofMeasure,
      sub_nonpos] using hle
  have hae := (integral_eq_zero_iff_of_nonneg hmono hI).mp hint
  filter_upwards [hae] with ω hω hz
  have hzv : (focalCount Γ i a ω).val = 0 := congrArg Fin.val hz
  apply Fin.ext
  change (focalCount Γ i (broadcastAction a) ω).val = 0
  by_contra hpos
  simp [successIndicator, hzv, hpos] at hω

theorem focalCount_insertDraw (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) (p : UserDraw n × Background m n Seed) (τ : Equiv.Perm (Fin n)) :
    focalCount Γ i a (insertDraw i p, τ) = focalCount Γ i a (p.2, τ) := by
  classical
  have hobs (j : Fin n) : observe (deviated i a (insertDraw i p, τ)) j =
      observe (deviated i a (p.2, τ)) j := by
    funext l
    by_cases hl : l = i
    · subst l
      simp only [observe, deviated_recipients_self, deviated_bid_self]
    · simp only [observe, deviated_recipients_other i l hl, deviated_bid_other i l hl,
        insertDraw, Function.update_of_ne hl]
  apply Fin.ext
  change inclusionCount _ _ _ _ = inclusionCount _ _ _ _
  have halloc (j : Fin n) :
      allocation (deviated i a (insertDraw i p, τ)) Γ.policy (insertDraw i p).2 j =
      allocation (deviated i a (p.2, τ)) Γ.policy p.2.2 j :=
    congrArg (fun L => (Γ.policy j L (p.2.2 j)).val) (hobs j)
  simp only [inclusionCount_eq_sum, halloc]

noncomputable def playedBroadcastCount (Γ : FiniteGame m n c Seed) (i : Fin m)
    (ω : Background m n Seed) : Fin (n + 1) :=
  focalCount Γ i (broadcastAction (ω.1 i).1.2) (ω, (ω.1 i).2)

theorem measurable_playedBroadcastCount (Γ : FiniteGame m n c Seed) (i : Fin m) :
    Measurable (playedBroadcastCount Γ i) := by
  have hd : Measurable (fun ω : Background m n Seed => ω.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hm := (measurable_focalCount_joint Γ i).comp
    ((measurable_broadcastAction.comp (measurable_snd.comp (measurable_fst.comp hd))).prodMk
      (measurable_id.prodMk (measurable_snd.comp hd)))
  exact hm

theorem ae_played_no_broadcast_rescue (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (i : Fin m) : ∀ᵐ ω ∂backgroundLaw Γ,
    0 < (ω.1 i).1.1 - (ω.1 i).1.2.bid - Γ.g →
      playedCount Γ i ω = 0 → playedBroadcastCount Γ i ω = 0 := by
  have ha : Measurable (fun p : (ℝ × JointAction n) × Sample m n Seed => (p.1.2, p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hc := (measurable_focalCount_joint Γ i).comp ha
  change Measurable (fun p : (ℝ × JointAction n) × Sample m n Seed =>
    focalCount Γ i p.1.2 p.2) at hc
  have had : Measurable (fun p : (ℝ × JointAction n) × Sample m n Seed =>
      (broadcastAction p.1.2, p.2)) :=
    (measurable_broadcastAction.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hb := (measurable_focalCount_joint Γ i).comp had
  change Measurable (fun p : (ℝ × JointAction n) × Sample m n Seed =>
    focalCount Γ i (broadcastAction p.1.2) p.2) at hb
  have hp : MeasurableSet {p : (ℝ × JointAction n) × Sample m n Seed |
      0 < p.1.1 - p.1.2.bid - Γ.g → focalCount Γ i p.1.2 p.2 = 0 →
        focalCount Γ i (broadcastAction p.1.2) p.2 = 0} := by
    have hs : MeasurableSet {p : (ℝ × JointAction n) × Sample m n Seed |
        0 < p.1.1 - p.1.2.bid - Γ.g} := measurableSet_lt measurable_const
      (((measurable_fst.comp measurable_fst).sub
        ((measurable_bid n).comp (measurable_snd.comp measurable_fst))).sub_const Γ.g)
    simpa only [imp_iff_not_or, Set.preimage, Set.mem_singleton_iff,
      Set.compl_setOf, Set.setOf_or] using hs.compl.union
      ((hc (measurableSet_singleton 0)).compl.union (hb (measurableSet_singleton 0)))
  have hprod : ∀ᵐ p ∂(Γ.F ⊗ₘ Γ.σ).prod (sampleLaw Γ),
      0 < p.1.1 - p.1.2.bid - Γ.g → focalCount Γ i p.1.2 p.2 = 0 →
        focalCount Γ i (broadcastAction p.1.2) p.2 = 0 := by
    apply (Measure.ae_prod_iff_ae_ae hp).mpr
    filter_upwards [ae_bestResponse_compProd Γ hu i] with x hx
    by_cases hs : 0 < x.1 - x.2.bid - Γ.g
    · exact (ae_no_broadcast_rescue_of_bestResponse Γ hA hG i x.1 x.2 hx hs).mono
        fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => (hs h).elim
  have hd : Measurable (fun ω : Background m n Seed => ω.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hplayed : MeasurableSet {ω : Background m n Seed |
      0 < (ω.1 i).1.1 - (ω.1 i).1.2.bid - Γ.g →
        playedCount Γ i ω = 0 → playedBroadcastCount Γ i ω = 0} := by
    have hs : MeasurableSet {ω : Background m n Seed |
        0 < (ω.1 i).1.1 - (ω.1 i).1.2.bid - Γ.g} := measurableSet_lt measurable_const
      (((measurable_fst.comp (measurable_fst.comp hd)).sub
        ((measurable_bid n).comp (measurable_snd.comp (measurable_fst.comp hd)))).sub_const Γ.g)
    simpa only [imp_iff_not_or, Set.preimage, Set.mem_singleton_iff,
      Set.compl_setOf, Set.setOf_or] using hs.compl.union
      (((measurable_playedCount Γ i) (measurableSet_singleton 0)).compl.union
        ((measurable_playedBroadcastCount Γ i) (measurableSet_singleton 0)))
  have hpres := playFromDeviation_measurePreserving Γ i
  rw [← hpres.map_eq]
  apply (ae_map_iff hpres.measurable.aemeasurable hplayed).mpr
  filter_upwards [hprod] with p hp
  have hv : ((playFromDeviation i p).1 i).1 = p.1 := by
    simp [playFromDeviation, insertDraw]
  have hτ : ((playFromDeviation i p).1 i).2 = p.2.2 := by
    simp [playFromDeviation, insertDraw]
  have hk := playedCount_insertDraw Γ i ((p.1, p.2.2), p.2.1)
  have hkb := focalCount_insertDraw Γ i (broadcastAction p.1.2)
    ((p.1, p.2.2), p.2.1) p.2.2
  have heK : playedCount Γ i (playFromDeviation i p) = focalCount Γ i p.1.2 p.2 := hk
  have heB : playedBroadcastCount Γ i (playFromDeviation i p) =
      focalCount Γ i (broadcastAction p.1.2) p.2 := by
    unfold playedBroadcastCount
    rw [hv, hτ]
    exact hkb
  rw [hv, heK, heB]
  exact hp

def SymmetricProposersOnPath (Γ : FiniteGame m n c Seed) : Prop :=
  ∀ j, ∀ᵐ ℓ ∂observedListLaw Γ j, SymmetricAtList Γ ℓ (seedLottery Γ j ℓ)

theorem ae_singleton_accepts (Γ : FiniteGame m n c Seed) (hc : 0 < c)
    (j : Fin n) (hj : ProposerRationalAtFeasibleLists Γ j)
    (ℓ : LocalList m) (hfeas : FeasibleObservedList j ℓ)
    (i : Fin m) (b : ℝ) (hb : 0 < b) (hi : ℓ i = some b)
    (hother : ∀ l, l ≠ i → ℓ l = none) :
    ∀ᵐ s ∂Γ.seedLaw, i ∈ (Γ.policy j ℓ s).val := by
  classical
  obtain ⟨belief, hopt⟩ := hj
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hA (r : ℕ) (hr : 0 < r) (hrn : r ≤ n) : (1 / (n : ℝ)) * r ≤ Γ.A.charge r := by
    have hrR : (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hratio : (r : ℝ) / n ≤ 1 := (div_le_one hn).mpr hrR
    simpa [div_eq_mul_inv, mul_comm] using hratio.trans (Γ.A.lower r hr hrn)
  have hreceipt := (beliefReceipts_bounds Γ.A (belief ℓ) ℓ (1 / (n : ℝ)) hA
    i b hb.le hi).1
  have hpos : 0 < beliefReceipts Γ.A (belief ℓ) ℓ i :=
    lt_of_lt_of_le (mul_pos (one_div_pos.mpr hn) hb) hreceipt
  filter_upwards [hopt ℓ hfeas] with s hs
  apply Finite.included_of_few_competitors c _ _ hs i hpos
  have hempty : (Finset.univ.filter fun l => l ≠ i ∧
      beliefReceipts Γ.A (belief ℓ) ℓ i ≤ beliefReceipts Γ.A (belief ℓ) ℓ l) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro l _ h
    have hz := beliefReceipts_none Γ.A (belief ℓ) ℓ l (hother l h.1)
    linarith [h.2]
  simpa only [hempty, Finset.card_empty] using hc

theorem exists_common_route_failure (Γ : FiniteGame m n c Seed) (hcm : c < m)
    (d : UserProfile m n) (R : Finset (Fin n))
    (hd : ∀ i, firstK (d i).2 (d i).1.2.routeCount = R)
    (hsym : ∀ j, j ∈ R → SymmetricAtList Γ (observe (drawsRealization d) j)
      (seedLottery Γ j (observe (drawsRealization d) j))) :
    ∃ (i : Fin m) (E : Set (Fin n → Seed)),
      (Measure.pi fun _ : Fin n => Γ.seedLaw) E ≠ 0 ∧
        ∀ s ∈ E, playedCount Γ i (d, s) = 0 := by
  classical
  have hrec (i : Fin m) : (drawsRealization d).recipients i = R := hd i
  rcases R.eq_empty_or_nonempty with hR | hR
  · refine ⟨⟨0, by omega⟩, Set.univ, by simp, ?_⟩
    intro s _
    apply Fin.ext
    change (accepted (drawsRealization d) Γ.policy s ⟨0, by omega⟩).card = 0
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have h := accepted_subset_recipients (drawsRealization d) Γ.policy s
      ⟨0, by omega⟩ hj
    rw [hrec, hR] at h
    exact Finset.notMem_empty _ h
  · obtain ⟨j, hj⟩ := hR
    let ℓ := observe (drawsRealization d) j
    let μ := seedLottery Γ j ℓ
    have hμ : SymmetricAtList Γ ℓ μ := hsym j hj
    obtain ⟨S, hS⟩ := CommonList.exists_support μ
    have hcard : S.card ≤ c := seedLottery_feasible Γ j ℓ S hS
    obtain ⟨i, hi⟩ : ∃ i : Fin m, i ∉ S := by
      by_contra! h
      have he : S = Finset.univ := Finset.eq_univ_of_forall h
      rw [he, Finset.card_univ, Fintype.card_fin] at hcard
      omega
    let E : Set (Fin n → Seed) :=
      Set.univ.pi fun l => {s | (Γ.policy l ℓ s).val = S}
    have hmass (l : Fin n) : Γ.seedLaw {s | (Γ.policy l ℓ s).val = S} ≠ 0 := by
      intro hz
      apply hS
      rw [← hμ l]
      unfold seedLottery
      rw [FiniteLaw.ofMeasure_mass, hz, ENNReal.toReal_zero]
    refine ⟨i, E, ?_, ?_⟩
    · rw [Measure.pi_pi]
      exact Finset.prod_ne_zero_iff.mpr fun l _ => hmass l
    · intro s hs
      have halloc (l : Fin n) (hl : l ∈ R) : allocation (drawsRealization d) Γ.policy s l = S := by
        have hobs : observe (drawsRealization d) l = ℓ := by
          funext a
          simp [ℓ, observe, drawsRealization, hd a, hl, hj]
        exact (congrArg (fun L => (Γ.policy l L (s l)).val) hobs).trans
          (hs l (Set.mem_univ l))
      apply Fin.ext
      change (accepted (drawsRealization d) Γ.policy s i).card = 0
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro l hl
      have hli : i ∈ allocation (drawsRealization d) Γ.policy s l := (Finset.mem_filter.mp hl).2
      have hr : l ∈ R := hrec i ▸ accepted_subset_recipients (drawsRealization d) Γ.policy s i hl
      rw [halloc l hr] at hli
      exact hi hli

theorem ae_outside_broadcast_positive (Γ : FiniteGame m n c Seed) (hc : 0 < c)
    (d : UserProfile m n) (R : Finset (Fin n))
    (hd : ∀ i, firstK (d i).2 (d i).1.2.routeCount = R)
    (j : Fin n) (hj : j ∉ R) (hrat : ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (hb : 0 < (d i).1.2.bid) :
    ∀ᵐ s ∂(Measure.pi fun _ : Fin n => Γ.seedLaw), 0 < (playedBroadcastCount Γ i (d, s)).val := by
  classical
  let ℓ := presentDrawList d i (d i).1.2.bid j
  have hi : ℓ i = some (d i).1.2.bid := by simp [ℓ, presentDrawList]
  have hother (l : Fin m) (hl : l ≠ i) : ℓ l = none := by
    simp [ℓ, presentDrawList, hl, observe, drawsRealization, hd l, hj]
  have hs := ae_singleton_accepts Γ hc j hrat ℓ
    (presentDrawList_feasible d i (d i).1.2.bid (d i).1.2.bid_nonneg j) i _ hb hi hother
  have hs' := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae hs
  filter_upwards [hs'] with s hs
  have hroute : j ∈ firstK (d i).2 (broadcastAction (d i).1.2).routeCount := by
    simp [broadcastAction, mem_firstK]
  have hacc := (mem_allocation_deviated_iff Γ i (broadcastAction (d i).1.2)
    ((d, s), (d i).2) j).mpr ⟨hroute, hs⟩
  change 0 < (accepted (deviated i (broadcastAction (d i).1.2)
    ((d, s), (d i).2)) Γ.policy s i).card
  apply Finset.card_pos.mpr
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hacc⟩⟩

def broadcastViolationAt (g : ℝ) (R : Finset (Fin n)) : Set (UserDraw n) :=
  {d | 0 < d.1.2.bid ∧ 0 < d.1.1 - d.1.2.bid - g ∧
    firstK d.2 d.1.2.routeCount = R}

theorem measure_broadcastViolationAt_zero (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hsym : SymmetricProposersOnPath Γ) (R : Finset (Fin n)) (hR : R.card < n) :
    userLaw Γ (broadcastViolationAt Γ.g R) = 0 := by
  classical
  by_contra hmass
  have hzero : ∀ᵐ ω ∂backgroundLaw Γ, ∀ i : Fin m,
      0 < (ω.1 i).1.1 - (ω.1 i).1.2.bid - Γ.g →
        playedCount Γ i ω = 0 → playedBroadcastCount Γ i ω = 0 :=
    ae_all_iff.mpr (ae_played_no_broadcast_rescue Γ hA hG hu)
  have hdrawzero := Measure.ae_ae_of_ae_prod hzero
  have hdrawsym : ∀ᵐ d ∂userProfileLaw Γ, ∀ j : Fin n,
      SymmetricAtList Γ (observe (drawsRealization d) j)
        (seedLottery Γ j (observe (drawsRealization d) j)) :=
    ae_all_iff.mpr fun j => ae_of_ae_map (measurable_observe_draws j).aemeasurable (hsym j)
  let D : Set (UserProfile m n) := Set.univ.pi fun _ : Fin m => broadcastViolationAt Γ.g R
  have hD : userProfileLaw Γ D ≠ 0 := by
    simp only [D, userProfileLaw, Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hmass
  obtain ⟨d, hdD, hdz, hds⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hD
    (ae_restrict_of_ae (hdrawzero.and hdrawsym))
  have hd (i : Fin m) : 0 < (d i).1.2.bid ∧ 0 < (d i).1.1 - (d i).1.2.bid - Γ.g ∧
      firstK (d i).2 (d i).1.2.routeCount = R := hdD i (Set.mem_univ i)
  obtain ⟨i, E, hE, hfail⟩ := exists_common_route_failure Γ hcm d R
    (fun i => (hd i).2.2) (fun j _ => hds j)
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ∉ R := by
    by_contra! h
    have he : R = Finset.univ := Finset.eq_univ_of_forall h
    rw [he, Finset.card_univ, Fintype.card_fin] at hR
    omega
  have hpos := ae_outside_broadcast_positive Γ hc d R (fun i => (hd i).2.2)
    j hj (hrat j) i (hd i).1
  obtain ⟨s, hsE, hsz, hsp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hE
    (ae_restrict_of_ae (hdz.and hpos))
  have hz := hsz i (hd i).2.1 (hfail s hsE)
  have hzv : (playedBroadcastCount Γ i (d, s)).val = 0 := congrArg Fin.val hz
  omega

theorem ae_positive_surplus_broadcast_userLaw (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hsym : SymmetricProposersOnPath Γ) :
    ∀ᵐ d ∂userLaw Γ, 0 < d.1.2.bid → 0 < d.1.1 - d.1.2.bid - Γ.g →
      d.1.2.routeCount = n := by
  classical
  have hall : ∀ᵐ d ∂userLaw Γ, ∀ R : Finset (Fin n), R.card < n →
      d ∉ broadcastViolationAt Γ.g R :=
    ae_all_iff.mpr fun R => by
      by_cases hR : R.card < n
      · exact (measure_eq_zero_iff_ae_notMem.mp
          (measure_broadcastViolationAt_zero Γ hc hcm hA hG hu hrat hsym R hR)).mono
          fun _ h _ => h
      · exact Filter.Eventually.of_forall fun _ h => (hR h).elim
  filter_upwards [hall] with d hd hb hs
  by_contra hfull
  have hlt : d.1.2.routeCount < n := lt_of_le_of_ne d.1.2.routeCount_le hfull
  have hr : (firstK d.2 d.1.2.routeCount).card < n := by
    rw [card_firstK _ _ d.1.2.routeCount_le]
    exact hlt
  exact hd (firstK d.2 d.1.2.routeCount) hr ⟨hb, hs, rfl⟩

theorem ae_positive_surplus_broadcast_compProd (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hsym : SymmetricProposersOnPath Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid → 0 < x.1 - x.2.bid - Γ.g → x.2.routeCount = n := by
  have h := Measure.ae_ae_of_ae_prod
    (ae_positive_surplus_broadcast_userLaw Γ hc hcm hA hG hu hrat hsym)
  filter_upwards [h] with x hx
  obtain ⟨_, hτ⟩ := hx.exists
  exact hτ

theorem ae_positive_surplus_broadcast (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hsym : SymmetricProposersOnPath Γ) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, 0 < a.bid → 0 < v - a.bid - Γ.g → a.routeCount = n :=
  Measure.ae_ae_of_ae_compProd
    (ae_positive_surplus_broadcast_compProd Γ hc hcm hA hG hu hrat hsym)

end FCAppendix.Bayes
