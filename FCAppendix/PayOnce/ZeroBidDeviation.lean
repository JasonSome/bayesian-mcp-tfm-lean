import FCAppendix.PayOnce.Participation

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem few_positive_rivals_of_zero_accepts_local (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (ω : Background m n Seed)
    (belief : Fin m → FiniteLaw (Fin n))
    (hopt : Finite.Optimal c (beliefReceipts Γ.A belief (presentList ω i 0 j))
      (Γ.policy j (presentList ω i 0 j) (ω.2 j)).val)
    (hacc : Accepts Γ i 0 j ω) : rivals i (aboveAt j 0) ω < c := by
  classical
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hA (r : ℕ) (hr : 0 < r) (hrn : r ≤ n) : (1 / (n : ℝ)) * r ≤ Γ.A.charge r := by
    have hrR : (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hratio : (r : ℝ) / n ≤ 1 := (div_le_one hn).mpr hrR
    simpa [div_eq_mul_inv, mul_comm] using hratio.trans (Γ.A.lower r hr hrn)
  let ℓ := presentList ω i 0 j
  let r := beliefReceipts Γ.A belief ℓ
  have hri := (beliefReceipts_bounds Γ.A belief ℓ (1 / (n : ℝ)) hA
    i 0 le_rfl (presentList_self ω i 0 j)).2
  by_contra hmany
  push Not at hmany
  apply Finite.excluded_of_many_better c r _ hopt i _ hacc
  rw [rivals_eq_card] at hmany
  refine le_trans hmany (Finset.card_le_card ?_)
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    aboveAt, Set.mem_setOf_eq] at hl
  obtain ⟨hli, hreach, hbid⟩ := hl
  have hsome : ℓ l = some (ω.1 l).1.2.bid := by
    simp only [ℓ, presentList_other ω i l hli, if_pos hreach]
  have hrl := (beliefReceipts_bounds Γ.A belief ℓ (1 / (n : ℝ)) hA
    l _ (ω.1 l).1.2.bid_nonneg hsome).1
  have hpos := mul_pos (one_div_pos.mpr hn) hbid
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change r i < r l
  change r i ≤ 0 at hri
  change (1 / (n : ℝ)) * (ω.1 l).1.2.bid ≤ r l at hrl
  linarith

theorem ae_zero_accepts_few_positive (Γ : FiniteGame m n c Seed)
    (j : Fin n) (hj : ProposerRationalAtFeasibleLists Γ j) (i : Fin m) :
    ∀ᵐ ω ∂backgroundLaw Γ, Accepts Γ i 0 j ω → rivals i (aboveAt j 0) ω < c := by
  have hac := measurableSet_accepts Γ i 0 j
  have hf := measurableSet_rivals_lt (Seed := Seed) i (aboveAt j 0) (measurableSet_aboveAt j 0) c
  have hp : MeasurableSet {ω : Background m n Seed |
      Accepts Γ i 0 j ω → rivals i (aboveAt j 0) ω < c} := by
    simpa only [imp_iff_not_or, Set.compl_setOf, Set.setOf_or] using hac.compl.union hf
  apply (Measure.ae_prod_iff_ae_ae hp).mpr
  obtain ⟨belief, hopt⟩ := hj
  apply Filter.Eventually.of_forall
  intro d
  let ℓ := presentDrawList d i 0 j
  have hs := hopt ℓ (presentDrawList_feasible d i 0 le_rfl j)
  have hseeds := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae hs
  filter_upwards [hseeds] with s hS hacc
  exact few_positive_rivals_of_zero_accepts_local Γ j i (d, s) (belief ℓ) hS hacc

theorem ae_positive_accepts_of_zero_accepts (Γ : FiniteGame m n c Seed)
    (j : Fin n) (hj : ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (b : ℝ) (hb : 0 < b) :
    ∀ᵐ ω ∂backgroundLaw Γ, Accepts Γ i 0 j ω → Accepts Γ i b j ω := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hA (r : ℕ) (hr : 0 < r) (hrn : r ≤ n) : (1 / (n : ℝ)) * r ≤ Γ.A.charge r := by
    have hrR : (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hratio : (r : ℝ) / n ≤ 1 := (div_le_one hn).mpr hrR
    simpa [div_eq_mul_inv, mul_comm] using hratio.trans (Γ.A.lower r hr hrn)
  have hrank := ae_receipt_rank_bounds Γ j hj i (1 / n) (one_div_pos.mpr hn) hA b hb
  filter_upwards [ae_zero_accepts_few_positive Γ j hj i, hrank] with ω hzero hpos ha
  apply hpos.1
  apply lt_of_le_of_lt _ (hzero ha)
  rw [rivals_eq_card, rivals_eq_card]
  apply Finset.card_le_card
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    atLeastAt, aboveAt, Set.mem_setOf_eq] at hl ⊢
  exact ⟨hl.1, hl.2.1, lt_of_lt_of_le (mul_pos (one_div_pos.mpr hn) hb) hl.2.2⟩

theorem ae_zero_bid_count_le_fullBid (Γ : FiniteGame m n c Seed)
    (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j) (i : Fin m)
    (a : JointAction n) (ha : a.bid = 0) (b : ℝ) (hb : 0 < b) :
    ∀ᵐ ω ∂sampleLaw Γ, (focalCount Γ i a ω).val ≤
      (focalCount Γ i (fullBid n b hb.le) ω).val := by
  classical
  have hacc : ∀ᵐ ω ∂backgroundLaw Γ, ∀ j, Accepts Γ i 0 j ω → Accepts Γ i b j ω :=
    ae_all_iff.mpr fun j => ae_positive_accepts_of_zero_accepts Γ j (hrat j) i b hb
  have hs := (measurePreserving_fst (μ := backgroundLaw Γ)
    (ν := permLaw n)).quasiMeasurePreserving.ae hacc
  filter_upwards [hs] with ω hω
  change (accepted (deviated i a ω) Γ.policy ω.1.2 i).card ≤
    (accepted (deviated i (fullBid n b hb.le) ω) Γ.policy ω.1.2 i).card
  apply Finset.card_le_card
  intro j hj
  have hsel := (Finset.mem_filter.mp hj).2
  obtain ⟨_, hzero⟩ := (mem_allocation_deviated_iff Γ i a ω j).mp hsel
  rw [ha] at hzero
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  apply (mem_allocation_deviated_iff Γ i (fullBid n b hb.le) ω j).mpr
  refine ⟨?_, hω j hzero⟩
  simp [fullBid, mem_firstK]

def ZeroRivals (i : Fin m) (ω : Sample m n Seed) : Prop :=
  ∀ l : Fin m, l ≠ i → (ω.1.1 l).1.2.bid = 0

theorem measurableSet_zeroRivals (i : Fin m) :
    MeasurableSet {ω : Sample m n Seed | ZeroRivals i ω} := by
  classical
  unfold ZeroRivals
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro l
  apply MeasurableSet.iInter
  intro _
  have hm : Measurable (fun ω : Sample m n Seed => (ω.1.1 l).1.2.bid) :=
    (measurable_bid n).comp (measurable_snd.comp (measurable_fst.comp
      ((measurable_pi_apply l).comp (measurable_fst.comp measurable_fst))))
  exact measurableSet_eq_fun hm measurable_const

theorem ae_fullBid_positive_of_zeroRivals (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (hc : 0 < c) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (b : ℝ) (hb : 0 < b) :
    ∀ᵐ ω ∂sampleLaw Γ, ZeroRivals i ω → 0 < (focalCount Γ i (fullBid n b hb.le) ω).val := by
  classical
  let j : Fin n := ⟨0, hn⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hA (r : ℕ) (hr : 0 < r) (hrn : r ≤ n) : (1 / (n : ℝ)) * r ≤ Γ.A.charge r := by
    have hrR : (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hratio : (r : ℝ) / n ≤ 1 := (div_le_one hnR).mpr hrR
    simpa [div_eq_mul_inv, mul_comm] using hratio.trans (Γ.A.lower r hr hrn)
  have hrank := ae_receipt_rank_bounds Γ j (hrat j) i (1 / n) (one_div_pos.mpr hnR) hA b hb
  have hs := (measurePreserving_fst (μ := backgroundLaw Γ)
    (ν := permLaw n)).quasiMeasurePreserving.ae hrank
  filter_upwards [hs] with ω hω hz
  have hfew : rivals i (atLeastAt j (1 / n * b)) ω.1 < c := by
    rw [rivals_eq_card]
    have he : ((Finset.univ.erase i).filter fun l => ω.1.1 l ∈ atLeastAt j (1 / n * b)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro l hl hmem
      have hli := (Finset.mem_erase.mp hl).1
      have hbid := hmem.2
      rw [hz l hli] at hbid
      exact (not_le_of_gt (mul_pos (one_div_pos.mpr hnR) hb)) hbid
    rw [he, Finset.card_empty]
    exact hc
  have hacc := hω.1 hfew
  have hin := (mem_allocation_deviated_iff Γ i (fullBid n b hb.le) ω j).mpr
    ⟨by simp [fullBid, mem_firstK], hacc⟩
  change 0 < (accepted (deviated i (fullBid n b hb.le) ω) Γ.policy ω.1.2 i).card
  exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hin⟩⟩

def zeroRescueSet (Γ : FiniteGame m n c Seed) (i : Fin m) (a : JointAction n) :
    Set (Sample m n Seed) := {ω | ZeroRivals i ω ∧ focalCount Γ i a ω = 0}

theorem measurableSet_zeroRescueSet (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) : MeasurableSet (zeroRescueSet Γ i a) :=
  (measurableSet_zeroRivals i).inter (measurableSet_eq_fun (measurable_focalCount Γ i a) measurable_const)

theorem zeroRescue_prob_le_success_gain (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (hc : 0 < c) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (a : JointAction n) (ha : a.bid = 0) (b : ℝ) (hb : 0 < b) :
    (sampleLaw Γ).real (zeroRescueSet Γ i a) ≤
      ((problem Γ i).outcome (fullBid n b hb.le)).success - ((problem Γ i).outcome a).success := by
  classical
  let E := zeroRescueSet Γ i a
  have hE := measurableSet_zeroRescueSet Γ i a
  have hIfull := CountLaw.integrable_comp (sampleLaw Γ) _
    (measurable_focalCount Γ i (fullBid n b hb.le)) (fun r => successIndicator r.val)
  have hIold := CountLaw.integrable_comp (sampleLaw Γ) _
    (measurable_focalCount Γ i a) (fun r => successIndicator r.val)
  have hmono : ∀ᵐ ω ∂sampleLaw Γ, E.indicator (fun _ => (1 : ℝ)) ω ≤
      successIndicator (focalCount Γ i (fullBid n b hb.le) ω).val -
        successIndicator (focalCount Γ i a ω).val := by
    filter_upwards [ae_zero_bid_count_le_fullBid Γ hrat i a ha b hb,
      ae_fullBid_positive_of_zeroRivals Γ hn hc hrat i b hb] with ω hcount hnew
    by_cases he : ω ∈ E
    · have hold : (focalCount Γ i a ω).val = 0 := congrArg Fin.val he.2
      have hpos : (focalCount Γ i (fullBid n b hb.le) ω).val ≠ 0 := ne_of_gt (hnew he.1)
      simp [Set.indicator_of_mem he, successIndicator, hold, hpos]
    · rw [Set.indicator_of_notMem he]
      exact sub_nonneg.mpr (successIndicator_mono_nat hcount)
  have hi := integral_mono_ae ((integrable_const (1 : ℝ)).indicator hE)
    (hIfull.sub hIold) hmono
  rw [integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one] at hi
  simp only [Pi.sub_apply] at hi
  rw [integral_sub hIfull hIold] at hi
  simpa only [problem_outcome, CountLaw.success, CountLaw.expect_ofMeasure] using hi

theorem zeroRescue_null_of_zero_bestResponse (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (hc : 0 < c) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (i : Fin m) (v : ℝ) (hv : Γ.g < v) (a : JointAction n) (ha : a.bid = 0)
    (hbr : (problem Γ i).BestResponse v a) :
    sampleLaw Γ (zeroRescueSet Γ i a) = 0 := by
  by_contra hmass
  let q := (sampleLaw Γ).real (zeroRescueSet Γ i a)
  have hq : 0 < q := ENNReal.toReal_pos hmass (measure_ne_top _ _)
  let b := (v - Γ.g) * q / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hgain := zeroRescue_prob_le_success_gain Γ hn hc hrat i a ha b hb
  have hbest := hbr (fullBid n b hb.le)
  rw [payoff_once Γ hA hG, payoff_once Γ hA hG, ha] at hbest
  change (v - b - Γ.g) * ((problem Γ i).outcome (fullBid n b hb.le)).success ≤
    (v - 0 - Γ.g) * ((problem Γ i).outcome a).success at hbest
  have hcost := mul_le_mul_of_nonneg_left
    (CountLaw.success_le_one ((problem Γ i).outcome (fullBid n b hb.le))) hb.le
  change q ≤ _ at hgain
  have hw : 0 < v - Γ.g := sub_pos.mpr hv
  have hpaid := mul_le_mul_of_nonneg_left hgain hw.le
  dsimp [b] at hbest hcost
  nlinarith

private theorem measurableSet_implies {α : Type*} [MeasurableSpace α]
    {p q : α → Prop} (hp : MeasurableSet {x | p x}) (hq : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x → q x} := by
  simpa only [imp_iff_not_or, Set.compl_setOf, Set.setOf_or] using hp.compl.union hq

theorem ae_played_zero_bid_success_among_zero_rivals (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (hc : 0 < c) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (i : Fin m) : ∀ᵐ ω ∂backgroundLaw Γ,
    Γ.g < (ω.1 i).1.1 → (ω.1 i).1.2.bid = 0 →
      (∀ l : Fin m, l ≠ i → (ω.1 l).1.2.bid = 0) → playedCount Γ i ω ≠ 0 := by
  have harg : Measurable (fun p : (ℝ × JointAction n) × Sample m n Seed => (p.1.2, p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hcnt := (measurable_focalCount_joint Γ i).comp harg
  change Measurable (fun p : (ℝ × JointAction n) × Sample m n Seed =>
    focalCount Γ i p.1.2 p.2) at hcnt
  have hne : MeasurableSet {p : (ℝ × JointAction n) × Sample m n Seed |
      focalCount Γ i p.1.2 p.2 ≠ 0} := by
    simpa only [Set.compl_setOf] using (measurableSet_eq_fun hcnt measurable_const).compl
  have hp : MeasurableSet {p : (ℝ × JointAction n) × Sample m n Seed |
      Γ.g < p.1.1 → p.1.2.bid = 0 → ZeroRivals i p.2 → focalCount Γ i p.1.2 p.2 ≠ 0} :=
    measurableSet_implies (measurableSet_lt measurable_const (measurable_fst.comp measurable_fst))
      (measurableSet_implies (measurableSet_eq_fun
        ((measurable_bid n).comp (measurable_snd.comp measurable_fst)) measurable_const)
        (measurableSet_implies (measurable_snd (measurableSet_zeroRivals i)) hne))
  have hprod : ∀ᵐ p ∂(Γ.F ⊗ₘ Γ.σ).prod (sampleLaw Γ),
      Γ.g < p.1.1 → p.1.2.bid = 0 → ZeroRivals i p.2 → focalCount Γ i p.1.2 p.2 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae hp).mpr
    filter_upwards [ae_bestResponse_compProd Γ hu i] with x hx
    by_cases hv : Γ.g < x.1
    · by_cases hb : x.2.bid = 0
      · have hnul := measure_eq_zero_iff_ae_notMem.mp
          (zeroRescue_null_of_zero_bestResponse Γ hn hc hrat hA hG i x.1 hv x.2 hb hx)
        filter_upwards [hnul] with ω hω _ _ hz hcount
        exact hω ⟨hz, hcount⟩
      · exact Filter.Eventually.of_forall fun _ _ h => (hb h).elim
    · exact Filter.Eventually.of_forall fun _ h => (hv h).elim
  have hd : Measurable (fun ω : Background m n Seed => ω.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hv := measurable_fst.comp (measurable_fst.comp hd)
  have hb := (measurable_bid n).comp (measurable_snd.comp (measurable_fst.comp hd))
  have hz : MeasurableSet {ω : Background m n Seed |
      ∀ l : Fin m, l ≠ i → (ω.1 l).1.2.bid = 0} :=
    (measurable_id.prodMk (measurable_const (a := Equiv.refl (Fin n)))) (measurableSet_zeroRivals i)
  have hplayed : MeasurableSet {ω : Background m n Seed |
      Γ.g < (ω.1 i).1.1 → (ω.1 i).1.2.bid = 0 →
        (∀ l : Fin m, l ≠ i → (ω.1 l).1.2.bid = 0) → playedCount Γ i ω ≠ 0} := by
    apply measurableSet_implies (measurableSet_lt measurable_const hv)
    apply measurableSet_implies (measurableSet_eq_fun hb measurable_const)
    apply measurableSet_implies hz
    simpa only [Set.compl_setOf] using
      (measurableSet_eq_fun (measurable_playedCount Γ i) measurable_const).compl
  have hpres := playFromDeviation_measurePreserving Γ i
  rw [← hpres.map_eq]
  apply (ae_map_iff hpres.measurable.aemeasurable hplayed).mpr
  filter_upwards [hprod] with p hp hv hb hz
  have he : ((playFromDeviation i p).1 i).1 = p.1 := by simp [playFromDeviation, insertDraw]
  have hk : playedCount Γ i (playFromDeviation i p) = focalCount Γ i p.1.2 p.2 :=
    playedCount_insertDraw Γ i ((p.1, p.2.2), p.2.1)
  rw [hk]
  apply hp
  · simpa only [he] using hv
  · simpa only [he] using hb
  · intro l hl
    have h := hz l hl
    simpa only [playFromDeviation, insertDraw, Function.update_of_ne hl] using h

def zeroBidViolationAt (g : ℝ) (R : Finset (Fin n)) : Set (UserDraw n) :=
  {d | g < d.1.1 ∧ d.1.2.bid = 0 ∧ firstK d.2 d.1.2.routeCount = R}

theorem measure_zeroBidViolationAt_zero (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hsym : SymmetricProposersOnPath Γ) (R : Finset (Fin n)) :
    userLaw Γ (zeroBidViolationAt Γ.g R) = 0 := by
  classical
  by_contra hmass
  have hsuccess : ∀ᵐ ω ∂backgroundLaw Γ, ∀ i : Fin m,
      Γ.g < (ω.1 i).1.1 → (ω.1 i).1.2.bid = 0 →
        (∀ l : Fin m, l ≠ i → (ω.1 l).1.2.bid = 0) → playedCount Γ i ω ≠ 0 :=
    ae_all_iff.mpr (ae_played_zero_bid_success_among_zero_rivals Γ hn hc hrat hA hG hu)
  have hdrawsuccess := Measure.ae_ae_of_ae_prod hsuccess
  have hdrawsym : ∀ᵐ d ∂userProfileLaw Γ, ∀ j : Fin n,
      SymmetricAtList Γ (observe (drawsRealization d) j)
        (seedLottery Γ j (observe (drawsRealization d) j)) :=
    ae_all_iff.mpr fun j => ae_of_ae_map (measurable_observe_draws j).aemeasurable (hsym j)
  let D : Set (UserProfile m n) := Set.univ.pi fun _ : Fin m => zeroBidViolationAt Γ.g R
  have hD : userProfileLaw Γ D ≠ 0 := by
    simp only [D, userProfileLaw, Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hmass
  obtain ⟨d, hdD, hdsuccess, hdsym⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hD
    (ae_restrict_of_ae (hdrawsuccess.and hdrawsym))
  have hd (i : Fin m) : Γ.g < (d i).1.1 ∧ (d i).1.2.bid = 0 ∧
      firstK (d i).2 (d i).1.2.routeCount = R := hdD i (Set.mem_univ i)
  obtain ⟨i, E, hE, hfail⟩ := exists_common_route_failure Γ hcm d R
    (fun i => (hd i).2.2) (fun j _ => hdsym j)
  obtain ⟨s, hsE, hsucc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hE
    (ae_restrict_of_ae hdsuccess)
  exact hsucc i (hd i).1 (hd i).2.1 (fun l _ => (hd l).2.1) (hfail s hsE)

theorem ae_positive_value_bid_pos_userLaw (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hsym : SymmetricProposersOnPath Γ) :
    ∀ᵐ d ∂userLaw Γ, Γ.g < d.1.1 → 0 < d.1.2.bid := by
  classical
  have hall : ∀ᵐ d ∂userLaw Γ, ∀ R : Finset (Fin n), d ∉ zeroBidViolationAt Γ.g R :=
    ae_all_iff.mpr fun R => measure_eq_zero_iff_ae_notMem.mp
      (measure_zeroBidViolationAt_zero Γ hn hc hcm hA hG hu hrat hsym R)
  filter_upwards [hall] with d hd hv
  apply lt_of_le_of_ne d.1.2.bid_nonneg
  intro hz
  exact hd (firstK d.2 d.1.2.routeCount) ⟨hv, hz.symm, rfl⟩

theorem ae_positive_value_bid_pos_compProd (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hsym : SymmetricProposersOnPath Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), Γ.g < x.1 → 0 < x.2.bid := by
  have h := Measure.ae_ae_of_ae_prod
    (ae_positive_value_bid_pos_userLaw Γ hn hc hcm hA hG hu hrat hsym)
  filter_upwards [h] with x hx
  exact hx.exists.choose_spec

theorem ae_positive_value_bid_pos (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hsym : SymmetricProposersOnPath Γ) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, Γ.g < v → 0 < a.bid :=
  Measure.ae_ae_of_ae_compProd
    (ae_positive_value_bid_pos_compProd Γ hn hc hcm hA hG hu hrat hsym)

end FCAppendix.Bayes
