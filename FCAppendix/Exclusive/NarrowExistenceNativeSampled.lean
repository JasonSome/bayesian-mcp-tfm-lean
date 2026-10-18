import FCAppendix.Exclusive.NarrowExistenceNativeStatistics
import FCAppendix.Exclusive.NarrowGlobalHighSample

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Existence Exclusive.Narrow.Global
open scoped BigOperators

def actionBidVector {m n : ℕ} (b : ℝ) (acts : Fin m → JointAction n) : Fin (m+1) → ℝ :=
  Fin.cases b (fun j => if (acts j).routeCount = 0 then 0 else (acts j).bid)

def actionPrice {m : ℕ} (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ℝ)
    (acts : Fin m → JointAction n) : ℝ := canonicalPrice n hn c (actionBidVector b acts)

theorem totalDemand_focalList_eq_actionBidVector {m n : ℕ} (i : Fin (m+1)) (b : ℝ)
    (profile : UserProfile (m+1) n) (t : ℝ) :
    totalDemand n (listBids (focalList i b profile)) t =
      totalDemand n (actionBidVector b (fun j : Fin m => (profile (i.succAbove j)).1.2)) t := by
  classical
  unfold totalDemand
  rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succ]
  simp only [listBids, focalList, if_true, readBid, actionBidVector, Fin.cases_zero, Fin.cases_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.succAbove_ne, if_false]
  split_ifs <;> rfl

theorem native_focalPrice_eq_actionPrice {m n c : ℕ} (hn : 2 ≤ n) (hc : 0 < c)
    (i : Fin (m+1)) (b : ℝ) (profile : UserProfile (m+1) n) :
    ExclusiveSource.focalPrice n hn c i b profile =
      actionPrice n hn c b (fun j : Fin m => (profile (i.succAbove j)).1.2) :=
  canonicalPrice_eq_of_totalDemand_eq n hn c hc _ _
    (totalDemand_focalList_eq_actionBidVector i b profile)

theorem native_focalMarginal_eq_actionPrice {m n c : ℕ} (hn : 2 ≤ n) (hc : 0 < c)
    (i : Fin (m+1)) (b : ℝ) (profile : UserProfile (m+1) n) :
    ExclusiveSource.focalMarginal n hn c i b profile =
      activeDemand n b (actionPrice n hn c b (fun j : Fin m => (profile (i.succAbove j)).1.2)) := by
  have he : ExclusiveSource.focalMarginal n hn c i b profile =
      activeDemand n b (ExclusiveSource.focalPrice n hn c i b profile) := by
    simp only [ExclusiveSource.focalMarginal, canonicalListMarginal, canonicalMarginal,
      ExclusiveSource.focalPrice, listBids, focalList, if_true, readBid]
  rw [he, native_focalPrice_eq_actionPrice hn hc]

theorem activeDemand_scale (n : ℕ) (H : ℝ) (hH : 0 < H) (b t : ℝ) :
    activeDemand n (H*b) (H*t) = activeDemand n b t := by
  unfold activeDemand
  have he : 0 < H*b ↔ 0 < b := mul_pos_iff_of_pos_left hH
  simp only [he]
  split_ifs
  · have hquot : (H*t)/(H*b) = t/b := by field_simp
    simp only [demand, hquot]
  · rfl

theorem totalDemand_scale {I : Type*} [Fintype I] (n : ℕ) (H : ℝ) (hH : 0 < H)
    (b : I → ℝ) (t : ℝ) :
    totalDemand n (fun i => H*b i) (H*t) = totalDemand n b t := by
  unfold totalDemand
  simp_rw [activeDemand_scale n H hH]

theorem canonicalPrice_scale {I : Type*} [Fintype I] (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c)
    (H : ℝ) (hH : 0 < H) (b : I → ℝ) :
    canonicalPrice n hn c (fun i => H*b i) = H*canonicalPrice n hn c b := by
  let C := canonicalPrice n hn c (fun i => H*b i)
  let D := canonicalPrice n hn c b
  have he (t : ℝ) : C < H*t ↔ D < t := by
    rw [canonicalPrice_lt_iff n hn c hc, canonicalPrice_lt_iff n hn c hc,
      totalDemand_scale n H hH]
    exact and_congr (mul_pos_iff_of_pos_left hH) Iff.rfl
  apply le_antisymm
  · apply le_of_not_gt
    intro hlt
    have hd : D < C/H := (lt_div_iff₀ hH).mpr (by simpa only [mul_comm] using hlt)
    have hh := (he (C/H)).mpr hd
    rw [mul_div_cancel₀ _ hH.ne'] at hh
    exact (lt_irrefl C) hh
  · apply le_of_not_gt
    intro hlt
    exact (lt_irrefl D) ((he D).mp hlt)

theorem actionBidVector_flag {m n : ℕ} {V : Type*} (hn : 0 < n) (scale b : ℝ)
    (hscale : 0 ≤ scale) (beta : V → ℝ) (omega : RivalProfile m V) :
    actionBidVector b (fun j => flagAction n (fun v => scale*Real.exp (beta v)) (omega j)) =
      sampledBids scale beta b omega := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    have hnonneg := mul_nonneg hscale (Real.exp_pos (beta (omega j).2)).le
    cases hx : (omega j).1 <;>
      simp [actionBidVector, flagAction, sampledBids, sampledRivalBid, hx, hn.ne', Interim.abstain,
        max_eq_left hnonneg]

theorem sampledBids_scale {m : ℕ} {V : Type*} (H scale b : ℝ)
    (beta : V → ℝ) (omega : RivalProfile m V) :
    sampledBids (H*scale) beta (H*b) omega = fun i => H*sampledBids scale beta b omega i := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    cases hx : (omega j).1 <;> simp [sampledBids, sampledRivalBid, hx, mul_assoc]

theorem actionPrice_flag_scale {m : ℕ} {V : Type*} (d : ℕ) (hd : 1 ≤ d) (c : ℕ) (hc : 0 < c)
    (H scale b : ℝ) (hH : 0 < H) (hscale : 0 < scale) (beta : V → ℝ) (omega : RivalProfile m V) :
    actionPrice (d+1) (by omega) c (H*b)
      (fun j => flagAction (d+1) (fun v => H*scale*Real.exp (beta v)) (omega j)) =
        H*sampledPrice d hd c scale beta b omega := by
  unfold actionPrice
  rw [actionBidVector_flag (by omega) _ _ (mul_pos hH hscale).le,
    sampledBids_scale, canonicalPrice_scale (d+1) (by omega) c hc H hH]
  rfl

theorem measurable_actionPrice {m : ℕ} (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c) (b : ℝ) :
    Measurable (actionPrice (m := m) n hn c b) := by
  apply (measurable_canonicalPrice n hn c hc).comp
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ ?_ i
  · exact measurable_const
  · intro j
    exact Measurable.ite
      (measurableSet_eq_fun ((measurable_routeCount n).comp (measurable_pi_apply j)) measurable_const)
      measurable_const ((measurable_bid n).comp (measurable_pi_apply j))

def actionMenuPayoff {m : ℕ} (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (a : UserTariff)
    (G : Schedule n) (k : ℕ) (g v b : ℝ) (acts : Fin m → JointAction n) : ℝ :=
  LowType.binomialPayoff a G k g v b (activeDemand n b (actionPrice n hn c b acts))

theorem measurable_actionMenuPayoff {m : ℕ} (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c)
    (a : UserTariff) (G : Schedule n) (k : ℕ) (g v b : ℝ) :
    Measurable (actionMenuPayoff (m := m) n hn c a G k g v b) :=
  (LowType.continuous_binomialPayoff a G k g v b).measurable.comp
    ((measurable_activeDemand n hn).comp (measurable_const.prodMk (measurable_actionPrice n hn c hc b)))

theorem actionMenuPayoff_flag_scale {m : ℕ} {V : Type*} (d : ℕ) (hd : 1 ≤ d)
    (c : ℕ) (hc : 0 < c) (a : UserTariff) (G : Schedule (d+1)) (k : ℕ)
    (H scale g v b : ℝ) (hH : 0 < H) (hscale : 0 < scale) (beta : V → ℝ) (omega : RivalProfile m V) :
    actionMenuPayoff (d+1) (by omega) c a G k (H*g) (H*v) (H*b)
      (fun j => flagAction (d+1) (fun w => H*scale*Real.exp (beta w)) (omega j)) =
        H*LowType.binomialPayoff a G k g v b
          (activeDemand (d+1) b (sampledPrice d hd c scale beta b omega)) := by
  unfold actionMenuPayoff
  rw [actionPrice_flag_scale d hd c hc H scale b hH hscale, activeDemand_scale (d+1) H hH]
  dsimp [LowType.binomialPayoff]
  ring

theorem source_menu_payoff_sampled {m d c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {V : Type*} [MeasurableSpace V]
    (Gamma : FiniteGame (m+1) (d+1) c Seed) (hd : 1 ≤ d) (hc : 0 < c)
    (cutoff : ℝ) (fallback : LocalPolicy (m+1) c Seed)
    (hfallback : Measurable (fun p : LocalList (m+1) × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ L, FiniteLaw.ofMeasure Gamma.seedLaw (fun s => (fallback L s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery (d+1) (by omega) c (listBids L))
    (hpolicy : ∀ j L s, (Gamma.policy j L s).val =
      (Marker.sourceContinuation (m := m+1) (n := d+1) (c := c)
        (by omega) (by omega) hc cutoff fallback L s).val)
    (i : Fin (m+1))
    (hhigh : ∀ᵐ profile ∂userProfileLaw Gamma, ExclusiveSource.HighRivals cutoff i profile)
    (a : UserTariff) (H scale g v : ℝ) (hH : 0 < H) (hscale : 0 < scale)
    (hcharge : Gamma.g = H*g) (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Measurable beta) (action : JointAction (d+1)) (hb : cutoff ≤ action.bid)
    (hlaw : (userProfileLaw Gamma).map (fun profile j => (profile (i.succAbove j)).1.2) =
      (iidRivalLaw m h nu).map (fun omega j => flagAction (d+1)
        (fun w => H*scale*Real.exp (beta w)) (omega j))) :
    exclusiveTariffPayoff Gamma a i (H*v) action =
      H*∫ omega, LowType.binomialPayoff a Gamma.G action.routeCount g v (action.bid/H)
        (activeDemand (d+1) (action.bid/H)
          (sampledPrice d hd c scale beta (action.bid/H) omega)) ∂iidRivalLaw m h nu := by
  let b := action.bid/H
  have hbid : H*b = action.bid := by dsimp [b]; field_simp
  let test := actionMenuPayoff (m := m) (d+1) (by omega) c a Gamma.G action.routeCount (H*g) (H*v) (H*b)
  have htest : Measurable test := measurable_actionMenuPayoff (d+1) (by omega) c hc a Gamma.G _ _ _ _
  have hproj : Measurable (fun profile : UserProfile (m+1) (d+1) =>
      fun j : Fin m => (profile (i.succAbove j)).1.2) :=
    measurable_pi_lambda _ (fun j => measurable_snd.comp (measurable_fst.comp (measurable_pi_apply _)))
  have hflag : Measurable (fun omega : RivalProfile m V => fun j => flagAction (d+1)
      (fun w => H*scale*Real.exp (beta w)) (omega j)) :=
    measurable_pi_lambda _ (fun j =>
      (measurable_flagAction (d+1) (measurable_const.mul (Real.continuous_exp.measurable.comp hbeta))).comp
        (measurable_pi_apply j))
  rw [ExclusiveSource.source_actual_payoff_large_bid Gamma (by omega) (by omega) hc cutoff
    fallback hfallback hcanonical hpolicy a i hhigh _ action hb]
  calc
    _ = ∫ profile, test (fun j : Fin m => (profile (i.succAbove j)).1.2) ∂userProfileLaw Gamma := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun profile => by
        dsimp [test, actionMenuPayoff]
        rw [hbid, ← hcharge, native_focalMarginal_eq_actionPrice (by omega) hc])
    _ = ∫ acts, test acts ∂(userProfileLaw Gamma).map
        (fun profile j => (profile (i.succAbove j)).1.2) :=
      (integral_map hproj.aemeasurable htest.aestronglyMeasurable).symm
    _ = ∫ acts, test acts ∂(iidRivalLaw m h nu).map
        (fun omega j => flagAction (d+1) (fun w => H*scale*Real.exp (beta w)) (omega j)) := by rw [hlaw]
    _ = ∫ omega, test (fun j => flagAction (d+1) (fun w => H*scale*Real.exp (beta w)) (omega j)) ∂iidRivalLaw m h nu :=
      integral_map hflag.aemeasurable htest.aestronglyMeasurable
    _ = ∫ omega, H*LowType.binomialPayoff a Gamma.G action.routeCount g v b
        (activeDemand (d+1) b (sampledPrice d hd c scale beta b omega)) ∂iidRivalLaw m h nu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (actionMenuPayoff_flag_scale d hd c hc a Gamma.G action.routeCount
        H scale g v b hH hscale beta)
    _ = _ := integral_const_mul _ _

theorem canonical_actual_payoff {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m n c Seed) (hn : 2 ≤ n)
    (hcanonical : ∀ j L, seedLottery Gamma j L = canonicalLottery n hn c (listBids L))
    (i : Fin m) (hhigh : ∀ᵐ profile ∂userProfileLaw Gamma, ExclusiveSource.HighRivals 0 i profile)
    (a : UserTariff) (v : ℝ) (action : JointAction n) :
    exclusiveTariffPayoff Gamma a i v action =
      ∫ profile, LowType.binomialPayoff a Gamma.G action.routeCount Gamma.g v action.bid
        (ExclusiveSource.focalMarginal n hn c i action.bid profile) ∂userProfileLaw Gamma := by
  rw [ExclusiveSource.exclusiveTariffPayoff_eq_test, interim_expect_eq_profile_update Gamma i (v,action)]
  have he (tau : Equiv.Perm (Fin n)) :
      (∫ profile, (profileCountLaw Gamma (Function.update profile i ((v,action),tau)) i).expect
        (fun r => ExclusiveSource.payoffTest a Gamma.G Gamma.g v action.bid r.val) ∂userProfileLaw Gamma) =
      ∫ profile, LowType.binomialPayoff a Gamma.G action.routeCount Gamma.g v action.bid
        (ExclusiveSource.focalMarginal n hn c i action.bid profile) ∂userProfileLaw Gamma := by
    apply integral_congr_ae
    filter_upwards [hhigh] with profile hprofile
    have hs : SymmetricAtList Gamma (focalList i action.bid profile)
        (canonicalLottery n hn c (listBids (focalList i action.bid profile))) :=
      fun j => hcanonical j _
    have hh := ExclusiveSource.profile_test_of_recipient_common_list Gamma (Function.update profile i ((v,action),tau)) i
      (focalList i action.bid profile)
      (ExclusiveSource.observe_update_recipient_eq_focalList 0 i profile hprofile (v,action) tau)
      (canonicalLottery n hn c (listBids (focalList i action.bid profile))) hs
      (ExclusiveSource.payoffTest a Gamma.G Gamma.g v action.bid)
    have ht : (profileCountLaw Gamma (Function.update profile i ((v,action),tau)) i).expect
        (fun r => ExclusiveSource.payoffTest a Gamma.G Gamma.g v action.bid r.val) =
      Narrow.binomialPolynomial action.routeCount (ExclusiveSource.payoffTest a Gamma.G Gamma.g v action.bid)
        (ExclusiveSource.focalMarginal n hn c i action.bid profile) := by
      simpa only [drawsRealization, Function.update_self,
        card_firstK tau action.routeCount action.routeCount_le, canonicalLottery_marginal,
        ExclusiveSource.focalMarginal, canonicalListMarginal] using hh
    rw [ht]
    exact ExclusiveSource.binomial_payoffTest a Gamma.G action.routeCount Gamma.g v action.bid _
      (ExclusiveSource.focalMarginal_bounds hn i action.bid profile).1
      (ExclusiveSource.focalMarginal_bounds hn i action.bid profile).2
  simp_rw [he]
  simp

theorem canonical_menu_payoff_sampled {m d c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {V : Type*} [MeasurableSpace V]
    (Gamma : FiniteGame (m+1) (d+1) c Seed) (hd : 1 ≤ d) (hc : 0 < c)
    (hcanonical : ∀ j L, seedLottery Gamma j L = canonicalLottery (d+1) (by omega) c (listBids L))
    (i : Fin (m+1))
    (hhigh : ∀ᵐ profile ∂userProfileLaw Gamma, ExclusiveSource.HighRivals 0 i profile)
    (a : UserTariff) (H scale g v : ℝ) (hH : 0 < H) (hscale : 0 < scale)
    (hcharge : Gamma.g = H*g) (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Measurable beta) (action : JointAction (d+1))
    (hlaw : (userProfileLaw Gamma).map (fun profile j => (profile (i.succAbove j)).1.2) =
      (iidRivalLaw m h nu).map (fun omega j => flagAction (d+1)
        (fun w => H*scale*Real.exp (beta w)) (omega j))) :
    exclusiveTariffPayoff Gamma a i (H*v) action =
      H*∫ omega, LowType.binomialPayoff a Gamma.G action.routeCount g v (action.bid/H)
        (activeDemand (d+1) (action.bid/H)
          (sampledPrice d hd c scale beta (action.bid/H) omega)) ∂iidRivalLaw m h nu := by
  let b := action.bid/H
  have hbid : H*b = action.bid := by dsimp [b]; field_simp
  let test := actionMenuPayoff (m := m) (d+1) (by omega) c a Gamma.G action.routeCount (H*g) (H*v) (H*b)
  have htest : Measurable test := measurable_actionMenuPayoff (d+1) (by omega) c hc a Gamma.G _ _ _ _
  have hproj : Measurable (fun profile : UserProfile (m+1) (d+1) =>
      fun j : Fin m => (profile (i.succAbove j)).1.2) :=
    measurable_pi_lambda _ (fun j => measurable_snd.comp (measurable_fst.comp (measurable_pi_apply _)))
  have hflag : Measurable (fun omega : RivalProfile m V => fun j => flagAction (d+1)
      (fun w => H*scale*Real.exp (beta w)) (omega j)) :=
    measurable_pi_lambda _ (fun j =>
      (measurable_flagAction (d+1) (measurable_const.mul (Real.continuous_exp.measurable.comp hbeta))).comp
        (measurable_pi_apply j))
  rw [canonical_actual_payoff Gamma (by omega) hcanonical i hhigh]
  calc
    _ = ∫ profile, test (fun j : Fin m => (profile (i.succAbove j)).1.2) ∂userProfileLaw Gamma := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun profile => by
        dsimp [test, actionMenuPayoff]
        rw [hbid, ← hcharge, native_focalMarginal_eq_actionPrice (by omega) hc])
    _ = ∫ acts, test acts ∂(userProfileLaw Gamma).map
        (fun profile j => (profile (i.succAbove j)).1.2) :=
      (integral_map hproj.aemeasurable htest.aestronglyMeasurable).symm
    _ = ∫ acts, test acts ∂(iidRivalLaw m h nu).map
        (fun omega j => flagAction (d+1) (fun w => H*scale*Real.exp (beta w)) (omega j)) := by rw [hlaw]
    _ = ∫ omega, test (fun j => flagAction (d+1) (fun w => H*scale*Real.exp (beta w)) (omega j)) ∂iidRivalLaw m h nu :=
      integral_map hflag.aemeasurable htest.aestronglyMeasurable
    _ = ∫ omega, H*LowType.binomialPayoff a Gamma.G action.routeCount g v b
        (activeDemand (d+1) b (sampledPrice d hd c scale beta b omega)) ∂iidRivalLaw m h nu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (actionMenuPayoff_flag_scale d hd c hc a Gamma.G action.routeCount
        H scale g v b hH hscale beta)
    _ = _ := integral_const_mul _ _

end FCAppendix.Bayes.ExclusiveConstruction
