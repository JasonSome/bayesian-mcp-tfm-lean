import FCAppendix.Exclusive.NarrowRivalCalculus
import FCAppendix.Exclusive.BayesianKernel
import FCAppendix.PayOnce.InterimCountTransport

noncomputable section
namespace FCAppendix.Bayes.ExclusiveNarrow
open MeasureTheory ProbabilityTheory Game Exclusive Exclusive.Narrow
open Exclusive.Narrow.Finite Set Filter Topology
open scoped BigOperators ProbabilityTheory

variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def CorridorPlay (Γ : FiniteGame m n c Seed) (P : Corridor n m c) : Prop :=
  ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨
    (x.2.routeCount = n ∧ x.2.bid ∈ Icc P.lower P.upper)

def GoodProfile (P : Corridor n m c) (d : UserProfile m n) : Prop :=
  ∀ j, (d j).1.2.routeCount = 0 ∨
    ((d j).1.2.routeCount = n ∧ (d j).1.2.bid ∈ Icc P.lower P.upper)

lemma ae_goodProfile (Γ : FiniteGame m n c Seed) (P : Corridor n m c)
    (hplay : CorridorPlay Γ P) : ∀ᵐ d ∂userProfileLaw Γ, GoodProfile P d := by
  have hu := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw n)).quasiMeasurePreserving.ae hplay
  exact ae_all_iff.mpr fun j =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) j).quasiMeasurePreserving.ae hu

def activeRivals (i : Fin m) (d : UserProfile m n) : Finset (Fin m) := by
  classical
  exact (Finset.univ.erase i).filter fun j => (d j).1.2.routeCount ≠ 0

def rivalCount (i : Fin m) (d : UserProfile m n) : ℕ := (activeRivals i d).card + 1

def rivalWeight (i : Fin m) (d : UserProfile m n) : ℝ :=
  ∑ j ∈ activeRivals i d, inverseBid n (d j).1.2.bid

lemma not_mem_activeRivals (i : Fin m) (d : UserProfile m n) : i ∉ activeRivals i d := by
  classical
  simp [activeRivals]

lemma mem_activeRivals (i j : Fin m) (d : UserProfile m n) :
    j ∈ activeRivals i d ↔ j ≠ i ∧ (d j).1.2.routeCount ≠ 0 := by
  classical
  simp [activeRivals]

lemma measurable_rivalCount (i : Fin m) : Measurable (rivalCount (n := n) i) := by
  classical
  let f : (Fin m → ℕ) → ℕ := fun z =>
    ((Finset.univ.erase i).filter fun j => z j ≠ 0).card + 1
  exact (measurable_of_countable f).comp
    (measurable_pi_lambda _ fun j => (measurable_routeCount n).comp
      (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply j))))

lemma measurable_rivalWeight (i : Fin m) : Measurable (rivalWeight (n := n) i) := by
  classical
  have he : rivalWeight (n := n) i = (fun d : UserProfile m n =>
      ∑ j ∈ Finset.univ.erase i, if (d j).1.2.routeCount ≠ 0 then
        inverseBid n (d j).1.2.bid else 0) := by
    funext d
    simp only [rivalWeight, activeRivals, Finset.sum_filter]
  rw [he]
  apply Finset.measurable_sum
  intro j _
  have heval : Measurable (fun d : UserProfile m n => d j) := measurable_pi_apply j
  have hk := (measurable_routeCount n).comp
    (measurable_snd.comp (measurable_fst.comp heval))
  have hb := (measurable_bid n).comp
    (measurable_snd.comp (measurable_fst.comp heval))
  exact Measurable.ite (measurableSet_eq_fun hk measurable_const).compl
    (hb.pow_const (-rate n)) measurable_const

lemma rival_bounds (P : Corridor n m c) (i : Fin m) (d : UserProfile m n)
    (hd : GoodProfile P d) : P.ListBounds (rivalCount i d) (rivalWeight i d) := by
  classical
  have hcard := Finset.card_le_card (Finset.filter_subset
    (fun j => (d j).1.2.routeCount ≠ 0) (Finset.univ.erase i))
  have hcard' : (activeRivals i d).card ≤ m - 1 := by
    simpa [activeRivals, Finset.card_erase_of_mem (Finset.mem_univ i)] using hcard
  have hband (j : Fin m) (hj : j ∈ activeRivals i d) :
      (d j).1.2.bid ∈ Icc P.lower P.upper := by
    rcases hd j with hz | ⟨_,hb⟩
    · exact ((mem_activeRivals i j d).mp hj).2 hz |>.elim
    · exact hb
  refine ⟨by simp [rivalCount], ?_, ?_, ?_⟩
  · have := P.population
    dsimp only [rivalCount]
    omega
  · have hh := Finset.sum_le_sum (s := activeRivals i d) fun j hj => (P.weight_bounds (hband j hj)).1
    simpa [rivalWeight, rivalCount, nsmul_eq_mul] using hh
  · have hh := Finset.sum_le_sum (s := activeRivals i d) fun j hj => (P.weight_bounds (hband j hj)).2
    simpa [rivalWeight, rivalCount, nsmul_eq_mul] using hh

def gameRow (Γ : FiniteGame m n c Seed) (P : Corridor n m c)
    (hplay : CorridorPlay Γ P) (i : Fin m) : Row P (userProfileLaw Γ) where
  count := rivalCount i
  weight := rivalWeight i
  count_measurable := measurable_rivalCount i
  weight_measurable := measurable_rivalWeight i
  bounds := (ae_goodProfile Γ P hplay).mono fun d hd => rival_bounds P i d hd

lemma activeRivals_update (i : Fin m) (d : UserProfile m n) (u : UserDraw n) :
    activeRivals i (Function.update d i u) = activeRivals i d := by
  classical
  ext j
  by_cases hj : j = i
  · subst j; simp [activeRivals]
  · simp [activeRivals, Function.update_of_ne hj]

lemma rivalCount_update (i : Fin m) (d : UserProfile m n) (u : UserDraw n) :
    rivalCount i (Function.update d i u) = rivalCount i d := by
  simp only [rivalCount, activeRivals_update]

lemma rivalWeight_update (i : Fin m) (d : UserProfile m n) (u : UserDraw n) :
    rivalWeight i (Function.update d i u) = rivalWeight i d := by
  classical
  rw [rivalWeight, activeRivals_update]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne ((mem_activeRivals i j d).mp hj).1]

def focalList (i : Fin m) (b : ℝ) (d : UserProfile m n) : LocalList m := by
  classical
  exact fun j => if j = i then some b else
    if (d j).1.2.routeCount = 0 then none else some (d j).1.2.bid

lemma focalList_visible (i j : Fin m) (b : ℝ) (d : UserProfile m n) :
    focalList i b d j ≠ none ↔ j ∈ insert i (activeRivals i d) := by
  classical
  by_cases hj : j = i
  · subst j; simp [focalList]
  · simp [focalList, hj, activeRivals]

lemma focalList_card (i : Fin m) (b : ℝ) (d : UserProfile m n) :
    Fintype.card (VisibleUser (focalList i b d)) = rivalCount i d := by
  classical
  let e : VisibleUser (focalList i b d) ≃ ↥(insert i (activeRivals i d) : Finset (Fin m)) :=
    { toFun := fun j => ⟨j.val, (focalList_visible i j.val b d).mp j.property⟩
      invFun := fun j => ⟨j.val, (focalList_visible i j.val b d).mpr j.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = Fintype.card ↥(insert i (activeRivals i d) : Finset (Fin m)) := Fintype.card_congr e
    _ = _ := by rw [Fintype.card_coe, Finset.card_insert_of_notMem (not_mem_activeRivals i d)]; rfl

lemma focalList_sum_weights (i : Fin m) (b : ℝ) (d : UserProfile m n) :
    (∑ j : VisibleUser (focalList i b d), inverseBid n (visibleBid (focalList i b d) j)) =
      rivalWeight i d + inverseBid n b := by
  classical
  let e : VisibleUser (focalList i b d) ≃ ↥(insert i (activeRivals i d) : Finset (Fin m)) :=
    { toFun := fun j => ⟨j.val, (focalList_visible i j.val b d).mp j.property⟩
      invFun := fun j => ⟨j.val, (focalList_visible i j.val b d).mpr j.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := e.sum_comp (fun j : ↥(insert i (activeRivals i d) : Finset (Fin m)) =>
    inverseBid n ((focalList i b d j.val).getD 0))
  change (∑ j : VisibleUser (focalList i b d), inverseBid n (visibleBid (focalList i b d) j)) = _ at he
  rw [he, ← Finset.sum_subtype (insert i (activeRivals i d)) (fun _ => Iff.rfl)
    (fun j => inverseBid n ((focalList i b d j).getD 0)),
    Finset.sum_insert (not_mem_activeRivals i d)]
  have hfocal : (focalList i b d i).getD 0 = b := by simp [focalList]
  rw [hfocal]
  have hrival : (∑ j ∈ activeRivals i d, inverseBid n ((focalList i b d j).getD 0)) =
      rivalWeight i d := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hne,hk⟩ := (mem_activeRivals i j d).mp hj
    simp [focalList, hne, hk]
  rw [hrival, add_comm]

lemma focalList_bands (P : Corridor n m c) (i : Fin m) (d : UserProfile m n)
    (hd : GoodProfile P d) {b : ℝ} (hb : b ∈ Icc P.lower P.upper) :
    ∀ j : VisibleUser (focalList i b d), visibleBid (focalList i b d) j ∈ Icc P.lower P.upper := by
  classical
  intro j
  by_cases hji : j.val = i
  · simpa [visibleBid, focalList, hji] using hb
  · have hactive : (d j.val).1.2.routeCount ≠ 0 := by
      intro hz
      exact j.property (by simp [focalList, hji, hz])
    rcases hd j.val with hz | ⟨_,hband⟩
    · exact (hactive hz).elim
    · simpa [visibleBid, focalList, hji, hactive] using hband

lemma observe_update_eq_focalList (P : Corridor n m c) (i : Fin m)
    (d : UserProfile m n) (hd : GoodProfile P d) (x : ℝ × JointAction n)
    (hx : x.2.routeCount = n) (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    observe (drawsRealization (Function.update d i (x,τ))) j = focalList i x.2.bid d := by
  classical
  funext l
  by_cases hli : l = i
  · subst l
    simp [observe, drawsRealization, focalList, mem_firstK, hx]
  · rcases hd l with hz | ⟨hr,_⟩
    · simp [observe, drawsRealization, focalList, hli,
        mem_firstK, hz]
    · have hn : n ≠ 0 := by have := P.proposers; omega
      simp [observe, drawsRealization, focalList, hli,
        mem_firstK, hr, hn]

structure BroadcastCorridorContinuation (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (P : Corridor n m c) : Prop where
  common : ∀ j ℓ, FeasibleObservedList j ℓ →
    (∀ i : VisibleUser ℓ, visibleBid ℓ i ∈ Icc P.lower P.upper) →
    ∀ᵐ d ∂B.posterior j ℓ, ∀ l, observe (drawsRealization d) l = ℓ
  symmetric : ∀ j ℓ, FeasibleObservedList j ℓ →
    (∀ i : VisibleUser ℓ, visibleBid ℓ i ∈ Icc P.lower P.upper) →
    SymmetricAtList Γ ℓ (seedLottery Γ j ℓ)
  optimal : ∀ j ℓ, FeasibleObservedList j ℓ →
    (∀ i : VisibleUser ℓ, visibleBid ℓ i ∈ Icc P.lower P.upper) →
    ∀ᵐ s ∂Γ.seedLaw, FCAppendix.Finite.Optimal c
      (exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ) (Γ.policy j ℓ s).val

lemma focalList_marginal (_Γ : FiniteGame m (k+1) c Seed) (P : Corridor (k+1) m c)
    (i : Fin m) (d : UserProfile m (k+1)) (hd : GoodProfile P d)
    {b : ℝ} (hb : b ∈ Icc P.lower P.upper)
    (ν : FiniteLaw (Finset (Fin m)))
    (hg : ExclusiveEquilibrium (k+1) c (visibleBid (focalList i b d))
      (visibleLottery (focalList i b d) ν)) :
    Proposer.marginal ν i = P.allocation (rivalCount i d) (rivalWeight i d) b := by
  classical
  let ℓ := focalList i b d
  let ii : VisibleUser ℓ := ⟨i, by simp [ℓ,focalList]⟩
  have hband := focalList_bands P i d hd hb
  have hpos (j : VisibleUser ℓ) : 0 < visibleBid ℓ j := P.lower_pos.trans_le (hband j).1
  have hN : Fintype.card (VisibleUser ℓ) ≤ m := by
    calc
      _ ≤ Fintype.card (Fin m) := Fintype.card_le_of_injective
        (fun j : VisibleUser ℓ => j.val) Subtype.val_injective
      _ = m := Fintype.card_fin m
  have hact := equilibrium_all_active_of_corridor (k+1) P.proposers (visibleBid ℓ)
    c m hN P.lower_pos hband P.demand_spread (visibleLottery ℓ ν) hg
  have hbself : visibleBid ℓ ii = b := by simp [visibleBid,ℓ,ii,focalList]
  have hvis : Proposer.marginal ν i = Proposer.marginal (visibleLottery ℓ ν) ii :=
    (visibleLottery_marginal ℓ ν ii).symm
  have hcard : Fintype.card (VisibleUser ℓ) = rivalCount i d := focalList_card i b d
  rw [hvis]
  by_cases hover : c < Fintype.card (VisibleUser ℓ)
  · obtain ⟨_,_,_,hcoord,_⟩ := equilibrium_inverse_power_formula (k+1) P.proposers
      (visibleBid ℓ) hpos c hover (visibleLottery ℓ ν) hg hact
    rw [hcoord ii, hbself, focalList_sum_weights, focalList_card]
    have hcN : c ≤ rivalCount i d := by simpa only [hcard] using hover.le
    simp only [Corridor.allocation, focalMarginal, inverseBid, Nat.cast_sub hcN]
  · have hNc : rivalCount i d ≤ c := by simpa only [hcard] using le_of_not_gt hover
    rw [exclusive_small_list_unique (k+1) P.proposers (visibleBid ℓ) hpos c
      (le_of_not_gt hover) (visibleLottery ℓ ν) hg,
      P.allocation_underloaded (rivalWeight i d) b hNc]
    simp [CommonList.marginal_dirac]

lemma profile_test_update (Γ : FiniteGame m (k+1) c Seed) (P : Corridor (k+1) m c)
    (i : Fin m) (d : UserProfile m (k+1)) (hd : GoodProfile P d)
    (x : ℝ × JointAction (k+1)) (hx : x.2.routeCount = k+1)
    (hb : x.2.bid ∈ Icc P.lower P.upper) (τ : Equiv.Perm (Fin (k+1)))
    (ν : FiniteLaw (Finset (Fin m)))
    (hs : SymmetricAtList Γ (focalList i x.2.bid d) ν)
    (hg : ExclusiveEquilibrium (k+1) c (visibleBid (focalList i x.2.bid d))
      (visibleLottery (focalList i x.2.bid d) ν)) (f : ℕ → ℝ) :
    (profileCountLaw Γ (Function.update d i (x,τ)) i).expect (fun r => f r.val) =
      binomialPolynomial (k+1) f
        (P.allocation (rivalCount i d) (rivalWeight i d) x.2.bid) := by
  have hlaw := profileCountLaw_binomial Γ (Function.update d i (x,τ))
    (focalList i x.2.bid d) (observe_update_eq_focalList P i d hd x hx τ) ν hs i
  rw [hlaw, ← binomialPolynomial_eq_expect, focalList_marginal Γ P i d hd hb ν hg]

theorem interim_moment_of_continuation (Γ : FiniteGame m (k+1) c Seed)
    (P : Corridor (k+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hC : BroadcastCorridorContinuation Γ B P) (i : Fin m)
    (x : ℝ × JointAction (k+1)) (hx : x.2.routeCount = k+1)
    (hb : x.2.bid ∈ Icc P.lower P.upper) (f : ℕ → ℝ) :
    ((problem Γ i).outcome x.2).expect (fun r => f r.val) =
      (gameRow Γ P hplay i).moment f x.2.bid := by
  classical
  let j : Fin (k+1) := ⟨0,by omega⟩
  rw [interim_expect_eq_profile_update Γ i x]
  have he : ∀ τ : Equiv.Perm (Fin (k+1)),
      (∫ d, (profileCountLaw Γ (Function.update d i (x,τ)) i).expect
        (fun r => f r.val) ∂userProfileLaw Γ) =
      (gameRow Γ P hplay i).moment f x.2.bid := by
    intro τ
    apply integral_congr_ae
    filter_upwards [ae_goodProfile Γ P hplay] with d hd
    let ℓ := focalList i x.2.bid d
    have hfeas : FeasibleObservedList j ℓ :=
      ⟨Function.update d i (x,τ), observe_update_eq_focalList P i d hd x hx τ j⟩
    have hband := focalList_bands P i d hd hb
    have hs := hC.symmetric j ℓ hfeas hband
    have hg := visible_exclusiveEquilibrium_of_posterior_ae Γ B j ℓ
      (hC.optimal j ℓ hfeas hband) (hC.common j ℓ hfeas hband) _ hs
    exact profile_test_update Γ P i d hd x hx hb τ _ hs hg f
  simp_rw [he]
  simp

theorem ae_interim_moment_onPath (Γ : FiniteGame m (k+1) c Seed)
    (P : Corridor (k+1) m c) (hplay : CorridorPlay Γ P) (B : PosteriorSystem Γ)
    (hB : ExclusiveOptimalOnPath Γ B) (hsym : SymmetricProposersOnPath Γ) (i : Fin m) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1 →
      ∀ f : ℕ → ℝ, ((problem Γ i).outcome x.2).expect (fun r => f r.val) =
        (gameRow Γ P hplay i).moment f x.2.bid := by
  classical
  let j : Fin (k+1) := ⟨0,by omega⟩
  have hr : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ x.2.routeCount = k+1 :=
    hplay.mono fun x hx => hx.imp_right And.left
  have hg := ae_visible_exclusiveEquilibrium_of_routes Γ B hB j hr (hsym j)
  have hgd := ae_of_ae_map (measurable_observe_draws j).aemeasurable hg
  have hsd := ae_of_ae_map (measurable_observe_draws j).aemeasurable (hsym j)
  have hpres : MeasurePreserving
      (fun z : UserDraw (k+1) × UserProfile m (k+1) => Function.update z.2 i z.1)
      ((userLaw Γ).prod (userProfileLaw Γ)) (userProfileLaw Γ) :=
    ⟨Resample.measurable_update_pair i, Resample.map_update_eq (userLaw Γ) i⟩
  have hu := Measure.ae_ae_of_ae_prod (hpres.quasiMeasurePreserving.ae (hgd.and hsd))
  have hx := Measure.ae_ae_of_ae_prod hu
  filter_upwards [hx,hplay] with x hx hp hfull
  have hb : x.2.bid ∈ Icc P.lower P.upper := by
    rcases hp with hz | ⟨_,hb⟩
    · have := P.proposers; omega
    · exact hb
  intro f
  rw [interim_expect_eq_profile_update Γ i x]
  have he : ∀ᵐ τ ∂permLaw (k+1),
      (∫ d, (profileCountLaw Γ (Function.update d i (x,τ)) i).expect
        (fun r => f r.val) ∂userProfileLaw Γ) =
      (gameRow Γ P hplay i).moment f x.2.bid := by
    filter_upwards [hx] with τ hτ
    apply integral_congr_ae
    filter_upwards [hτ,ae_goodProfile Γ P hplay] with d hd hgood
    have heq := observe_update_eq_focalList P i d hgood x hfull τ j
    rw [heq] at hd
    exact profile_test_update Γ P i d hgood x hfull hb τ _ hd.2 hd.1 f
  rw [integral_congr_ae he]
  simp

end FCAppendix.Bayes.ExclusiveNarrow
