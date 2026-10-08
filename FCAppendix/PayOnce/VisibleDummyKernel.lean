import FCAppendix.PayOnce.FiniteJensen
import FCAppendix.PayOnce.DummyKernel
import FCAppendix.PayOnce.CompactifiedBidLaws

namespace FCAppendix.CommonList
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem equilibrium_kernel_any (n : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    (c : ℕ) (μ : FiniteLaw (Finset ι)) (hμ : PayOnceEquilibrium n c b μ) :
    ∃ L, 0 < L ∧ (∀ i, Proposer.marginal μ i = kernel n (b i) L) ∧
      ∑ i, kernel n (b i) L = min c (Fintype.card ι) := by
  by_cases hc : c ≤ Fintype.card ι
  · simpa only [min_eq_left hc] using equilibrium_kernel n hn b hb c hc μ hμ
  · have hroom : Fintype.card ι ≤ c := by omega
    have he := (payOnceEquilibrium_small_list_iff n (by omega) b hb c hroom μ).mp hμ
    have hm := (payOnceEquilibrium_small_list_iff n (by omega) b hb (Fintype.card ι) le_rfl μ).mpr he
    simpa only [min_eq_right hroom] using
      equilibrium_kernel n hn b hb (Fintype.card ι) le_rfl μ hm

end FCAppendix.CommonList

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set CommonList
open PayOnce.CompactifiedBidLaws
open scoped BigOperators ProbabilityTheory
variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem seedLottery_marginal_absent (Γ : FiniteGame m n c Seed) (j : Fin n)
    (ℓ : LocalList m) (i : Fin m) (hi : ℓ i = none) :
    Proposer.marginal (seedLottery Γ j ℓ) i = 0 := by
  apply CommonList.marginal_eq_zero_of_forall
  intro S hS his
  obtain ⟨s,rfl⟩ := seedLottery_support_exists Γ j ℓ S hS
  exact (Γ.policy j ℓ s).property.2 i his hi

theorem sum_kernel_visible {n : ℕ} (ℓ : LocalList m) {L : ℝ} (hL : 0 < L) :
    (∑ i : VisibleUser ℓ, kernel n (visibleBid ℓ i) L) =
      ∑ i, kernel n ((ℓ i).getD 0) L := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (p := fun i => ℓ i ≠ none)
    (fun i => kernel n ((ℓ i).getD 0) L)
  have hz : (∑ i : {i // ¬ℓ i ≠ none}, kernel n ((ℓ i.val).getD 0) L) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have he : ℓ i.val = none := not_not.mp i.property
    simp only [he,Option.getD_none]
    exact kernel_of_le n hL.le
  rw [hz,add_zero] at h
  unfold visibleBid
  convert h using 1
  apply Finset.sum_congr
  · ext i
    simp
  · intro i _
    rfl

theorem visible_equilibrium_kernel_with_dummies (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (j : Fin (k+1)) (ℓ : LocalList m)
    (hb : ∀ i : VisibleUser ℓ, 0 < visibleBid ℓ i)
    (hgame : PayOnceEquilibrium (k+1) c (visibleBid ℓ) (visibleLottery ℓ (seedLottery Γ j ℓ))) :
    ∃ L, 0 < L ∧
      (∀ i, Proposer.marginal (seedLottery Γ j ℓ) i = kernel (k+1) ((ℓ i).getD 0) L) ∧
      ∑ i, kernel (k+1) ((ℓ i).getD 0) L = min c (Fintype.card (VisibleUser ℓ)) := by
  classical
  obtain ⟨L,hL,he,hcap⟩ := CommonList.equilibrium_kernel_any (k+1) (by omega)
    (visibleBid ℓ) hb c (visibleLottery ℓ (seedLottery Γ j ℓ)) hgame
  refine ⟨L,hL,?_,?_⟩
  · intro i
    by_cases hi : ℓ i = none
    · rw [seedLottery_marginal_absent Γ j ℓ i hi,hi,Option.getD_none,kernel_of_le (k+1) hL.le]
    · have hh := he ⟨i,hi⟩
      rwa [visibleLottery_marginal] at hh
  · rw [← sum_kernel_visible ℓ hL]
    exact hcap

theorem observe_getD_eq_effectiveBid (d : UserProfile m n) (j : Fin n)
    (hd : ∀ i, (d i).1.2.routeCount = 0 ∨ (d i).1.2.routeCount = n) (i : Fin m) :
    ((observe (drawsRealization d) j) i).getD 0 = effectiveBid (d i).1.2 := by
  rcases hd i with hi | hi
  · simp [observe,drawsRealization,effectiveBid,hi,mem_firstK]
  · have hn : n ≠ 0 := ne_of_gt (Nat.zero_lt_of_lt j.isLt)
    simp [observe,drawsRealization,effectiveBid,hi,hn,mem_firstK]

theorem visibleCard_eq_active (ℓ : LocalList m) (hb : ∀ i : VisibleUser ℓ, 0 < visibleBid ℓ i) :
    Fintype.card (VisibleUser ℓ) = Fintype.card (PayOnce.DummyKernel.Active (fun i => (ℓ i).getD 0)) := by
  classical
  have he (i : Fin m) : ℓ i ≠ none ↔ 0 < (ℓ i).getD 0 := by
    constructor
    · intro hi
      exact hb ⟨i,hi⟩
    · intro hi hz
      simp only [hz,Option.getD_none] at hi
      exact (lt_irrefl _ hi).elim
  let e : VisibleUser ℓ ≃ PayOnce.DummyKernel.Active (fun i => (ℓ i).getD 0) :=
    { toFun := fun i => ⟨i.val,(he i.val).mp i.property⟩
      invFun := fun i => ⟨i.val,(he i.val).mpr i.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Fintype.card_congr e

theorem ae_dummy_kernel_representation (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k+1)) :
    ∀ᵐ d ∂userProfileLaw Γ, ∃ L : ℝ, ∃ hL : 0 < L,
      (∀ i, profileCountLaw Γ d i = IndependentCounts.binomial (k+1)
        (kernel (k+1) (effectiveBid (d i).1.2) L)
        (PayOnce.KernelTailEvent.kernel_bounds (by omega) hL _).1
        (PayOnce.KernelTailEvent.kernel_bounds (by omega) hL _).2) ∧
      (∑ i, kernel (k+1) (effectiveBid (d i).1.2) L) =
        min c (Fintype.card (PayOnce.DummyKernel.Active (fun i => effectiveBid (d i).1.2))) := by
  classical
  let j : Fin (k+1) := ⟨0,by omega⟩
  have hr := hroute.mono fun _ hx => hx.imp_right And.right
  have hcommon := ae_commonLists_of_zero_or_full_routes Γ hr j
  have hopt : PosteriorProposerOptimalOnPath Γ B := by
    intro l
    filter_upwards [B.ae_observation Γ l] with ℓ hℓ
    obtain ⟨d,hd⟩ := hℓ.exists
    exact hB l ℓ ⟨d,hd⟩
  have hgame := ae_visible_payOnceEquilibrium_of_routes Γ hA B hopt j hr (hsym j)
  have hgameD := ae_of_ae_map (measurable_observe_draws j).aemeasurable hgame
  have hsymD := ae_of_ae_map (measurable_observe_draws j).aemeasurable (hsym j)
  have huser := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw (k+1))).quasiMeasurePreserving.ae hroute
  have hdraw : ∀ᵐ d ∂userProfileLaw Γ, ∀ i,
      (d i).1.2.routeCount = 0 ∨ (0 < (d i).1.2.bid ∧ (d i).1.2.routeCount = k+1) :=
    ae_all_iff.mpr fun i => (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae huser
  filter_upwards [hcommon,hgameD,hsymD,hdraw] with d hd hg hs hrD
  let ℓ := observe (drawsRealization d) j
  have hrD' (i : Fin m) := (hrD i).imp_right And.right
  have hbid : ∀ i : VisibleUser ℓ, 0 < visibleBid ℓ i := by
    intro i
    rcases hrD i.val with hz | ⟨hb,hfull⟩
    · have hh : ℓ i.val = none := by simp [ℓ,observe,drawsRealization,mem_firstK,hz]
      exact (i.property hh).elim
    · have he : ℓ i.val = some (d i.val).1.2.bid := by
        simp [ℓ,observe,drawsRealization,mem_firstK,hfull]
        exact Nat.le_of_lt_succ ((d i.val).2 j).isLt
      simpa only [visibleBid,he,Option.getD_some] using hb
  obtain ⟨L,hL,he,hcap⟩ := visible_equilibrium_kernel_with_dummies Γ hk j ℓ hbid hg
  have hdummy (i : Fin m) : (ℓ i).getD 0 = effectiveBid (d i).1.2 :=
    observe_getD_eq_effectiveBid d j hrD' i
  refine ⟨L,hL,?_,?_⟩
  · intro i
    have hlaw := profileCountLaw_binomial Γ d ℓ hd (seedLottery Γ j ℓ) hs i
    simpa only [he i,hdummy] using hlaw
  · rw [visibleCard_eq_active ℓ hbid] at hcap
    simpa only [hdummy] using hcap

end FCAppendix.Bayes
