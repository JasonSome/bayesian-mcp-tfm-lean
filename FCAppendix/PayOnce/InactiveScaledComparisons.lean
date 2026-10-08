import FCAppendix.PayOnce.DummyRareSuccess
import FCAppendix.PayOnce.DummyScaling

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce.DummyKernel PayOnce.DummyRareSuccess PayOnce.CompactifiedBidLaws
open PayOnce.AnalyticalKernel (rescaledRealLaw)
variable {N c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exists_ae_inactive_scaled_comparisons (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < N+1)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hatom : PositiveVisibleAtomless Γ) (hinactive : InactiveAbstain Γ)
    (i : Fin (N+1)) (a : ℝ) (ha : 0 < a) :
    let hn : 2 ≤ k+1 := by omega
    let G := PayOnce.BidScaling.realBidLaw Γ
    ∃ S : Set ℝ, MeasurableSet S ∧ (∀ b ∈ S, 0 < b) ∧
      (∀ᵐ b ∂(G : Measure ℝ), 0 < b → b ∈ S) ∧
      ∀ᵐ z ∂(Γ.F ⊗ₘ Γ.σ), Γ.g < z.1 → 0 < z.2.bid ∧
        z.2.bid/a ∈ regularSupportedSet (ι := Fin N) (k+1) c
          (rescaledRealLaw G a : Measure ℝ) ((fun b => b/a) '' S) ∧
        ∀ y ∈ S,
          (z.1-Γ.g-y)*coverage (k+1) c hn
            (Measure.pi (fun _ : Fin N => (G : Measure ℝ))) y ≤
          (z.1-Γ.g-z.2.bid)*coverage (k+1) c hn
            (Measure.pi (fun _ : Fin N => (G : Measure ℝ))) z.2.bid := by
  dsimp only
  let hn : 2 ≤ k+1 := by omega
  let G := PayOnce.BidScaling.realBidLaw Γ
  have hroute := ae_positive_broadcast_or_abstain Γ hc hcm hA hG hu B hB hsym hvalue hinactive
  have hatomG b hb : (G : Measure ℝ) {b} = 0 :=
    realEffectiveBidLaw_positive_atomless Γ hc hcm hA hG hu B hB hsym hvalue hatom hb
  obtain ⟨S,hSm,hS,hposS,hagree⟩ := exists_common_dummy_agreement_set Γ hk hA B hB hsym hroute i
  have hdiv : MeasurableEmbedding (fun b : ℝ => b/a) := by
    simpa only [div_eq_mul_inv] using measurableEmbedding_mulRight₀ (inv_ne_zero ha.ne')
  have hS' : ∀ᵐ b ∂(rescaledRealLaw G a : Measure ℝ), 0 < b → b ∈ (fun b => b/a) '' S := by
    apply hdiv.ae_map_iff.mpr
    filter_upwards [hS] with b hb hpos
    exact mem_image_of_mem _ (hb ((div_pos_iff_of_pos_right ha).mp hpos))
  have hgood := ae_mem_regularSupportedSet (ι := Fin N) (c := c) (rescaledRealLaw G a : Measure ℝ)
    (fun b hb => positive_atomless_rescaledRealLaw G hatomG ha hb) hn hS'
  have hbase : ∀ᵐ b ∂(G : Measure ℝ), 0 < b → b/a ∈ regularSupportedSet (ι := Fin N) (k+1) c
      (rescaledRealLaw G a : Measure ℝ) ((fun b => b/a) '' S) := by
    have hh := ae_of_ae_map (measurable_id.div_const a).aemeasurable hgood
    filter_upwards [hh] with b hb hpos
    exact hb (div_pos hpos ha)
  change ∀ᵐ b ∂(PayOnce.BidScaling.realBidLaw Γ : Measure ℝ), 0 < b → _ at hbase
  rw [realEffectiveBidLaw_eq_action_map] at hbase
  have hgoodz := ae_of_ae_map ((measurable_effectiveBid (k+1)).comp measurable_snd).aemeasurable hbase
  have hSmap := hS
  rw [realEffectiveBidLaw_eq_action_map] at hSmap
  have hSz := ae_of_ae_map ((measurable_effectiveBid (k+1)).comp measurable_snd).aemeasurable hSmap
  have hcard : Fintype.card (Fin N) = Fintype.card (Rival i) := by
    have hh := card_rival_add_one i
    simp only [Fintype.card_fin]
    omega
  let e : Fin N ≃ Rival i := Fintype.equivOfCardEq hcard
  have hQ (b : ℝ) : coverage (k+1) c hn (Measure.pi (fun _ : Fin N => (G : Measure ℝ))) b =
      coverage (k+1) c hn (Measure.pi (fun _ : Rival i => (G : Measure ℝ))) b :=
    integral_allocation_test_equiv e hn (G : Measure ℝ) b (PayOnce.success (k+1))
  refine ⟨S,hSm,hposS,hS,?_⟩
  filter_upwards [hgoodz,hSz,ae_bestResponse_compProd Γ hu i,
    ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hvalue]
    with z hgood hSz hbest hp hv
  have hfull := hp.2.2 hv
  have hpos := hp.1.mpr hv
  have heff : effectiveBid z.2 = z.2.bid := by
    simp only [effectiveBid,hfull,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]
  have hbid : 0 < z.2.bid := heff ▸ hpos
  refine ⟨hbid,?_,?_⟩
  · simpa only [Function.comp_def,← realEffectiveBidLaw_eq_action_map,heff] using hgood hpos
  · intro y hy
    let act := fullBid (k+1) y (hposS y hy).le
    have hact : act.bid = y := rfl
    have har : act.routeCount = k+1 := rfl
    have hyQ := hagree y hy act hact har
    have hzQ := hagree z.2.bid (heff ▸ hSz hpos) z.2 rfl hfull
    have hcmp := hbest act
    rw [payoff_once Γ hA hG,payoff_once Γ hA hG,hyQ,hzQ,hact,← hQ,← hQ] at hcmp
    convert hcmp using 1 <;> ring

end FCAppendix.Bayes
