import FCAppendix.PayOnce.WeightedDerivative
import FCAppendix.PayOnce.FiniteJensen
import FCAppendix.Game.RealizedIntegrals

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

abbrev Rival (i : Fin m) := {j : Fin m // j ≠ i}

theorem card_rival_add_one (i : Fin m) : Fintype.card (Rival i) + 1 = m := by
  have hm : 0 < m := Nat.zero_lt_of_lt i.isLt
  change Fintype.card {j : Fin m // ¬j = i} + 1 = m
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_unique]
  omega

noncomputable def rivalBids (i : Fin m) (d : UserProfile m n) : Rival i → ℝ :=
  fun j => (d j.val).1.2.bid

theorem measurable_rivalBids (i : Fin m) : Measurable (rivalBids (n := n) i) := by
  apply measurable_pi_lambda
  intro j
  exact (measurable_bid n).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply j.val)))

theorem sum_focal_rivals (i : Fin m) (f : Fin m → ℝ) :
    f i + ∑ j : Rival i, f j.val = ∑ j, f j := by
  have h := Fintype.sum_subtype_add_sum_subtype (p := fun j : Fin m => j = i) f
  have he : (default : {j : Fin m // j = i}).val = i := (default : {j : Fin m // j = i}).property
  simpa only [Fintype.sum_unique, he] using h

theorem ae_profile_success_eq_analytical {k : ℕ} (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k + 1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) (i : Fin m) :
    ∀ᵐ d ∂userProfileLaw Γ,
      (profileCountLaw Γ d i).success = PayOnce.success (k+1)
        (PayOnce.AnalyticalKernel.allocation (k+1) c (by omega)
          (by simpa only [card_rival_add_one] using hcm) (rivalBids i d) (d i).1.2.bid) := by
  let j : Fin (k+1) := ⟨0, by omega⟩
  have hgame := ae_fullList_equilibrium_of_full_routes Γ hA B hB hsym hroute j
  have huserbid := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw (k+1))).quasiMeasurePreserving.ae hbid
  have hdrawbid : ∀ᵐ d ∂userProfileLaw Γ, ∀ l, 0 < (d l).1.2.bid :=
    ae_all_iff.mpr fun l => (measurePreserving_eval (fun _ : Fin m => userLaw Γ) l).quasiMeasurePreserving.ae huserbid
  filter_upwards [hgame, hdrawbid] with d hg hb
  let ℓ := observe (drawsRealization d) j
  let μ := seedLottery Γ j ℓ
  have hlaw := profileCountLaw_binomial Γ d ℓ hg.1 μ hg.2.1 i
  obtain ⟨L, hL, he, hcap⟩ := CommonList.equilibrium_kernel (k+1) (by omega)
    (fun l => (d l).1.2.bid) hb c (by simpa using hcm) μ hg.2.2
  rw [hlaw, IndependentCounts.binomial_success]
  apply congrArg (PayOnce.success (k+1))
  rw [he i]
  symm
  apply PayOnce.AnalyticalKernel.allocation_eq_kernel _ _ (rivalBids i d) (fun l => hb l.val) (hb i) hL
  exact (sum_focal_rivals i (fun l => CommonList.kernel (k+1) (d l).1.2.bid L)).trans hcap

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem interim_success_eq_profile_update (Γ : FiniteGame m n c Seed) (i : Fin m)
    (x : ℝ × JointAction n) :
    ((problem Γ i).outcome x.2).success =
      ∫ r, ∫ d, (profileCountLaw Γ (Function.update d i (x, r)) i).success
        ∂userProfileLaw Γ ∂permLaw n := by
  let f := fun ω : Sample m n Seed => successIndicator (focalCount Γ i x.2 ω).val
  have hi : Integrable f (sampleLaw Γ) :=
    CountLaw.integrable_comp _ _ (measurable_focalCount Γ i x.2) (fun q : Fin (n+1) => successIndicator q.val)
  rw [problem_outcome, CountLaw.success, CountLaw.expect_ofMeasure]
  change (∫ ω, f ω ∂(backgroundLaw Γ).prod (permLaw n)) = _
  rw [integral_prod_symm f hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  dsimp only
  have hir : Integrable (fun ω : Background m n Seed => f (ω, r)) (backgroundLaw Γ) := by
    apply CountLaw.integrable_comp _ _ _ (fun q : Fin (n+1) => successIndicator q.val)
    exact (measurable_focalCount Γ i x.2).comp (measurable_id.prodMk measurable_const)
  change Integrable (fun ω : Background m n Seed => f (ω,r))
    ((userProfileLaw Γ).prod (Measure.pi fun _ : Fin n => Γ.seedLaw)) at hir
  change (∫ ω : Background m n Seed, f (ω,r)
    ∂(userProfileLaw Γ).prod (Measure.pi fun _ : Fin n => Γ.seedLaw)) = _
  rw [integral_prod _ hir]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro d
  dsimp only
  rw [CountLaw.success]
  unfold profileCountLaw
  rw [CountLaw.expect_ofMeasure]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro s
  have he := playedCount_insertDraw Γ i ((x, r), (d, s))
  exact congrArg (fun q : Fin (n+1) => successIndicator q.val) he.symm

noncomputable def analyticalRivalLaw (Γ : FiniteGame m n c Seed) (i : Fin m) : Measure (Rival i → ℝ) :=
  (userProfileLaw Γ).map (rivalBids i)

instance (Γ : FiniteGame m n c Seed) (i : Fin m) : IsProbabilityMeasure (analyticalRivalLaw Γ i) :=
  Measure.isProbabilityMeasure_map (measurable_rivalBids i).aemeasurable

theorem ae_interim_success_eq_analytical {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) (i : Fin m) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ((problem Γ i).outcome x.2).success =
      PayOnce.AnalyticalKernel.coverage (k+1) c (by omega)
        (by simpa only [card_rival_add_one] using hcm) (analyticalRivalLaw Γ i) x.2.bid := by
  have hp := ae_profile_success_eq_analytical Γ hk hcm hA B hB hsym hroute hbid i
  have hpres : MeasurePreserving (fun z : UserDraw (k+1) × UserProfile m (k+1) =>
      Function.update z.2 i z.1) ((userLaw Γ).prod (userProfileLaw Γ)) (userProfileLaw Γ) :=
    ⟨Resample.measurable_update_pair i, Resample.map_update_eq (userLaw Γ) i⟩
  have hup := Measure.ae_ae_of_ae_prod (hpres.quasiMeasurePreserving.ae hp)
  have hx := Measure.ae_ae_of_ae_prod hup
  filter_upwards [hx, hbid] with x hx hxb
  rw [interim_success_eq_profile_update Γ i x]
  have he : ∀ᵐ r ∂permLaw (k+1),
      (∫ d, (profileCountLaw Γ (Function.update d i (x,r)) i).success ∂userProfileLaw Γ) =
        PayOnce.AnalyticalKernel.coverage (k+1) c (by omega)
          (by simpa only [card_rival_add_one] using hcm) (analyticalRivalLaw Γ i) x.2.bid := by
    filter_upwards [hx] with r hr
    unfold PayOnce.AnalyticalKernel.coverage analyticalRivalLaw
    rw [integral_map (measurable_rivalBids i).aemeasurable
      (PayOnce.AnalyticalKernel.measurable_success_allocation (by omega)
        (by simpa only [card_rival_add_one] using hcm) hxb).aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hr] with d hd
    have hrv : rivalBids i (Function.update d i (x,r)) = rivalBids i d := by
      funext j
      simp only [rivalBids, Function.update_of_ne j.property]
    simpa only [Function.update_self, hrv] using hd
  rw [integral_congr_ae he]
  simp only [integral_const, probReal_univ, one_smul]

end FCAppendix.Bayes

namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory Set OwnImpact
variable {ι : Type*} [Fintype ι]

theorem allocation_eq_zero_of_nonpos {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι + 1) (rivals : ι → ℝ) {b : ℝ} (hb : b ≤ 0) :
    allocation n c hn hc rivals b = 0 := by
  rw [allocation, dif_neg (fun h => (not_lt_of_ge hb) h.1)]

theorem allocation_monotone {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι + 1) (rivals : ι → ℝ) :
    Monotone (allocation n c hn hc rivals) := by
  classical
  intro b a hba
  by_cases hb : 0 < b
  · by_cases hr : ∀ j, 0 < rivals j
    · obtain ⟨L, hL, heL, hcapL⟩ := allocation_root hn hc rivals hr hb
      obtain ⟨T, hT, heT, hcapT⟩ := allocation_root hn hc rivals hr (hb.trans_le hba)
      rw [heL, heT]
      exact focal_kernel_monotone hn rivals hb hba hL hT hcapL hcapT
    · simp only [allocation, dif_neg (show ¬(0 < b ∧ ∀ j, 0 < rivals j) from fun h => hr h.2),
        dif_neg (show ¬(0 < a ∧ ∀ j, 0 < rivals j) from fun h => hr h.2), le_refl]
  · rw [allocation_eq_zero_of_nonpos hn hc rivals (le_of_not_gt hb)]
    exact (allocation_bounds hn hc rivals a).1

theorem integrable_success_allocation {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι + 1) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] (b : ℝ) :
    Integrable (fun rivals => success n (allocation n c hn hc rivals b)) μ := by
  by_cases hb : 0 < b
  · exact UnitInterval.integrable μ _ (measurable_success_allocation hn hc hb)
      (fun rivals => (success_allocation_bounds hn hc rivals b).1)
      (fun rivals => (success_allocation_bounds hn hc rivals b).2)
  · simp_rw [allocation_eq_zero_of_nonpos hn hc _ (le_of_not_gt hb)]
    exact integrable_const _

theorem coverage_monotone {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι + 1) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] :
    Monotone (coverage n c hn hc μ) := by
  intro b a hba
  apply integral_mono (integrable_success_allocation hn hc μ b) (integrable_success_allocation hn hc μ a)
  intro rivals
  unfold success
  have hp := allocation_monotone hn hc rivals hba
  have ha := (allocation_bounds hn hc rivals a).2
  have hh := pow_le_pow_left₀ (sub_nonneg.mpr ha) (by linarith :
    1-allocation n c hn hc rivals a ≤ 1-allocation n c hn hc rivals b) n
  linarith

theorem measurable_coverage {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι + 1) (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] :
    Measurable (coverage n c hn hc μ) := (coverage_monotone hn hc μ).measurable

end FCAppendix.PayOnce.AnalyticalKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def realBidLaw (Γ : FiniteGame m n c Seed) : Measure ℝ :=
  (userLaw Γ).map (fun d => d.1.2.bid)

theorem measurable_drawBid : Measurable (fun d : UserDraw n => d.1.2.bid) :=
  (measurable_bid n).comp (measurable_snd.comp measurable_fst)

instance (Γ : FiniteGame m n c Seed) : IsProbabilityMeasure (realBidLaw Γ) :=
  Measure.isProbabilityMeasure_map measurable_drawBid.aemeasurable

theorem realBidLaw_eq_action_map (Γ : FiniteGame m n c Seed) :
    realBidLaw Γ = (Γ.F ⊗ₘ Γ.σ).map (fun x => x.2.bid) := by
  have h := measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)
  rw [← h.map_eq, Measure.map_map (show Measurable (fun x : ℝ × JointAction n => x.2.bid) from (measurable_bid n).comp measurable_snd) measurable_fst]
  rfl

theorem analyticalRivalLaw_eq_pi (Γ : FiniteGame m n c Seed) (i : Fin m) :
    analyticalRivalLaw Γ i = Measure.pi (fun _ : Rival i => realBidLaw Γ) := by
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin m => userLaw Γ)
    (fun j : Fin m => j ≠ i)
  have hfst := (measurePreserving_fst (μ := Measure.pi fun _ : Rival i => userLaw Γ)
    (ν := Measure.pi fun _ : {j : Fin m // ¬j ≠ i} => userLaw Γ)).comp hp
  have hbid := measurePreserving_pi (fun _ : Rival i => userLaw Γ)
    (fun _ : Rival i => realBidLaw Γ)
    (fun _ => show MeasurePreserving (fun d : UserDraw n => d.1.2.bid) (userLaw Γ) (realBidLaw Γ) from
      ⟨measurable_drawBid, rfl⟩)
  exact (hbid.comp hfst).map_eq

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def safeFullBid (n : ℕ) (b : ℝ) : JointAction n :=
  fullBid n (max b 0) (le_max_right _ _)

theorem measurable_safeFullBid (n : ℕ) : Measurable (safeFullBid n) := by
  apply measurable_comap_iff.mpr
  exact (measurable_id.max measurable_const).prodMk measurable_const

theorem safeFullBid_eq_of_fullRoute (a : JointAction n) (ha : a.routeCount = n) :
    safeFullBid n a.bid = a := by
  cases a
  simp_all [safeFullBid, fullBid]

theorem exists_common_analytical_agreement_set {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) (i : Fin m) :
    ∃ S : Set ℝ, MeasurableSet S ∧ (∀ᵐ b ∂realBidLaw Γ, b ∈ S) ∧
      (∀ b ∈ S, 0 < b) ∧
      ∀ b ∈ S, ∀ a : JointAction (k+1), a.bid = b → a.routeCount = k+1 →
        ((problem Γ i).outcome a).success = PayOnce.AnalyticalKernel.coverage (k+1) c (by omega)
          (by simpa only [card_rival_add_one] using hcm) (analyticalRivalLaw Γ i) b := by
  let Q := PayOnce.AnalyticalKernel.coverage (k+1) c (by omega)
    (by simpa only [card_rival_add_one] using hcm) (analyticalRivalLaw Γ i)
  let S := {b : ℝ | 0 < b ∧ ((problem Γ i).outcome (safeFullBid (k+1) b)).success = Q b}
  have hm : MeasurableSet S := (measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_eq_fun ((measurable_success Γ i).comp (measurable_safeFullBid (k+1)))
      (PayOnce.AnalyticalKernel.measurable_coverage _ _ _))
  have hae : ∀ᵐ b ∂realBidLaw Γ, b ∈ S := by
    rw [realBidLaw_eq_action_map]
    apply (ae_map_iff ((measurable_bid (k+1)).comp measurable_snd).aemeasurable hm).mpr
    filter_upwards [ae_interim_success_eq_analytical Γ hk hcm hA B hB hsym hroute hbid i,
      hroute, hbid] with x hx hr hb
    refine ⟨hb, ?_⟩
    change ((problem Γ i).outcome (safeFullBid (k+1) x.2.bid)).success = Q x.2.bid
    rw [safeFullBid_eq_of_fullRoute x.2 hr]
    exact hx
  refine ⟨S, hm, hae, fun b hb => hb.1, ?_⟩
  intro b hb a hab har
  have he : safeFullBid (k+1) b = a := hab ▸ safeFullBid_eq_of_fullRoute a har
  exact he ▸ hb.2

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_realBidLaw_pos (Γ : FiniteGame m n c Seed)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) : ∀ᵐ b ∂realBidLaw Γ, 0 < b := by
  rw [realBidLaw_eq_action_map]
  exact (ae_map_iff ((measurable_bid n).comp measurable_snd).aemeasurable measurableSet_Ioi).mpr hbid

theorem nullSingleton_realBidLaw_of_full_routes (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = n)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) : NullSingletonClass (realBidLaw Γ) := by
  constructor
  intro b
  change ((userLaw Γ).map (fun d => d.1.2.bid)) {b} = 0
  rw [Measure.map_apply measurable_drawBid (measurableSet_singleton b)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hpos := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)).quasiMeasurePreserving.ae hbid
  by_cases hb : 0 < b
  · let j : Fin n := ⟨0, hn⟩
    have hr := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)).quasiMeasurePreserving.ae hroute
    have hz := measure_eq_zero_iff_ae_notMem.mp (hatom j b hb)
    filter_upwards [hr, hz] with d hd hdz he
    have heb : d.1.2.bid = b := he
    apply hdz
    refine ⟨?_, heb⟩
    rw [hd, mem_firstK]
    exact Nat.succ_le_of_lt (d.2 j).isLt
  · filter_upwards [hpos] with d hd he
    have heb : d.1.2.bid = b := he
    exact hb (heb ▸ hd)

end FCAppendix.Bayes
