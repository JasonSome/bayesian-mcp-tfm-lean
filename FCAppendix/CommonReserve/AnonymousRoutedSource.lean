import FCAppendix.CommonReserve.ReserveFiltering
import FCAppendix.CommonReserve.ActualConditioning
import FCAppendix.CommonReserve.AnonymousTightness
import FCAppendix.CommonReserve.Quantiles

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def routedAction (r : ℝ) (d : Bayes.UserDraw n) : Action n r := by
  classical
  refine ⟨fun j => if r ≤ d.1.2.bid ∧ j ∈ firstK d.2 d.1.2.routeCount
      then some d.1.2.bid else none, ?_⟩
  intro j b hb
  dsimp only at hb
  split_ifs at hb with h
  · have he : d.1.2.bid = b := Option.some.inj hb
    exact he ▸ h.1

theorem measurable_routedAction (r : ℝ) : Measurable (routedAction (n := n) r) := by
  classical
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro j
  have hb : Measurable (fun d : Bayes.UserDraw n => d.1.2.bid) :=
    (measurable_bid n).comp (measurable_snd.comp measurable_fst)
  have hk : Measurable (fun d : Bayes.UserDraw n => d.1.2.routeCount) :=
    (measurable_routeCount n).comp (measurable_snd.comp measurable_fst)
  have hr : MeasurableSet {d : Bayes.UserDraw n |
      j ∈ firstK d.2 d.1.2.routeCount} :=
    (measurable_snd.prodMk hk) (Bayes.measurableSet_mem_firstK j)
  exact Measurable.ite ((measurableSet_le measurable_const hb).inter hr)
    (measurable_some.comp hb) measurable_const

def routedDraw (r : ℝ) (d : Bayes.UserDraw n) : UserDraw n r := (0, routedAction r d)

theorem measurable_routedDraw (r : ℝ) : Measurable (routedDraw (n := n) r) :=
  measurable_const.prodMk (measurable_routedAction r)

def routedSource (Γ : Bayes.FiniteGame m n c Seed) (r : ℝ) (hr : 0 ≤ r) :
    FiniteGame m n c r Seed where
  F := Measure.dirac 0
  hF := by infer_instance
  σ := Kernel.const ℝ ((Bayes.userLaw Γ).map (routedAction r))
  hσ := by
    haveI : IsProbabilityMeasure ((Bayes.userLaw Γ).map (routedAction r)) :=
      Measure.isProbabilityMeasure_map (measurable_routedAction r).aemeasurable
    infer_instance
  seedLaw := Γ.seedLaw
  hseed := Γ.hseed
  policy := Γ.policy
  policy_measurable := Γ.policy_measurable
  G := Γ.G
  g := Γ.g
  g_nonneg := Γ.g_nonneg
  reserve_nonneg := hr

theorem routedSource_userLaw (Γ : Bayes.FiniteGame m n c Seed) (r : ℝ) (hr : 0 ≤ r) :
    (routedSource Γ r hr).userLaw = (Bayes.userLaw Γ).map (routedDraw r) := by
  haveI : IsProbabilityMeasure ((Bayes.userLaw Γ).map (routedAction r)) :=
    Measure.isProbabilityMeasure_map (measurable_routedAction r).aemeasurable
  rw [FiniteGame.userLaw, routedSource, Measure.compProd_const, Measure.dirac_prod,
    Measure.map_map measurable_prodMk_left (measurable_routedAction r)]
  rfl

def routedSample (r : ℝ) (ω : Bayes.Background m n Seed) : Sample m n r Seed :=
  (fun i => routedDraw r (ω.1 i), ω.2)

theorem routedSample_measurePreserving (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) :
    MeasurePreserving (routedSample (m := m) (Seed := Seed) r)
      (Bayes.backgroundLaw Γ) (routedSource Γ r hr).sampleLaw := by
  have hdraw : MeasurePreserving (routedDraw r) (Bayes.userLaw Γ)
      (routedSource Γ r hr).userLaw :=
    ⟨measurable_routedDraw r, (routedSource_userLaw Γ r hr).symm⟩
  exact (measurePreserving_pi _ _ (fun _ : Fin m => hdraw)).prod
    (MeasurePreserving.id (Measure.pi fun _ : Fin n => Γ.seedLaw))

theorem routedProfile_eq_ofRealization (r : ℝ) (d : Fin m → Bayes.UserDraw n) :
    (fun i => routedAction r (d i)) =
      ofRealization (reserveRealization r (Bayes.drawsRealization d))
        (reserveRealization_eligible r (Bayes.drawsRealization d)) := by
  classical
  funext i
  apply Subtype.ext
  funext j
  by_cases hb : r ≤ (d i).1.2.bid <;>
    by_cases hj : j ∈ firstK (d i).2 (d i).1.2.routeCount <;>
    simp [routedAction, ofRealization, Game.observe, reserveRealization,
      Bayes.drawsRealization, hb, hj]

theorem observe_routedProfile (r : ℝ) (d : Fin m → Bayes.UserDraw n) (j : Fin n) :
    observe (fun i => routedAction r (d i)) j =
      reserveList (Game.observe (Bayes.drawsRealization d) j) r := by
  rw [routedProfile_eq_ofRealization, observe_ofRealization, observe_reserveRealization]

omit [MeasurableSpace Seed] in
theorem count_routedProfile (r : ℝ) (d : Fin m → Bayes.UserDraw n)
    (policy : Fin n → LocalPolicy m c Seed) (s : Fin n → Seed) (i : Fin m) :
    count (fun l => routedAction r (d l)) policy s i =
      Game.inclusionCount (reserveRealization r (Bayes.drawsRealization d)) policy s i := by
  rw [routedProfile_eq_ofRealization, count_ofRealization]

omit [MeasurableSpace Seed] in
theorem observe_routed_deviated (r : ℝ) (i : Fin m) (a : JointAction n)
    (d : Fin m → Bayes.UserDraw n) (s : Fin n → Seed)
    (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    observe (FiniteGame.deviated i (routedAction r ((0, a), τ))
      (routedSample r (d, s))) j =
      reserveList (Game.observe (Bayes.deviated i a ((d, s), τ)) j) r := by
  classical
  let d' : Fin m → Bayes.UserDraw n := Function.update d i ((0, a), τ)
  have hprofile : FiniteGame.deviated i (routedAction r ((0, a), τ))
      (routedSample r (d, s)) = fun l => routedAction r (d' l) := by
    funext l
    by_cases hl : l = i
    · simp [FiniteGame.deviated, routedSample, routedDraw, d', hl]
    · simp [FiniteGame.deviated, routedSample, routedDraw, d', hl]
  rw [hprofile, observe_routedProfile]
  congr 1
  exact Bayes.observe_insertDraw i (((0, a), τ), (d, s)) j

theorem anonymous_list_nonneg (x : Realization m n) (j : Fin n)
    (i : Fin m) (b : ℝ) (hb : Game.observe x j i = some b) : 0 ≤ b := by
  classical
  by_cases hj : j ∈ x.recipients i
  · have he : (x.action i).bid = b := by simpa [Game.observe, hj] using hb
    exact he ▸ (x.action i).bid_nonneg
  · simp [Game.observe, hj] at hb

theorem integral_routed_playedCount_seed (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (d : Fin m → Bayes.UserDraw n) (i : Fin m) (f : Fin (n + 1) → ℝ) :
    (∫ s, f ((routedSource Γ r hr).playedCount i (routedSample r (d, s)))
      ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)) =
      ∫ s, f (Bayes.playedCount Γ i (d, s))
        ∂(Measure.pi fun _ : Fin n => Γ.seedLaw) := by
  have hc (s : Fin n → Seed) :
      (routedSource Γ r hr).playedCount i (routedSample r (d, s)) =
        Bayes.selectionCount (Bayes.selectionVector Γ
          (fun j => reserveList (Game.observe (Bayes.drawsRealization d) j) r) s) i := by
    apply Fin.ext
    change count (fun l => routedAction r (d l)) Γ.policy s i = _
    rw [count_routedProfile]
    simp only [Game.inclusionCount, Game.accepted, Game.allocation,
      Bayes.selectionCount, Bayes.selectionVector]
    apply congrArg Finset.card
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [observe_reserveRealization]
  simp_rw [hc]
  exact integral_selectionCount_reserveList Γ r hr hT
    (fun j => Game.observe (Bayes.drawsRealization d) j)
    (fun j => anonymous_list_nonneg _ j) i f

theorem integral_routed_focalCount_seed (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (d : Fin m → Bayes.UserDraw n) (i : Fin m) (a : JointAction n)
    (τ : Equiv.Perm (Fin n)) (f : Fin (n + 1) → ℝ) :
    (∫ s, f ((routedSource Γ r hr).focalCount i (routedAction r ((0, a), τ))
      (routedSample r (d, s))) ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)) =
      ∫ s, f (Bayes.focalCount Γ i a ((d, s), τ))
        ∂(Measure.pi fun _ : Fin n => Γ.seedLaw) := by
  let L : Fin n → LocalList m := fun j =>
    Game.observe (Game.deviate (Bayes.drawsRealization d) i a.bid a.bid_nonneg
      (firstK τ a.routeCount)) j
  have hc (s : Fin n → Seed) :
      (routedSource Γ r hr).focalCount i (routedAction r ((0, a), τ))
        (routedSample r (d, s)) =
      Bayes.selectionCount (Bayes.selectionVector Γ (fun j => reserveList (L j) r) s) i := by
    apply Fin.ext
    simp only [FiniteGame.focalCount, count, accepted, allocation, routedSource,
      Bayes.selectionCount, Bayes.selectionVector]
    apply congrArg Finset.card
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [observe_routed_deviated]
    rfl
  simp_rw [hc]
  exact integral_selectionCount_reserveList Γ r hr hT L
    (fun j => anonymous_list_nonneg _ j) i f

theorem anonymous_integral_typeCount_eq_routed (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (f : Fin (n + 1) → ℝ) :
    (∫ v, (Bayes.typeOutcome Γ i v).expect f ∂Γ.F) =
      ∫ v, ((routedSource Γ r hr).typeOutcome i v).expect f ∂(routedSource Γ r hr).F := by
  let Γ' := routedSource Γ r hr
  have hactual : (∫ v, (Bayes.typeOutcome Γ i v).expect f ∂Γ.F) =
      ∫ ω, f (Bayes.playedCount Γ i ω) ∂Bayes.backgroundLaw Γ := by
    rw [Bayes.integral_typeOutcome_expect]
    exact (Bayes.integral_realized_eq_interim Γ i (fun p => f p.2)
      ((measurable_of_countable f).comp measurable_snd) (∑ k, ‖f k‖)
      (fun p => Finset.single_le_sum (fun k _ => norm_nonneg (f k))
        (Finset.mem_univ p.2))).symm
  rw [hactual, Γ'.integral_typeOutcome_expect_eq_actual]
  have hpres := routedSample_measurePreserving Γ r hr
  have hm : Measurable (fun ω => Γ'.playedCount i (routedSample r ω)) :=
    (Γ'.measurable_playedCount i).comp hpres.measurable
  have hmap : (∫ ω, f (Γ'.playedCount i ω)
        ∂(Bayes.backgroundLaw Γ).map (routedSample r)) =
      ∫ ω, f (Γ'.playedCount i (routedSample r ω)) ∂Bayes.backgroundLaw Γ :=
    integral_map_of_stronglyMeasurable hpres.measurable
      ((measurable_of_countable f).comp (Γ'.measurable_playedCount i)).stronglyMeasurable
  rw [← hpres.map_eq, hmap]
  rw [show Bayes.backgroundLaw Γ =
      (Measure.pi fun _ : Fin m => Bayes.userLaw Γ).prod
        (Measure.pi fun _ : Fin n => Γ.seedLaw) from rfl,
    integral_prod _ (CountLaw.integrable_comp _ _ (Bayes.measurable_playedCount Γ i) f),
    integral_prod _ (CountLaw.integrable_comp _ _ hm f)]
  apply integral_congr_ae
  exact Eventually.of_forall fun d => (integral_routed_playedCount_seed Γ r hr hT d i f).symm

theorem routed_bidTail_eq (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (j : Fin n) (b : ℝ) :
    bidTail (routedSource Γ r hr) j b = anonymousEligibleTail Γ r j b := by
  classical
  change (((routedSource Γ r hr).userLaw) (aboveAt j b)).toReal =
    ((Bayes.userLaw Γ) {d | r ≤ d.1.2.bid ∧ d ∈ Bayes.aboveAt j b}).toReal
  rw [routedSource_userLaw, Measure.map_apply
    (measurable_routedDraw r) (measurableSet_aboveAt j b)]
  apply congrArg (fun A : Set (Bayes.UserDraw n) => ((Bayes.userLaw Γ) A).toReal)
  ext d
  by_cases hb : r ≤ d.1.2.bid <;>
    by_cases hj : j ∈ firstK d.2 d.1.2.routeCount <;>
    simp [aboveAt, routedDraw, routedAction, Bayes.aboveAt, Bayes.entryBid, hb, hj]

theorem anonymousEligibleTail_eq_alphaGt (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (j : Fin n) (b : ℝ) (hb : r ≤ b) :
    anonymousEligibleTail Γ r j b = Bayes.alphaGt Γ j b := by
  unfold anonymousEligibleTail Bayes.alphaGt
  apply congrArg (Bayes.userLaw Γ).real
  ext d
  exact ⟨fun h => h.2, fun h => ⟨hb.trans h.2.le, h⟩⟩

theorem routed_quantile_eq (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (j l : Fin n) (δ : ℝ) :
    quantile (routedSource Γ r hr) j δ = quantile (routedSource Γ r hr) l δ := by
  unfold quantile ReserveQuantile.quantile
  congr 1
  ext b
  by_cases hb : r ≤ b
  · simp only [Set.mem_setOf_eq, hb, true_and, routed_bidTail_eq,
      anonymousEligibleTail_eq_alphaGt Γ r _ b hb, Bayes.alphaGt_eq Γ j l]
  · simp only [Set.mem_setOf_eq, hb, false_and]

theorem routed_price_eq_quantile (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (j : Fin n) (δ : ℝ) :
    price (routedSource Γ r hr) δ = quantile (routedSource Γ r hr) j δ := by
  obtain ⟨l, hl⟩ := exists_price_minimizer (routedSource Γ r hr) δ
    (Nat.zero_lt_of_lt j.isLt)
  exact hl.trans (routed_quantile_eq Γ r hr l j δ)

end FCAppendix.CommonReserve
