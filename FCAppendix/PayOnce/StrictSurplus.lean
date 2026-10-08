import FCAppendix.PayOnce.ZeroBidDeviation

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exists_real_cut_of_null_fibers {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hμ : μ ≠ 0)
    (hatom : ∀ r, μ {x | f x = r} = 0) :
    ∃ q : ℚ, μ {x | f x < q} ≠ 0 ∧ μ {x | (q : ℝ) < f x} ≠ 0 := by
  classical
  haveI := ae_neBot.mpr hμ
  by_contra! hsplit
  have hcuts : ∀ᵐ x ∂μ, ∀ q : ℚ,
      (μ {y | f y < q} = 0 → ¬ f x < q) ∧
      (μ {y | (q : ℝ) < f y} = 0 → ¬ (q : ℝ) < f x) := by
    apply ae_all_iff.mpr
    intro q
    have hlo : ∀ᵐ x ∂μ, μ {y | f y < q} = 0 → ¬ f x < q := by
      by_cases h : μ {y | f y < q} = 0
      · exact (measure_eq_zero_iff_ae_notMem.mp h).mono fun _ hx _ => hx
      · exact Filter.Eventually.of_forall fun _ hx => (h hx).elim
    have hhi : ∀ᵐ x ∂μ, μ {y | (q : ℝ) < f y} = 0 → ¬ (q : ℝ) < f x := by
      by_cases h : μ {y | (q : ℝ) < f y} = 0
      · exact (measure_eq_zero_iff_ae_notMem.mp h).mono fun _ hx _ => hx
      · exact Filter.Eventually.of_forall fun _ hx => (h hx).elim
    exact hlo.and hhi
  obtain ⟨x, hx⟩ := hcuts.exists
  have hconst : ∀ᵐ y ∂μ, f y = f x := by
    filter_upwards [hcuts] with y hy
    apply le_antisymm
    · by_contra h
      obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn (lt_of_not_ge h)
      by_cases hlow : μ {z | f z < q} = 0
      · exact (hx q).1 hlow hxq
      · exact (hy q).2 (hsplit q hlow) hqy
    · by_contra h
      obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn (lt_of_not_ge h)
      by_cases hlow : μ {z | f z < q} = 0
      · exact (hy q).1 hlow hyq
      · exact (hx q).2 (hsplit q hlow) hqx
  obtain ⟨y, hy, hne⟩ := (hconst.and (measure_eq_zero_iff_ae_notMem.mp (hatom (f x)))).exists
  exact hne hy

def PositiveValueAtomless (Γ : FiniteGame m n c Seed) : Prop :=
  ∀ v : ℝ, Γ.g < v → Γ.F {v} = 0

theorem measure_positive_zero_service_at_zero (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hc : 0 < c) (j : Fin n)
    (hrat : ProposerRationalAtFeasibleLists Γ j)
    (P : ℝ × JointAction n → Prop) (hP : MeasurableSet {x | P x})
    (hbid : ∀ x, P x → 0 < x.2.bid)
    (hzero : ∀ i x, P x → ((problem Γ i).outcome x.2).success = 0) :
    userLaw Γ {d | P d.1 ∧ j ∈ firstK d.2 d.1.2.routeCount} = 0 := by
  classical
  by_contra hmass
  have hz (i : Fin m) : ∀ᵐ ω ∂backgroundLaw Γ, P (ω.1 i).1 → playedCount Γ i ω = 0 := by
    apply ae_played_of_ae_deviation Γ i (fun x r => P x → r = 0)
    · have hp : MeasurableSet {p : (ℝ × JointAction n) × Fin (n + 1) | P p.1} :=
        measurable_fst hP
      have hcnt : MeasurableSet {p : (ℝ × JointAction n) × Fin (n + 1) | p.2 = 0} :=
        measurableSet_eq_fun measurable_snd measurable_const
      simpa only [imp_iff_not_or, Set.compl_setOf, Set.setOf_or] using hp.compl.union hcnt
    · apply Filter.Eventually.of_forall
      intro x
      by_cases hx : P x
      · exact (ae_focalCount_zero_of_success_zero Γ i x.2 (hzero i x hx)).mono fun _ h _ => h
      · exact Filter.Eventually.of_forall fun _ h => (hx h).elim
  have hdrawzero := Measure.ae_ae_of_ae_prod (ae_all_iff.mpr hz)
  let D : Set (UserProfile m n) := Set.univ.pi fun _ : Fin m =>
    {d | P d.1 ∧ j ∈ firstK d.2 d.1.2.routeCount}
  have hD : userProfileLaw Γ D ≠ 0 := by
    simp only [D, userProfileLaw, Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hmass
  obtain ⟨d, hdD, hdz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hD
    (ae_restrict_of_ae hdrawzero)
  obtain ⟨belief, hopt⟩ := hrat
  let ℓ := observe (drawsRealization d) j
  have ho := hopt ℓ ⟨d, rfl⟩
  have hos := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae ho
  obtain ⟨s, hsz, hso⟩ := (hdz.and hos).exists
  have hd (i : Fin m) : P (d i).1 ∧ j ∈ firstK (d i).2 (d i).1.2.routeCount :=
    hdD i (Set.mem_univ i)
  have hempty : allocation (drawsRealization d) Γ.policy s j = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hmem : j ∈ accepted (drawsRealization d) Γ.policy s i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hi⟩
    have hpos := Finset.card_pos.mpr ⟨j, hmem⟩
    have hzv : (accepted (drawsRealization d) Γ.policy s i).card = 0 :=
      congrArg Fin.val (hsz i (hd i).1)
    omega
  let i : Fin m := ⟨0, hm⟩
  have hi : ℓ i = some (d i).1.2.bid := by simp [ℓ, observe, drawsRealization, (hd i).2]
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hA (r : ℕ) (hr : 0 < r) (hrn : r ≤ n) : (1 / (n : ℝ)) * r ≤ Γ.A.charge r := by
    have hrR : (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hratio : (r : ℝ) / n ≤ 1 := (div_le_one hn).mpr hrR
    simpa [div_eq_mul_inv, mul_comm] using hratio.trans (Γ.A.lower r hr hrn)
  have hreceipt := (beliefReceipts_bounds Γ.A (belief ℓ) ℓ (1 / (n : ℝ)) hA
    i _ (d i).1.2.bid_nonneg hi).1
  have hpos : 0 < beliefReceipts Γ.A (belief ℓ) ℓ i :=
    lt_of_lt_of_le (mul_pos (one_div_pos.mpr hn) (hbid (d i).1 (hd i).1)) hreceipt
  have hfill := Finite.optimal_fills c _ _ hso i
    (by change i ∉ allocation (drawsRealization d) Γ.policy s j; simp [hempty]) hpos
  change (allocation (drawsRealization d) Γ.policy s j).card = c at hfill
  rw [hempty, Finset.card_empty] at hfill
  omega

theorem measure_positive_zero_service_zero (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (P : ℝ × JointAction n → Prop) (hP : MeasurableSet {x | P x})
    (hval : ∀ x, P x → Γ.g < x.1) (hbid : ∀ x, P x → 0 < x.2.bid)
    (hzero : ∀ i x, P x → ((problem Γ i).outcome x.2).success = 0) :
    (Γ.F ⊗ₘ Γ.σ) {x | P x} = 0 := by
  classical
  have hall : ∀ᵐ d ∂userLaw Γ, ∀ j : Fin n, ¬ (P d.1 ∧ j ∈ firstK d.2 d.1.2.routeCount) :=
    ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp
      (measure_positive_zero_service_at_zero Γ hm hc j (hrat j) P hP hbid hzero)
  have hnot : ∀ᵐ d ∂userLaw Γ, ¬ P d.1 := by
    filter_upwards [hall, ae_positive_value_routes_userLaw Γ hm hn hc hA hG hu hrat] with d hd hr hPd
    have hk := hr (hval d.1 hPd)
    have hcard : 0 < (firstK d.2 d.1.2.routeCount).card := by
      rwa [card_firstK _ _ d.1.2.routeCount_le]
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
    exact hd j ⟨hPd, hj⟩
  apply measure_eq_zero_iff_ae_notMem.mpr
  have h := Measure.ae_ae_of_ae_prod hnot
  filter_upwards [h] with x hx
  exact hx.exists.choose_spec

def ZeroSurplus (g : ℝ) (x : ℝ × JointAction n) : Prop :=
  g < x.1 ∧ x.2.bid = x.1 - g

theorem measurableSet_zeroSurplus (g : ℝ) :
    MeasurableSet {x : ℝ × JointAction n | ZeroSurplus g x} :=
  (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_eq_fun ((measurable_bid n).comp measurable_snd) (measurable_fst.sub_const g))

theorem measure_zeroSurplus_zero (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveValueAtomless Γ) :
    (Γ.F ⊗ₘ Γ.σ) {x | ZeroSurplus Γ.g x} = 0 := by
  classical
  let E : Set (ℝ × JointAction n) := {x | ZeroSurplus Γ.g x}
  have hE : MeasurableSet E := measurableSet_zeroSurplus Γ.g
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
      have hxpos : Γ.g < x.1 := hx.1
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
  let P := fun x : ℝ × JointAction n => ZeroSurplus Γ.g x ∧ x.1 < q
  have hP : MeasurableSet {x | P x} := hE.inter hqlo
  have hzero (i : Fin m) (x : ℝ × JointAction n) (hx : P x) :
      ((problem Γ i).outcome x.2).success = 0 := by
    have hupay : (problem Γ i).payoff u.1 u.2 = 0 := by
      rw [payoff_once Γ hA hG, huE.2.2]
      have he : u.1 - (u.1 - Γ.g) - Γ.g = 0 := by ring
      rw [he, zero_mul]
    have hcompare := hubest i x.2
    rw [hupay, payoff_once Γ hA hG, hx.1.2] at hcompare
    have hlow : x.1 < (q : ℝ) := hx.2
    have hhigh : (q : ℝ) < u.1 := huE.1
    have hsurplus : 0 < u.1 - (x.1 - Γ.g) - Γ.g := by linarith
    have hnonneg := CountLaw.success_nonneg ((problem Γ i).outcome x.2)
    nlinarith
  have hlowerzero := measure_positive_zero_service_zero Γ hm hn hc hA hG hu hrat P hP
    (fun _ hx => hx.1.1) (fun x hx => by rw [hx.1.2]; exact sub_pos.mpr hx.1.1) hzero
  apply hlo
  rw [Measure.restrict_apply hqlo]
  have hset : {x : ℝ × JointAction n | x.1 < (q : ℝ)} ∩ E = {x | P x} := by
    ext x
    exact and_comm
  rw [hset]
  exact hlowerzero

theorem ae_positive_value_strict_surplus_broadcast (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, Γ.g < v → 0 < a.bid ∧ a.bid < v - Γ.g ∧ a.routeCount = n := by
  have hm : 0 < m := lt_trans hc hcm
  have hrat := posterior_rationalAtFeasibleLists Γ B hB
  have hEq := posterior_isAEEquilibrium Γ hu B hB
  have hno := ae_no_overbid_compProd_onPath Γ hm hc hEq
  have hroute := ae_positive_value_routes_compProd Γ hm hn hc hA hG hu hrat
  have hpos := ae_positive_value_bid_pos_compProd Γ hn hc hcm hA hG hu hrat hsym
  have hneq := measure_eq_zero_iff_ae_notMem.mp
    (measure_zeroSurplus_zero Γ hm hn hc hA hG hu hrat hatom)
  have hbroad := ae_positive_surplus_broadcast_compProd Γ hc hcm hA hG hu hrat hsym
  apply Measure.ae_ae_of_ae_compProd (μ := Γ.F) (κ := Γ.σ)
    (p := fun x : ℝ × JointAction n =>
    Γ.g < x.1 → 0 < x.2.bid ∧ x.2.bid < x.1 - Γ.g ∧ x.2.routeCount = n)
  filter_upwards [hno, hroute, hpos, hneq, hbroad] with x hno hr hp hne hb hv
  have hle := hno (hr hv)
  rw [max_eq_left (sub_pos.mpr hv).le] at hle
  have hlt : x.2.bid < x.1 - Γ.g := lt_of_le_of_ne hle (fun he => hne ⟨hv, he⟩)
  refine ⟨hp hv, hlt, hb (hp hv) ?_⟩
  linarith

end FCAppendix.Bayes
