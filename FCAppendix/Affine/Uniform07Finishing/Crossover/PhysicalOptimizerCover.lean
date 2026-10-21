import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalFamilies
import FCAppendix.Affine.Hybrid.NativeLowIncentives

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology
namespace Physical
variable {population : ℕ→ℕ} {Seed : ℕ→ Type*} [∀ m, MeasurableSpace (Seed m)]
variable (Γ : ∀ m, FiniteGame (population m) 2 (Uniform07.capacity (population m)) (Seed m))

structure NativeLowerOptimizerSequence (row : Uniform07.Row) where
  market : ℕ→ℕ
  marketTendsto : Tendsto market atTop atTop
  identity : ∀ k, Fin (population (market k))
  value : ℕ→ℝ
  action : ℕ→ JointAction 2
  valueMem : ∀ k, value k∈Ioc (0:ℝ) (Uniform07.cutoff row)
  route : ∀ k, (action k).routeCount=1
  bidMem : ∀ k, (action k).bid∈Icc (0:ℝ) (min (value k) (Early.bidCap row))
  optimal : ∀ k, ∀ a' : JointAction 2, a'.routeCount=1 → a'.bid≤ Early.bidCap row →
    (problem (Γ (market k)) (identity k)).payoff (value k) a'≤
      (problem (Γ (market k)) (identity k)).payoff (value k) (action k)

structure EntryFullMenu06 (row : Uniform07.Row) where
  compare : ∀ s : NativeLowerOptimizerSequence Γ row,
    Tendsto s.value atTop (𝓝 (Uniform07.entry row)) →
    ∀ᶠ k in atTop, ∃ b∈Icc (0:ℝ) (Early.bidCap row),
      (problem (Γ (s.market k)) (s.identity k)).payoff (s.value k) (s.action k)<
        (problem (Γ (s.market k)) (s.identity k)).payoff (s.value k) (two b)

structure CanonicalOptimizer06 (row : Uniform07.Row) where
  compare : ∀ s : NativeLowerOptimizerSequence Γ row, ∀ v0 b0 : ℝ,
    Tendsto s.value atTop (𝓝 v0) →
    Tendsto (fun k => (s.action k).bid) atTop (𝓝 b0) →
    v0< Uniform07.entry row → b0∈Ioo (sourceCrossoverStart row) (Uniform07.entry row) →
    Uniform07.canonicalRate row (b0/Uniform07.cutoff row)< Uniform07.pureRate row (Uniform07.x row) →
    ∀ᶠ k in atTop, ∃ b∈Icc (0:ℝ) (Early.bidCap row),
      (problem (Γ (s.market k)) (s.identity k)).payoff (s.value k) (s.action k)<
        (problem (Γ (s.market k)) (s.identity k)).payoff (s.value k) (two b)

variable {Γ}

theorem eventually_every_native_lower_optimizer_loses
    {row : Uniform07.Row} {upper : ℕ→ℝ}
    (C : CrossoverFamily06 Γ row) (L : LowFamily06 Γ row)
    (P : ProductFamily05 Γ row upper) (E : EntryFullMenu06 Γ row)
    (K : CanonicalOptimizer06 Γ row)
    (hSchedule : ∀ m, (Γ m).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ m, (Γ m).g=0) :
    ∀ᶠ m in atTop, ∀ i : Fin (population m), ∀ v∈Ioc (0:ℝ) (Uniform07.cutoff row),
      ∀ a : JointAction 2, a.routeCount=1 →
      a.bid∈Icc (0:ℝ) (min v (Early.bidCap row)) →
      (∀ a' : JointAction 2, a'.routeCount=1 → a'.bid≤ Early.bidCap row →
        (problem (Γ m) i).payoff v a'≤(problem (Γ m) i).payoff v a) →
      ∃ b∈Icc (0:ℝ) (Early.bidCap row),
        (problem (Γ m) i).payoff v a<(problem (Γ m) i).payoff v (two b) := by
  classical
  by_contra hnot
  have hfreq : ∃ᶠ m in atTop, ∃ i : Fin (population m), ∃ v∈Ioc (0:ℝ) (Uniform07.cutoff row),
      ∃ a : JointAction 2, a.routeCount=1 ∧ a.bid∈Icc (0:ℝ) (min v (Early.bidCap row)) ∧
      (∀ a' : JointAction 2, a'.routeCount=1 → a'.bid≤ Early.bidCap row →
        (problem (Γ m) i).payoff v a'≤(problem (Γ m) i).payoff v a) ∧
      ¬∃ b∈Icc (0:ℝ) (Early.bidCap row),
        (problem (Γ m) i).payoff v a<(problem (Γ m) i).payoff v (two b) := by
    simpa only [not_eventually,not_forall,Classical.not_imp,exists_prop] using hnot
  obtain ⟨phi,hphi,hbad⟩ := extraction_of_frequently_atTop hfreq
  choose i v hv a ha hb hopt hlose using hbad
  have hcompact : IsCompact (Icc (0:ℝ) (Uniform07.cutoff row) ×ˢ
      Icc (0:ℝ) (Uniform07.cutoff row)) := isCompact_Icc.prod isCompact_Icc
  have hmem (k : ℕ) : (v k,(a k).bid)∈Icc (0:ℝ) (Uniform07.cutoff row) ×ˢ
      Icc (0:ℝ) (Uniform07.cutoff row) :=
    ⟨⟨(hv k).1.le,(hv k).2⟩,
      ⟨(hb k).1,((hb k).2.trans (min_le_left _ _)).trans (hv k).2⟩⟩
  obtain ⟨z,hz,chi,hchi,hconv⟩ := hcompact.isSeqCompact hmem
  let s : NativeLowerOptimizerSequence Γ row := {
    market := phi ∘ chi
    marketTendsto := hphi.tendsto_atTop.comp hchi.tendsto_atTop
    identity := fun k => i (chi k)
    value := v ∘ chi
    action := a ∘ chi
    valueMem := fun k => hv (chi k)
    route := fun k => ha (chi k)
    bidMem := fun k => hb (chi k)
    optimal := fun k => hopt (chi k) }
  have hvconv : Tendsto s.value atTop (𝓝 z.1) := continuous_fst.tendsto z |>.comp hconv
  have hbconv : Tendsto (fun k => (s.action k).bid) atTop (𝓝 z.2) :=
    continuous_snd.tendsto z |>.comp hconv
  have hbv : z.2≤ z.1 := le_of_tendsto_of_tendsto hbconv hvconv
    (.of_forall fun k => (s.bidMem k).2.trans (min_le_left _ _))
  have hwin : ∀ᶠ k in atTop, ∃ b∈Icc (0:ℝ) (Early.bidCap row),
      (problem (Γ (s.market k)) (s.identity k)).payoff (s.value k) (s.action k)<
        (problem (Γ (s.market k)) (s.identity k)).payoff (s.value k) (two b) := by
    rcases optimizer_limit_regimes (entry := Uniform07.entry row)
      (lowStart := sourceCrossoverStart row) (lowTop := sourceLowTop row)
      (crossoverEnd := sourceCrossoverEnd row) hbv (source_low_overlap row) with
      he | hac | ⟨hvlt,hcases⟩
    · exact E.compare s (by simpa only [he] using hvconv)
    · exact P.every_moving_active_singleton_loses hSchedule hFee s.market s.marketTendsto
        s.identity s.value s.action s.valueMem s.route
        (fun k => (s.bidMem k).2.trans (min_le_left _ _))
        (fun k => (s.bidMem k).2.trans (min_le_right _ _)) hac hvconv
    · rcases hcases with hlo | hcross | hcanonical
      · have hsmall := hbconv.eventually (Iio_mem_nhds hlo)
        filter_upwards [hsmall,s.marketTendsto.eventually L.small_duplicate,
          s.marketTendsto.eventually L.halfValue] with k hbk hdk hhk
        have hh := source_half_value_cap row (s.valueMem k).2
        obtain ⟨b,hb',hgain⟩ := every_low_singleton_action_loses (Γ (s.market k)) (s.identity k)
          (source_eta_mem row) (hSchedule (s.market k)) (hFee (s.market k))
          (s.valueMem k).1 hdk.1 hh.1 hh.2 (hhk (s.identity k) (s.value k) (s.valueMem k))
          (hdk.2 (s.identity k)) (s.action k) (s.route k)
          ((s.bidMem k).2.trans (min_le_right _ _)) hbk.le
        exact ⟨b,⟨hb'.1,hb'.2.trans (min_le_right _ _)⟩,hgain⟩
      · have hc := C.every_moving_crossover_optimizer_loses hSchedule hFee s.market s.marketTendsto
          s.identity s.value s.action s.route
          (fun k => (s.bidMem k).2.trans (min_le_left _ _)) s.optimal hcross hbconv
        filter_upwards [hc] with k hk
        have hroute : LowBody.addSecondRoute (s.action k)=two (s.action k).bid := by
          simpa only [LowBody.addSecondRoute] using raw_two_eq (LowBody.addSecondRoute (s.action k)) rfl
        refine ⟨(s.action k).bid,
          ⟨(s.bidMem k).1,(s.bidMem k).2.trans (min_le_right _ _)⟩,?_⟩
        simpa only [hroute] using hk
      · exact K.compare s z.1 z.2 hvconv hbconv hvlt
          ⟨(source_crossover_end_gt_start row).trans_le hcanonical.1,hcanonical.2⟩
          (source_canonical_below_pure_entry row hcanonical.1 hcanonical.2)
  obtain ⟨k,hk⟩ := hwin.exists
  exact hlose (chi k) hk

theorem eventually_every_native_capped_singleton_loses
    {row : Uniform07.Row} {upper : ℕ→ℝ}
    (C : CrossoverFamily06 Γ row) (L : LowFamily06 Γ row)
    (P : ProductFamily05 Γ row upper) (E : EntryFullMenu06 Γ row)
    (K : CanonicalOptimizer06 Γ row)
    (hSchedule : ∀ m, (Γ m).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ m, (Γ m).g=0) :
    ∀ᶠ m in atTop, ∀ i : Fin (population m), ∀ v∈Ioc (0:ℝ) (Uniform07.cutoff row),
      ∀ a : JointAction 2, a.routeCount=1 → a.bid≤ Early.bidCap row →
      ∃ b∈Icc (0:ℝ) (Early.bidCap row),
        (problem (Γ m) i).payoff v a<(problem (Γ m) i).payoff v (two b) := by
  have hopt := eventually_every_native_lower_optimizer_loses C L P E K hSchedule hFee
  filter_upwards [hopt,L.small_duplicate,L.halfValue] with m hm hd hh
  intro i v hv
  have hhalf := source_half_value_cap row hv.2
  have heta : Uniform07.eta row∈Ioc (0:ℝ) 1 :=
    ⟨Uniform07.eta_pos row,(source_eta_mem row).2⟩
  have hcont := (C.broadcast m).actual_marginal_continuousOn_positive i heta
    (hSchedule m) (hFee m) (div_pos (source_low_positive row) (by norm_num : (0:ℝ)<2))
  exact every_lower_singleton_action_of_optimizer_exclusion (Γ m) i heta
    (hSchedule m) (hFee m) hv.1 hd.1 (source_low_positive row)
    hhalf.1 hhalf.2 (hh i v hv) (hd.2 i) hcont (hm i v hv)

theorem eventually_every_native_lower_singleton_capped_winner
    {row : Uniform07.Row} {upper : ℕ→ℝ}
    (C : CrossoverFamily06 Γ row) (L : LowFamily06 Γ row)
    (P : ProductFamily05 Γ row upper) (E : EntryFullMenu06 Γ row)
    (K : CanonicalOptimizer06 Γ row)
    (hSchedule : ∀ m, (Γ m).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ m, (Γ m).g=0) :
    ∀ᶠ m in atTop, ∀ v : ℝ, 0< v → v≤ Uniform07.cutoff row → ∀ i : Fin (population m),
      ∀ a : JointAction 2, a.routeCount=1 → a.bid< upper m →
        ∃ b∈Icc (0:ℝ) (Early.bidCap row),
          (problem (Γ m) i).payoff v a<(problem (Γ m) i).payoff v (two b) := by
  have hc := eventually_every_native_capped_singleton_loses C L P E K hSchedule hFee
  have ho := P.eventually_every_omitted_singleton_loses L hSchedule hFee
  filter_upwards [hc,ho,P.floorAboveCap] with m hcm hom hR
  intro v hv hvt i a ha hab
  by_cases hU : a.bid≤ Early.bidCap row
  · exact hcm i v ⟨hv,hvt⟩ a ha hU
  · exact hom i v ⟨hv,hvt⟩ a ha ⟨lt_of_not_ge hU,hab⟩

theorem eventually_every_native_lower_raw_singleton_loses
    {row : Uniform07.Row} {upper : ℕ→ℝ}
    (C : CrossoverFamily06 Γ row) (L : LowFamily06 Γ row)
    (P : ProductFamily05 Γ row upper) (E : EntryFullMenu06 Γ row)
    (K : CanonicalOptimizer06 Γ row)
    (hSchedule : ∀ m, (Γ m).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ m, (Γ m).g=0) :
    ∀ᶠ m in atTop, ∀ v : ℝ, 0< v → v≤ Uniform07.cutoff row → ∀ i : Fin (population m),
      ∀ a : JointAction 2, a.routeCount=1 → a.bid< upper m →
        ∃ b : JointAction 2, b.routeCount=2 ∧ b.bid< upper m ∧
          (problem (Γ m) i).payoff v a<(problem (Γ m) i).payoff v b := by
  have hc := eventually_every_native_lower_singleton_capped_winner C L P E K hSchedule hFee
  filter_upwards [hc,P.floorAboveCap] with m hcm hR
  intro v hv hvt i a ha hab
  obtain ⟨z,hz,hgain⟩ := hcm v hv hvt i a ha hab
  refine ⟨two z,two_routes z,?_,hgain⟩
  simpa only [two_bid hz.1] using hz.2.trans_lt hR

theorem LowFamily06.eventually_every_native_abstention_loses
    {row : Uniform07.Row} (L : LowFamily06 Γ row)
    (hSchedule : ∀ m, (Γ m).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ m, (Γ m).g=0) :
    ∀ᶠ m in atTop, ∀ i : Fin (population m), ∀ v∈Ioc (0:ℝ) (Uniform07.cutoff row),
      ∀ a : JointAction 2, a.routeCount=0 →
      (problem (Γ m) i).payoff v a<(problem (Γ m) i).payoff v (two (v/2)) := by
  filter_upwards [L.small_duplicate,L.halfValue] with m hd hh
  intro i v hv a ha
  have hhalf := source_half_value_cap row hv.2
  have hD := hd.2 i (v/2) ⟨div_nonneg hv.1.le (by norm_num),hhalf.2⟩
  have hpay := half_value_broadcast_payoff_lower (Γ m) i (source_eta_mem row)
    (hSchedule m) (hFee m) hv.1.le hd.1.le (hh i v hv) (hD.trans (by linarith [hd.1]))
  have hnonpos := Hybrid.NativeLowIncentives.payoff_nonpos_of_zero_routes (Γ m) i v a ha
  exact hnonpos.trans_lt ((div_pos (mul_pos hv.1 hd.1) (by norm_num)).trans_le hpay)

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
