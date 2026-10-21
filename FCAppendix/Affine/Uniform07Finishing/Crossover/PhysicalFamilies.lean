import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalProduct

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology
namespace Physical

variable {population : ℕ→ℕ} {Seed : ℕ→ Type*} [∀ m, MeasurableSpace (Seed m)]
variable (Γ : ∀ m, FiniteGame (population m) 2 (Uniform07.capacity (population m)) (Seed m))

lemma tail_population_tendsto (M0 : ℕ) : Tendsto (fun k : ℕ => M0+k) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n] with k hk
  omega

lemma eventual_tail_to_every_market {P : ℕ→ Prop} (M0 : ℕ)
    (h : ∀ᶠ k in atTop, P (M0+k)) : ∀ᶠ m in atTop, P m := by
  obtain ⟨k0,hk0⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨M0+k0,?_⟩
  intro m hm
  have hk : k0≤ m-M0 := by omega
  have heq : M0+(m-M0)=m := by omega
  simpa only [heq] using hk0 (m-M0) hk

def sourceLowTop (row : Uniform07.Row) : ℝ := (501/1000:ℝ)*Uniform07.cutoff row

def sourceCrossoverStart (row : Uniform07.Row) : ℝ := Uniform07.cutoff row/2

def sourceCrossoverEnd (row : Uniform07.Row) : ℝ := Uniform07.sourceZhi row*Uniform07.cutoff row

lemma source_low_overlap (row : Uniform07.Row) :
    sourceCrossoverStart row< sourceLowTop row := by
  unfold sourceCrossoverStart sourceLowTop
  nlinarith [Uniform07.cutoff_pos row]

lemma source_crossover_end_gt_start (row : Uniform07.Row) :
    sourceCrossoverStart row< sourceCrossoverEnd row := by
  have ht := Uniform07.cutoff_pos row
  cases row <;> norm_num [sourceCrossoverStart,sourceCrossoverEnd,Uniform07.sourceZhi] at * <;> linarith

lemma source_canonical_below_pure_entry (row : Uniform07.Row) {b : ℝ}
    (hb : sourceCrossoverEnd row≤ b) (hbl : b< Uniform07.entry row) :
    Uniform07.canonicalRate row (b/Uniform07.cutoff row)<
      Uniform07.pureRate row (Uniform07.x row) := by
  have ht := Uniform07.cutoff_pos row
  have hzhi : Uniform07.sourceZhi row∈Icc (1/2:ℝ) (Uniform07.x row) := by
    cases row <;> norm_num [Uniform07.sourceZhi,Uniform07.x,Uniform07.xQ]
  have hzb : Uniform07.sourceZhi row≤ b/Uniform07.cutoff row :=
    (le_div_iff₀ ht).2 hb
  have hbx : b/Uniform07.cutoff row≤ Uniform07.x row := by
    apply (div_le_iff₀ ht).2
    exact hbl.le
  have hmono := Uniform07.source_rate_antitone row hzhi ⟨hzhi.1.trans hzb,hbx⟩ hzb
  have hend : Uniform07.canonicalRate row (Uniform07.sourceZhi row)<
      Uniform07.pureRate row (Uniform07.x row) := by
    cases row
    · exact Uniform07.canonical_upper_endpoint_gap.1
    · exact Uniform07.canonical_upper_endpoint_gap.2
  exact hmono.trans_lt hend

lemma source_low_positive (row : Uniform07.Row) : 0< sourceLowTop row := by
  unfold sourceLowTop
  exact mul_pos (by norm_num) (Uniform07.cutoff_pos row)

lemma source_half_value_cap (row : Uniform07.Row) {v : ℝ} (hv : v≤ Uniform07.cutoff row) :
    v/2≤ Early.bidCap row ∧ v/2≤ sourceLowTop row := by
  have ht := Uniform07.cutoff_pos row
  constructor
  · have hc : Uniform07.cutoff row/2< Early.bidCap row := by
      cases row <;> norm_num [Early.bidCap,Early.capRatioQ,Uniform07.xQ,
        Uniform07.kappaQ,Uniform07.xiQ,Uniform07.etaQ] at * <;> linarith
    linarith
  · unfold sourceLowTop
    linarith

structure LowFamily06 (row : Uniform07.Row) where
  ell : ℕ→ℝ
  duplicateBound : ℕ→ℝ
  ellPositive : ∀ᶠ m in atTop, 0< ell m
  halfValue : ∀ᶠ m in atTop, ∀ i : Fin (population m), ∀ v∈Ioc (0:ℝ) (Uniform07.cutoff row),
    ell m≤ q (Γ m) i (v/2)
  duplicate : ∀ᶠ m in atTop, ∀ i : Fin (population m), ∀ b∈Icc (0:ℝ) (sourceLowTop row),
    Physical.duplicate (Γ m) i b≤ duplicateBound m
  relativeError : Tendsto (fun m => duplicateBound m/ell m) atTop (𝓝 0)

structure ProductFamily05 (row : Uniform07.Row) (upper : ℕ→ℝ) where
  error : ℕ→ℝ
  errorNonnegative : ∀ᶠ m in atTop, 0≤ error m
  errorSmall : Tendsto error atTop (𝓝 0)
  floorAboveCap : ∀ᶠ m in atTop, Early.bidCap row< upper m
  kernels : ∀ᶠ m in atTop, ∀ i : Fin (population m),
    Nonempty (ProductKernels05 row (Γ m) i (upper m) (error m))

structure CrossoverFamily06 (row : Uniform07.Row) where
  populationTendsto : Tendsto population atTop atTop
  broadcast : ∀ m, BroadcastLaw05 (Γ m) (Uniform07.cutoff row) (Early.bidCap row)
  canonicalEvent : ∀ m, Fin (population m) → CanonicalEvent (Γ m)
  A : ℝ→ℝ
  Amin : ℝ
  Amax : ℝ
  Rmax : ℝ
  Dmax : ℝ
  AminPositive : 0< Amin
  RmaxNonnegative : 0≤ Rmax
  DmaxNonnegative : 0≤ Dmax
  e19 : ℕ→ℝ
  eS : ℕ→ℝ
  eD : ℕ→ℝ
  ell : ℕ→ℝ
  nonnegative : ∀ᶠ m in atTop, 0≤ e19 m ∧ 0≤ eS m ∧ 0≤ eD m ∧ 0< ell m
  core : ∀ᶠ m in atTop, ∀ i : Fin (population m),
    Nonempty (RemoteCore06 row (Γ m) i (canonicalEvent m i)
      (sourceCrossoverStart row) (sourceCrossoverEnd row) (Early.bidCap row)
      (broadcast m) A Amin Amax Rmax Dmax (e19 m) (ell m))
  split : ∀ᶠ m in atTop, ∀ i : Fin (population m),
    Nonempty (PureDerivativeBounds06 (Γ m) i (canonicalEvent m i) (Uniform07.cutoff row)
      (sourceCrossoverStart row) (sourceCrossoverEnd row) (eS m) (eD m))
  e19Small : Tendsto e19 atTop (𝓝 0)
  successCoefficient : ℝ
  successRate : ℝ
  successRatePositive : 0< successRate
  successChernoff : ∀ᶠ m in atTop,
    eS m≤ successCoefficient*Real.exp (-successRate*(population m:ℝ))
  duplicateSmall : Tendsto eD atTop (𝓝 0)
  duplicateRentSmall : Tendsto
    (fun m => eD m/((population m:ℝ)*sourceCrossoverStart row*ell m/2)) atTop (𝓝 0)

variable {Γ}

lemma LowFamily06.small_duplicate {row : Uniform07.Row} (D : LowFamily06 Γ row) :
    ∀ᶠ m in atTop, 0< D.ell m ∧
      ∀ i : Fin (population m), ∀ b∈Icc (0:ℝ) (sourceLowTop row),
        Physical.duplicate (Γ m) i b≤ D.ell m/8 := by
  have hsmall := D.relativeError.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/8))
  filter_upwards [D.ellPositive,D.duplicate,hsmall] with m hm hd hs
  refine ⟨hm,?_⟩
  intro i b hb
  have h := (div_lt_iff₀ hm).mp hs
  exact (hd i b hb).trans (by linarith)

lemma CrossoverFamily06.weighted_success_small {row : Uniform07.Row} (D : CrossoverFamily06 Γ row) :
    Tendsto (fun m => (population m:ℝ)*D.eS m) atTop (𝓝 0) := by
  apply weighted_success_error_tendsto_of_chernoff D.populationTendsto D.successRatePositive
  filter_upwards [D.nonnegative,D.successChernoff] with m hn hc
  exact ⟨hn.2.1,hc⟩

lemma CrossoverFamily06.success_small {row : Uniform07.Row} (D : CrossoverFamily06 Γ row) :
    Tendsto D.eS atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds D.weighted_success_small
  · filter_upwards [D.nonnegative] with m hm
    exact hm.2.1
  · filter_upwards [D.nonnegative,D.populationTendsto.eventually (eventually_ge_atTop 1)] with m hm hsize
    have hreal : 1≤(population m:ℝ) := by exact_mod_cast hsize
    nlinarith [mul_nonneg hm.2.1 (sub_nonneg.mpr hreal)]

lemma CrossoverFamily06.unified_small {row : Uniform07.Row} (D : CrossoverFamily06 Γ row) :
    Tendsto (fun m => (population m:ℝ)*D.eS m+D.eD m) atTop (𝓝 0) :=
  unified_error_tendsto_zero D.weighted_success_small D.duplicateSmall

lemma CrossoverFamily06.actual_data {row : Uniform07.Row} (D : CrossoverFamily06 Γ row) :
    ∀ᶠ m in atTop, ∀ i : Fin (population m),
      Nonempty (RemoteKernels06 row (Γ m) i (D.canonicalEvent m i)
        (sourceCrossoverStart row) (sourceCrossoverEnd row) (Early.bidCap row)
        (D.broadcast m) D.A D.Amin D.Amax D.Rmax D.Dmax (D.e19 m)
        ((population m:ℝ)*D.eS m+D.eD m) (D.ell m)) ∧
      Nonempty (PureDerivativeBounds06 (Γ m) i (D.canonicalEvent m i) (Uniform07.cutoff row)
        (sourceCrossoverStart row) (sourceCrossoverEnd row) (D.eS m) (D.eD m)) := by
  filter_upwards [D.core,D.split,D.nonnegative,D.populationTendsto.eventually (eventually_ge_atTop 1)] with m hc hs hn hm
  intro i
  obtain ⟨Y⟩ := hc i
  obtain ⟨X⟩ := hs i
  have hreal : 0<(population m:ℝ) := by exact_mod_cast (show 0< population m by omega)
  exact ⟨⟨PureDerivativeBounds06.toRemoteKernels06 Y X hreal hn.2.1 hn.2.2.1⟩,⟨X⟩⟩

theorem CrossoverFamily06.every_moving_crossover_optimizer_loses
    {row : Uniform07.Row} (D : CrossoverFamily06 Γ row)
    (hSchedule : ∀ m, (Γ m).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ m, (Γ m).g=0)
    (market : ℕ→ℕ) (hmarket : Tendsto market atTop atTop)
    (i : ∀ k, Fin (population (market k))) (v : ℕ→ℝ) (a : ℕ→ JointAction 2)
    (haroute : ∀ k, (a k).routeCount=1) (hav : ∀ k, (a k).bid≤ v k)
    (hopt : ∀ k, ∀ a' : JointAction 2, a'.routeCount=1 → a'.bid≤ Early.bidCap row →
      (problem (Γ (market k)) (i k)).payoff (v k) a'≤
        (problem (Γ (market k)) (i k)).payoff (v k) (a k))
    {b0 : ℝ} (hb0 : b0∈Ioo (sourceCrossoverStart row) (sourceCrossoverEnd row))
    (hbid : Tendsto (fun k => (a k).bid) atTop (𝓝 b0)) :
    ∀ᶠ k in atTop,
      (problem (Γ (market k)) (i k)).payoff (v k) (a k)<
        (problem (Γ (market k)) (i k)).payoff (v k) (LowBody.addSecondRoute (a k)) := by
  have hd : ∀ᶠ k in atTop,
      Nonempty (RemoteKernels06 row (Γ (market k)) (i k) (D.canonicalEvent (market k) (i k))
        (sourceCrossoverStart row) (sourceCrossoverEnd row) (Early.bidCap row)
        (D.broadcast (market k)) D.A D.Amin D.Amax D.Rmax D.Dmax (D.e19 (market k))
        ((population (market k):ℝ)*D.eS (market k)+D.eD (market k)) (D.ell (market k))) ∧
      Nonempty (PureDerivativeBounds06 (Γ (market k)) (i k) (D.canonicalEvent (market k) (i k))
        (Uniform07.cutoff row) (sourceCrossoverStart row) (sourceCrossoverEnd row)
        (D.eS (market k)) (D.eD (market k))) := by
    filter_upwards [hmarket.eventually D.actual_data] with k hk
    exact hk (i k)
  have hn : ∀ᶠ k in atTop,
      0≤ D.e19 (market k) ∧ 0≤(population (market k):ℝ)*D.eS (market k)+D.eD (market k) ∧
      0< D.ell (market k) ∧ 0≤ D.eS (market k) ∧ 0≤ D.eD (market k) := by
    filter_upwards [hmarket.eventually D.nonnegative] with k hk
    exact ⟨hk.1,add_nonneg (mul_nonneg (Nat.cast_nonneg _) hk.2.1) hk.2.2.1,
      hk.2.2.2,hk.2.1,hk.2.2.1⟩
  exact eventually_raw_crossover_optimizer_loses
    (fun k => Γ (market k)) i (fun k => D.canonicalEvent (market k) (i k))
    (fun k => D.broadcast (market k)) (D.populationTendsto.comp hmarket) D.AminPositive D.RmaxNonnegative D.DmaxNonnegative
    (fun k => hSchedule (market k)) (fun k => hFee (market k)) hd hn
    (D.e19Small.comp hmarket) (D.unified_small.comp hmarket) (D.success_small.comp hmarket)
    (D.duplicateSmall.comp hmarket) (D.duplicateRentSmall.comp hmarket)
    v a haroute hav hopt hb0 hbid

theorem ProductFamily05.every_moving_active_singleton_loses
    {row : Uniform07.Row} {upper : ℕ→ℝ} (D : ProductFamily05 Γ row upper)
    (hSchedule : ∀ m, (Γ m).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ m, (Γ m).g=0)
    (market : ℕ→ℕ) (hmarket : Tendsto market atTop atTop)
    (i : ∀ k, Fin (population (market k))) (v : ℕ→ℝ) (a : ℕ→ JointAction 2)
    (hv : ∀ k, v k∈Ioc (0:ℝ) (Uniform07.cutoff row))
    (haroute : ∀ k, (a k).routeCount=1) (hav : ∀ k, (a k).bid≤ v k)
    (haU : ∀ k, (a k).bid≤ Early.bidCap row)
    {v0 : ℝ} (hv0 : Uniform07.entry row< v0) (hvalue : Tendsto v atTop (𝓝 v0)) :
    ∀ᶠ k in atTop, ∃ z∈Icc (0:ℝ) (Early.bidCap row),
      (problem (Γ (market k)) (i k)).payoff (v k) (a k)<
        (problem (Γ (market k)) (i k)).payoff (v k) (two z) := by
  let vmin : ℝ := (Uniform07.entry row+v0)/2
  let gap : ℝ := (1-sourceSingletonFraction row)*(vmin-Uniform07.entry row)^2/Uniform07.cutoff row
  have hvmin : Uniform07.entry row< vmin := by dsimp [vmin]; linarith
  have hgap : 0< gap := by
    dsimp [gap]
    exact div_pos (mul_pos (sub_pos.mpr (source_fraction_mem row).2)
      (sq_pos_of_pos (sub_pos.mpr hvmin))) (Uniform07.cutoff_pos row)
  have herror : Tendsto (fun k => 4*Uniform07.cutoff row*D.error (market k)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using
      (D.errorSmall.comp hmarket).const_mul (4*Uniform07.cutoff row)
  have hsmall := herror.eventually (Iio_mem_nhds hgap)
  have hvalueGood := hvalue.eventually (Ioi_mem_nhds (show vmin< v0 by dsimp [vmin]; linarith))
  filter_upwards [hsmall,hvalueGood,hmarket.eventually D.kernels,
    hmarket.eventually D.floorAboveCap,hmarket.eventually D.errorNonnegative]
      with k he hvk hk hR he0
  obtain ⟨E⟩ := hk (i k)
  have hg := actual_active_singleton_uniform_gap E he0 hR (hSchedule (market k)) (hFee (market k))
    hvmin ⟨hvk.le,(hv k).2⟩ (a k) (haroute k) ((haU k).trans_lt hR) (hav k)
  have hs := source_active_bid_spec row (hvmin.trans hvk) (hv k).2
  exact ⟨sourceActiveBid row (v k),
    ⟨(source_entry_positive row).le.trans hs.1.le,hs.2.2.1.le⟩,
    sub_pos.mp ((sub_pos.mpr he).trans_le hg)⟩

theorem ProductFamily05.eventually_every_omitted_singleton_loses
    {row : Uniform07.Row} {upper : ℕ→ℝ} (D : ProductFamily05 Γ row upper)
    (H : LowFamily06 Γ row)
    (hSchedule : ∀ m, (Γ m).A=Schedule.affine 2 (Uniform07.eta row)
      (source_eta_mem row).1 (source_eta_mem row).2)
    (hFee : ∀ m, (Γ m).g=0) :
    ∀ᶠ m in atTop, ∀ i : Fin (population m), ∀ v∈Ioc (0:ℝ) (Uniform07.cutoff row),
      ∀ a : JointAction 2, a.routeCount=1 → a.bid∈Ioo (Early.bidCap row) (upper m) →
      ∃ z∈Icc (0:ℝ) (Early.bidCap row),
        (problem (Γ m) i).payoff v a<(problem (Γ m) i).payoff v (two z) := by
  let gap : ℝ := (1-sourceSingletonFraction row)*
    (Early.bidCap row-Uniform07.entry row)^2/Uniform07.cutoff row
  have hgap : 0< gap := by
    dsimp [gap]
    exact div_pos (mul_pos (sub_pos.mpr (source_fraction_mem row).2)
      (sq_pos_of_pos (sub_pos.mpr (source_entry_lt_cap row)))) (Uniform07.cutoff_pos row)
  have herror : Tendsto (fun m => 4*Uniform07.cutoff row*D.error m) atTop (𝓝 0) := by
    simpa only [mul_zero] using D.errorSmall.const_mul (4*Uniform07.cutoff row)
  have hsmall := herror.eventually (Iio_mem_nhds hgap)
  filter_upwards [D.kernels,D.floorAboveCap,D.errorNonnegative,H.small_duplicate,H.halfValue,hsmall]
    with m hm hR he hdup hhalf hsmallm
  intro i v hv a ha hab
  obtain ⟨E⟩ := hm i
  have hh := source_half_value_cap row hv.2
  have hD := hdup.2 i (v/2) ⟨div_nonneg hv.1.le (by norm_num),hh.2⟩
  exact every_omitted_lower_singleton_loses E he hR (hSchedule m) (hFee m) hv hdup.1 hh.1
    (hhalf i v hv) (hD.trans (by linarith [hdup.1])) hsmallm a ha hab

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
