import FCAppendix.PayOnce.InactivePopulationPrice
import FCAppendix.PayOnce.PriceConcentrationLimit
import FCAppendix.PayOnce.KernelTailMeanGrowth

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.KernelTailMeanGrowth
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_kernel_tail_block
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∃ ell blo bhi U V q : ℝ, 0 < ell ∧ ell < blo ∧ blo < L ∧ L < bhi ∧
      bhi < U ∧ U < V ∧ V < ((k+1:ℕ):ℝ)*ell ∧ 0 < q ∧ ∀ᶠ t in atTop,
      bar t ∈ Ioo blo bhi ∧ q ≤ (BidScaling.realBidLaw (Γ t) : Measure ℝ).real (Icc U V) := by
  dsimp only
  have hk := h.proposers_two
  let G := fun t => BidScaling.realBidLaw (Γ t)
  have hweak := payOnce_inactive_bidLaw_tendsto Γ B F g ρ h
  have hweakRaw : Tendsto (fun t => scaledLaw (G t) 1) atTop
      (𝓝 (inactiveLimitBidLaw F (k+1) g
        (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))) := by
    simpa only [G,BidScaling.scaled_realBidLaw_one] using hweak
  obtain ⟨hL,hroot,huniq,U,V,hU,hUV,hV,hwin⟩ :=
    payOnce_inactive_limit_root_window Γ B F g ρ h hweak
  obtain ⟨ell,u,q,dlo,dhi,hell,hellL,hLu,huU,hVell,hq,_,_,he⟩ :=
    PriceConcentration.exists_eventually_price_margins M h.population_grows (by omega) G
      (fun t => ae_realEffectiveBidLaw_nonneg (Γ t)) hweakRaw hL hroot huniq h.capacity_ratio
      hU hUV hV hwin
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let blo := (ell+L)/2
  let bhi := (L+u)/2
  have hlob : ell < blo := by dsimp [blo]; linarith
  have hblo : blo < L := by dsimp [blo]; linarith
  have hbhi : L < bhi := by dsimp [bhi]; linarith
  have hhiu : bhi < u := by dsimp [bhi]; linarith
  refine ⟨ell,blo,bhi,U,V,q,hell,hlob,hblo,hbhi,hhiu.trans huU,hUV,hVell,hq,?_⟩
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  filter_upwards [he,hbar.eventually (Ioo_mem_nhds hblo hbhi)] with t ht hbt
  refine ⟨hbt,?_⟩
  have hm : (G t : Measure ℝ).real (Ioo U V) ≤ (G t : Measure ℝ).real (Icc U V) :=
    measureReal_mono (h₂ := measure_ne_top _ _) Ioo_subset_Icc_self
  exact (show q ≤ (G t : Measure ℝ).real (Ioo U V) by linarith [ht.2.2.2]).trans hm

theorem payOnce_inactive_kernel_tail_mean_growth
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∃ ell blo bhi ε c : ℝ, 0 < ell ∧ ell < blo ∧ blo < L ∧ L < bhi ∧
      0 < ε ∧ ε ≤ 1 ∧ 0 < c ∧ ∀ᶠ t in atTop,
      bar t ∈ Ioo blo bhi ∧ ∀ b ∈ Icc blo bhi, ∀ s ∈ Icc (0:ℝ) ε,
        b*H (k+1) s ∈ Icc ell bhi ∧
        c*s ≤ ∫ v, kernel (k+1) v (b*H (k+1) s)-kernel (k+1) v b
          ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ) := by
  dsimp only
  have hk := h.proposers_two
  obtain ⟨ell,blo,bhi,U,V,q,hell,hlo,hblo,hbhi,hU,hUV,hV,hq,he⟩ :=
    payOnce_inactive_kernel_tail_block Γ B F g ρ h
  let ε := min 1 ((blo-ell)/(((k+1:ℕ):ℝ)*bhi))
  let c := q*ell/(((k+1:ℕ):ℝ)^2*V)
  have hbb : blo ≤ bhi := hblo.le.trans hbhi.le
  have hhip : 0 < bhi := (hell.trans hlo).trans_le hbb
  have hVp : 0 < V := hhip.trans (hU.trans hUV)
  have hnR : (0:ℝ) < k+1 := by positivity
  refine ⟨ell,blo,bhi,ε,c,hell,hlo,hblo,hbhi,
    lt_min (by norm_num) (by positivity),min_le_left _ _,by dsimp [c]; positivity,?_⟩
  filter_upwards [he] with t ht
  refine ⟨ht.1,?_⟩
  intro b hb s hs
  have hh := (tail_mean_growth_on_compact (BidScaling.realBidLaw (Γ t) : Measure ℝ)
    (by omega) hell hlo hbb hU hUV.le hV hq ht.2).2.2 b hb s hs
  exact ⟨hh.1,hh.2.2⟩

end FCAppendix.Bayes
