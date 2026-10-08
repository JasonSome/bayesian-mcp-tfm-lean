import FCAppendix.PayOnce.InactiveKernelTailWindow
import FCAppendix.PayOnce.InactiveKernelVarianceWindow
import FCAppendix.PayOnce.KernelTailMeanGap

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.KernelTailMeanGrowth
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_kernel_tail_geometry
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∃ ell blo bhi U V q v : ℝ, 0 < ell ∧ ell < blo ∧ blo < L ∧ L < bhi ∧
      bhi < U ∧ U < V ∧ V < ((k+1:ℕ):ℝ)*ell ∧ 0 < q ∧ 0 < v ∧ ∀ᶠ t in atTop,
      bar t ∈ Ioo blo bhi ∧ q ≤ (BidScaling.realBidLaw (Γ t) : Measure ℝ).real (Icc U V) ∧
      ∀ T ∈ Icc ell bhi, v ≤ variance (fun b => kernel (k+1) b T)
        (BidScaling.realBidLaw (Γ t) : Measure ℝ) := by
  dsimp only
  obtain ⟨e,lo,hi,U,V,q,he,helo,hlo,hhi,hU,hUV,hV,hq,htail⟩ :=
    payOnce_inactive_kernel_tail_block Γ B F g ρ h
  obtain ⟨e',u',v,he',_,hv,hwindow,hvariance⟩ :=
    payOnce_inactive_kernel_variance_window Γ B F g ρ h hlocal
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let ell := max e e'
  let blo := (ell+L)/2
  let bhi := (L+min hi u')/2
  have hell : 0 < ell := he.trans_le (le_max_left _ _)
  have heL : ell < L := max_lt (helo.trans hlo) hwindow.1
  have hlo' : ell < blo := by dsimp [blo]; linarith
  have hbL : blo < L := by dsimp [blo]; linarith
  have hLhi : L < min hi u' := lt_min hhi hwindow.2
  have hLbh : L < bhi := by dsimp [bhi]; linarith
  have hbh : bhi < min hi u' := by dsimp [bhi]; linarith
  have hbhi : bhi < hi := hbh.trans_le (min_le_left _ _)
  have hbhu : bhi < u' := hbh.trans_le (min_le_right _ _)
  have hnR : (0:ℝ) ≤ ((k+1:ℕ):ℝ) := Nat.cast_nonneg _
  refine ⟨ell,blo,bhi,U,V,q,v,hell,hlo',hbL,hLbh,hbhi.trans hU,hUV,
    hV.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) hnR),hq,hv,?_⟩
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  filter_upwards [htail,hvariance,hbar.eventually (Ioo_mem_nhds hbL hLbh)] with t ht hvt hbt
  refine ⟨hbt,ht.2,?_⟩
  intro T hT
  exact hvt T ⟨(le_max_right _ _).trans hT.1,hT.2.trans hbhu.le⟩

theorem payOnce_inactive_kernel_tail_data
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∃ blo bhi ε α β v c : ℝ, 0 < blo ∧ blo < L ∧ L < bhi ∧
      0 < ε ∧ ε ≤ 1 ∧ 0 < α ∧ 0 < β ∧ 0 < v ∧ 0 < c ∧ ∀ᶠ t in atTop,
      2 ≤ M t ∧ bar t ∈ Ioo blo bhi ∧
      ∀ b ∈ Icc blo bhi, b ≤ bar t → ∀ s ∈ Icc (0:ℝ) ε,
        0 < b*H (k+1) s ∧
        v ≤ variance (fun B => kernel (k+1) B (b*H (k+1) s))
          (BidScaling.realBidLaw (Γ t) : Measure ℝ) ∧
        c*s ≤ ∫ B, kernel (k+1) B (b*H (k+1) s)-kernel (k+1) B b
          ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ) ∧
        α*((bar t-b)+s)-1/((M t-1:ℕ):ℝ) ≤
          (∫ B, kernel (k+1) B (b*H (k+1) s) ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ))-
            ((C t:ℝ)-s)/((M t-1:ℕ):ℝ) ∧
        (∫ B, kernel (k+1) B (b*H (k+1) s) ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ))-
            ((C t:ℝ)-s)/((M t-1:ℕ):ℝ) ≤ β*((bar t-b)+s)+1/((M t-1:ℕ):ℝ) := by
  dsimp only
  have hk := h.proposers_two
  have hn : 2 ≤ k+1 := by omega
  obtain ⟨ell,blo,bhi,U,V,q,v,hell,hlo,hblo,hbhi,hU,hUV,hV,hq,hv,he⟩ :=
    payOnce_inactive_kernel_tail_geometry Γ B F g ρ h hlocal
  let ε := min 1 ((blo-ell)/(((k+1:ℕ):ℝ)*bhi))
  let α := min (q/(((k+1:ℕ):ℝ)*V)) (q*ell/(((k+1:ℕ):ℝ)^2*V))
  let β := max (((k+1:ℕ):ℝ)/ell) (((k+1:ℕ):ℝ)^2*bhi/ell)
  let c := q*ell/(((k+1:ℕ):ℝ)^2*V)
  have hbb := hblo.le.trans hbhi.le
  have hcompact := KernelTailMeanGap.tail_mean_gap_bounds_on_compact hn
    hell hlo hbb hU hUV.le hV hq
  have hVp : 0 < V := (hell.trans hlo).trans_le (hbb.trans (hU.le.trans hUV.le))
  refine ⟨blo,bhi,ε,α,β,v,c,hell.trans hlo,hblo,hbhi,hcompact.1,hcompact.2.1,
    hcompact.2.2.1,hcompact.2.2.2.1,hv,by dsimp [c]; positivity,?_⟩
  filter_upwards [he,payOnce_inactive_population_kernel_mean Γ B F g ρ h,
    h.population_grows.eventually_ge_atTop 2,h.eventually_scarce] with t ht hmean hM hC
  refine ⟨hM,ht.1,?_⟩
  intro b hb hbT s hs
  have hp := receipt_price_mem_of_small_tail hn hell hlo hb hs
  have hg := (tail_mean_growth_on_compact (BidScaling.realBidLaw (Γ t) : Measure ℝ)
    hn hell hlo hbb hU hUV.le hV hq ht.2.1).2.2 b hb s hs
  have hMt : M t-1+1=M t := by omega
  have hMr : ((M t-1:ℕ):ℝ)+1=(M t:ℝ) := by exact_mod_cast hMt
  have hm : (∫ B, kernel (k+1) B (KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))
      ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ))=(C t:ℝ)/(((M t-1:ℕ):ℝ)+1) := by
    simpa only [hMr] using hmean
  have hbds := hcompact.2.2.2.2 (BidScaling.realBidLaw (Γ t) : Measure ℝ) (M t-1) (C t)
    (by omega) (by omega) ht.2.1 b hb _ ⟨ht.1.1.le,ht.1.2.le⟩ hbT s hs hm
  exact ⟨hell.trans_le hp.1,ht.2.2 _ hp,hg.2.2,hbds⟩

end FCAppendix.Bayes
