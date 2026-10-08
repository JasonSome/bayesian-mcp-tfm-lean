import FCAppendix.PayOnce.InactiveKernelTailData
import FCAppendix.Probability.LocalTiltControl

set_option maxHeartbeats 800000

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws ExponentialTilt
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_kernel_tail_tilt
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))
    (E : ℝ) (hE : 0 < E) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    ∃ η K a c₁ c₂ v₁ v₂ c : ℝ,
      0 < η ∧ η ≤ 1 ∧ 0 < K ∧ 0 < a ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < v₁ ∧ 0 < v₂ ∧ 0 < c ∧
      ∀ᶠ t in atTop, 2 ≤ M t ∧ ∀ b : ℝ,
        bar t-η ≤ b → b ≤ bar t → K/((M t-1:ℕ):ℝ) ≤ bar t-b →
        ∀ s ∈ Icc (0:ℝ) η,
          let μ := (BidScaling.realBidLaw (Γ t) : Measure ℝ)
          let X := fun B => kernel (k+1) B (b*H (k+1) s)
          0 < b*H (k+1) s ∧
          c*s ≤ ∫ B, X B-kernel (k+1) B b ∂μ ∧
          ∃ u : ℝ, u ∈ Ioo (-a) 0 ∧
            (∫ B, X B ∂μ.tilted (fun B => u*X B))=((C t:ℝ)-s)/((M t-1:ℕ):ℝ) ∧
            c₁*((bar t-b)+s) ≤ |u| ∧ |u| ≤ c₂*((bar t-b)+s) ∧
            v₁ ≤ variance X (μ.tilted (fun B => u*X B)) ∧
            variance X (μ.tilted (fun B => u*X B)) ≤ v₂ ∧
            0 < sqrt (((M t-1:ℕ):ℝ)*variance X (μ.tilted (fun B => u*X B))) ∧
            (E/sqrt (((M t-1:ℕ):ℝ)*variance X (μ.tilted (fun B => u*X B))))*
              (1+|u| *sqrt (((M t-1:ℕ):ℝ)*variance X (μ.tilted (fun B => u*X B)))) ≤
                GaussianTilt.lowerConstant/4 := by
  dsimp only
  have hk := h.proposers_two
  have hn : 2 ≤ k+1 := by omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  obtain ⟨blo,bhi,ε,α,β,v,c,hblo,hlo,hhi,hε,hε1,hα,hβ,hv,hc,hdata⟩ :=
    payOnce_inactive_kernel_tail_data Γ B F g ρ h hlocal
  obtain ⟨a,δ,ha,hδ,N₀,htilt⟩ := exists_uniform_local_tilt_control E v hE hv
  let η := min ε (min (δ/(8*β)) ((L-blo)/2))
  let K := 2/α
  have hη : 0 < η := lt_min hε (lt_min (by positivity) (by dsimp [L] at *; linarith))
  have hηε : η ≤ ε := min_le_left _ _
  have hηδ : η ≤ δ/(8*β) := (min_le_right _ _).trans (min_le_left _ _)
  have hηL : η ≤ (L-blo)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hK : 0 < K := by dsimp [K]; positivity
  have hlo' : (blo+L)/2 < L := by linarith
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hNg : Tendsto (fun t => M t-1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp h.population_grows
  have hNr : Tendsto (fun t => ((M t-1:ℕ):ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hNg
  refine ⟨η,K,a,exp (-2*a)*(α/2),(exp (2*a)/v)*(β+α/2),exp (-2*a)*v,exp (2*a),c,
    hη,hηε.trans hε1,hK,ha,by positivity,by positivity,by positivity,exp_pos _,hc,?_⟩
  filter_upwards [hdata,hbar.eventually (Ioo_mem_nhds hlo' hhi),
    hNg.eventually_ge_atTop N₀,hNr.eventually_gt_atTop (4/δ)] with t ht hbt hN₀ hNrδ
  refine ⟨ht.1,?_⟩
  intro b hb hbT hd s hs
  have hN : 0 < ((M t-1:ℕ):ℝ) := Nat.cast_pos.mpr (by omega)
  have hbmem : b ∈ Icc blo bhi := ⟨by linarith [hbt.1],hbT.trans ht.2.1.2.le⟩
  have hsε : s ∈ Icc (0:ℝ) ε := ⟨hs.1,hs.2.trans hηε⟩
  have hx := ht.2.2 b hbmem hbT s hsε
  have hdinv : 1/((M t-1:ℕ):ℝ) ≤ (α/2)*(bar t-b) := by
    have hh := (div_le_iff₀ hN).mp hd
    change 2/α ≤ _ at hh
    have hh' := (div_le_iff₀ hα).mp hh
    apply (div_le_iff₀ hN).mpr
    nlinarith
  have hdp : 0 < bar t-b := (div_pos hK hN).trans_le hd
  have hsum : 0 < (bar t-b)+s := add_pos_of_pos_of_nonneg hdp hs.1
  let gap := (∫ B, kernel (k+1) B (b*H (k+1) s)
    ∂(BidScaling.realBidLaw (Γ t) : Measure ℝ))-((C t:ℝ)-s)/((M t-1:ℕ):ℝ)
  have hgaplo : (α/2)*((bar t-b)+s) ≤ gap := by
    dsimp [gap]
    nlinarith [hx.2.2.2.1,mul_nonneg hα.le hs.1]
  have hgaphi : gap ≤ (β+α/2)*((bar t-b)+s) := by
    dsimp [gap]
    nlinarith [hx.2.2.2.2,mul_nonneg hα.le hs.1]
  have hinv : 1/((M t-1:ℕ):ℝ) < δ/4 := by
    have hh := (div_lt_iff₀ hδ).mp hNrδ
    apply (div_lt_iff₀ hN).mpr
    nlinarith
  have hηmul : β*η ≤ δ/8 := by
    have hh := (le_div_iff₀ (show 0 < 8*β by positivity)).mp hηδ
    nlinarith
  have hgapδ : gap < δ := by
    have hdη : bar t-b ≤ η := by change bar t-η ≤ b at hb; linarith
    have htemp := mul_le_mul_of_nonneg_left (add_le_add hdη hs.2) hβ.le
    dsimp [gap]
    nlinarith [hx.2.2.2.2]
  obtain ⟨u,hu,hm,hul,huh,hvl,hvh,hroot,hsmall⟩ := htilt
    (BidScaling.realBidLaw (Γ t) : Measure ℝ)
    (fun B => kernel (k+1) B (b*H (k+1) s)) (((C t:ℝ)-s)/((M t-1:ℕ):ℝ)) (M t-1)
    (KernelTailEvent.continuous_kernel_bid hn hx.1).measurable
    (.of_forall fun B => KernelTailEvent.kernel_bounds hn hx.1 B) hx.2.1
    ((mul_pos (by positivity) hsum).trans_le hgaplo) hgapδ hN₀
  refine ⟨hx.1,hx.2.2.1,u,hu,hm,?_,?_,hvl,hvh,hroot,hsmall⟩
  · calc
      exp (-2*a)*(α/2)*((bar t-b)+s) ≤ exp (-2*a)*gap := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hgaplo (exp_pos (-2*a)).le
      _ ≤ |u| := hul
  · exact huh.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hgaphi (div_pos (exp_pos (2*a)) hv).le)

end FCAppendix.Bayes
