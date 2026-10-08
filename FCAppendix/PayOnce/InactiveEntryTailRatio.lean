import FCAppendix.PayOnce.InactiveKernelTailTilt
import FCAppendix.PayOnce.DummyEntryTail
import FCAppendix.Probability.LocalTiltTailRatio

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel ExponentialTilt
open PayOnce.GaussianTilt
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_entry_tail_ratio
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∃ η K A κ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧ 0 < A ∧ 0 < κ ∧
      ∀ᶠ t in atTop, 2 ≤ M t ∧ ∀ b : ℝ,
        bar t-η ≤ b → b ≤ bar t → K/((M t-1:ℕ):ℝ) ≤ bar t-b →
        let P := Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))
        let F₀ := P.real {z | 0 < allocation (k+1) (C t) hn z b}
        0 < F₀ ∧ ∀ s : ℝ, 0 < s → s ≤ η →
          P.real {z | s ≤ allocation (k+1) (C t) hn z b}/F₀ ≤
            A*exp (-κ*((M t-1:ℕ):ℝ)*(bar t-b)*s) := by
  dsimp only
  have hk := h.proposers_two
  have hn : 2 ≤ k+1 := by omega
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  obtain ⟨E,hE,hratio⟩ := exists_bounded_iid_tilt_tail_ratio.{0}
  obtain ⟨η,K,a,c₁,c₂,v₁,v₂,c,hη,hη1,hK,_,hc₁,hc₂,hv₁,hv₂,hc,htilt⟩ :=
    payOnce_inactive_kernel_tail_tilt Γ B F g ρ h hlocal E hE
  let A := (3*upperConstant/lowerConstant)*max 1 ((c₂*sqrt v₂)/(c₁*sqrt v₁))
  let κ := exp (-a)*c₁*c
  have hA : 0 < A := mul_pos
    (div_pos (mul_pos (by norm_num) upperConstant_pos) lowerConstant_pos)
    ((show (0:ℝ) < 1 by norm_num).trans_le (le_max_left _ _))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨η,K,A,κ,hη,hη1,hK,hA,hκ,?_⟩
  filter_upwards [htilt] with t ht
  refine ⟨ht.1,?_⟩
  intro b hb hbT hd
  let N := M t-1
  let μ := (BidScaling.realBidLaw (Γ t) : Measure ℝ)
  let P := Measure.pi (fun _ : Fin N => μ)
  let X := fun z : ℝ => kernel (k+1) z b
  have hN : 0 < N := by dsimp [N]; omega
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hdp : 0 < bar t-b := (div_pos hK hNR).trans_le hd
  have ht₀ := ht.2 b hb hbT hd 0 ⟨le_rfl,hη.le⟩
  dsimp only at ht₀
  simp only [H_zero (k+1) (by omega),mul_one,sub_zero,add_zero] at ht₀
  obtain ⟨hbp,_,u,hu,hmr,hul,huh,_,hvh,hsX,hsmallX⟩ := ht₀
  have hraw (s : ℝ) (hs : s ∈ Icc (0:ℝ) η) :
      0 < P.real {z | iidSum X N z < (C t:ℝ)} ∧
      P.real {z | iidSum (fun z => kernel (k+1) z (b*H (k+1) s)) N z ≤ (C t:ℝ)-s}/
        P.real {z | iidSum X N z < (C t:ℝ)} ≤ A*exp (-κ*(N:ℝ)*(bar t-b)*s) := by
    have hts := ht.2 b hb hbT hd s hs
    dsimp only at hts
    obtain ⟨hsp,hinc,w,hw,hmq,hwl,_,hvs,_,hsY,hsmallY⟩ := hts
    let Y := fun z : ℝ => kernel (k+1) z (b*H (k+1) s)
    have hX : Measurable X := (KernelTailEvent.continuous_kernel_bid hn hbp).measurable
    have hY : Measurable Y := (KernelTailEvent.continuous_kernel_bid hn hsp).measurable
    have hbX : ∀ᵐ z ∂μ, X z ∈ Icc (0:ℝ) 1 :=
      .of_forall fun z => KernelTailEvent.kernel_bounds hn hbp z
    have hbY : ∀ᵐ z ∂μ, Y z ∈ Icc (0:ℝ) 1 :=
      .of_forall fun z => KernelTailEvent.kernel_bounds hn hsp z
    have hXY : ∀ᵐ z ∂μ, X z ≤ Y z := .of_forall fun z =>
      (KernelTailMeanGrowth.tail_kernel_order_bounds hn hbp ⟨hs.1,hs.2.trans hη1⟩ z).2.2
    have hua : |u| ≤ a := by rw [abs_of_neg hu.2]; linarith [hu.1]
    have hfin := hratio μ X Y u w a ((C t:ℝ)/(N:ℝ)) (((C t:ℝ)-s)/(N:ℝ)) N
      hX hY hbX hbY hXY hu.2.le hw.2.le hua hmr hmq hsX hsY hsmallX hsmallY
    dsimp only at hfin
    have hrnorm : (N:ℝ)*((C t:ℝ)/(N:ℝ)) = (C t:ℝ) := by field_simp
    have hqnorm : (N:ℝ)*(((C t:ℝ)-s)/(N:ℝ)) = (C t:ℝ)-s := by field_simp
    rw [hrnorm,hqnorm] at hfin
    have hsXu : sqrt ((N:ℝ)*variance X (μ.tilted (fun z => u*X z))) ≤ sqrt v₂*sqrt N := by
      rw [sqrt_mul (Nat.cast_nonneg N)]
      exact (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hvh) (sqrt_nonneg _)).trans_eq (mul_comm _ _)
    have hsYl : sqrt v₁*sqrt N ≤ sqrt ((N:ℝ)*variance Y (μ.tilted (fun z => w*Y z))) := by
      rw [sqrt_mul (Nat.cast_nonneg N),mul_comm (sqrt v₁)]
      exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt hvs) (sqrt_nonneg _)
    have hrq : 0 ≤ (C t:ℝ)/(N:ℝ)-((C t:ℝ)-s)/(N:ℝ) := by
      rw [← sub_div]
      exact div_nonneg (by linarith [hs.1]) hNR.le
    have hh := tail_ratio_le_local_exponential hdp hs.1 hc₁ hc₂ hc₁ hc
      (sqrt_pos.mpr hv₂) (sqrt_pos.mpr hv₁) hsX.le hul huh hwl hsXu hsYl hinc hrq hfin.2
    refine ⟨hfin.1,hh.trans_eq ?_⟩
    dsimp [A,κ]
    congr 1
    congr 1
    ring
  have he : P.real {z | 0 < allocation (k+1) (C t) hn z b} =
      P.real {z | iidSum X N z < (C t:ℝ)} := allocation_entry_probability_eq μ hn hbp
  refine ⟨by rw [he]; exact (hraw 0 ⟨le_rfl,hη.le⟩).1,?_⟩
  intro s hs hsη
  rw [show (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
      {z | s ≤ allocation (k+1) (C t) hn z b} =
      P.real {z | iidSum (fun z => kernel (k+1) z (b*H (k+1) s)) N z ≤ (C t:ℝ)-s} from
        allocation_tail_probability_eq_iidSum μ hn hbp hs (hsη.trans hη1),he]
  exact (hraw s ⟨hs.le,hsη⟩).2

end FCAppendix.Bayes
