import FCAppendix.PayOnce.FocalDerivativeLimit
import FCAppendix.PayOnce.AnalyticalRareSuccess
import FCAppendix.PayOnce.LimitFormulas

namespace FCAppendix.PayOnce.OwnImpact
open Set

theorem H_sub_mul_Hslope {n : ℕ} (hn : 0 < n) (p : ℝ) :
    H n p-p*Hslope n p = (1-p)^(n-1) := by
  have he : (fun x : ℝ => (n:ℝ)*x*H n x) = success n := funext (H_mul n hn)
  have hd := ((hasDerivAt_id p).const_mul (n:ℝ)).mul (hasDerivAt_H n p)
  change HasDerivAt (fun x : ℝ => (n:ℝ)*x*H n x)
    ((n:ℝ)*1*H n p+(n:ℝ)*p*(-Hslope n p)) p at hd
  rw [he] at hd
  have hs : HasDerivAt (success n) ((n:ℝ)*(1-p)^(n-1)) p := by
    convert ((((hasDerivAt_id p).const_sub 1).pow n).const_sub 1) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hh := hd.unique hs
  have hnR : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hz : (n:ℝ)*(H n p-p*Hslope n p-(1-p)^(n-1)) = 0 := by
    nlinarith
  have hzero := (mul_eq_zero.mp hz).resolve_left hnR
  linarith

end FCAppendix.PayOnce.OwnImpact

namespace FCAppendix.PayOnce.AnalyticalKernel
open Set CommonList OwnImpact RareSuccessSlope

theorem served_equation_of_first_order {n : ℕ} (hn : 2 ≤ n)
    {L b w : ℝ} (hL : 0 < L) (hb : L < b)
    (hfirst : success n (kernel n b L) =
      (w-b)*(phi n (kernel n b L)/b)) :
    kernel n b L ∈ Ioo (0:ℝ) 1 ∧ b < (n:ℝ)*L ∧
      w*(1-kernel n b L)^(n-1) = L := by
  let p := kernel n b L
  have hbpos := hL.trans hb
  have hp : p ∈ Icc (0:ℝ) 1 := KernelTailEvent.kernel_bounds hn hL b
  have hp0 : 0 < p := by
    apply lt_of_le_of_ne hp.1
    intro he
    exact hb.not_ge ((kernel_eq_zero_iff n hn hbpos hL).mp he.symm)
  have hp1 : p < 1 := by
    apply lt_of_le_of_ne hp.2
    intro he
    change success n p = (w-b)*(phi n p/b) at hfirst
    rw [he,phi_one hn] at hfirst
    simp only [success,sub_self,zero_pow (show n ≠ 0 by omega),sub_zero,zero_div,mul_zero] at hfirst
    norm_num at hfirst
  have hscore := (scalarThreshold_kernel n hn hbpos hL).2.2.2.2 hp0 hp1
  have hbn : b < (n:ℝ)*L := by
    by_contra hbad
    have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    have he : kernel n b L = 1 := (kernel_eq_one_iff n hn hbpos hL).mpr
      ((le_div_iff₀ hnR).mpr (by nlinarith [le_of_not_gt hbad]))
    exact hp1.ne he
  refine ⟨⟨hp0,hp1⟩,hbn,?_⟩
  have hsl := Hslope_pos hn ⟨hp0.le,hp1.le⟩
  have hH := H_pos n (by omega) p hp0.le hp1.le
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hpH := H_sub_mul_Hslope (show 0 < n by omega) p
  change success n p = (w-b)*(phi n p/b) at hfirst
  rw [← H_mul n (by omega) p,phi] at hfirst
  field_simp at hfirst
  change w*(1-p)^(n-1) = L
  change b*H n p = L at hscore
  nlinarith [hscore]

theorem marginal_eq_pStar_of_equation {n : ℕ} (hn : 2 ≤ n)
    {L w p : ℝ} (hL : 0 < L) (hp : p ∈ Ioo (0:ℝ) 1)
    (heq : w*(1-p)^(n-1) = L) : L < w ∧ p = Limit.pStar n L w := by
  have hq : 0 < 1-p := sub_pos.mpr hp.2
  have hpow : 0 < (1-p)^(n-1) := pow_pos hq _
  have hw : 0 < w := (mul_pos_iff_of_pos_right hpow).mp (by rw [heq]; exact hL)
  have hpw : (1-p)^(n-1) < 1 := pow_lt_one₀ hq.le (by linarith [hp.1]) (by omega)
  have hLw : L < w := by
    have hh := mul_lt_mul_of_pos_left hpw hw
    rw [heq,mul_one] at hh
    exact hh
  refine ⟨hLw,?_⟩
  have hratio : L/w = (1-p)^(n-1) := (div_eq_iff hw.ne').mpr (by nlinarith [heq])
  have hexp : 1/((n:ℝ)-1) = (((n-1:ℕ):ℝ))⁻¹ := by
    rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one,one_div]
  rw [Limit.pStar_of_lt hn hL.le hLw,hratio,hexp,Real.pow_rpow_inv_natCast hq.le (by omega)]
  ring

theorem served_formulas_of_first_order {n : ℕ} (hn : 2 ≤ n)
    {L b w : ℝ} (hL : 0 < L) (hb : L < b)
    (hfirst : success n (kernel n b L) =
      (w-b)*(phi n (kernel n b L)/b)) :
    L < w ∧ kernel n b L = Limit.pStar n L w ∧
      b = L/H n (Limit.pStar n L w) ∧ b < (n:ℝ)*L := by
  obtain ⟨hp,hbn,heq⟩ := served_equation_of_first_order hn hL hb hfirst
  obtain ⟨hw,hpStar⟩ := marginal_eq_pStar_of_equation hn hL hp heq
  refine ⟨hw,hpStar,?_,hbn⟩
  have hscore := (scalarThreshold_kernel n hn (hL.trans hb) hL).2.2.2.2 hp.1 hp.2
  have hH := H_pos n (by omega) (kernel n b L) hp.1.le hp.2.le
  rw [← hpStar]
  exact (eq_div_iff hH.ne').mpr hscore

end FCAppendix.PayOnce.AnalyticalKernel

namespace FCAppendix.PayOnce.AnalyticalRareSuccess
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList
open AnalyticalKernel KernelLawConvergence KernelTailEvent CompactifiedBidLaws RareSuccessSlope

theorem served_formulas_of_supported_IC_limit
    (N : ℕ → ℕ) (hNpos : ∀ t, 0 < N t) (hN : Tendsto N atTop atTop)
    {n : ℕ} (hn : 2 ≤ n) (G : ℕ → ProbabilityMeasure ℝ)
    (hpos : ∀ t, ∀ᵐ b ∂(G t : Measure ℝ), 0 < b)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {c : ℕ → ℕ} (hc : ∀ t, c t ≤ Fintype.card (Fin (N t))+1)
    {ρ L : ℝ} (hL : 0 < L)
    (hroot : KernelDemand.demand n (G₀ : Measure ENNReal) L = ρ)
    (hunique : ∀ T, 0 < T → KernelDemand.demand n (G₀ : Measure ENNReal) T = ρ → T = L)
    (hcapacity : Tendsto (fun t => (c t:ℝ)/N t) atTop (𝓝 ρ))
    {a z : ℝ} (ha : L < a) (haz : a < z) (hz : z < (n:ℝ)*L)
    (hwin : 0 < (G₀ : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z)))
    {T : ℕ → Set ℝ} {x w : ℕ → ℝ} {x₀ w₀ : ℝ}
    (hgood : ∀ t, x t ∈ regularSupportedSet (ι := Fin (N t)) n (c t) (G t : Measure ℝ) (T t))
    (hx₀ : L < x₀) (hxx : Tendsto x atTop (𝓝 x₀)) (hww : Tendsto w atTop (𝓝 w₀))
    (hIC : ∀ t y, y ∈ T t →
      (w t-y)*coverage n (c t) hn (hc t) (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) y ≤
      (w t-x t)*coverage n (c t) hn (hc t) (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) (x t)) :
    L < w₀ ∧ kernel n x₀ L = Limit.pStar n L w₀ ∧
      x₀ = L/H n (Limit.pStar n L w₀) ∧ x₀ < (n:ℝ)*L := by
  let P := fun t => Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))
  let Q := fun t => coverage n (c t) hn (hc t) (P t)
  have hx t : 0 < x t := (hgood t).1
  have hreg t : ∀ᵐ r ∂P t, RegularClearing n (c t) r (x t) := (hgood t).2.1
  have hd := tendsto_focal_coverage_derivative N hNpos hN hn G hpos hweak hc hL hroot hunique
    hcapacity ha haz hz hwin x hx hx₀ hxx hreg
  have hq := tendsto_focal_coverage N hNpos hN hn G hpos hweak hc hL hroot hunique hcapacity x hx hxx
  have hf t : Q t (x t) = (w t-x t)*deriv (Q t) (x t) := by
    have hderiv := hasDerivAt_coverage_of_regular hn (hc t) (P t) (hx t) (hreg t)
    exact SupportedFOC.payOnce_first_order_condition hderiv.2.differentiableAt.hasDerivAt
      (hgood t).2.2.1 (hgood t).2.2.2 (hIC t)
  have hprod := (hww.sub hxx).mul hd
  have he : success n (kernel n x₀ L) = (w₀-x₀)*(phi n (kernel n x₀ L)/x₀) :=
    tendsto_nhds_unique hq (hprod.congr fun t => (hf t).symm)
  exact served_formulas_of_first_order hn hL hx₀ he

end FCAppendix.PayOnce.AnalyticalRareSuccess
