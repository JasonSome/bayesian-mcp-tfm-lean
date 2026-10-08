import FCAppendix.PayOnce.NearEntryFOCResponse
import FCAppendix.PayOnce.KernelLawConvergence
import FCAppendix.PayOnce.BidFormula

namespace FCAppendix.PayOnce.InteriorFOCResponse
open Set Real CommonList OwnImpact RareSuccessSlope ResponseFactor Filter Topology
open NearEntryFOCResponse KernelTailEvent

theorem root_difference_le_of_lower {k : ℕ} (hk : 0 < k) {x y q : ℝ}
    (hq : 0 < q) (hx : q ≤ x) (hy : 0 ≤ y) :
    |x-y| ≤ |x^k-y^k|/q^(k-1) := by
  apply (le_div_iff₀ (pow_pos hq _)).mpr
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq.le hx _) (abs_nonneg _)).trans
    (mul_pow_sub_le_abs_pow_sub hk (hq.le.trans hx) hy)

theorem response_error_of_residual {n : ℕ} (hn : 2 ≤ n) {L b w p q e : ℝ}
    (hL : 0 < L) (hLw : L ≤ w) (hq : 0 < q) (hp : p ∈ Icc (0:ℝ) (1-q))
    (hreceipt : b*H n p = L)
    (herr : |b*success n p-(w-b)*phi n p| ≤ e) :
    |p-Limit.pStar n L w| ≤ ((n:ℝ)/q^(n-2))*e/L := by
  let z := (L/w)^(1/((n:ℝ)-1))
  have hw : 0 < w := hL.trans_le hLw
  have hpunit : p ∈ Icc (0:ℝ) 1 := ⟨hp.1,by linarith [hp.2]⟩
  have hz : 0 ≤ z := rpow_nonneg (div_nonneg hL.le hw.le) _
  have hzpow : z^(n-1)=L/w := by
    dsimp only [z]
    have hexp : 1/((n:ℝ)-1)=(((n-1:ℕ):ℝ))⁻¹ := by
      rw [Nat.cast_sub (by omega),Nat.cast_one,one_div]
    rw [hexp,rpow_inv_natCast_pow (div_nonneg hL.le hw.le) (by omega)]
  have hres : J n p*|L-w*(1-p)^(n-1)| ≤ e := by
    rw [residual_identity hn hpunit hreceipt,abs_mul,abs_of_pos (J_pos hn hpunit)] at herr
    exact herr
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hJ := (J_bounds hn hpunit).1
  have hraw : |L-w*(1-p)^(n-1)| ≤ (n:ℝ)*e := by
    have hh := (mul_le_mul_of_nonneg_right hJ (abs_nonneg _)).trans hres
    have hh' := mul_le_mul_of_nonneg_left hh hnR.le
    field_simp at hh'
    exact hh'
  have hroot := root_difference_le_of_lower (k := n-1) (by omega)
    (x := 1-p) (y := z) hq (by linarith [hp.2]) hz
  have hnorm : w*|(1-p)^(n-1)-z^(n-1)| = |L-w*(1-p)^(n-1)| := by
    rw [hzpow]
    calc
      _ = |w*((1-p)^(n-1)-L/w)| := by rw [abs_mul,abs_of_pos hw]
      _ = _ := by rw [mul_sub,mul_div_cancel₀ L hw.ne',abs_sub_comm]
  have hbound : L*|(1-p)-z| ≤ ((n:ℝ)/q^(n-2))*e := by
    calc
      _ ≤ w*|(1-p)-z| := mul_le_mul_of_nonneg_right hLw (abs_nonneg _)
      _ ≤ w*(|(1-p)^(n-1)-z^(n-1)|/q^((n-1)-1)) := mul_le_mul_of_nonneg_left hroot hw.le
      _ = |L-w*(1-p)^(n-1)|/q^(n-2) := by rw [show (n-1)-1=n-2 by omega,← hnorm]; ring
      _ ≤ ((n:ℝ)*e)/q^(n-2) := div_le_div_of_nonneg_right hraw (pow_pos hq _).le
      _ = _ := by ring
  rw [pStar_of_le hn hL hLw]
  apply (le_div_iff₀ hL).mpr
  have habs : |p-(1-z)| = |(1-p)-z| := by
    rw [show p-(1-z)=-((1-p)-z) by ring,abs_neg]
  change |p-(1-z)| *L ≤ _
  rw [habs,mul_comm]
  exact hbound

theorem response_scaled_tendsto {n : ℕ} (hn : 2 ≤ n) {L w : ℝ}
    (hL : 0 < L) (hLw : L < w) (ell b Q R s : ℕ → ℝ)
    (hell : Tendsto ell atTop (𝓝 L)) (hb : Tendsto b atTop (𝓝 (Limit.bidStar n L w)))
    (hFOC : ∀ᶠ t in atTop, b t*Q t=(w-b t)*R t)
    (hQ : Tendsto (fun t => s t*(Q t-success n (kernel n (b t) (ell t)))) atTop (𝓝 0))
    (hR : Tendsto (fun t => s t*(R t-phi n (kernel n (b t) (ell t)))) atTop (𝓝 0)) :
    Tendsto (fun t => s t*(kernel n (b t) (ell t)-Limit.pStar n (ell t) w)) atTop (𝓝 0) := by
  let p := fun t => kernel n (b t) (ell t)
  let p₀ := Limit.pStar n L w
  have hp₀ : p₀ ∈ Ioo (0:ℝ) 1 :=
    ⟨(Limit.pStar_pos_iff hn hL.le).mpr hLw,Limit.pStar_lt_one hn hL hLw⟩
  have hp : Tendsto p atTop (𝓝 p₀) := by
    have hh := (KernelLawConvergence.tendstoUniformly_kernel hn hL hell).tendsto_comp
      (continuous_kernel_bid hn hL).continuousAt hb
    simpa only [Limit.kernel_bidStar hn hL] using hh
  let q := (1-p₀)/2
  have hq : 0 < q := by dsimp only [q]; linarith [hp₀.2]
  have hpq : p₀ < 1-q := by dsimp only [q]; linarith [hp₀.2]
  let E := fun t => b t*success n (p t)-(w-b t)*phi n (p t)
  have hsum : Tendsto (fun t => -b t*(s t*(Q t-success n (p t)))+
      (w-b t)*(s t*(R t-phi n (p t)))) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (hb.neg.mul hQ).add ((tendsto_const_nhds.sub hb).mul hR)
  have hres : Tendsto (fun t => s t*E t) atTop (𝓝 0) := by
    apply hsum.congr'
    filter_upwards [hFOC] with t ht
    dsimp only [E]
    linear_combination -(s t)*ht
  have hcoef : Tendsto (fun t => ((n:ℝ)/q^(n-2))/(ell t)) atTop (𝓝 (((n:ℝ)/q^(n-2))/L)) :=
    tendsto_const_nhds.div hell hL.ne'
  have hboundlim : Tendsto (fun t => (((n:ℝ)/q^(n-2))/(ell t))*|s t*E t|) atTop (𝓝 0) := by
    simpa only [abs_zero,mul_zero] using hcoef.mul hres.abs
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) ?_ hboundlim
  filter_upwards [hell.eventually_const_lt hL,hell.eventually_lt_const hLw,
    hp.eventually_const_lt hp₀.1,hp.eventually_lt_const hpq] with t hLt hwLt hpt hqt
  have hLb : ell t ≤ b t := by
    by_contra hh
    have hbL : b t ≤ ell t := (lt_of_not_ge hh).le
    have hz := kernel_of_le n hbL
    change 0 < kernel n (b t) (ell t) at hpt
    rw [hz] at hpt
    exact hpt.false
  have hpunit : p t ∈ Icc (0:ℝ) (1-q) := ⟨hpt.le,hqt.le⟩
  have hreceipt := kernel_receipt_of_ge hn hLt hLb (show p t<1 by linarith)
  have herr := response_error_of_residual hn hLt hwLt.le hq hpunit hreceipt (le_refl |E t|)
  change |s t*(p t-Limit.pStar n (ell t) w)| ≤ _
  calc
    _ = |s t| *|p t-Limit.pStar n (ell t) w| := abs_mul _ _
    _ ≤ |s t| *(((n:ℝ)/q^(n-2))*|E t|/(ell t)) := mul_le_mul_of_nonneg_left herr (abs_nonneg _)
    _ = _ := by rw [abs_mul]; ring

theorem mean_response_scaled_tendsto {n : ℕ} (hn : 2 ≤ n) {L w : ℝ}
    (hL : 0 < L) (hLw : L < w) (ell b Q R mean s : ℕ → ℝ)
    (hell : Tendsto ell atTop (𝓝 L)) (hb : Tendsto b atTop (𝓝 (Limit.bidStar n L w)))
    (hFOC : ∀ᶠ t in atTop, b t*Q t=(w-b t)*R t)
    (hQ : Tendsto (fun t => s t*(Q t-success n (kernel n (b t) (ell t)))) atTop (𝓝 0))
    (hR : Tendsto (fun t => s t*(R t-phi n (kernel n (b t) (ell t)))) atTop (𝓝 0))
    (hmean : Tendsto (fun t => s t*(mean t-kernel n (b t) (ell t))) atTop (𝓝 0)) :
    Tendsto (fun t => s t*(mean t-Limit.pStar n (ell t) w)) atTop (𝓝 0) := by
  have hh := hmean.add (response_scaled_tendsto hn hL hLw ell b Q R s hell hb hFOC hQ hR)
  simpa only [← mul_add,sub_add_sub_cancel,zero_add] using hh

end FCAppendix.PayOnce.InteriorFOCResponse
