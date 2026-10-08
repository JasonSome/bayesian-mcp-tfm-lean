import FCAppendix.Proposer.CommonListGame
import Mathlib.MeasureTheory.Measure.Support

namespace FCAppendix.PayOnce.KernelTailEvent
open Finset Set Filter Topology MeasureTheory
open FCAppendix.CommonList

theorem kernel_antitone_price {n : ℕ} (hn : 2 ≤ n) {b L T : ℝ}
    (hL : 0 < L) (hT : 0 < T) (hLT : L ≤ T) : kernel n b T ≤ kernel n b L := by
  by_cases hb : 0 < b
  · have hp := scalarThreshold_kernel n hn hb hL
    have hq := scalarThreshold_kernel n hn hb hT
    by_contra h
    have hpq : kernel n b L < kernel n b T := lt_of_not_ge h
    have hlo := scalar_receipt_le_of_lt_one n b L _ hp (hpq.trans_le hq.2.1)
    have hhi := scalar_price_le_of_pos n b T _ hq (hp.1.trans_lt hpq)
    have hH := H_strict n hn _ _ hpq hq.2.1
    have hh := mul_lt_mul_of_pos_left hH hb
    linarith
  · have hb' : b ≤ 0 := le_of_not_gt hb
    rw [kernel_of_le n (hb'.trans hL.le), kernel_of_le n (hb'.trans hT.le)]

theorem le_kernel_iff {n : ℕ} (hn : 2 ≤ n) {b L s : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hs : 0 < s) (hs1 : s ≤ 1) :
    s ≤ kernel n b L ↔ L ≤ b * H n s := by
  have hp := scalarThreshold_kernel n hn hb hL
  constructor
  · intro hsp
    have hlo := scalar_price_le_of_pos n b L _ hp (hs.trans_le hsp)
    have hH : H n (kernel n b L) ≤ H n s := by
      rcases hsp.eq_or_lt with h | h
      · rw [h]
      · exact (H_strict n hn _ _ h hp.2.1).le
    exact hlo.trans (mul_le_mul_of_nonneg_left hH hb.le)
  · intro hLscore
    by_contra h
    have hps := lt_of_not_ge h
    have hhi := scalar_receipt_le_of_lt_one n b L _ hp (hps.trans_le hs1)
    have hH := H_strict n hn _ _ hps hs1
    have hh := mul_lt_mul_of_pos_left hH hb
    linarith

theorem kernel_at_score {n : ℕ} (hn : 2 ≤ n) {b s : ℝ}
    (hb : 0 < b) (hs : 0 ≤ s) (hs1 : s ≤ 1) : kernel n b (b * H n s) = s := by
  have hH := H_pos n (by omega) s hs hs1
  apply (eq_kernel_of_scalarThreshold n hn hb (mul_pos hb hH) ?_).symm
  exact ⟨hs, hs1, fun _ => le_rfl, fun _ => le_rfl, fun _ _ => rfl⟩

theorem focal_tail_iff_rival_sum {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) {b L s c : ℝ} (rival : ι → ℝ)
    (hb : 0 < b) (hL : 0 < L) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcap : kernel n b L + ∑ j, kernel n (rival j) L = c) :
    s ≤ kernel n b L ↔ ∑ j, kernel n (rival j) (b * H n s) ≤ c - s := by
  have hscore : 0 < b * H n s := mul_pos hb (H_pos n (by omega) s hs.le hs1)
  constructor
  · intro hsp
    have hprice := (le_kernel_iff hn hb hL hs hs1).mp hsp
    have hsum : (∑ j, kernel n (rival j) (b * H n s)) ≤ ∑ j, kernel n (rival j) L :=
      sum_le_sum fun j _ => kernel_antitone_price hn hL hscore hprice
    linarith
  · intro hsum
    by_contra h
    have hps := lt_of_not_ge h
    have hprice : b * H n s < L :=
      lt_of_not_ge (fun hle => hps.not_ge ((le_kernel_iff hn hb hL hs hs1).mpr hle))
    have hsum' : (∑ j, kernel n (rival j) L) ≤ ∑ j, kernel n (rival j) (b * H n s) :=
      sum_le_sum fun j _ => kernel_antitone_price hn hscore hL hprice.le
    linarith

theorem focal_tail_event {Ω ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) {b s c : ℝ} (rival : Ω → ι → ℝ) (price : Ω → ℝ)
    (hb : 0 < b) (hprice : ∀ ω, 0 < price ω) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcap : ∀ ω, kernel n b (price ω) + ∑ j, kernel n (rival ω j) (price ω) = c) :
    {ω | s ≤ kernel n b (price ω)} =
      {ω | ∑ j, kernel n (rival ω j) (b * H n s) ≤ c - s} := by
  ext ω
  exact focal_tail_iff_rival_sum hn (rival ω) hb (hprice ω) hs hs1 (hcap ω)

theorem kernel_eq_scalarDemand_ratio {n : ℕ} (hn : 2 ≤ n) {b L : ℝ}
    (hb : 0 < b) (hL : 0 < L) :
    kernel n b L = scalarDemand n hn 1 (by norm_num) (L / b) := by
  have hp := scalarDemand_spec n hn 1 (by norm_num) (L / b)
  apply (eq_kernel_of_scalarThreshold n hn hb hL ?_).symm
  refine ⟨hp.1, hp.2.1, ?_, ?_, ?_⟩
  · intro hzero
    have hh := hp.2.2.1 hzero
    rw [one_mul, le_div_iff₀ hb] at hh
    simpa only [mul_comm] using hh
  · intro hone
    have hh := hp.2.2.2.1 hone
    rw [one_mul, div_le_iff₀ hb] at hh
    simpa only [mul_comm] using hh
  · intro hlo hhi
    have hh := hp.2.2.2.2 hlo hhi
    rw [one_mul, eq_div_iff hb.ne'] at hh
    simpa only [mul_comm] using hh

theorem continuousAt_kernel_bid {n : ℕ} (hn : 2 ≤ n) {b L : ℝ}
    (hb : 0 < b) (hL : 0 < L) : ContinuousAt (fun x => kernel n x L) b := by
  have he : ∀ᶠ x in 𝓝 b,
      scalarDemand n hn 1 (by norm_num) (L / x) = kernel n x L := by
    filter_upwards [eventually_gt_nhds hb] with x hx
    exact (kernel_eq_scalarDemand_ratio hn hx hL).symm
  have ht : Tendsto (fun x => scalarDemand n hn 1 (by norm_num) (L / x)) (𝓝 b)
      (𝓝 (kernel n b L)) := by
    rw [kernel_eq_scalarDemand_ratio hn hb hL]
    exact (scalarDemand_continuous n hn 1 (by norm_num)).continuousAt.comp
      (continuousAt_const.div continuousAt_id hb.ne')
  exact ht.congr' he

theorem continuous_kernel_bid {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) :
    Continuous (fun b => kernel n b L) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  by_cases hb : 0 < b
  · exact continuousAt_kernel_bid hn hb hL
  · have hbL : b < L := (le_of_not_gt hb).trans_lt hL
    have he : ∀ᶠ x in 𝓝 b, (0 : ℝ) = kernel n x L := by
      filter_upwards [eventually_lt_nhds hbL] with x hx
      exact (kernel_of_le n hx.le).symm
    change Tendsto (fun x => kernel n x L) (𝓝 b) (𝓝 (kernel n b L))
    rw [kernel_of_le n hbL.le]
    exact tendsto_const_nhds.congr' he

theorem kernel_bounds {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) (b : ℝ) :
    kernel n b L ∈ Icc (0 : ℝ) 1 := by
  by_cases hb : 0 < b
  · exact ⟨kernel_nonneg n hn hb hL, kernel_le_one n hn hb hL⟩
  · rw [kernel_of_le n ((le_of_not_gt hb).trans hL.le)]
    norm_num

theorem transformed_kernel_mono {n : ℕ} (hn : 2 ≤ n) {x δ ε b : ℝ}
    (hx : 0 < x) (hδ : 0 ≤ δ) (hδε : δ ≤ ε) (hε : ε ≤ 1) :
    kernel n b (x * H n δ) ≤ kernel n b (x * H n ε) := by
  have hδ1 := hδε.trans hε
  have hε0 := hδ.trans hδε
  have hH : H n ε ≤ H n δ := by
    rcases hδε.eq_or_lt with h | h
    · rw [h]
    · exact (H_strict n hn _ _ h hε).le
  apply kernel_antitone_price hn
    (mul_pos hx (H_pos n (by omega) ε hε0 hε))
    (mul_pos hx (H_pos n (by omega) δ hδ hδ1))
    (mul_le_mul_of_nonneg_left hH hx.le)

theorem transformed_kernel_strict_mass {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ℝ) {x δ ε : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ)
    (hδε : δ < ε) (hε : ε ≤ 1) (hsupport : x ∈ G.support) :
    0 < G {b | kernel n b (x * H n δ) < kernel n b (x * H n ε)} := by
  have hδ1 := hδε.le.trans hε
  have hε0 := hδ.trans hδε.le
  have hcd := continuousAt_kernel_bid hn hx (mul_pos hx (H_pos n (by omega) δ hδ hδ1))
  have hce := continuousAt_kernel_bid hn hx (mul_pos hx (H_pos n (by omega) ε hε0 hε))
  have he : kernel n x (x * H n δ) < kernel n x (x * H n ε) := by
    rw [kernel_at_score hn hx hδ hδ1, kernel_at_score hn hx hε0 hε]
    exact hδε
  have hnear := (hcd.sub hce).eventually_lt_const (show
    kernel n x (x * H n δ) - kernel n x (x * H n ε) < 0 from sub_neg.mpr he)
  apply (Measure.mem_support_iff_forall x).mp hsupport
  exact hnear.mono fun _ hh => sub_neg.mp hh

end FCAppendix.PayOnce.KernelTailEvent
