import FCAppendix.Finite.PPITailArea
import FCAppendix.Finite.PPILocalEnvelope

noncomputable section
namespace FCAppendix
open MeasureTheory Set Filter Topology

theorem integral_inverse_square_gap (a y t : ℝ) (hay : a ≤ y) (hyt : y < t) :
    (∫ v in a..y, 1 / (t - v) ^ 2) = (t - y)⁻¹ - (t - a)⁻¹ := by
  have hne (v : ℝ) (hv : v ∈ uIcc a y) : t - v ≠ 0 := by
    rw [uIcc_of_le hay] at hv
    exact (sub_pos.mpr (hv.2.trans_lt hyt)).ne'
  have hder (v : ℝ) (hv : v ∈ uIcc a y) :
      HasDerivAt (fun v => (t - v)⁻¹) (1 / (t - v) ^ 2) v := by
    simpa only [neg_neg, id_eq] using (((hasDerivAt_id v).const_sub t).fun_inv (hne v hv))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
      (fun v hv => pow_ne_zero 2 (hne v hv))).intervalIntegrable)

namespace Interim.Problem
variable {n : ℕ}

theorem envelope_tail_bound (P : Problem n) (a y t B C : ℝ)
    (hay : a ≤ y) (hyt : y < t) (hC : 0 ≤ C)
    (sel : ℝ → Game.JointAction n)
    (hsel : ∀ᵐ v, v ∈ Icc a y → P.BestResponse v (sel v))
    (hbase : P.envelope a ≤ B)
    (hupper : ∀ᵐ v, v ∈ Icc a y →
      (P.outcome (sel v)).success ≤ C / (t - v) ^ 2) :
    P.envelope y ≤ B + C / (t - y) := by
  let s : ℝ → ℝ := fun v => derivWithin P.envelope (Ioi v) v
  have hs (v : ℝ) (hv : v ∈ Icc a y) (w : ℝ) (hw : w ∈ Icc a y) :
      P.envelope v + (w - v) * s v ≤ P.envelope w :=
    Subgradient.rightDeriv_subgradient P.envelope_convex (by simp) (mem_univ w)
  have he : ∀ᵐ v, v ∈ Icc a y → (P.outcome (sel v)).success = s v := by
    apply Subgradient.ae_eq_of_ae_subgradient hs
    filter_upwards [hsel] with v hv hvI w _
    exact P.supporting_line v (sel v) (hv hvI) w
  have hne (v : ℝ) (hv : v ∈ uIcc a y) : t - v ≠ 0 := by
    rw [uIcc_of_le hay] at hv
    exact (sub_pos.mpr (hv.2.trans_lt hyt)).ne'
  have hint : IntervalIntegrable (fun v => C / (t - v) ^ 2) volume a y :=
    (continuousOn_const.div ((continuousOn_const.sub continuousOn_id).pow 2)
      (fun v hv => pow_ne_zero 2 (hne v hv))).intervalIntegrable
  have hsint := Subgradient.intervalIntegrable hs (left_mem_Icc.mpr hay) (right_mem_Icc.mpr hay)
  have hm := intervalIntegral.integral_mono_ae_restrict hay hsint hint (by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [he, hupper] with v heq hup hvI
    rw [← heq hvI]
    exact hup hvI)
  have heq := Subgradient.sub_eq_integral hay hs
  have hi : (∫ v in a..y, C / (t - v) ^ 2) = C * ((t - y)⁻¹ - (t - a)⁻¹) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul]
    have hh := integral_inverse_square_gap a y t hay hyt
    simpa only [one_div] using congrArg (fun z : ℝ => C * z) hh
  rw [hi] at hm
  have ha0 : 0 ≤ (t - a)⁻¹ := inv_nonneg.mpr (sub_pos.mpr (hay.trans_lt hyt)).le
  rw [div_eq_mul_inv]
  nlinarith [mul_nonneg hC ha0]

theorem envelope_base_bound (P : Problem n) (t d C : ℝ) (hd : 0 < d) (hC : 0 ≤ C)
    (sel : ℝ → Game.JointAction n)
    (hsel : ∀ᵐ v, v ∈ Ioo (t - d) (t - d / 2) → P.BestResponse v (sel v))
    (hupper : ∀ v ∈ Ioo (t - d) (t - d / 2), ∀ act, P.BestResponse v act →
      (P.outcome act).success ≤ C / (t - v) ^ 2) :
    P.envelope (t - d) ≤ max (t - P.g) 0 * (4 * C / d ^ 2) := by
  have hn : volume (Ioo (t - d) (t - d / 2)) ≠ 0 := by
    rw [Real.volume_Ioo, ENNReal.ofReal_ne_zero_iff]
    linarith
  obtain ⟨v, hv, hbr⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hn (ae_restrict_of_ae hsel)
  have ha := hbr hv
  have hlow := P.envelope_monotone hv.1.le
  have hu := (P.outcome (sel v)).utility_le_bid_net_success v (sel v).bid P.g P.A P.G
    (sel v).bid_nonneg P.g_nonneg
  change P.payoff v (sel v) ≤ _ at hu
  rw [P.bestResponse_iff_attains v (sel v) |>.mp ha] at hu
  have hup := hupper v hv (sel v) ha
  have hgap : d / 2 ≤ t - v := by linarith [hv.2]
  have hbd : C / (t - v) ^ 2 ≤ 4 * C / d ^ 2 := by
    calc
      _ ≤ C / (d / 2) ^ 2 := div_le_div_of_nonneg_left hC (sq_pos_of_pos (half_pos hd))
        (by nlinarith)
      _ = _ := by ring
  have hvm : v - P.g - (sel v).bid ≤ max (t - P.g) 0 := by
    have hmax := le_max_left (t - P.g) 0
    have hb := (sel v).bid_nonneg
    linarith [hv.2]
  exact hlow.trans (hu.trans ((mul_le_mul_of_nonneg_right hvm (P.outcome (sel v)).success_nonneg).trans
    (mul_le_mul_of_nonneg_left (hup.trans hbd) (le_max_right _ _))))

theorem envelope_tail_anchor_of_square_bound
    (P : ℕ → Problem n) (t g d : ℝ) (hd : 0 < d)
    (hg : ∀ k, (P k).g = g)
    (h C : ℕ → ℝ) (hh0 : Tendsto h atTop (𝓝 0))
    (hh : ∀ᶠ k in atTop, 0 < h k) (hC : ∀ k, 0 ≤ C k)
    (hCh : Tendsto (fun k => C k / h k) atTop (𝓝 0))
    (K : ℝ) (hK : 0 ≤ K) (hChh : ∀ᶠ k in atTop, C k / h k ^ 2 ≤ K)
    (sel : ℕ → ℝ → Game.JointAction n)
    (hsel : ∀ k, ∀ᵐ v, v ∈ Ioo (t - d) t → (P k).BestResponse v (sel k v))
    (hupper : ∀ᶠ k in atTop, ∀ v ∈ Ioo (t - d) (t - h k), ∀ act,
      (P k).BestResponse v act → ((P k).outcome act).success ≤ C k / (t - v) ^ 2) :
    ∀ ε > 0, ∃ R₀ ≥ 0, ∀ R ≥ R₀,
      ∀ᶠ k in atTop, (P k).envelope (t - h k * R) / h k < ε := by
  intro ε hε
  let R₀ := 2 + 4 * K / ε
  have hR0 : 2 ≤ R₀ := by
    have hh : 0 ≤ 4 * K / ε := by positivity
    dsimp [R₀]
    linarith
  refine ⟨R₀, by linarith, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  have hKR : K / R < ε / 2 := by
    apply (div_lt_iff₀ hRpos).mpr
    have hhK : 4 * K ≤ ε * R := by
      have hh : 4 * K / ε ≤ R := by dsimp [R₀] at hR; linarith
      have hmul := (div_le_iff₀ hε).mp hh
      nlinarith
    nlinarith
  let B := max (t - g) 0 * 4 / d ^ 2
  have hb : Tendsto (fun k => B * (C k / h k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hCh.const_mul B
  have hr : Tendsto (fun k => h k * R) atTop (𝓝 0) := by
    simpa only [zero_mul] using hh0.mul_const R
  filter_upwards [hh, hupper, hChh, (tendsto_order.mp hb).2 (ε / 2) (half_pos hε),
    (tendsto_order.mp hr).2 d hd, (tendsto_order.mp hh0).2 (d / 2) (half_pos hd)]
    with k hk hUk hCk hBk hdk hhalf
  have hyr : t - d < t - h k * R := by linarith
  have hyt : t - h k * R < t := by nlinarith
  have hR1 : 1 < R := by linarith
  have hyh : t - h k * R < t - h k := by nlinarith
  have hbase : (P k).envelope (t - d) ≤ B * C k := by
    have hbsel : ∀ᵐ v, v ∈ Ioo (t - d) (t - d / 2) → (P k).BestResponse v (sel k v) := by
      filter_upwards [hsel k] with v hv hvI
      exact hv ⟨hvI.1, by linarith [hvI.2]⟩
    have hh := (P k).envelope_base_bound t d (C k) hd (hC k) (sel k) hbsel (by
      intro v hv act ha
      exact hUk v ⟨hv.1, by linarith [hv.2]⟩ act ha)
    rw [hg k] at hh
    convert hh using 1
    dsimp [B]
    ring
  have hselI : ∀ᵐ v, v ∈ Icc (t - d) (t - h k * R) → (P k).BestResponse v (sel k v) := by
    filter_upwards [hsel k, measure_eq_zero_iff_ae_notMem.mp (measure_singleton (t - d) : volume {t - d} = 0)]
      with v hv hne hvI
    exact hv ⟨lt_of_le_of_ne hvI.1 (by simpa only [mem_singleton_iff] using Ne.symm hne), hvI.2.trans_lt hyt⟩
  have huppI : ∀ᵐ v, v ∈ Icc (t - d) (t - h k * R) →
      ((P k).outcome (sel k v)).success ≤ C k / (t - v) ^ 2 := by
    filter_upwards [hselI, measure_eq_zero_iff_ae_notMem.mp (measure_singleton (t - d) : volume {t - d} = 0)]
      with v hv hne hvI
    exact hUk v ⟨lt_of_le_of_ne hvI.1 (by simpa only [mem_singleton_iff] using Ne.symm hne),
      hvI.2.trans_lt hyh⟩ (sel k v) (hv hvI)
  have hu := (P k).envelope_tail_bound (t - d) (t - h k * R) t (B * C k) (C k)
    hyr.le hyt (hC k) (sel k) hselI hbase huppI
  have hur := div_le_div_of_nonneg_right hu hk.le
  have he : (B * C k + C k / (t - (t - h k * R))) / h k =
      B * (C k / h k) + (C k / h k ^ 2) / R := by
    field_simp
    ring
  rw [he] at hur
  have hdiv := div_le_div_of_nonneg_right hCk hRpos.le
  linarith

end Interim.Problem
end FCAppendix
