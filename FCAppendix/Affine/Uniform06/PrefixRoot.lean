import FCAppendix.Affine.Uniform06.LowChernoffSource

set_option autoImplicit false
noncomputable section

namespace FCAppendix.Affine.Uniform06.PrefixRoot

open MeasureTheory Set
open FCAppendix.Affine.Uniform07

def psi (d z b : ℝ) : ℝ := max 0 (b-z)/(d+max 0 (b-z))
def sourcePsi (i : Row) (z b : ℝ) : ℝ := psi (cutoff i/1000) z b
def requiredDemand (i : Row) : ℝ := (cutoff i-delta)/(2*cutoff i)
def tailStartQ : Row → ℚ | .first => 17/20 | .second => 4/5
def meanBoundQ : Row → ℚ | .first => 29/200 | .second => 193/1000
def prefixQ (i : Row) : ℚ := xQ i+1/100
def activeAtTailQ (i : Row) : ℚ :=
  xQ i*tailStartQ i/(kappaQ i*tailStartQ i+xiQ i*xQ i)
def lowerActiveQ (i : Row) : ℚ := activeAtTailQ i-1/10000
def psiAtTailQ (i : Row) : ℚ :=
  (lowerActiveQ i-prefixQ i)/(1/1000+lowerActiveQ i-prefixQ i)

def normalizedActiveBid (i : Row) (y : ℝ) : ℝ :=
  x i*y/(kappa i*y+xi i*x i)

theorem normalizedActiveBid_mono (i : Row) :
    MonotoneOn (normalizedActiveBid i) (Ici (0:ℝ)) := by
  intro a ha b hb hab
  have hx : 0 < x i := by cases i <;> norm_num [x, xQ]
  have hk : 0 < kappa i := by cases i <;> norm_num [kappa, kappaQ, xiQ, etaQ]
  have hxi := xi_pos i
  have hA : 0 < kappa i*a+xi i*x i := by
    have hm := mul_nonneg hk.le ha
    have hp := mul_pos hxi hx
    linarith
  have hB : 0 < kappa i*b+xi i*x i := by
    have hm := mul_nonneg hk.le hb
    have hp := mul_pos hxi hx
    linarith
  apply (div_le_div_iff₀ hA hB).mpr
  have hp := mul_nonneg (mul_nonneg hxi.le (sq_nonneg (x i))) (sub_nonneg.mpr hab)
  nlinarith

theorem normalizedActiveBid_tail (i : Row) :
    normalizedActiveBid i (tailStartQ i : ℝ) = (activeAtTailQ i : ℝ) := by
  cases i <;> norm_num [normalizedActiveBid, activeAtTailQ,
    tailStartQ, x, xQ, kappa, kappaQ, xi, xiQ, etaQ]

theorem psi_bounds {d z b : ℝ} (hd : 0 < d) : psi d z b ∈ Icc (0:ℝ) 1 := by
  have hx := le_max_left 0 (b-z)
  have hden : 0 < d+max 0 (b-z) := by linarith
  constructor
  · exact div_nonneg hx hden.le
  · exact (div_le_iff₀ hden).mpr (by linarith)

theorem continuous_psi_bid {d z : ℝ} (hd : 0 < d) : Continuous (psi d z) := by
  unfold psi
  apply (continuous_const.max (continuous_id.sub continuous_const)).div
    (continuous_const.add (continuous_const.max (continuous_id.sub continuous_const)))
  intro b
  change d+max 0 (b-z) ≠ 0
  have hx := le_max_left 0 (b-z)
  exact ne_of_gt (by linarith)

theorem psi_monotone_bid {d z : ℝ} (hd : 0 < d) : Monotone (psi d z) := by
  intro a b hab
  have hA : 0 < d+max 0 (a-z) := by linarith [le_max_left 0 (a-z)]
  have hB : 0 < d+max 0 (b-z) := by linarith [le_max_left 0 (b-z)]
  have hx := max_le_max_left 0 (sub_le_sub_right hab z)
  exact (div_le_div_iff₀ hA hB).mpr (by nlinarith)

theorem psi_antitone_price {d a b v : ℝ} (hd : 0 < d) (hab : a ≤ b) :
    psi d b v ≤ psi d a v := by
  have hA : 0 < d+max 0 (v-b) := by linarith [le_max_left 0 (v-b)]
  have hB : 0 < d+max 0 (v-a) := by linarith [le_max_left 0 (v-a)]
  have hx := max_le_max_left 0 (sub_le_sub_left hab v)
  exact (div_le_div_iff₀ hA hB).mpr (by nlinarith)

theorem tail_numeric_guard (i : Row) :
    0 < tailStartQ i ∧ tailStartQ i < 1 ∧
    prefixQ i < lowerActiveQ i ∧ 0 < psiAtTailQ i ∧
    meanBoundQ i < (1-tailStartQ i)*psiAtTailQ i := by
  cases i <;> norm_num [tailStartQ, prefixQ, lowerActiveQ, activeAtTailQ,
    psiAtTailQ, meanBoundQ, xQ, kappaQ, xiQ, etaQ]

theorem meanBound_above_three_demand (i : Row) :
    3*requiredDemand i < (meanBoundQ i : ℝ) := by
  have ht := cutoff_pos i
  have hT := (LowChernoff.sourceTBox_ok i).2
  unfold requiredDemand
  rw [← mul_div_assoc, div_lt_iff₀ (show 0 < 2*cutoff i by positivity)]
  cases i <;> norm_num [meanBoundQ, LowChernoff.sourceTBox, delta] at hT ⊢ <;> linarith

theorem sourcePsi_at_lower_active (i : Row) :
    sourcePsi i ((prefixQ i : ℝ)*cutoff i) ((lowerActiveQ i : ℝ)*cutoff i) =
      (psiAtTailQ i : ℝ) := by
  have ht := cutoff_pos i
  have hh : (prefixQ i : ℝ) < lowerActiveQ i := by
    exact_mod_cast (tail_numeric_guard i).2.2.1
  have hnon : 0 ≤ (lowerActiveQ i : ℝ)*cutoff i-(prefixQ i : ℝ)*cutoff i := by nlinarith
  unfold sourcePsi psi psiAtTailQ
  rw [max_eq_right hnon]
  push_cast
  field_simp [ht.ne']
  ring

theorem active_tail_probability (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst = LowChernoff.conditionalValueLaw i) :
    G.real {p | p.1 ∈ Icc ((tailStartQ i : ℝ)*cutoff i) (cutoff i)} =
      1-(tailStartQ i : ℝ) := by
  have ht := cutoff_pos i
  have ha0 : (0:ℝ) ≤ tailStartQ i := by
    exact_mod_cast (tail_numeric_guard i).1.le
  have ha1 : (tailStartQ i : ℝ) ≤ 1 := by
    exact_mod_cast (tail_numeric_guard i).2.1.le
  have hat : (tailStartQ i : ℝ)*cutoff i ≤ cutoff i := by nlinarith
  have hset : Icc ((tailStartQ i : ℝ)*cutoff i) (cutoff i) ∩
      Icc (0:ℝ) (cutoff i) = Icc ((tailStartQ i : ℝ)*cutoff i) (cutoff i) := by
    apply inter_eq_self_of_subset_left
    exact Icc_subset_Icc (mul_nonneg ha0 ht.le) le_rfl
  change (G (Prod.fst ⁻¹' Icc ((tailStartQ i : ℝ)*cutoff i) (cutoff i))).toReal = _
  rw [← Measure.map_apply measurable_fst measurableSet_Icc, hvalue,
    LowChernoff.conditionalValueLaw, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Icc, hset, smul_eq_mul,
    Real.volume_Icc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (sub_nonneg.mpr hat)]
  field_simp [ht.ne']

theorem sourcePsi_integrable (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (z : ℝ) :
    Integrable (fun p => sourcePsi i z p.2) G := by
  have hd : 0 < cutoff i/1000 := div_pos (cutoff_pos i) (by norm_num)
  apply Integrable.mono' (integrable_const (1:ℝ))
    (((continuous_psi_bid hd).measurable.comp measurable_snd).aestronglyMeasurable)
  filter_upwards [] with p
  have hp := psi_bounds (z := z) (b := p.2) hd
  simpa only [Real.norm_eq_abs,Function.comp_apply,sourcePsi,abs_of_nonneg hp.1] using hp.2

theorem active_tail_mean_guard (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst = LowChernoff.conditionalValueLaw i)
    (hactive : ∀ᵐ p ∂G,
      p.1 ∈ Icc ((tailStartQ i : ℝ)*cutoff i) (cutoff i) →
        (lowerActiveQ i : ℝ)*cutoff i ≤ p.2) :
    (meanBoundQ i : ℝ) <
      ∫ p, sourcePsi i ((prefixQ i : ℝ)*cutoff i) p.2 ∂G := by
  let A : Set (ℝ × ℝ) :=
    {p | p.1 ∈ Icc ((tailStartQ i : ℝ)*cutoff i) (cutoff i)}
  have hA : MeasurableSet A := measurable_fst measurableSet_Icc
  have hd : 0 < cutoff i/1000 := div_pos (cutoff_pos i) (by norm_num)
  have hnum : (meanBoundQ i : ℝ) < (1-(tailStartQ i : ℝ))*(psiAtTailQ i : ℝ) := by
    exact_mod_cast (tail_numeric_guard i).2.2.2.2
  have hineq : (∫ p, A.indicator (fun _ => (psiAtTailQ i : ℝ)) p ∂G) ≤
      ∫ p, sourcePsi i ((prefixQ i : ℝ)*cutoff i) p.2 ∂G := by
    apply integral_mono_ae ((integrable_const _).indicator hA) (sourcePsi_integrable i G _)
    filter_upwards [hactive] with p hp
    by_cases hpa : p ∈ A
    · rw [indicator_of_mem hpa]
      rw [← sourcePsi_at_lower_active i]
      exact psi_monotone_bid hd (hp hpa)
    · rw [indicator_of_notMem hpa]
      exact (psi_bounds hd).1
  rw [integral_indicator hA, setIntegral_const, smul_eq_mul,
    show G.real A = 1-(tailStartQ i : ℝ) from active_tail_probability i G hvalue] at hineq
  exact hnum.trans_le hineq

theorem source_root_above_prefix (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst = LowChernoff.conditionalValueLaw i)
    (hactive : ∀ᵐ p ∂G,
      p.1 ∈ Icc ((tailStartQ i : ℝ)*cutoff i) (cutoff i) →
        (lowerActiveQ i : ℝ)*cutoff i ≤ p.2)
    {zG : ℝ} (hroot : (∫ p, sourcePsi i zG p.2 ∂G) = 3*requiredDemand i) :
    entry i+cutoff i/100 < zG := by
  have hmean := (meanBound_above_three_demand i).trans
    (active_tail_mean_guard i G hvalue hactive)
  have he : entry i+cutoff i/100 = (prefixQ i : ℝ)*cutoff i := by
    unfold entry prefixQ x
    push_cast
    ring
  rw [he]
  by_contra hz
  have hz' : zG ≤ (prefixQ i : ℝ)*cutoff i := le_of_not_gt hz
  have hmono := integral_mono (sourcePsi_integrable i G _) (sourcePsi_integrable i G _)
    (fun p => psi_antitone_price (div_pos (cutoff_pos i) (by norm_num)) hz')
  rw [hroot] at hmono
  linarith

theorem active_tail_lower_of_graph_error (i : Row)
    (G : Measure (ℝ × ℝ))
    (hgraph : ∀ᵐ p ∂G,
      p.1 ∈ Icc ((tailStartQ i : ℝ)*cutoff i) (cutoff i) →
        |p.2/cutoff i-normalizedActiveBid i (p.1/cutoff i)| ≤ 1/10000) :
    ∀ᵐ p ∂G,
      p.1 ∈ Icc ((tailStartQ i : ℝ)*cutoff i) (cutoff i) →
        (lowerActiveQ i : ℝ)*cutoff i ≤ p.2 := by
  have ht := cutoff_pos i
  have ha : (0:ℝ) ≤ tailStartQ i := by
    exact_mod_cast (tail_numeric_guard i).1.le
  filter_upwards [hgraph] with p hp
  intro hv
  have hav : (tailStartQ i : ℝ) ≤ p.1/cutoff i :=
    (le_div_iff₀ ht).mpr hv.1
  have hmono := normalizedActiveBid_mono i ha (ha.trans hav) hav
  rw [normalizedActiveBid_tail] at hmono
  have herror := (abs_le.mp (hp hv)).1
  have hdiv : (lowerActiveQ i : ℝ) ≤ p.2/cutoff i := by
    unfold lowerActiveQ
    push_cast
    linarith
  exact (le_div_iff₀ ht).mp hdiv

theorem source_root_above_prefix_of_active_graph (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst = LowChernoff.conditionalValueLaw i)
    (hgraph : ∀ᵐ p ∂G,
      p.1 ∈ Icc ((tailStartQ i : ℝ)*cutoff i) (cutoff i) →
        |p.2/cutoff i-normalizedActiveBid i (p.1/cutoff i)| ≤ 1/10000)
    {zG : ℝ} (hroot : (∫ p, sourcePsi i zG p.2 ∂G) = 3*requiredDemand i) :
    entry i+cutoff i/100 < zG :=
  source_root_above_prefix i G hvalue (active_tail_lower_of_graph_error i G hgraph) hroot

end FCAppendix.Affine.Uniform06.PrefixRoot
