import FCAppendix.Exclusive.SourceLowTypeMarket

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter Topology

theorem markerCritical_le_one (n : ℕ) (hn : 2 ≤ n) :
    (1-1/(n:ℝ))^(n-1) ≤ 1 := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hbase0 : 0 ≤ 1-1/(n:ℝ) := by
    have hh := (div_lt_one (by positivity : (0 : ℝ) < n)).mpr hnR
    linarith
  have hbase1 : 1-1/(n:ℝ) ≤ 1 := by
    have : 0 ≤ 1/(n:ℝ) := by positivity
    linarith
  exact pow_le_one₀ hbase0 hbase1

theorem exists_low_marker_width (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t < (1-1/(n:ℝ))^(n-1)) :
    ∃ deltaCap : ℝ, 0 < deltaCap ∧ t ≤ Real.exp (-deltaCap) ∧
      t ≤ Real.exp (-deltaCap)*(1-1/(n:ℝ))^(n-1) := by
  let crit := (1-1/(n:ℝ))^(n-1)
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hbase0 : 0 ≤ 1-1/(n:ℝ) := by
    have hh := (div_lt_one (by positivity : (0 : ℝ) < n)).mpr hnR
    linarith
  have hbase1 : 1-1/(n:ℝ) ≤ 1 := by
    have : 0 ≤ 1/(n:ℝ) := by positivity
    linarith
  have hcrit1 : crit ≤ 1 := pow_le_one₀ hbase0 hbase1
  have hc : ContinuousAt (fun z : ℝ => Real.exp (-z)*crit) 0 := by fun_prop
  have he : ∀ᶠ z in 𝓝 (0 : ℝ), t < Real.exp (-z)*crit :=
    hc.eventually (eventually_gt_nhds (by simpa only [neg_zero,Real.exp_zero,one_mul] using ht))
  obtain ⟨e,hepos,hsmall⟩ := Metric.eventually_nhds_iff.mp he
  have hhalf : dist (e/2) (0 : ℝ) < e := by rw [Real.dist_eq,sub_zero,abs_of_pos (half_pos hepos)]; linarith
  have hmark := hsmall hhalf
  refine ⟨e/2,half_pos hepos,?_,hmark.le⟩
  exact hmark.le.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hcrit1 (Real.exp_pos (-(e/2))).le)

structure LowMarketConstants (n : ℕ) (scaleLo q : ℝ) where
  t : ℝ
  tolerance : ℝ
  lowUpper : ℝ
  deltaCap : ℝ
  t_pos : 0 < t
  tolerance_pos : 0 < tolerance
  low_pos : 0 < lowUpper
  separation : q+tolerance/scaleLo < t
  low_margin : lowUpper < min (scaleLo*t) (scaleLo*q-tolerance)
  width_pos : 0 < deltaCap
  marker_floor : t ≤ Real.exp (-deltaCap)
  marker_threshold : t ≤ Real.exp (-deltaCap)*(1-1/(n:ℝ))^(n-1)
  low_lt_half_scaleLo : lowUpper < scaleLo/2

theorem exists_lowMarketConstants (n : ℕ) (hn : 2 ≤ n) (scaleLo q : ℝ)
    (hscaleLo : 0 < scaleLo) (hq : 0 < q)
    (hcrit : q < (1-1/(n:ℝ))^(n-1)) : Nonempty (LowMarketConstants n scaleLo q) := by
  let crit := (1-1/(n:ℝ))^(n-1)
  let t := (q+crit)/2
  have hqt : q < t := by dsimp [t]; linarith
  have htc : t < crit := by dsimp [t]; linarith
  have hq1 : q < 1 := hcrit.trans_le (markerCritical_le_one n hn)
  have ht : 0 < t := hq.trans hqt
  let e := min q (t-q)/4
  have he : 0 < e := by dsimp [e]; positivity
  have heq : e < q := by have := min_le_left q (t-q); dsimp [e]; linarith
  have hegap : e < t-q := by have := min_le_right q (t-q); dsimp [e]; linarith
  let tolerance := scaleLo*e
  have htol : 0 < tolerance := mul_pos hscaleLo he
  have htolq : tolerance < scaleLo*q := mul_lt_mul_of_pos_left heq hscaleLo
  have hfloor : 0 < min (scaleLo*t) (scaleLo*q-tolerance) :=
    lt_min (mul_pos hscaleLo ht) (sub_pos.mpr htolq)
  let lowUpper := min (scaleLo*t) (scaleLo*q-tolerance)/2
  obtain ⟨deltaCap,hdelta,hmarkerFloor,hmarkerThreshold⟩ := exists_low_marker_width n hn htc
  refine ⟨⟨t,tolerance,lowUpper,deltaCap,ht,htol,half_pos hfloor,?_,?_,
    hdelta,hmarkerFloor,hmarkerThreshold,?_⟩⟩
  · have heq' : tolerance/scaleLo=e := by dsimp [tolerance]; field_simp
    rw [heq']
    linarith
  · dsimp only [lowUpper]
    linarith
  · have hf := min_le_right (scaleLo*t) (scaleLo*q-tolerance)
    have hqscale := mul_lt_mul_of_pos_left hq1 hscaleLo
    dsimp only [lowUpper]
    nlinarith

end FCAppendix.Bayes.ExclusiveSource
