import FCAppendix.Exclusive.CompletionExistingSourceFamily

noncomputable section
namespace FCAppendix.Completion.Exclusive
open MeasureTheory Filter Topology Set
open FCAppendix Game Bayes Exclusive Exclusive.Narrow Exclusive.Narrow.Finite

theorem source_family_scalar_inputs_capped (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    {h rho etaCap : ℝ} (hh : 0 < h) (hrho : 0 < rho) (hrhoh : rho < h)
    (hh1 : h ≤ 1) (hcap : 0 < etaCap) :
    ∃ eta delta l u L U eps : ℝ,
      eta ∈ Ioo (0 : ℝ) 1 ∧ eta < etaCap ∧ 0 < delta ∧ 0 < l ∧ l < u ∧ u < 1 ∧
      0 < L ∧ L ≤ U ∧ 0 < eps ∧
      ∀ H g : ℝ, 0 < H → 0 ≤ g → g/H < eps →
        ∃ k K : ℝ, 0 < k ∧ 0 ≤ K ∧
          ∀ a : UserTariff, a.Allowed →
            (∀ cap : ℝ, |cap-rho| < delta →
              ScalarCorridor d (H*sourceBid d a h rho*(1-eta))
                (H*sourceBid d a h rho*(1+eta)) h cap l u (H*L) (H*U) ∧
              spreadRatio d eta cap < 1) ∧
            (∀ lam ∈ Icc (H*L) (H*U), ∀ p ∈ Icc l u,
              lam*dfTariff d a p+g*deriv (baseMarginalCost d G) p ∈ Icc k K) := by
  obtain ⟨eta0, delta, l, u, L, U, eps0, heta0, hdelta, hl, hlu, hu, hL, hLU,
      _heps0, hprice, hscalar, _hmono⟩ := select_source_rectangle d hd G hh hrho hrhoh hh1
  obtain ⟨eps, heps, hslope⟩ := source_slope_bounds d hd G hl.le hlu.le hu hL hLU
  let eta := min (eta0/2) (etaCap/2)
  have heta0pos := heta0.1
  have heta : eta ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by dsimp [eta]; positivity, ?_⟩
    have := min_le_left (eta0/2) (etaCap/2)
    dsimp [eta]
    linarith [heta0.2]
  have hetaCap : eta < etaCap := by
    have := min_le_right (eta0/2) (etaCap/2)
    dsimp [eta]
    linarith
  have habs : |eta| < eta0 := by
    rw [abs_of_pos heta.1]
    have := min_le_left (eta0/2) (etaCap/2)
    dsimp [eta]
    linarith [heta0.1]
  refine ⟨eta, delta, l, u, L, U, eps, heta, hetaCap, hdelta, hl, hlu, hu, hL, hLU, heps, ?_⟩
  intro H g hH hg hsmall
  obtain ⟨k, K, hk, hK, hderiv⟩ := hslope H g hH hg hsmall
  refine ⟨k, K, hk, hK, ?_⟩
  intro a ha
  refine ⟨?_, hderiv a ha⟩
  intro cap hcapacity
  obtain ⟨hc0, hch, hqL, hqU, hpL, hpU, hspread⟩ := hscalar eta cap habs hcapacity
  have hc := scalarCorridor_of_source d hd hh hrhoh hc0.le hch hH hL heta
    (hprice a ha) hqL.le hqU.le hpL.le hpU.le
  have hcenter : H*sourcePrice d a h rho/(sourceQ h rho)^d = H*sourceBid d a h rho := by
    unfold sourceBid
    ring
  rw [hcenter] at hc
  exact ⟨hc, hspread⟩

theorem uniform_source_classification_capped (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    {h rho etaCap : ℝ} (hh : 0 < h) (hrho : 0 < rho) (hrhoh : rho < h)
    (hh1 : h ≤ 1) (hcap : 0 < etaCap) :
    ∃ eta eps l u L U : ℝ,
      eta ∈ Ioo (0 : ℝ) 1 ∧ eta < etaCap ∧ eps ∈ Ioo (0 : ℝ) 1 ∧
      0 < l ∧ l < u ∧ u < 1 ∧ 0 < L ∧ L ≤ U ∧
      ∀ H g : ℝ, 0 < H → 0 ≤ g → g/H < eps →
        ClassifiesSourceBand d G h rho eta eps H g l u L U := by
  obtain ⟨eta, delta, l, u, L, U, eps0, heta, hetaCap, hdelta, hl, hlu, hu, hL,
      hLU, heps0, hdata⟩ := source_family_scalar_inputs_capped d hd G hh hrho hrhoh hh1 hcap
  let eps := min eps0 (1/2)
  have heps : eps ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨lt_min heps0 (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩
  refine ⟨eta, eps, l, u, L, U, heta, hetaCap, heps, hl, hlu, hu, hL, hLU, ?_⟩
  intro H g hH hg hsmall
  obtain ⟨k, K, hk, hK, hinputs⟩ := hdata H g hH hg (hsmall.trans_le (min_le_left _ _))
  have hcenter (a : UserTariff) (ha : a.Allowed) : 0 < sourceBid d a h rho := by
    have hp0 : 0 ≤ rho/h := (div_pos hrho hh).le
    have hp1 : rho/h < 1 := (div_lt_one hh).mpr hrhoh
    have hf := (fTariff_pos_and_derivative_pos d hd a ha hp0 hp1).1
    exact div_pos (one_div_pos.mpr hf) (pow_pos (sub_pos.mpr hp1) d)
  exact classify_source_band d hd G hh hh1 hrho heta heps hH hl hlu.le hu hL hdelta hk hK
    hcenter (fun a ha => (hinputs a ha).1) (fun a ha => (hinputs a ha).2)

theorem exists_log_band_inside_relative {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ z ∈ Icc (-delta) delta,
      Real.exp z ∈ Ioo (1-eta) (1+eta) := by
  have he := Real.continuous_exp.continuousAt.eventually
    (Ioo_mem_nhds (show 1-eta < Real.exp 0 by simp; linarith)
      (show Real.exp 0 < 1+eta by simp; linarith))
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨e/2, by positivity, ?_⟩
  intro z hz
  apply hball
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  have habs : |z| ≤ e/2 := abs_le.mpr hz
  linarith

end FCAppendix.Completion.Exclusive
