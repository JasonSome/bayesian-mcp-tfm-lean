import FCAppendix.Exclusive.NarrowGlobalGuardsPrice
import FCAppendix.Exclusive.NarrowExistenceGameNeighborhoodConstants

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open MeasureTheory Set Filter Topology

def lowerPriceFactor (d : ℕ) (x : Fin 4 → ℝ) : ℝ :=
  Real.exp (-x 3)*(1-x 1/x 0)^d
def upperPriceFactor (d : ℕ) (x : Fin 4 → ℝ) : ℝ :=
  Real.exp (x 3)*(1-x 1/x 0+x 2/x 0)^d
def priceReferenceState (h rho : ℝ) : Fin 4 → ℝ := ![h, rho, 0, 0]

theorem price_factor_neighborhood (d : ℕ) (h rho tolerance : ℝ)
    (hh : 0 < h) (htol : 0 < tolerance) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ s t u z : ℝ,
      |s-h| < eta → |t-rho| < eta → |u| < eta → |z| < eta →
      |Real.exp (-z)*(1-t/s)^d-(1-rho/h)^d| < tolerance ∧
      |Real.exp z*(1-t/s+u/s)^d-(1-rho/h)^d| < tolerance := by
  have hl : ContinuousAt (lowerPriceFactor d) (priceReferenceState h rho) := by
    apply ContinuousAt.mul
    · exact (Real.continuous_exp.comp (continuous_apply 3).neg).continuousAt
    · apply ContinuousAt.pow
      exact continuousAt_const.sub ((continuous_apply 1).continuousAt.div
        (continuous_apply 0).continuousAt hh.ne')
  have hu : ContinuousAt (upperPriceFactor d) (priceReferenceState h rho) := by
    apply ContinuousAt.mul
    · exact (Real.continuous_exp.comp (continuous_apply 3)).continuousAt
    · apply ContinuousAt.pow
      exact (continuousAt_const.sub ((continuous_apply 1).continuousAt.div
        (continuous_apply 0).continuousAt hh.ne')).add
        ((continuous_apply 2).continuousAt.div (continuous_apply 0).continuousAt hh.ne')
  have hlv : lowerPriceFactor d (priceReferenceState h rho) = (1-rho/h)^d := by
    simp [lowerPriceFactor, priceReferenceState]
  have huv : upperPriceFactor d (priceReferenceState h rho) = (1-rho/h)^d := by
    simp [upperPriceFactor, priceReferenceState]
  have he := (hl.eventually (Metric.ball_mem_nhds _ htol)).and
    (hu.eventually (Metric.ball_mem_nhds _ htol))
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨eta, heta, ?_⟩
  intro s t u z hs ht hU hz
  have hd : dist (![s,t,u,z] : Fin 4 → ℝ) (priceReferenceState h rho) < eta := by
    apply (dist_pi_lt_iff heta).mpr
    intro i
    fin_cases i
    · exact hs
    · exact ht
    · change |u-0| < eta
      simpa only [sub_zero] using hU
    · change |z-0| < eta
      simpa only [sub_zero] using hz
  have hx := hball hd
  have hxL : dist (Real.exp (-z)*(1-t/s)^d)
      (lowerPriceFactor d (priceReferenceState h rho)) < tolerance := hx.1
  have hxU : dist (Real.exp z*(1-t/s+u/s)^d)
      (upperPriceFactor d (priceReferenceState h rho)) < tolerance := hx.2
  rw [hlv] at hxL
  rw [huv] at hxU
  exact ⟨hxL, hxU⟩

theorem close_of_price_bracket (scale cap tolerance L U q price : ℝ)
    (hscale : 0 < scale) (hcap : 0 < cap) (hscaleCap : scale ≤ cap) (htol : 0 < tolerance)
    (hL : |L-q| < tolerance/cap) (hU : |U-q| < tolerance/cap)
    (hprice : price ∈ Icc (scale*L) (scale*U)) : |price-scale*q| < tolerance := by
  have hbudget : scale*(tolerance/cap) ≤ tolerance := by
    have hb := mul_le_mul_of_nonneg_right hscaleCap (div_pos htol hcap).le
    have he : cap*(tolerance/cap) = tolerance := by field_simp
    rwa [he] at hb
  have hl := mul_lt_mul_of_pos_left (abs_lt.mp hL).1 hscale
  have hu := mul_lt_mul_of_pos_left (abs_lt.mp hU).2 hscale
  apply abs_lt.mpr
  constructor <;> nlinarith [hprice.1, hprice.2]

theorem canonical_native_price_neighborhood (d : ℕ) (hd : 1 ≤ d)
    (h rho cap tolerance : ℝ) (hh : 0 < h) (hrho : 0 < rho) (hrh : rho < h)
    (hcap : 0 < cap) (htol : 0 < tolerance) :
    ∃ delta eta : ℝ, ∃ M0 : ℕ, 0 < delta ∧ 0 < eta ∧ 0 < M0 ∧
      ∀ (M c : ℕ), M0 ≤ M → ∀ (B : Fin M → ℝ) (i : Fin M) (scale : ℝ),
      0 < scale → scale ≤ cap →
      (∀ j, j ≠ i → B j = 0 ∨ B j ∈ Icc (scale*Real.exp (-delta)) (scale*Real.exp delta)) →
      |((Fintype.card (PositiveRival B i) : ℝ)+1)/(M : ℝ)-h| < eta →
      |(c : ℝ)/(M : ℝ)-rho| < eta →
      c < Fintype.card (PositiveRival B i) ∧ 0 < c ∧
        |canonicalPrice (d+1) (by omega) c B-scale*(1-rho/h)^d| < tolerance := by
  obtain ⟨e, he, hfac⟩ := price_factor_neighborhood d h rho (tolerance/cap) hh (by positivity)
  let eta := min e (min (rho/2) ((h-rho)/4))/4
  let delta := e/2
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hetaE : 2*eta < e := by
    have := min_le_left e (min (rho/2) ((h-rho)/4))
    dsimp [eta]
    linarith
  have hetaR : eta ≤ rho/2 := by
    have := (min_le_right e (min (rho/2) ((h-rho)/4))).trans (min_le_left _ _)
    dsimp [eta]
    linarith
  have hetaGap : 4*eta < h-rho := by
    have := (min_le_right e (min (rho/2) ((h-rho)/4))).trans (min_le_right _ _)
    dsimp [eta]
    linarith
  obtain ⟨M0, hM0⟩ := exists_nat_gt (1/eta)
  have hM0pos : 0 < M0 := by
    have : (0 : ℝ) < M0 := (one_div_pos.mpr heta).trans hM0
    exact_mod_cast this
  refine ⟨delta, eta, M0, hdelta, heta, hM0pos, ?_⟩
  intro M c hM B i scale hscale hscaleCap hB hN hC
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr (hM0pos.trans_le hM)
  have hlarge : 1/eta < (M : ℝ) := hM0.trans_le (by exact_mod_cast hM)
  have hInv : 1/(M : ℝ) < eta := by
    apply (div_lt_iff₀ hMR).mpr
    have hx := (div_lt_iff₀ heta).mp hlarge
    nlinarith
  let N : ℝ := Fintype.card (PositiveRival B i)
  have hNratio : |N/(M : ℝ)-h| < 2*eta := by
    have heq : N/(M : ℝ)-h = ((N+1)/(M : ℝ)-h)-1/(M : ℝ) := by ring
    rw [heq]
    have ht := abs_sub_le ((N+1)/(M : ℝ)-h) (0 : ℝ) (1/(M : ℝ))
    rw [sub_zero, zero_sub, abs_neg, abs_of_pos (one_div_pos.mpr hMR)] at ht
    have hh' := add_lt_add hN hInv
    linarith
  have hCN : (c : ℝ)/(M : ℝ) < N/(M : ℝ) := by
    have hcl := (abs_lt.mp hC).2
    have hnl := (abs_lt.mp hNratio).1
    linarith
  have hcN : c < Fintype.card (PositiveRival B i) := by
    have hnum : (c : ℝ) < (Fintype.card (PositiveRival B i) : ℝ) :=
      (div_lt_div_iff_of_pos_right hMR).mp hCN
    exact_mod_cast hnum
  have hcpos : 0 < c := by
    have hcp : 0 < (c : ℝ)/(M : ℝ) := by have := (abs_lt.mp hC).1; linarith
    exact Nat.cast_pos.mp ((div_pos_iff_of_pos_right hMR).mp hcp)
  have hNR : 0 < N := Nat.cast_pos.mpr (by omega)
  have hfactor := hfac (N/(M : ℝ)) ((c : ℝ)/(M : ℝ)) (1/(M : ℝ)) delta
    (hNratio.trans hetaE) (hC.trans (by linarith : eta < e))
    (by simpa only [abs_of_pos (one_div_pos.mpr hMR)] using hInv.trans (by linarith : eta < e))
    (by rw [abs_of_pos hdelta]; dsimp [delta]; linarith)
  have hbracket := canonical_native_price_bracket (d+1) c (by omega) hcpos B i
    (scale*Real.exp (-delta)) (scale*Real.exp delta) (mul_pos hscale (Real.exp_pos _)) hB hcN
  have heL : ((N-c)/N)^d = (1-((c : ℝ)/(M : ℝ))/(N/(M : ℝ)))^d := by
    congr 1
    field_simp
  have heU : ((N-c+1)/N)^d =
      (1-((c : ℝ)/(M : ℝ))/(N/(M : ℝ))+(1/(M : ℝ))/(N/(M : ℝ)))^d := by
    congr 1
    field_simp
  refine ⟨hcN, hcpos, ?_⟩
  apply close_of_price_bracket scale cap tolerance _ _ ((1-rho/h)^d) _
    hscale hcap hscaleCap htol hfactor.1 hfactor.2
  simpa only [Nat.add_sub_cancel, ← mul_assoc, N, ← heL, ← heU] using hbracket

end FCAppendix.Exclusive.Narrow.Global
