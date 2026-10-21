import FCAppendix.Affine.Uniform06.Rank

noncomputable section

namespace FCAppendix.Affine.Uniform06.Rank

open Set

def pureRank (N c : ℕ) (A w : ℝ) : ℝ := Bayes.binomBelow N (A-w) c

theorem pureRank_pos (N c : ℕ) (hc : 0 < c) {A w : ℝ}
    (hp : A-w ∈ Ioo (0 : ℝ) 1) : 0 < pureRank N c A w :=
  Bayes.binomBelow_pos N c hc (A-w) hp

theorem log_pureRank_short_band
    (N c : ℕ) (hc : 0 < c) (hcN : c ≤ N+1)
    {A x y : ℝ} (hxy : x ≤ y) (hyl : 0 < A-y) (hxu : A-x < 1) :
    Real.log (pureRank N c A y)-Real.log (pureRank N c A x) ≤
      (N : ℝ)/(1-A+x)*(y-x) := by
  have h := Bayes.log_binomBelow_sub_le N c hc hcN
    (A-y) (A-x) hyl (by linarith) hxu
  simpa only [pureRank,show 1-(A-x)=1-A+x by ring,
    show (A-x)-(A-y)=y-x by ring] using h

theorem pureRank_short_band_lower
    (N c : ℕ) (hc : 0 < c) (hcN : c ≤ N+1)
    {A x y K : ℝ} (hxy : x ≤ y) (hyl : 0 < A-y) (hxu : A-x < 1)
    (hsize : (N : ℝ)/(1-A+x)*(y-x) ≤ K) :
    Real.exp (-K)*pureRank N c A y ≤ pureRank N c A x := by
  have hxpos : 0 < pureRank N c A x := pureRank_pos N c hc ⟨by linarith,hxu⟩
  have hypos : 0 < pureRank N c A y := pureRank_pos N c hc ⟨hyl,by linarith⟩
  have hlog := (log_pureRank_short_band N c hc hcN hxy hyl hxu).trans hsize
  have he := Real.exp_le_exp.mpr
    (show -K+Real.log (pureRank N c A y) ≤ Real.log (pureRank N c A x) by linarith)
  simpa only [Real.exp_add, Real.exp_log hxpos, Real.exp_log hypos] using he

theorem pureRank_short_band_lower_uniform
    (N c : ℕ) (hc : 0 < c) (hcN : c ≤ N+1)
    {A x y q K : ℝ} (hxy : x ≤ y) (hyl : 0 < A-y) (hxu : A-x < 1)
    (hq : 0 < q) (hqd : q ≤ 1-A+x) (hK : 0 ≤ K)
    (hband : (N : ℝ)*(y-x) ≤ q*K) :
    Real.exp (-K)*pureRank N c A y ≤ pureRank N c A x := by
  apply pureRank_short_band_lower N c hc hcN hxy hyl hxu
  have hd : 0 < 1-A+x := hq.trans_le hqd
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  exact hband.trans (by nlinarith [mul_le_mul_of_nonneg_right hqd hK])

theorem finite_two_type_envelope_inequality
    {η v w a b Sa Sb Da Db : ℝ}
    (hIC : payoff η v a Sa Da ≤ payoff η v b Sb Db) :
    payoff η w a Sa Da+(v-w)*Sa ≤ payoff η v b Sb Db := by
  unfold payoff at *
  nlinarith

theorem rent_times_success_lower
    {η v w a b Sa Sb Da Db : ℝ}
    (hη : 0 ≤ η) (hb : 0 ≤ b) (hDb : 0 ≤ Db)
    (hIR : 0 ≤ payoff η w a Sa Da)
    (hIC : payoff η v a Sa Da ≤ payoff η v b Sb Db) :
    (v-w)*Sa ≤ (v-b)*Sb := by
  have he := finite_two_type_envelope_inequality (w := w) hIC
  have hn := mul_nonneg (mul_nonneg hη hb) hDb
  unfold payoff at he hIR
  nlinarith

theorem rent_pos_of_lower_type
    {η v w a b Sa Sb Da Db : ℝ}
    (hη : 0 ≤ η) (hb : 0 ≤ b) (hDb : 0 ≤ Db)
    (hIR : 0 ≤ payoff η w a Sa Da)
    (hIC : payoff η v a Sa Da ≤ payoff η v b Sb Db)
    (hvw : w < v) (hSa : 0 < Sa) (hSb : 0 ≤ Sb) : 0 < v-b := by
  have he := rent_times_success_lower hη hb hDb hIR hIC
  have hp := mul_pos (sub_pos.mpr hvw) hSa
  by_contra h
  have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hSb
  linarith

theorem quantitative_rent_from_pureRank
    (N c : ℕ) (hc : 0 < c) (hcN : c ≤ N+1)
    {η A v w a b Sa Sb Da Db C₀ C₁ K : ℝ}
    (hη : 0 ≤ η) (hb : 0 ≤ b) (hDb : 0 ≤ Db)
    (hIR : 0 ≤ payoff η w a Sa Da)
    (hIC : payoff η v a Sa Da ≤ payoff η v b Sb Db)
    (hvw : w < v) (hSb : 0 ≤ Sb)
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hlo : C₀*pureRank N c A w ≤ Sa)
    (hhi : Sb ≤ C₁*pureRank N c A v)
    (hvl : 0 < A-v) (hwu : A-w < 1)
    (hsize : (N : ℝ)/(1-A+w)*(v-w) ≤ K) :
    (v-w)*C₀*Real.exp (-K)/C₁ ≤ v-b := by
  have hQv : 0 < pureRank N c A v := pureRank_pos N c hc ⟨hvl,by linarith⟩
  have hQw : 0 < pureRank N c A w := pureRank_pos N c hc ⟨by linarith,hwu⟩
  have hSa : 0 < Sa := (mul_pos hC₀ hQw).trans_le hlo
  have hrent := rent_pos_of_lower_type hη hb hDb hIR hIC hvw hSa hSb
  have he := rent_times_success_lower hη hb hDb hIR hIC
  have hratio := pureRank_short_band_lower N c hc hcN hvw.le hvl hwu hsize
  have hSlo : C₀*Real.exp (-K)*pureRank N c A v ≤ Sa := by
    have h := mul_le_mul_of_nonneg_left hratio hC₀.le
    have hh : C₀*Real.exp (-K)*pureRank N c A v ≤ C₀*pureRank N c A w := by
      simpa only [mul_assoc] using h
    exact hh.trans hlo
  have hl := mul_le_mul_of_nonneg_left hSlo (sub_nonneg.mpr hvw.le)
  have hh := mul_le_mul_of_nonneg_left hhi hrent.le
  have hcancel : (v-w)*C₀*Real.exp (-K) ≤ (v-b)*C₁ := by
    apply (mul_le_mul_iff_of_pos_right hQv).mp
    nlinarith [hl,he,hh]
  exact (div_le_iff₀ hC₁).mpr hcancel

theorem IC_increment_upper
    {η v a b Sa Sb Da Db : ℝ}
    (hIC : payoff η v b Sb Db ≤ payoff η v a Sa Da) :
    (v-b)*(Sb-Sa) ≤ (b-a)*(Sa+η*Da)+η*b*(Db-Da) := by
  unfold payoff at hIC
  nlinarith

theorem IC_increment_lower
    {η w a b Sa Sb Da Db : ℝ}
    (hIC : payoff η w a Sa Da ≤ payoff η w b Sb Db) :
    (b-a)*(Sa+η*Da)+η*b*(Db-Da) ≤ (w-b)*(Sb-Sa) := by
  unfold payoff at hIC
  nlinarith

theorem nearby_rent_lower {v a b r : ℝ}
    (hr : r ≤ v-a) (hab : b-a ≤ r/2) : r/2 ≤ v-b := by
  linarith

end FCAppendix.Affine.Uniform06.Rank
