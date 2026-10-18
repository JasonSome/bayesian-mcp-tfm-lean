import FCAppendix.Exclusive.NarrowGlobalGuardsPrice
import FCAppendix.Exclusive.NarrowGlobalGuardsOptimum

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open Set

theorem lower_route_payment_times_failure (n k : ℕ) (hn : 2 ≤ n)
    (hk : 1 ≤ k) (hkn : k < n) (a : UserTariff) (ha : a.Allowed)
    {p b lam : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb : 0 ≤ b)
    (hprice : b*(1-p)^(n-1)=lam) :
    lam*p ≤ (b*a.expected (IndependentCounts.binomial k p hp0 hp1))*(1-p) := by
  have hq0 : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hq1 : 1-p ≤ 1 := by linarith
  cases a with
  | unique =>
    rw [UserTariff.expected_unique_binomial]
    have hpow : (1-p)^(n-1) ≤ (1-p)^k :=
      pow_le_pow_of_le_one hq0 hq1 (by omega)
    have hbp : 0 ≤ b*p := mul_nonneg hb hp0
    have hbase := mul_le_mul_of_nonneg_left hpow hbp
    have hkR : (1:ℝ) ≤ k := Nat.one_le_cast.mpr hk
    have hm := mul_le_mul_of_nonneg_left hkR (mul_nonneg hbp (pow_nonneg hq0 k))
    have he : (1-p)^(k-1)*(1-p)=(1-p)^k := by
      rw [← pow_succ,show k-1+1=k by omega]
    calc
      lam*p = (b*p)*(1-p)^(n-1) := by rw [← hprice]; ring
      _ ≤ (b*p)*(1-p)^k := hbase
      _ ≤ (b*p)*(1-p)^k*(k:ℝ) := by simpa only [mul_one] using hm
      _ = (b*((k:ℝ)*p*(1-p)^(k-1)))*(1-p) := by rw [← he]; ring
  | affine eta =>
    have hpow : (1-p)^(n-1) ≤ 1-p := by
      simpa only [pow_one] using pow_le_pow_of_le_one hq0 hq1 (show 1 ≤ n-1 by omega)
    have he := LowType.affine_expected_ge_success eta ha.1
      (IndependentCounts.binomial k p hp0 hp1)
    rw [IndependentCounts.binomial_success] at he
    have hpS := LowType.marginal_le_success hk hp0 hp1
    have hm := mul_le_mul_of_nonneg_left (hpS.trans he) (mul_nonneg hb hq0)
    calc
      lam*p = (b*p)*(1-p)^(n-1) := by rw [← hprice]; ring
      _ ≤ (b*p)*(1-p) := mul_le_mul_of_nonneg_left hpow (mul_nonneg hb hp0)
      _ ≤ (b*(UserTariff.affine eta).expected (IndependentCounts.binomial k p hp0 hp1))*(1-p) := by
        nlinarith only [hm]

theorem affine_payment_times_failure (n k : ℕ) (hn : 2 ≤ n)
    (hk : 1 ≤ k) (eta : ℝ) (heta : 0 ≤ eta)
    {p b lam : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb : 0 ≤ b)
    (hprice : b*(1-p)^(n-1)=lam) :
    lam*p ≤ (b*(UserTariff.affine eta).expected
      (IndependentCounts.binomial k p hp0 hp1))*(1-p) := by
  have hq0 : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hq1 : 1-p ≤ 1 := by linarith
  have hpow : (1-p)^(n-1) ≤ 1-p := by
    simpa only [pow_one] using pow_le_pow_of_le_one hq0 hq1 (show 1 ≤ n-1 by omega)
  have he := LowType.affine_expected_ge_success eta heta
    (IndependentCounts.binomial k p hp0 hp1)
  rw [IndependentCounts.binomial_success] at he
  have hpS := LowType.marginal_le_success hk hp0 hp1
  have hm := mul_le_mul_of_nonneg_left (hpS.trans he) (mul_nonneg hb hq0)
  calc
    lam*p = (b*p)*(1-p)^(n-1) := by rw [← hprice]; ring
    _ ≤ (b*p)*(1-p) := mul_le_mul_of_nonneg_left hpow (mul_nonneg hb hp0)
    _ ≤ (b*(UserTariff.affine eta).expected (IndependentCounts.binomial k p hp0 hp1))*(1-p) := by
      nlinarith only [hm]

theorem binomialPayoff_tail_negative (n k : ℕ) (hkn : k ≤ n)
    (a : UserTariff) (G : Schedule n) (g v b p lam margin : ℝ)
    (hg : 0 ≤ g) (hv : 0 ≤ v) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (hcost : lam*p ≤ (b*a.expected (IndependentCounts.binomial k p hp0 hp1.le))*(1-p))
    (htail : (v+margin)*(1-p) ≤ lam*p) :
    LowType.binomialPayoff a G k g v b p ≤ -margin := by
  let mu := IndependentCounts.binomial k p hp0 hp1.le
  have hbase : 0 ≤ mu.expect (fun r => G.charge r.val) :=
    mu.expect_nonneg fun r => G.nonneg r.val (by have := r.isLt; omega)
  have hc : v+margin ≤ b*a.expected mu := by
    exact le_of_mul_le_mul_right (htail.trans hcost) (sub_pos.mpr hp1)
  rw [LowType.binomialPayoff_eq a G k g v b p hp0 hp1.le]
  have hval := mul_le_mul_of_nonneg_left mu.success_le_one hv
  change v*mu.success-b*a.expected mu-g*mu.expect (fun r => G.charge r.val) ≤ _
  nlinarith only [hval,hc,mul_nonneg hg hbase]

theorem full_route_unique_endpoint_bound (n : ℕ) (G : Schedule n)
    (g v b p lam : ℝ) (hg : 0 ≤ g) (hv : 0 ≤ v)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hprice : b*(1-p)^(n-1)=lam) :
    LowType.binomialPayoff .unique G n g v b p ≤ v-(n:ℝ)*lam+(n:ℝ)*lam*(1-p) := by
  let mu := IndependentCounts.binomial n p hp0 hp1
  have hbase : 0 ≤ mu.expect (fun r => G.charge r.val) :=
    mu.expect_nonneg fun r => G.nonneg r.val (by have := r.isLt; omega)
  have hcost : b*UserTariff.unique.expected mu=(n:ℝ)*lam*p := by
    rw [UserTariff.expected_unique_binomial]
    rw [← hprice]
    ring
  rw [LowType.binomialPayoff_eq .unique G n g v b p hp0 hp1,hcost]
  have hval := mul_le_mul_of_nonneg_left mu.success_le_one hv
  change v*mu.success-(n:ℝ)*lam*p-g*mu.expect (fun r => G.charge r.val) ≤ _
  nlinarith only [hval,mul_nonneg hg hbase]

theorem large_bid_response (n : ℕ) (hn : 2 ≤ n)
    {b lam lower upper delta : ℝ} (hlower : 0 < lower)
    (hlam : lam ∈ Icc lower upper) (hd0 : 0 < delta) (hd1 : delta < 1)
    (hb : 0 < b) (hlarge : upper ≤ b*delta^(n-1)) :
    let p := demand n b lam
    1-delta ≤ p ∧ p < 1 ∧ b*(1-p)^(n-1)=lam := by
  have hlam0 : 0 < lam := hlower.trans_le hlam.1
  have hp : 1-delta ≤ demand n b lam := by
    rw [← LowType.demand_at_reference_failure n hn hb hd0 hd1.le]
    exact demand_antitone n hn hb hlam0.le (hlam.2.trans hlarge)
  have hpos : 0 < demand n b lam := (sub_pos.mpr hd1).trans_le hp
  have hbl : lam < b := (demand_pos_iff n hn hb hlam0.le).mp hpos
  exact ⟨hp,demand_lt_one n hb hlam0,by
    rw [demand_receipt n hn hb hlam0,min_eq_right hbl.le]⟩

theorem large_bid_lower_route_negative (n k : ℕ) (hn : 2 ≤ n)
    (hk : 1 ≤ k) (hkn : k < n) (a : UserTariff) (ha : a.Allowed)
    (G : Schedule n) (g v b lam lower upper delta V margin : ℝ)
    (hg : 0 ≤ g) (hv0 : 0 ≤ v) (hvV : v ≤ V) (hm : 0 ≤ margin)
    (hlower : 0 < lower) (hlam : lam ∈ Icc lower upper)
    (hd0 : 0 < delta) (hdhalf : delta ≤ 1/2)
    (hsmall : delta*(V+margin) ≤ lower/2)
    (hb : 0 < b) (hlarge : upper ≤ b*delta^(n-1)) :
    LowType.binomialPayoff a G k g v b (demand n b lam) ≤ -margin := by
  obtain ⟨hp,hp1,hprice⟩ := large_bid_response n hn hlower hlam hd0 (by linarith) hb hlarge
  have hp0 : 0 ≤ demand n b lam := demand_nonneg _ _ _
  apply binomialPayoff_tail_negative n k hkn.le a G g v b _ lam margin hg hv0 hp0 hp1
    (lower_route_payment_times_failure n k hn hk hkn a ha hp0 hp1.le hb.le hprice)
  have hq : 1-demand n b lam ≤ delta := by linarith
  have hV : 0 ≤ V+margin := by linarith
  have hleft : (v+margin)*(1-demand n b lam) ≤ delta*(V+margin) := by
    exact (mul_le_mul_of_nonneg_right (by linarith : v+margin ≤ V+margin)
      (sub_nonneg.mpr hp1.le)).trans (by nlinarith only [mul_le_mul_of_nonneg_left hq hV])
  have hright : lower/2 ≤ lam*demand n b lam := by
    have hhalf : 1/2 ≤ demand n b lam := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left hhalf hlower.le,
      mul_le_mul_of_nonneg_right hlam.1 hp0]
  exact hleft.trans (hsmall.trans hright)

theorem large_bid_affine_negative (n k : ℕ) (hn : 2 ≤ n)
    (hk : 1 ≤ k) (hkn : k ≤ n) (eta : ℝ) (heta : 0 ≤ eta)
    (G : Schedule n) (g v b lam lower upper delta V margin : ℝ)
    (hg : 0 ≤ g) (hv0 : 0 ≤ v) (hvV : v ≤ V) (hm : 0 ≤ margin)
    (hlower : 0 < lower) (hlam : lam ∈ Icc lower upper)
    (hd0 : 0 < delta) (hdhalf : delta ≤ 1/2)
    (hsmall : delta*(V+margin) ≤ lower/2)
    (hb : 0 < b) (hlarge : upper ≤ b*delta^(n-1)) :
    LowType.binomialPayoff (.affine eta) G k g v b (demand n b lam) ≤ -margin := by
  obtain ⟨hp,hp1,hprice⟩ := large_bid_response n hn hlower hlam hd0 (by linarith) hb hlarge
  have hp0 : 0 ≤ demand n b lam := demand_nonneg _ _ _
  apply binomialPayoff_tail_negative n k hkn (.affine eta) G g v b _ lam margin hg hv0 hp0 hp1
    (affine_payment_times_failure n k hn hk eta heta hp0 hp1.le hb.le hprice)
  have hq : 1-demand n b lam ≤ delta := by linarith
  have hV : 0 ≤ V+margin := by linarith
  have hleft : (v+margin)*(1-demand n b lam) ≤ delta*(V+margin) := by
    exact (mul_le_mul_of_nonneg_right (by linarith : v+margin ≤ V+margin)
      (sub_nonneg.mpr hp1.le)).trans (by nlinarith only [mul_le_mul_of_nonneg_left hq hV])
  have hright : lower/2 ≤ lam*demand n b lam := by
    have hhalf : 1/2 ≤ demand n b lam := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left hhalf hlower.le,
      mul_le_mul_of_nonneg_right hlam.1 hp0]
  exact hleft.trans (hsmall.trans hright)

theorem large_bid_unique_endpoint_bound (n : ℕ) (hn : 2 ≤ n) (G : Schedule n)
    (g v b lam lower upper delta V : ℝ) (hg : 0 ≤ g) (hv0 : 0 ≤ v) (hvV : v ≤ V)
    (hlower : 0 < lower) (hlam : lam ∈ Icc lower upper)
    (hd0 : 0 < delta) (hd1 : delta < 1) (hb : 0 < b)
    (hlarge : upper ≤ b*delta^(n-1)) :
    LowType.binomialPayoff .unique G n g v b (demand n b lam) ≤
      V-(n:ℝ)*lower+(n:ℝ)*upper*delta := by
  obtain ⟨hp,hp1,hprice⟩ := large_bid_response n hn hlower hlam hd0 hd1 hb hlarge
  have hp0 : 0 ≤ demand n b lam := demand_nonneg _ _ _
  have hbase := full_route_unique_endpoint_bound n G g v b _ lam hg hv0 hp0 hp1.le hprice
  have hq : 1-demand n b lam ≤ delta := by linarith
  have hlo : 0 ≤ lam := (hlower.trans_le hlam.1).le
  have hcost : (n:ℝ)*lam*(1-demand n b lam) ≤ (n:ℝ)*upper*delta := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul hlam.2 hq (sub_nonneg.mpr hp1.le) (hlo.trans hlam.2))
        (Nat.cast_nonneg n)
  nlinarith only [hbase,hcost,mul_le_mul_of_nonneg_left hlam.1 (Nat.cast_nonneg n),hvV]

theorem large_bid_unique_reference_gap (d : ℕ) (hd : 1 ≤ d)
    (G : Schedule (d+1)) (g v b lam lower upper delta V refValue refPrice p0 error : ℝ)
    (hg : 0 ≤ g) (hv0 : 0 ≤ v) (hvV : v ≤ V)
    (hlower : 0 < lower) (hlam : lam ∈ Icc lower upper)
    (hd0 : 0 < delta) (hd1 : delta < 1) (hb : 0 < b)
    (hlarge : upper ≤ b*delta^d)
    (href : 0 < refPrice) (hp0 : p0 < 1) (hFOC : refValue*(1-p0)^d=refPrice)
    (hV : V ≤ refValue+error) (hlo : refPrice-error ≤ lower)
    (hbudget : ((d+1:ℕ)+1:ℝ)*error+(d+1:ℕ)*upper*delta ≤
      ((d:ℝ)*refPrice*(1-p0))/2) :
    LowType.binomialPayoff .unique G (d+1) g v b (demand (d+1) b lam)+
      ((d:ℝ)*refPrice*(1-p0))/2 ≤ referenceUtility d .unique refPrice refValue p0 := by
  have hend := large_bid_unique_endpoint_bound (d+1) (by omega) G g v b lam
    lower upper delta V hg hv0 hvV hlower hlam hd0 hd1 hb (by simpa only [Nat.add_sub_cancel] using hlarge)
  have hgap := (unique_full_route_endpoint_gap d hd refValue refPrice p0 href hp0 hFOC).1
  change LowType.binomialPayoff .unique G (d+1) g v b (demand (d+1) b lam)+
    ((d:ℝ)*refPrice*(1-p0))/2 ≤
      refValue*PayOnce.success (d+1) p0-refPrice*(d+1:ℕ)*p0
  have hlo' := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg (d+1))
  push_cast at hbudget hend hgap hlo' ⊢
  nlinarith only [hend,hgap,hV,hlo',hbudget]

theorem exists_small_failure_bid_cutoff (n : ℕ) (lower upper V cap : ℝ)
    (hlower : 0 < lower) (hlohi : lower ≤ upper) (hV : 0 ≤ V) (hcap : 0 < cap) :
    ∃ delta B : ℝ, 0 < delta ∧ delta ≤ cap ∧ delta ≤ 1/2 ∧ 0 < B ∧
      delta*(V+1) ≤ lower/2 ∧ ∀ b : ℝ, B ≤ b → 0 < b ∧ upper ≤ b*delta^(n-1) := by
  let delta := min cap (min (1/2) (lower/(2*(V+1))))
  have hd0 : 0 < delta := lt_min hcap (lt_min (by norm_num)
    (div_pos hlower (by positivity)))
  have hdcap : delta ≤ cap := min_le_left _ _
  have hdhalf : delta ≤ 1/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdsmall : delta*(V+1) ≤ lower/2 := by
    have hh : delta ≤ lower/(2*(V+1)) := (min_le_right _ _).trans (min_le_right _ _)
    have he := (le_div_iff₀ (show (0:ℝ)<2*(V+1) by positivity)).mp hh
    linarith only [he]
  let B := 1+upper/delta^(n-1)
  have hu : 0 < upper := hlower.trans_le hlohi
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨delta,B,hd0,hdcap,hdhalf,hB,hdsmall,?_⟩
  intro b hb
  refine ⟨hB.trans_le hb,?_⟩
  have he : B*delta^(n-1)=delta^(n-1)+upper := by
    dsimp [B]
    field_simp [(pow_pos hd0 (n-1)).ne']
  have hh := mul_le_mul_of_nonneg_right hb (pow_pos hd0 (n-1)).le
  rw [he] at hh
  linarith only [hh,(pow_pos hd0 (n-1)).le]

end FCAppendix.Exclusive.Narrow.Global
