import FCAppendix.Exclusive.NarrowGlobalGuardsRawReference

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open Set MeasureTheory ProbabilityTheory

lemma pricedPayoff_lower_bound (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (a : UserTariff) (ha : a.Allowed) (b B lam : ℝ)
    (hb : b ∈ Icc (0:ℝ) B) (hlam : 0 < lam) :
    -B*n ≤ pricedPayoff n k a b lam := by
  let p := menuMarginal n b lam
  have hp := menuMarginal_bounds n b lam hlam
  have hE : binomialPolynomial k a.charge p ≤ n := by
    rw [binomialPolynomial_eq_expect _ _ _ hp.1 hp.2]
    let mu := IndependentCounts.binomial k p hp.1 hp.2
    change a.expected mu ≤ n
    have he : a.expected mu ≤ (k:ℝ) := by
      cases a with
      | unique =>
        apply le_trans (b := 1)
        · exact mu.expect_le_const (fun r => by
            simp only [UserTariff.charge]; split_ifs <;> norm_num)
        · exact Nat.one_le_cast.mpr hk
      | affine eta =>
        rw [UserTariff.expected_affine]
        have hcoef : 0 ≤ 1-eta := sub_nonneg.mpr ha.2
        have hmul := mul_nonneg hcoef (sub_nonneg.mpr mu.success_le_load)
        exact (show (1-eta)*mu.success+eta*mu.load ≤ mu.load by nlinarith only [hmul]).trans
          mu.load_le_n
    exact he.trans (Nat.cast_le.mpr hkn)
  have hE0 : 0 ≤ binomialPolynomial k a.charge p := by
    rw [binomialPolynomial_eq_expect _ _ _ hp.1 hp.2]
    exact FiniteLaw.expect_nonneg _ (fun r => a.charge_nonneg ha r.val)
  have hS : 0 ≤ PayOnce.success k p := by
    simpa only [IndependentCounts.binomial_success,PayOnce.success] using
      (IndependentCounts.binomial k p hp.1 hp.2).success_nonneg
  have hpay : b*binomialPolynomial k a.charge p ≤ B*n :=
    mul_le_mul hb.2 hE hE0 (hb.1.trans hb.2)
  change -B*n ≤ PayOnce.success k p-b*binomialPolynomial k a.charge p
  nlinarith only [hS,hpay]

theorem finite_lower_route_compact_guard (d k : ℕ) (hd : 1 ≤ d)
    (hk : 0 < k) (hkn : k < d+1) (p0 B lower upper : ℝ)
    (hp0 : 0 < p0) (hp1 : p0 < 1) (hB : 0 ≤ B) (hlower : 0 < lower)
    (hprices : ∀ a : UserTariff, a.Allowed → normalizedPrice d a p0 ∈ Icc lower upper) :
    ∃ gap delta valueTolerance badTolerance : ℝ,
      0 < gap ∧ 0 < delta ∧ 0 < valueTolerance ∧ 0 < badTolerance ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
        (E : Set Ω), MeasurableSet E → ∀ a : UserTariff, a.Allowed →
        ∀ G : Schedule (d+1), ∀ g v : ℝ, 0 ≤ g → v ≤ 2 →
        |v-1|+g*(d+1:ℕ) ≤ valueTolerance → ∀ b ∈ Icc (0:ℝ) B,
        ∀ lam : Ω → ℝ, Measurable lam → (∀ w, 0 ≤ lam w) →
        (∀ w ∈ E, lam w ∈ Icc lower upper ∧
          |lam w-normalizedPrice d a p0| < delta) → mu.real Eᶜ ≤ badTolerance →
        (∫ w, LowType.binomialPayoff a G k g v b (activeDemand (d+1) b (lam w)) ∂mu)+gap ≤
          referenceUtility d a (normalizedPrice d a p0) 1 p0 := by
  obtain ⟨gamma,hgamma,hgap⟩ := referenceRawGap_uniform_compact d k hd hk hkn p0 B hp0 hp1 hB
  obtain ⟨delta,hdelta,htransport⟩ := integral_binomialPayoff_compact_transport (d+1) k
    (by omega) hkn.le lower upper B (gamma/8) hlower (by positivity)
  let K : ℝ := 2+B*(d+1:ℕ)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨gamma/2,delta,gamma/8,gamma/(4*K),by positivity,hdelta,by positivity,by positivity,?_⟩
  intro Ω _ mu _ E hE a ha G g v hg hv hvalue b hb lam hlam hlam0 hgood hbad
  let C := pricedPayoff (d+1) k a b (normalizedPrice d a p0)+gamma/8+|v-1|+g*(d+1:ℕ)
  have hint := htransport mu E hE a ha G g v 2 hg (by norm_num) hv b hb
    (normalizedPrice d a p0) (hprices a ha) lam hlam hlam0 hgood
  change (∫ w, LowType.binomialPayoff a G k g v b (activeDemand (d+1) b (lam w)) ∂mu) ≤
    C+(2-C)*mu.real Eᶜ at hint
  have hr := hgap a ha b hb
  change gamma ≤ referenceUtility d a (normalizedPrice d a p0) 1 p0-
    pricedPayoff (d+1) k a b (normalizedPrice d a p0) at hr
  have hC : C ≤ referenceUtility d a (normalizedPrice d a p0) 1 p0-3*gamma/4 := by
    dsimp [C]
    linarith only [hr,hvalue]
  have hlow := pricedPayoff_lower_bound (d+1) k hk hkn.le a ha b B
    (normalizedPrice d a p0) hb (hlower.trans_le (hprices a ha).1)
  have hcoeff : 2-C ≤ K := by
    dsimp [K,C]
    nlinarith only [hlow,hgamma.le,abs_nonneg (v-1),
      mul_nonneg hg (Nat.cast_nonneg (d+1))]
  have hbadcost : (2-C)*mu.real Eᶜ ≤ gamma/4 := by
    have hm := mul_le_mul_of_nonneg_right hcoeff (measureReal_nonneg (μ := mu) (s := Eᶜ))
    have hbprob := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hK)).mp hbad
    nlinarith only [hm,hbprob]
  linarith only [hint,hC,hbadcost]

theorem finite_all_lower_routes_compact_guard (d : ℕ) (hd : 1 ≤ d) (p0 B lower upper : ℝ)
    (hp0 : 0 < p0) (hp1 : p0 < 1) (hB : 0 ≤ B) (hlower : 0 < lower)
    (hprices : ∀ a : UserTariff, a.Allowed → normalizedPrice d a p0 ∈ Icc lower upper) :
    ∃ gap delta valueTolerance badTolerance : ℝ,
      0 < gap ∧ 0 < delta ∧ 0 < valueTolerance ∧ 0 < badTolerance ∧
      ∀ k : ℕ, 1 ≤ k → k < d+1 → ∀ {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]
        (E : Set Ω), MeasurableSet E → ∀ a : UserTariff, a.Allowed →
        ∀ G : Schedule (d+1), ∀ g v : ℝ, 0 ≤ g → v ≤ 2 →
        |v-1|+g*(d+1:ℕ) ≤ valueTolerance → ∀ b ∈ Icc (0:ℝ) B,
        ∀ lam : Ω → ℝ, Measurable lam → (∀ w, 0 ≤ lam w) →
        (∀ w ∈ E, lam w ∈ Icc lower upper ∧
          |lam w-normalizedPrice d a p0| < delta) → mu.real Eᶜ ≤ badTolerance →
        (∫ w, LowType.binomialPayoff a G k g v b (activeDemand (d+1) b (lam w)) ∂mu)+gap ≤
          referenceUtility d a (normalizedPrice d a p0) 1 p0 := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0,by omega⟩⟩
  have hall (j : Fin d) := finite_lower_route_compact_guard d (j.val+1) hd
    (by omega) (by omega) p0 B lower upper hp0 hp1 hB hlower hprices
  choose gaps deltas values bads hg hdelt hv hb hguard using hall
  let g := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin d)).Nonempty) gaps
  let delta := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin d)).Nonempty) deltas
  let value := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin d)).Nonempty) values
  let bad := Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin d)).Nonempty) bads
  have hpos (f : Fin d → ℝ) (hf : ∀ j, 0 < f j) :
      0 < Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin d)).Nonempty) f :=
    (Finset.lt_inf'_iff _).mpr (fun j _ => hf j)
  refine ⟨g,delta,value,bad,hpos _ hg,hpos _ hdelt,hpos _ hv,hpos _ hb,?_⟩
  intro k hk hkn Ω _ mu _ E hE a ha G base v hbase hv2 hvalue b hbid lam hlam hlam0 hgood hbad
  let j : Fin d := ⟨k-1,by omega⟩
  have hkeq : j.val+1=k := by dsimp [j]; omega
  have hgmin : g ≤ gaps j := Finset.inf'_le _ (Finset.mem_univ j)
  have hdmin : delta ≤ deltas j := Finset.inf'_le _ (Finset.mem_univ j)
  have hvmin : value ≤ values j := Finset.inf'_le _ (Finset.mem_univ j)
  have hbmin : bad ≤ bads j := Finset.inf'_le _ (Finset.mem_univ j)
  have hselected := hguard j (Ω := Ω)
  rw [hkeq] at hselected
  have h := hselected mu E hE a ha G base v hbase hv2 (hvalue.trans hvmin) b hbid lam hlam hlam0
    (fun w hw => ⟨(hgood w hw).1,((hgood w hw).2).trans_le hdmin⟩) (hbad.trans hbmin)
  linarith only [h,hgmin]

end FCAppendix.Exclusive.Narrow.Global
