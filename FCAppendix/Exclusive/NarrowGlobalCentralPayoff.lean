import FCAppendix.Exclusive.NarrowGlobalGuardsTransport

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open MeasureTheory ProbabilityTheory Set Filter

theorem tariff_charge_le_count (a : UserTariff) (ha : a.Allowed) (r : ℕ) :
    a.charge r ≤ (r : ℝ) := by
  cases a with
  | unique =>
    dsimp [UserTariff.charge]
    split_ifs with hr
    · simp [hr]
    · positivity
  | affine eta =>
    by_cases hr : r = 0
    · simp [hr]
    · have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr (by omega)
      have hm := mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hr1)
      simp only [UserTariff.charge, successIndicator, if_neg hr]
      nlinarith

theorem binomialPayoff_lower_bound (n k : ℕ) (_hk : 1 ≤ k) (hkn : k ≤ n)
    (a : UserTariff) (ha : a.Allowed) (G : Schedule n) (g v b B p : ℝ)
    (hg : 0 ≤ g) (hv : 0 ≤ v) (hb : b ∈ Icc (0 : ℝ) B)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    -(B+g)*(n : ℝ) ≤ LowType.binomialPayoff a G k g v b p := by
  have hT : binomialPolynomial k a.charge p ≤ n := by
    rw [binomialPolynomial_eq_expect _ _ _ hp.1 hp.2]
    calc
      _ ≤ (IndependentCounts.binomial k p hp.1 hp.2).expect (fun r => (r.val : ℝ)) :=
        FiniteLaw.expect_mono _ fun r => tariff_charge_le_count a ha r.val
      _ ≤ (IndependentCounts.binomial k p hp.1 hp.2).expect (fun _ => (n : ℝ)) :=
        FiniteLaw.expect_mono _ fun r => Nat.cast_le.mpr (by have := r.isLt; omega)
      _ = n := FiniteLaw.expect_const _ _
  have hT0 : 0 ≤ binomialPolynomial k a.charge p := by
    rw [binomialPolynomial_eq_expect _ _ _ hp.1 hp.2]
    exact FiniteLaw.expect_nonneg _ (fun r => a.charge_nonneg ha r.val)
  have hG : binomialPolynomial k G.charge p ≤ n := by
    rw [binomialPolynomial_eq_expect _ _ _ hp.1 hp.2]
    apply le_trans ((IndependentCounts.binomial k p hp.1 hp.2).expect_mono
      (fun r => G.upper r.val (by have := r.isLt; omega)))
    calc
      _ ≤ (IndependentCounts.binomial k p hp.1 hp.2).expect (fun _ => (n : ℝ)) :=
        FiniteLaw.expect_mono _ fun r => Nat.cast_le.mpr (by have := r.isLt; omega)
      _ = n := FiniteLaw.expect_const _ _
  have hS : 0 ≤ PayOnce.success k p := by
    simpa only [IndependentCounts.binomial_success, PayOnce.success] using
      (IndependentCounts.binomial k p hp.1 hp.2).success_nonneg
  have hbid := mul_le_mul hb.2 hT hT0 (hb.1.trans hb.2)
  have hbase := mul_le_mul_of_nonneg_left hG hg
  have hval := mul_nonneg hv hS
  dsimp [LowType.binomialPayoff]
  nlinarith only [hbid, hbase, hval]

theorem integral_lower_of_good_event {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : Set Ω) (hE : MeasurableSet E)
    (f : Ω → ℝ) (hf : Integrable f mu) (reference error lower : ℝ)
    (hglobal : ∀ᵐ w ∂mu, -lower ≤ f w)
    (hgood : ∀ᵐ w ∂mu, w ∈ E → reference-error ≤ f w) :
    reference-error-(reference-error+lower)*mu.real Eᶜ ≤ ∫ w, f w ∂mu := by
  have hi := (integrable_const (μ := mu) (reference-error)).sub
    ((integrable_const (reference-error+lower)).indicator hE.compl)
  have hm := integral_mono_ae hi hf (by
    filter_upwards [hglobal, hgood] with w hw hg
    change reference-error-Eᶜ.indicator (fun _ => reference-error+lower) w ≤ f w
    by_cases he : w ∈ E
    · rw [indicator_of_notMem (show w ∉ Eᶜ from fun h => h he), sub_zero]
      exact hg he
    · rw [indicator_of_mem (show w ∈ Eᶜ from he)]
      linarith)
  change (∫ x, reference-error-Eᶜ.indicator (fun _ => reference-error+lower) x ∂mu) ≤ _ at hm
  rw [integral_sub (integrable_const _) ((integrable_const _).indicator hE.compl),
    integral_const, probReal_univ, one_smul, integral_indicator_const _ hE.compl,
    smul_eq_mul] at hm
  simpa only [mul_comm] using hm

theorem integral_central_payoff_lower (n : ℕ) (hn : 2 ≤ n)
    (lower upper B eps : ℝ) (hlower : 0 < lower) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (mu : Measure Ω) [IsProbabilityMeasure mu] (E : Set Ω), MeasurableSet E →
      ∀ a : UserTariff, a.Allowed → ∀ G : Schedule n,
      ∀ g v : ℝ, 0 ≤ g → 0 ≤ v → ∀ b ∈ Icc (0 : ℝ) B,
      ∀ ref ∈ Icc lower upper, ∀ lam : Ω → ℝ, Measurable lam → (∀ w, 0 ≤ lam w) →
      (∀ w ∈ E, lam w ∈ Icc lower upper ∧ |lam w-ref| < delta) →
      pricedPayoff n n a b ref ≤
        (∫ w, LowType.binomialPayoff a G n g v b (activeDemand n b (lam w)) ∂mu)+
          eps+|v-1|+g*n+(1+(B+g)*n)*mu.real Eᶜ := by
  obtain ⟨delta, hdelta, hmod⟩ := binomialPayoff_uniform_compact_transport n n hn le_rfl
    lower upper B eps hlower heps
  refine ⟨delta, hdelta, ?_⟩
  intro Ω _ mu _ E hE a ha G g v hg hv b hb ref href lam hlam hlam0 hgood
  let p : Ω → ℝ := fun w => activeDemand n b (lam w)
  let f : Ω → ℝ := fun w => LowType.binomialPayoff a G n g v b (p w)
  let refpay := pricedPayoff n n a b ref
  let error := eps+|v-1|+g*n
  have hp : Measurable p := (measurable_activeDemand n hn).comp (measurable_const.prodMk hlam)
  have hpbound : ∀ w, p w ∈ Icc (0 : ℝ) 1 := fun w => activeDemand_bounds n b (lam w) (hlam0 w)
  have hf : Integrable f mu := LowType.integrable_binomialPayoff mu a G n g v b p hp hpbound
  have hi := integral_lower_of_good_event mu E hE f hf refpay error ((B+g)*n)
    (Eventually.of_forall fun w => by
      simpa only [neg_mul] using binomialPayoff_lower_bound n n (by omega) le_rfl a ha G
        g v b B (p w) hg hv hb (hpbound w))
    (Eventually.of_forall fun w hw => by
      have hx := (abs_lt.mp (hmod a ha G g v hg b hb (lam w) (hgood w hw).1
        ref href (hgood w hw).2)).1
      dsimp [f, p, refpay, error]
      linarith)
  have hrefUpper : refpay ≤ 1 := by
    have hpr := menuMarginal_bounds n b ref (hlower.trans_le href.1)
    have hS : PayOnce.success n (menuMarginal n b ref) ≤ 1 := PayOnce.success_le_one n _ hpr.2
    have hT : 0 ≤ binomialPolynomial n a.charge (menuMarginal n b ref) := by
      rw [binomialPolynomial_eq_expect _ _ _ hpr.1 hpr.2]
      exact FiniteLaw.expect_nonneg _ fun r => a.charge_nonneg ha r.val
    dsimp [refpay, pricedPayoff]
    nlinarith [mul_nonneg hb.1 hT]
  have hbudget : 0 ≤ error := by dsimp [error]; positivity
  have hm := mul_le_mul_of_nonneg_right
    (show refpay-error+(B+g)*n ≤ 1+(B+g)*n by linarith) (measureReal_nonneg (μ := mu) (s := Eᶜ))
  dsimp only [refpay, error, f, p] at hi hm ⊢
  linarith

end FCAppendix.Exclusive.Narrow.Global
