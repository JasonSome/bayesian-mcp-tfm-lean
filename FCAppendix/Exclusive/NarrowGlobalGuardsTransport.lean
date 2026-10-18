import FCAppendix.Exclusive.NarrowGlobalGuardsUniform
import FCAppendix.Exclusive.NarrowGlobalGuardsPrice

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open Set MeasureTheory ProbabilityTheory Filter

def menuMarginal (n : ℕ) (b lam : ℝ) : ℝ := demand n (max b lam) lam

lemma menuMarginal_eq_activeDemand (n : ℕ) (hn : 2 ≤ n) (b lam : ℝ)
    (hlam : 0 < lam) : menuMarginal n b lam = activeDemand n b lam := by
  by_cases hb : 0 < b
  · by_cases hbl : lam ≤ b
    · simp only [menuMarginal,max_eq_left hbl,activeDemand,if_pos hb]
    · have hle : b ≤ lam := (lt_of_not_ge hbl).le
      rw [menuMarginal,max_eq_right hle,activeDemand,if_pos hb,
        (demand_eq_zero_iff n hn hb hlam.le).mpr hle]
      exact (demand_eq_zero_iff n hn hlam hlam.le).mpr le_rfl
  · have hle : b ≤ lam := (le_of_not_gt hb).trans hlam.le
    rw [menuMarginal,max_eq_right hle,activeDemand,if_neg hb]
    exact (demand_eq_zero_iff n hn hlam hlam.le).mpr le_rfl

lemma menuMarginal_bounds (n : ℕ) (b lam : ℝ) (hlam : 0 < lam) :
    menuMarginal n b lam ∈ Icc (0:ℝ) 1 :=
  ⟨demand_nonneg _ _ _,demand_le_one n (hlam.trans_le (le_max_right _ _)) hlam.le⟩

lemma continuousOn_menuMarginal (n : ℕ) (hn : 2 ≤ n) :
    ContinuousOn (fun x : ℝ × ℝ => menuMarginal n x.1 x.2) {x | 0 < x.2} := by
  intro x hx
  have hden : max x.1 x.2 ≠ 0 := (hx.trans_le (le_max_right _ _)).ne'
  have hq : ContinuousAt (fun y : ℝ × ℝ => y.2 / max y.1 y.2) x :=
    continuous_snd.continuousAt.div
      (continuous_fst.max continuous_snd).continuousAt hden
  have hr : ContinuousAt (fun y : ℝ × ℝ => (y.2/max y.1 y.2)^rate n) x :=
    (Real.continuous_rpow_const (rate_pos n hn).le).continuousAt.comp hq
  have hc : ContinuousAt (fun y : ℝ×ℝ => max 0 (1-(y.2/max y.1 y.2)^rate n)) x :=
    continuousAt_const.max (continuousAt_const.sub hr)
  exact hc.continuousWithinAt

def pricedPayoff (n k : ℕ) (a : UserTariff) (b lam : ℝ) : ℝ :=
  PayOnce.success k (menuMarginal n b lam)-
    b*binomialPolynomial k a.charge (menuMarginal n b lam)

lemma continuousOn_pricedPayoff (n k : ℕ) (hn : 2 ≤ n) (a : UserTariff) :
    ContinuousOn (fun x : ℝ × ℝ => pricedPayoff n k a x.1 x.2) {x | 0 < x.2} := by
  have hp := continuousOn_menuMarginal n hn
  have hf : Continuous (binomialPolynomial k a.charge) :=
    continuous_iff_continuousAt.mpr fun p => (hasDerivAt_binomialPolynomial k a.charge p).continuousAt
  unfold pricedPayoff PayOnce.success
  exact (continuousOn_const.sub ((continuousOn_const.sub hp).pow _)).sub
    (continuous_fst.continuousOn.mul (hf.comp_continuousOn hp))

lemma pricedPayoff_affine (n k : ℕ) (eta b lam : ℝ) (hlam : 0 < lam) :
    pricedPayoff n k (.affine eta) b lam =
      (1-eta)*pricedPayoff n k (.affine 0) b lam+
        eta*pricedPayoff n k (.affine 1) b lam := by
  obtain ⟨hp0,hp1⟩ := menuMarginal_bounds n b lam hlam
  unfold pricedPayoff
  rw [binomialPolynomial_eq_expect _ _ _ hp0 hp1,
    binomialPolynomial_eq_expect _ _ _ hp0 hp1,
    binomialPolynomial_eq_expect _ _ _ hp0 hp1]
  change _-b*(UserTariff.affine eta).expected _ =
    (1-eta)*(_-b*(UserTariff.affine 0).expected _)+
      eta*(_-b*(UserTariff.affine 1).expected _)
  rw [UserTariff.expected_affine,UserTariff.expected_affine,UserTariff.expected_affine]
  ring

lemma pricedPayoff_compact_modulus (n k : ℕ) (hn : 2 ≤ n)
    (a : UserTariff) (lower upper B eps : ℝ) (hlower : 0 < lower) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ b ∈ Icc (0:ℝ) B,
      ∀ lam ∈ Icc lower upper, ∀ ref ∈ Icc lower upper,
      |lam-ref| < delta → |pricedPayoff n k a b lam-pricedPayoff n k a b ref| < eps := by
  let K : Set (ℝ×ℝ) := Icc (0:ℝ) B ×ˢ Icc lower upper
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun x : ℝ×ℝ => pricedPayoff n k a x.1 x.2) K :=
    (continuousOn_pricedPayoff n k hn a).mono (fun _ hx => hlower.trans_le hx.2.1)
  obtain ⟨delta,hdelta,hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hc) eps heps
  refine ⟨delta,hdelta,?_⟩
  intro b hb lam hlam ref href hd
  have hh := hmod (b,lam) ⟨hb,hlam⟩ (b,ref) ⟨hb,href⟩
  simpa only [Prod.dist_eq,dist_self,Real.dist_eq,max_eq_right (abs_nonneg (lam-ref))] using hh (by
    simpa only [Prod.dist_eq,dist_self,Real.dist_eq,max_eq_right (abs_nonneg (lam-ref))] using hd)

theorem pricedPayoff_uniform_compact_modulus (n k : ℕ) (hn : 2 ≤ n)
    (lower upper B eps : ℝ) (hlower : 0 < lower) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ a : UserTariff, a.Allowed → ∀ b ∈ Icc (0:ℝ) B,
      ∀ lam ∈ Icc lower upper, ∀ ref ∈ Icc lower upper,
      |lam-ref| < delta → |pricedPayoff n k a b lam-pricedPayoff n k a b ref| < eps := by
  obtain ⟨du,hdu,hmu⟩ := pricedPayoff_compact_modulus n k hn .unique lower upper B eps hlower heps
  obtain ⟨d0,hd0,hm0⟩ := pricedPayoff_compact_modulus n k hn (.affine 0) lower upper B eps hlower heps
  obtain ⟨d1,hd1,hm1⟩ := pricedPayoff_compact_modulus n k hn (.affine 1) lower upper B eps hlower heps
  refine ⟨min du (min d0 d1),lt_min hdu (lt_min hd0 hd1),?_⟩
  intro a ha b hb lam hlam ref href hd
  have hu := hmu b hb lam hlam ref href (hd.trans_le (min_le_left _ _))
  have h0 := hm0 b hb lam hlam ref href
    (hd.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have h1 := hm1 b hb lam hlam ref href
    (hd.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  cases a with
  | unique => exact hu
  | affine eta =>
    rw [pricedPayoff_affine n k eta b lam (hlower.trans_le hlam.1),
      pricedPayoff_affine n k eta b ref (hlower.trans_le href.1)]
    have h0' := abs_lt.mp h0
    have h1' := abs_lt.mp h1
    have ha0 := ha.1
    have ha1 := sub_nonneg.mpr ha.2
    by_cases he : eta = 1
    · simpa only [he,sub_self,zero_mul,one_mul,zero_add] using h1
    · have heta : 0 < 1-eta := sub_pos.mpr (lt_of_le_of_ne ha.2 he)
      have hlo := add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left h0'.1 heta)
        (mul_le_mul_of_nonneg_left h1'.1.le ha0)
      have hhi := add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left h0'.2 heta)
        (mul_le_mul_of_nonneg_left h1'.2.le ha0)
      apply abs_lt.mpr
      constructor <;> nlinarith only [hlo,hhi]

theorem binomialPayoff_value_base_error (n k : ℕ) (hkn : k ≤ n)
    (a : UserTariff) (G : Schedule n) (g v b p : ℝ) (hg : 0 ≤ g)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |LowType.binomialPayoff a G k g v b p-
      (PayOnce.success k p-b*binomialPolynomial k a.charge p)| ≤ |v-1|+g*n := by
  let mu := IndependentCounts.binomial k p hp0 hp1
  have hS0 : 0 ≤ PayOnce.success k p := by simpa only [mu,IndependentCounts.binomial_success,PayOnce.success] using mu.success_nonneg
  have hS1 : PayOnce.success k p ≤ 1 := by simpa only [mu,IndependentCounts.binomial_success,PayOnce.success] using mu.success_le_one
  have hG0 : 0 ≤ binomialPolynomial k G.charge p := by
    rw [binomialPolynomial_eq_expect _ _ _ hp0 hp1]
    exact mu.expect_nonneg fun r => G.nonneg r.val (by have := r.isLt; omega)
  have hG1 : binomialPolynomial k G.charge p ≤ n := by
    rw [binomialPolynomial_eq_expect _ _ _ hp0 hp1]
    apply le_trans (mu.expect_mono (fun r => G.upper r.val (by omega)))
    rw [← mu.expect_const (n:ℝ)]
    exact mu.expect_mono (fun r => Nat.cast_le.mpr (by omega))
  have he : LowType.binomialPayoff a G k g v b p-
      (PayOnce.success k p-b*binomialPolynomial k a.charge p) =
      (v-1)*PayOnce.success k p-g*binomialPolynomial k G.charge p := by
    unfold LowType.binomialPayoff
    ring
  rw [he]
  calc
    |(v-1)*PayOnce.success k p-g*binomialPolynomial k G.charge p| ≤
        |(v-1)*PayOnce.success k p|+|g*binomialPolynomial k G.charge p| := abs_sub _ _
    _ = |v-1| * PayOnce.success k p+g*binomialPolynomial k G.charge p := by
      rw [abs_mul,abs_of_nonneg hS0,abs_of_nonneg (mul_nonneg hg hG0)]
    _ ≤ |v-1|+g*n := add_le_add (by nlinarith [abs_nonneg (v-1)])
      (mul_le_mul_of_nonneg_left hG1 hg)

theorem binomialPayoff_uniform_compact_transport (n k : ℕ) (hn : 2 ≤ n)
    (hkn : k ≤ n) (lower upper B eps : ℝ) (hlower : 0 < lower) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ a : UserTariff, a.Allowed → ∀ G : Schedule n,
      ∀ g v : ℝ, 0 ≤ g → ∀ b ∈ Icc (0:ℝ) B,
      ∀ lam ∈ Icc lower upper, ∀ ref ∈ Icc lower upper,
      |lam-ref| < delta →
      |LowType.binomialPayoff a G k g v b (activeDemand n b lam)-
        pricedPayoff n k a b ref| < eps+|v-1|+g*n := by
  obtain ⟨delta,hdelta,hmod⟩ := pricedPayoff_uniform_compact_modulus n k hn
    lower upper B eps hlower heps
  refine ⟨delta,hdelta,?_⟩
  intro a ha G g v hg b hb lam hlam ref href hd
  have hp := menuMarginal_bounds n b lam (hlower.trans_le hlam.1)
  have he := binomialPayoff_value_base_error n k hkn a G g v b
    (menuMarginal n b lam) hg hp.1 hp.2
  have hm := hmod a ha b hb lam hlam ref href hd
  rw [← menuMarginal_eq_activeDemand n hn b lam (hlower.trans_le hlam.1)]
  change |LowType.binomialPayoff a G k g v b (menuMarginal n b lam)-
    pricedPayoff n k a b lam| ≤ _ at he
  calc
    |LowType.binomialPayoff a G k g v b (menuMarginal n b lam)-pricedPayoff n k a b ref| ≤
        |LowType.binomialPayoff a G k g v b (menuMarginal n b lam)-pricedPayoff n k a b lam|+
          |pricedPayoff n k a b lam-pricedPayoff n k a b ref| := abs_sub_le _ _ _
    _ < (|v-1|+g*n)+eps := add_lt_add_of_le_of_lt he hm
    _ = eps+|v-1|+g*n := by ring

theorem integral_binomialPayoff_compact_transport (n k : ℕ) (hn : 2 ≤ n)
    (hkn : k ≤ n) (lower upper B eps : ℝ) (hlower : 0 < lower) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (mu : Measure Ω) [IsProbabilityMeasure mu] (E : Set Ω), MeasurableSet E →
      ∀ a : UserTariff, a.Allowed → ∀ G : Schedule n,
      ∀ g v V : ℝ, 0 ≤ g → 0 ≤ V → v ≤ V → ∀ b ∈ Icc (0:ℝ) B,
      ∀ ref ∈ Icc lower upper, ∀ lam : Ω → ℝ, Measurable lam → (∀ w, 0 ≤ lam w) →
      (∀ w ∈ E, lam w ∈ Icc lower upper ∧ |lam w-ref| < delta) →
      let C := pricedPayoff n k a b ref+eps+|v-1|+g*n
      (∫ w, LowType.binomialPayoff a G k g v b (activeDemand n b (lam w)) ∂mu) ≤
        C+(V-C)*mu.real Eᶜ := by
  obtain ⟨delta,hdelta,hmod⟩ := binomialPayoff_uniform_compact_transport n k hn hkn
    lower upper B eps hlower heps
  refine ⟨delta,hdelta,?_⟩
  intro Ω _ mu _ E hE a ha G g v V hg hV hv b hb ref href lam hlam hlam0 hgood
  let p : Ω → ℝ := fun w => activeDemand n b (lam w)
  let u : Ω → ℝ := fun w => LowType.binomialPayoff a G k g v b (p w)
  let C := pricedPayoff n k a b ref+eps+|v-1|+g*n
  have hp : Measurable p := (measurable_activeDemand n hn).comp (measurable_const.prodMk hlam)
  have hprange : ∀ w, p w ∈ Icc (0:ℝ) 1 := fun w => activeDemand_bounds n b (lam w) (hlam0 w)
  have hu : Integrable u mu := LowType.integrable_binomialPayoff mu a G k g v b p hp hprange
  have hbound := LowType.integral_upper_of_good_event mu E hE u hu V (-C)
    (Eventually.of_forall fun w => LowType.payoff_le_low_upper a ha G hkn hg hb.1
      (hprange w).1 (hprange w).2 hV (by linarith))
    (Eventually.of_forall fun w hw => by
      have h := hmod a ha G g v hg b hb (lam w) (hgood w hw).1 ref href (hgood w hw).2
      have hh := (abs_lt.mp h).2
      change u w ≤ - -C
      dsimp [u,p,C]
      linarith)
  rw [probReal_compl_eq_one_sub hE]
  change (∫ w, u w ∂mu) ≤ C+(V-C)*(1-mu.real E)
  linarith only [hbound]

end FCAppendix.Exclusive.Narrow.Global
