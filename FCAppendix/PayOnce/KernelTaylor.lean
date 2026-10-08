import FCAppendix.Probability.QuadraticExpectation
import FCAppendix.Probability.ClippedSubGaussianMoments
import FCAppendix.PayOnce.ResponseFactor
import FCAppendix.PayOnce.KernelPriceSlope
import FCAppendix.PayOnce.KernelLawConvergence

namespace FCAppendix.PayOnce.KernelTaylor
open MeasureTheory Set Real CommonList OwnImpact KernelTailEvent KernelLawConvergence
open ResponseFactor Probability

noncomputable def testPriceSlope (n : ℕ) (ψ : ℝ → ℝ) (b T : ℝ) : ℝ :=
  -(deriv ψ (kernel n b T))*sensitivity n b (kernel n b T)

theorem contDiffAt_phi_two {n : ℕ} (hn : 2 ≤ n) {p : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ 2 (RareSuccessSlope.phi n) p := by
  have hnum : ContDiff ℝ 2 (fun q : ℝ => (n:ℝ)*(1-q)^(n-1)*H n q) := by
    unfold H
    fun_prop
  have hden : ContDiff ℝ 2 (Hslope n) := by unfold Hslope; fun_prop
  exact hnum.contDiffAt.div hden.contDiffAt (Hslope_pos hn hp).ne'

theorem contDiffAt_success_two (n : ℕ) (p : ℝ) : ContDiffAt ℝ 2 (success n) p := by
  have hs : ContDiff ℝ 2 (success n) := by unfold success; fun_prop
  exact hs.contDiffAt

theorem exists_kernel_test_taylor {n : ℕ} (hn : 2 ≤ n) (ψ : ℝ → ℝ)
    (hψ : ∀ p ∈ Icc (0:ℝ) 1, ContDiffAt ℝ 2 ψ p)
    {ell : ℝ} (hell : 0 < ell) :
    ∃ A K : ℝ, 0 < A ∧ 0 < K ∧ ∀ b L T : ℝ,
      ell ≤ L → ell ≤ T → kernel n b L ∈ Ioo (0:ℝ) 1 → kernel n b T ∈ Ioo (0:ℝ) 1 →
        |testPriceSlope n ψ b T| ≤ A ∧
        |ψ (kernel n b L)-ψ (kernel n b T)-testPriceSlope n ψ b T*(L-T)| ≤ K*(L-T)^2 := by
  obtain ⟨Aψ,Kψ,hAψ,hKψ,hψder,hψrem⟩ := exists_unit_quadratic_taylor hψ
  have hHC2 : ContDiff ℝ 2 (H n) := by unfold H; fun_prop
  obtain ⟨_,KH,_,hKH,_,hHrem⟩ := exists_unit_quadratic_taylor (fun _ _ => hHC2.contDiffAt)
  let A := Aψ*((n:ℝ)/ell)
  let K := (Kψ+Aψ*(n:ℝ)*KH)*((n:ℝ)/ell)^2
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨A,K,hA,hK,?_⟩
  intro b L T hL hT hiL hiT
  have hLp := hell.trans_le hL
  have hTp := hell.trans_le hT
  have hbmid := (kernel_interior_iff hn hTp).mp hiT
  have hb : 0 < b := hTp.trans hbmid.1
  let p := kernel n b L
  let p₀ := kernel n b T
  have hp : p ∈ Icc (0:ℝ) 1 := ⟨hiL.1.le,hiL.2.le⟩
  have hp₀ : p₀ ∈ Icc (0:ℝ) 1 := ⟨hiT.1.le,hiT.2.le⟩
  have hspos := Hslope_pos hn hp₀
  have hsp := sensitivity_pos hn hb hp₀
  have hsbound : sensitivity n b p₀ ≤ (n:ℝ)/ell := by
    have hh := kernelPriceSlope_bounds hn hTp b
    rw [kernelPriceSlope,indicator_of_mem (show b ∈ Ioo T ((n:ℝ)*T) from hbmid)] at hh
    exact hh.2.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hell hT)
  have hcoef : |testPriceSlope n ψ b T| ≤ A := by
    rw [testPriceSlope,abs_mul,abs_neg,abs_of_pos hsp]
    exact mul_le_mul (hψder p₀ hp₀) hsbound hsp.le hAψ.le
  refine ⟨hcoef,?_⟩
  have hcapL : b*H n p = L := (scalarThreshold_kernel n hn hb hLp).2.2.2.2 hiL.1 hiL.2
  have hcapT : b*H n p₀ = T := (scalarThreshold_kernel n hn hb hTp).2.2.2.2 hiT.1 hiT.2
  have hcapdiff : L-T = b*(H n p-H n p₀) := by rw [← hcapL,← hcapT]; ring
  have hH := hHrem p hp p₀ hp₀
  rw [(hasDerivAt_H n p₀).deriv] at hH
  simp only [neg_mul,sub_neg_eq_add] at hH
  have hinv : 1/Hslope n p₀ ≤ (n:ℝ) := by
    have hh := one_div_le_one_div_of_le (one_div_pos.mpr hnR) (Hslope_bounds hn hp₀).1
    simpa only [one_div_one_div] using hh
  have hdelta : p-p₀+sensitivity n b p₀*(L-T) =
      (H n p-H n p₀+Hslope n p₀*(p-p₀))/Hslope n p₀ := by
    rw [hcapdiff]
    unfold sensitivity
    field_simp [hb.ne',hspos.ne']
    ring
  have hkernel : |p-p₀+sensitivity n b p₀*(L-T)| ≤ (n:ℝ)*KH*(p-p₀)^2 := by
    rw [hdelta,abs_div,abs_of_pos hspos]
    calc
      |H n p-H n p₀+Hslope n p₀*(p-p₀)|/Hslope n p₀ ≤ KH*(p-p₀)^2/Hslope n p₀ :=
        div_le_div_of_nonneg_right hH hspos.le
      _ = (KH*(p-p₀)^2)*(1/Hslope n p₀) := by ring
      _ ≤ (KH*(p-p₀)^2)*(n:ℝ) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hψR := hψrem p hp p₀ hp₀
  have he : ψ p-ψ p₀-testPriceSlope n ψ b T*(L-T) =
      (ψ p-ψ p₀-deriv ψ p₀*(p-p₀))+
        deriv ψ p₀*(p-p₀+sensitivity n b p₀*(L-T)) := by
    unfold testPriceSlope
    change ψ p-ψ p₀-(-deriv ψ p₀*sensitivity n b p₀)*(L-T) = _
    ring
  have htest : |ψ p-ψ p₀-testPriceSlope n ψ b T*(L-T)| ≤
      (Kψ+Aψ*(n:ℝ)*KH)*(p-p₀)^2 := by
    rw [he]
    have hh := (abs_add_le _ _).trans (add_le_add hψR (show
      |deriv ψ p₀*(p-p₀+sensitivity n b p₀*(L-T))| ≤ Aψ*((n:ℝ)*KH*(p-p₀)^2) from by
        rw [abs_mul]
        exact mul_le_mul (hψder p₀ hp₀) hkernel (abs_nonneg _) hAψ.le))
    exact hh.trans_eq (by ring)
  have hpd := kernel_price_difference hn hell hL hT b
  have hpd2 : (p-p₀)^2 ≤ ((n:ℝ)/ell)^2*(L-T)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hpd 2
    simpa only [mul_pow,sq_abs] using hh
  exact htest.trans ((mul_le_mul_of_nonneg_left hpd2 (by positivity)).trans_eq (by dsimp [K]; ring))

theorem measurable_kernel_of_positive_price {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 2 ≤ n) {b : ℝ} (hb : 0 < b) {X : Ω → ℝ}
    (hX : Measurable X) (hXpos : ∀ z, 0 < X z) : Measurable (fun z => kernel n b (X z)) := by
  have he : (fun z => kernel n b (X z)) = (fun z => scalarDemand n hn b hb (X z)) :=
    funext fun z => kernel_eq_scalarDemand hn hb (hXpos z)
  rw [he]
  exact (scalarDemand_continuous n hn b hb).measurable.comp hX

universe u

theorem exists_kernel_test_integral_bound {n : ℕ} (hn : 2 ≤ n) (ψ : ℝ → ℝ)
    (hψ : ∀ p ∈ Icc (0:ℝ) 1, ContDiffAt ℝ 2 ψ p) (hψm : Measurable ψ)
    {B ell u blo bhi : ℝ} (hψB : ∀ p ∈ Icc (0:ℝ) 1, |ψ p| ≤ B)
    (hell : 0 < ell) (hlo : u < blo) (hhi : bhi < (n:ℝ)*ell) :
    ∃ A K : ℝ, 0 < A ∧ 0 < K ∧ ∀ {Ω : Type u} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ), Measurable X →
      (∀ z, X z ∈ Icc ell u) → ∀ b ∈ Icc blo bhi, ∀ T ∈ Icc ell u,
      |(∫ z, ψ (kernel n b (X z)) ∂μ)-ψ (kernel n b T)| ≤
        A*|(∫ z, X z-T ∂μ)|+K*(∫ z, (X z-T)^2 ∂μ) := by
  obtain ⟨A,K,hA,hK,htaylor⟩ := exists_kernel_test_taylor hn ψ hψ hell
  refine ⟨A,K,hA,hK,?_⟩
  intro Ω _ μ _ X hX hXI b hb T hT
  have hbp : 0 < b := (hell.trans_le hT.1).trans ((hT.2.trans_lt hlo).trans_le hb.1)
  have hinterior (L : ℝ) (hL : L ∈ Icc ell u) : kernel n b L ∈ Ioo (0:ℝ) 1 :=
    (kernel_interior_iff hn (hell.trans_le hL.1)).mpr
      ⟨(hL.2.trans_lt hlo).trans_le hb.1,
        hb.2.trans_lt (hhi.trans_le (mul_le_mul_of_nonneg_left hL.1 (Nat.cast_nonneg n)))⟩
  have hXLp : MemLp X 2 μ := memLp_of_bounded (.of_forall hXI) hX.aestronglyMeasurable _
  have hXint : Integrable X μ := hXLp.integrable (by norm_num)
  have hX2 : Integrable (fun z => (X z-T)^2) μ := by
    have hh := (hXLp.sub (memLp_const T)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
    simpa only [Real.norm_eq_abs,sq_abs,Pi.sub_apply] using hh
  have hFX : Integrable (fun z => ψ (kernel n b (X z))) μ := by
    apply Integrable.of_bound (hψm.comp
      (measurable_kernel_of_positive_price hn hbp hX (fun z => hell.trans_le (hXI z).1))).aestronglyMeasurable B
    exact .of_forall fun z => by
      rw [Real.norm_eq_abs]
      exact hψB _ (kernel_bounds hn (hell.trans_le (hXI z).1) b)
  have hh := integral_quadratic_error_le μ X (fun L => ψ (kernel n b L))
    hXint hX2 hFX (fun z => (htaylor b (X z) T (hXI z).1 hT.1 (hinterior _ (hXI z)) (hinterior _ hT)).2)
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_right
    (htaylor b T T hT.1 hT.1 (hinterior _ hT) (hinterior _ hT)).1 (abs_nonneg _)) le_rfl)

theorem abs_integral_sub_le_of_eq_on {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) {B : ℝ}
    (hfB : ∀ z, |f z| ≤ B) (hgB : ∀ z, |g z| ≤ B)
    {E : Set Ω} (hE : MeasurableSet E) (heq : ∀ z ∈ E, f z = g z) :
    |(∫ z, f z ∂μ)-(∫ z, g z ∂μ)| ≤ 2*B*μ.real Eᶜ := by
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable B
    (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hfB z)
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable B
    (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hgB z)
  have hi : Integrable (Eᶜ.indicator (fun _ : Ω => 2*B)) μ := (integrable_const _).indicator hE.compl
  have hb (z : Ω) : |f z-g z| ≤ Eᶜ.indicator (fun _ : Ω => 2*B) z := by
    by_cases hz : z ∈ E
    · simp [heq z hz,hz]
    · rw [indicator_of_mem (show z ∈ Eᶜ from hz)]
      exact (abs_sub _ _).trans (by linarith [hfB z,hgB z])
  have hh := (abs_integral_le_integral_abs (f := fun z => f z-g z)).trans
    (integral_mono (hfi.sub hgi).abs hi hb)
  rw [integral_sub hfi hgi,integral_indicator hE.compl,setIntegral_const,smul_eq_mul] at hh
  nlinarith

theorem exists_clipped_kernel_test_integral_bound {n : ℕ} (hn : 2 ≤ n) (ψ : ℝ → ℝ)
    (hψ : ∀ p ∈ Icc (0:ℝ) 1, ContDiffAt ℝ 2 ψ p) (hψm : Measurable ψ)
    {B ell u blo bhi : ℝ} (hψB : ∀ p ∈ Icc (0:ℝ) 1, |ψ p| ≤ B)
    (hell : 0 < ell) (hlo : u < blo) (hhi : bhi < (n:ℝ)*ell) :
    ∃ A K : ℝ, 0 < A ∧ 0 < K ∧ ∀ {Ω : Type u} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ), Measurable X →
      (∀ z, 0 < X z) → ∀ b ∈ Icc blo bhi, ∀ T ∈ Icc ell u,
      |(∫ z, ψ (kernel n b (X z)) ∂μ)-ψ (kernel n b T)| ≤
        2*B*μ.real {z | X z ∉ Icc ell u}+
        A*|(∫ z, clipToInterval ell u (X z)-T ∂μ)|+
        K*(∫ z, (clipToInterval ell u (X z)-T)^2 ∂μ) := by
  obtain ⟨A,K,hA,hK,hint⟩ := exists_kernel_test_integral_bound hn ψ hψ hψm hψB hell hlo hhi
  refine ⟨A,K,hA,hK,?_⟩
  intro Ω _ μ _ X hX hXpos b hb T hT
  have hellu : ell ≤ u := hT.1.trans hT.2
  have hbp : 0 < b := (hell.trans_le hT.1).trans ((hT.2.trans_lt hlo).trans_le hb.1)
  let Y := fun z => clipToInterval ell u (X z)
  have hY : Measurable Y := (measurable_clipToInterval ell u).comp hX
  have hYI (z : Ω) : Y z ∈ Icc ell u := clipToInterval_mem hellu _
  have hYpos (z : Ω) : 0 < Y z := hell.trans_le (hYI z).1
  have hE : MeasurableSet {z | X z ∈ Icc ell u} := hX measurableSet_Icc
  have hcompare := abs_integral_sub_le_of_eq_on μ
    (hψm.comp (measurable_kernel_of_positive_price hn hbp hX hXpos))
    (hψm.comp (measurable_kernel_of_positive_price hn hbp hY hYpos))
    (fun z => hψB _ (kernel_bounds hn (hXpos z) b))
    (fun z => hψB _ (kernel_bounds hn (hYpos z) b)) hE (by
      intro z hz
      change ψ (kernel n b (X z)) = ψ (kernel n b (Y z))
      have hy : Y z = X z := by
        simp only [Y,clipToInterval,min_eq_right hz.2,max_eq_right hz.1]
      rw [hy])
  have hTaylor := hint μ Y hY hYI b hb T hT
  have hh := (abs_sub_le (∫ z, ψ (kernel n b (X z)) ∂μ)
    (∫ z, ψ (kernel n b (Y z)) ∂μ) (ψ (kernel n b T))).trans (add_le_add hcompare hTaylor)
  change |(∫ z, ψ (kernel n b (X z)) ∂μ)-ψ (kernel n b T)| ≤
    2*B*μ.real {z | X z ∈ Icc ell u}ᶜ +
      A*|(∫ z, Y z-T ∂μ)|+K*(∫ z, (Y z-T)^2 ∂μ)
  exact hh.trans_eq (by ring)

end FCAppendix.PayOnce.KernelTaylor
