import FCAppendix.Affine.Uniform06.RawArrayRareBounds

noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceCoarseAsymptotics

open MeasureTheory Set Filter LowBody
open scoped Topology BigOperators
open MixedIntervalLLT MixedProductCharacteristic
open Uniform07 RawMixedSource RawTiltedSource SourceCoarseIntegral
open RawArrayRareBounds LiteralExperiment

theorem finite_coarse_algebra {N A D θ Θ bad K c a d CT RT M1 M2 P : ℝ}
    (hN : 1 ≤ N) (ha : 0 < a) (hd : 0 < d) (hc : 0 < c) (hK : 0 < K)
    (hA : a*N ≤ A) (hD0 : 0 < D) (hD : D ≤ d*N) (hθ : θ ≤ Θ)
    (_hb0 : 0 ≤ bad) (hb : bad ≤ 1/N^3) (hNc : 2 ≤ c*N^2)
    (hm1 : M1 ≤ K/N) (hm2 : M2 ≤ K/N) (hw : c/N ≤ P)
    (hC : CT ≤ M1/A+bad) (hR : RT ≤ M2/A^2+bad)
    (hL : Real.exp (-2*θ)/D*(P-bad) ≤ CT) :
    (Real.exp (-2*Θ)*c/(2*d))/N^2 ≤ CT ∧
    CT ≤ (K/a+1)/N^2 ∧ RT ≤ (K/a^2+1)/N^3 := by
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have han : 0 < a*N := mul_pos ha hn
  have hAp : 0 < A := han.trans_le hA
  have hdn : 0 < d*N := mul_pos hd hn
  have hbwin : bad ≤ c/(2*N) := by
    apply hb.trans
    apply (div_le_div_iff₀ (pow_pos hn 3) (by positivity : 0 < 2*N)).mpr
    have hh := mul_le_mul_of_nonneg_right hNc hn.le
    nlinarith
  have hwin : c/(2*N) ≤ P-bad := by
    have he : c/N-c/(2*N)=c/(2*N) := by ring
    rw [← he]
    exact sub_le_sub hw hbwin
  have hw0 : 0 ≤ P-bad := (div_pos hc (by positivity)).le.trans hwin
  have hexp : Real.exp (-2*Θ) ≤ Real.exp (-2*θ) := Real.exp_le_exp.mpr (by linarith)
  have hcoeff : Real.exp (-2*Θ)/(d*N) ≤ Real.exp (-2*θ)/D :=
    (div_le_div_of_nonneg_left (Real.exp_pos _).le hD0 hD).trans
      (div_le_div_of_nonneg_right hexp hD0.le)
  have hlower := mul_le_mul hcoeff hwin (div_pos hc (by positivity)).le
    (div_nonneg (Real.exp_pos _).le hD0.le)
  have hlower' : (Real.exp (-2*Θ)*c/(2*d))/N^2 ≤ CT := by
    convert! hlower.trans hL using 1
    field_simp [hn.ne',hd.ne']
  have hM1A : M1/A ≤ K/(a*N^2) := by
    calc
      _ ≤ (K/N)/A := div_le_div_of_nonneg_right hm1 hAp.le
      _ ≤ (K/N)/(a*N) := div_le_div_of_nonneg_left (div_pos hK hn).le han hA
      _ = _ := by field_simp [ha.ne',hn.ne']
  have hM2A : M2/A^2 ≤ K/(a^2*N^3) := by
    calc
      _ ≤ (K/N)/A^2 := div_le_div_of_nonneg_right hm2 (sq_nonneg A)
      _ ≤ (K/N)/(a*N)^2 := div_le_div_of_nonneg_left (div_pos hK hn).le
        (sq_pos_of_pos han) (by nlinarith [sq_nonneg (A-a*N)])
      _ = _ := by field_simp [ha.ne',hn.ne']
  have hb2 : bad ≤ 1/N^2 := by
    apply hb.trans
    apply div_le_div_of_nonneg_left (by norm_num : 0 ≤ (1:ℝ)) (sq_pos_of_pos hn)
    have hh := mul_le_mul_of_nonneg_left hN (sq_nonneg N)
    nlinarith
  refine ⟨hlower',?_,?_⟩
  · have hh := hC.trans (add_le_add hM1A hb2)
    convert! hh using 1
    field_simp [ha.ne',hn.ne']
  · have hh := hR.trans (add_le_add hM2A hb)
    convert! hh using 1
    field_simp [ha.ne',hn.ne']

theorem source_tests_eq (i : Row) (A : CenteredArray RowRival)
    (G : ℕ → Measure (ℝ × ℝ)) (m : ℕ → ℕ) (b θ : ℕ → ℝ)
    (hN : ∀ n,A.N n=m n-1)
    (hlaw : ∀ n,A.law n=tiltedSource i (G n) (b n) (θ n))
    (hY : ∀ n,A.Y n=RawTiltedSource.integerSign) (n k : ℕ) (a : ℝ) :
    moment A (fun n => demand (xi i) (b n)) (fun n => (capacity (m n):ℝ)) θ a k n=
      tiltedMoment i (m n) (G n) (b n) (θ n) a k ∧
    window A (fun n => demand (xi i) (b n)) (fun n => (capacity (m n):ℝ)) n=
      equalWindow i (m n) (G n) (b n) (θ n) := by
  rw [RawArrayRareBounds.moment,RawArrayRareBounds.window,hN n,hlaw n,hY n]
  exact ⟨rfl,rfl⟩

theorem source_coarse_from_actual_array (i : Row) (A : CenteredArray RowRival)
    (hgap : A.CompactGap)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (m : ℕ → ℕ) (b θ r : ℕ → ℝ)
    (g : ℕ → GuardData) (cm : (n : ℕ) → (Fin (m n-1) → Fin 4) → ℝ)
    (hN : ∀ n,A.N n=m n-1)
    (hlaw : ∀ n,A.law n=tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))
    (hY : ∀ n,A.Y n=RawTiltedSource.integerSign)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b n) x-r n)
    (hshift : Tendsto (fun n => A.d n*((capacity (m n):ℝ)-(A.N n:ℝ)*r n)) atTop (𝓝 0))
    {θ0 Θ lo s ε q a d : ℝ} (hθlim : Tendsto θ atTop (𝓝 θ0)) (hθ0 : 0 < θ0)
    (hlo : 0 < lo) (hε : 0 < ε) (hq : 0 < q) (ha : 0 < a) (hd : 0 < d)
    (hscalar : ∀ᶠ n in atTop,
      2 ≤ m n ∧ 0 < b n ∧ 0 < θ n ∧ θ n ≤ Θ ∧
      0 < (g n).margin ∧ 0 < (g n).population ∧ 0 < (g n).requiredDemand ∧
      entry i-cutoff i/200 ≤ (g n).multiplier ∧ (g n).radius ≤ cutoff i/100 ∧
      0 < (g n).multiplier-(g n).radius ∧ lo < b n ∧ b n < s ∧ b n ≤ (g n).multiplier ∧
      b n ≤ ReceiptGap.cap i ∧
      (∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2 ≤ ReceiptGap.cap i) ∧
      (1-xi i)*ReceiptGap.cap i ≤ lo ∧
      ε*((m n-1:ℕ):ℝ)+2 < ((m n-1:ℕ):ℝ)*(rho-TiltedGood.upperProbability i (G n:Measure (ℝ × ℝ)) (b n) (θ n)) ∧
      2*ε*((m n-1:ℕ):ℝ)+3 ≤ ((m n-1:ℕ):ℝ)*(TiltedGood.lowerProbability i (G n:Measure (ℝ × ℝ)) (b n) (θ n)-
        (rho-TiltedGood.upperProbability i (G n:Measure (ℝ × ℝ)) (b n) (θ n))) ∧
      q ≤ (TiltedGood.law i (G n:Measure (ℝ × ℝ)) (b n) (θ n)).real
        (CostAmplification.activeStrip s (ReceiptGap.cap i)) ∧
      12*ε ≤ q ∧ 4 ≤ q*((m n-1:ℕ):ℝ) ∧
      2/((b n-lo)*(q*((m n-1:ℕ):ℝ)/2)/(xi i*ReceiptGap.cap i)) < (b n-lo)/(xi i*b n) ∧
      a*((m n-1:ℕ):ℝ) ≤ (b n-lo)*(q*((m n-1:ℕ):ℝ)/2)/(xi i*ReceiptGap.cap i) ∧
      1+b n*(m n:ℝ)/lo ≤ d*((m n-1:ℕ):ℝ)) :
    ∃ cC UC UR : ℝ,0 < cC ∧ 0 < UC ∧ 0 < UR ∧ ∀ᶠ n in atTop,
      let I := ExactUntilting.cost (source i (G n:Measure (ℝ × ℝ)))
        (demand (xi i) (b n)) (θ n) (capacity (m n)) (m n-1)
      let C := sourceCanonicalMarginal i (m n) (G n:Measure (ℝ × ℝ)) (g n) (cm n) (b n)
      let R := sourceCanonicalDuplicate i (m n) (G n:Measure (ℝ × ℝ)) (g n) (cm n) (b n)
      cC*Real.exp (-I)/((m n-1:ℕ):ℝ)^2 ≤ C ∧
      C ≤ UC*Real.exp (-I)/((m n-1:ℕ):ℝ)^2 ∧
      R ≤ UR*Real.exp (-I)/((m n-1:ℕ):ℝ)^3 ∧
      0 < C ∧ 0 ≤ R/C ∧ R/C ≤ (UR/cC)/((m n-1:ℕ):ℝ) := by
  obtain ⟨K,c,hK,hc,hrare⟩ := actual_moment_and_window_bounds A hgap
    (fun n => demand (xi i) (b n)) r (fun n => (capacity (m n):ℝ)) θ
    hcenter hshift hθlim hθ0 (receiptGap_pos i)
  let cC := Real.exp (-2*Θ)*c/(2*d)
  let UC := K/a+1
  let UR := K/a^2+1
  have hcC : 0 < cC := by dsimp [cC]; positivity
  have hUC : 0 < UC := by dsimp [UC]; positivity
  have hUR : 0 < UR := by dsimp [UR]; positivity
  have hreal : Tendsto (fun n => (A.N n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp A.market
  have hlarge : ∀ᶠ n in atTop,1 ≤ (A.N n:ℝ) ∧ 2 ≤ c*(A.N n:ℝ)^2 := by
    have he := hreal.eventually (eventually_gt_atTop (max 1 (2/c)))
    filter_upwards [he] with n hn
    have h1 : 1 ≤ (A.N n:ℝ) := (le_max_left _ _).trans hn.le
    have h2 : 2/c ≤ (A.N n:ℝ) := (le_max_right _ _).trans hn.le
    have hcn : 2 ≤ c*(A.N n:ℝ) := by
      have hh := (div_le_iff₀ hc).mp h2
      nlinarith
    have hnn : (A.N n:ℝ) ≤ (A.N n:ℝ)^2 := by nlinarith [A.N_pos n]
    exact ⟨h1,hcn.trans (mul_le_mul_of_nonneg_left hnn hc.le)⟩
  have hbadlim := (RareEmpiricalReplacement.polynomial_exp_tendsto A.N A.market 3
    (by positivity : 0 < 2*ε^2)).const_mul 8
  have hbad : ∀ᶠ n in atTop,
      8*Real.exp (-2*(A.N n:ℝ)*ε^2) ≤ 1/(A.N n:ℝ)^3 := by
    have he := hbadlim.eventually_lt_const (by norm_num : 8*(0:ℝ) < 1)
    filter_upwards [he] with n hn
    apply (le_div_iff₀ (pow_pos (A.N_pos n) 3)).mpr
    have heq : -2*(A.N n:ℝ)*ε^2=-(2*ε^2)*(A.N n:ℝ) := by ring
    rw [heq]
    nlinarith
  refine ⟨cC,UC,UR,hcC,hUC,hUR,?_⟩
  filter_upwards [hscalar,hrare,hlarge,hbad] with n hs hr hn hb
  rcases hs with ⟨hm,hbpos,hθpos,hθupper,hεg,hM,hreq,hroot,hrad,hguard,hlb,hbs,hbL,hbU,
    hcap,hloGuard,hpos,hroom,hstrip,hεq,hNq,hwindow,hA,hD⟩
  have hfinite := actual_finite_bounds i hm (G n:Measure (ℝ × ℝ)) (g n) (cm n)
    hbpos hθpos hlo hε hq hεg hM hreq hroot hrad hguard hlb hbs hbL hbU hcap hloGuard
    hpos hroom hstrip hεq hNq hwindow
  have ht1 := source_tests_eq i A (fun n => (G n:Measure (ℝ × ℝ))) m b θ hN hlaw hY n 1 (receiptGap i)
  have ht2 := source_tests_eq i A (fun n => (G n:Measure (ℝ × ℝ))) m b θ hN hlaw hY n 2 (receiptGap i)
  rw [ht1.1,ht2.1,ht1.2,hN n] at hr
  rw [hN n] at hn hb
  have hden : 0 < 1+b n*(m n:ℝ)/lo := by positivity
  have hcfinite := finite_coarse_algebra hn.1 ha hd hc hK hA hden hD hθupper
    (by positivity) hb hn.2 hr.1 hr.2.1 hr.2.2
    hfinite.1 hfinite.2.1 hfinite.2.2.1
  let I := ExactUntilting.cost (source i (G n:Measure (ℝ × ℝ)))
    (demand (xi i) (b n)) (θ n) (capacity (m n)) (m n-1)
  have hR0 : 0 ≤ tiltedR i (m n) (G n:Measure (ℝ × ℝ)) (g n) (cm n) (b n) (θ n) := by
    apply integral_nonneg
    intro ω
    have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
    have hp := (RawDeficitGeometry.numeric_unit_and_duplicate_le (xi_pos i) hξ1
      {(g n) with countMargin := cm n (fun j => (ω j).1)}
      (LowBody.patternTemplate (capacity (m n)) (fun j => (ω j).1)) (LowBody.rowBids (b n) ω) 0
      hεg hM hreq (by simpa only [LowBody.rowBids,Fin.cons_zero] using hbL)).2.1.1
    exact mul_nonneg (Real.exp_pos _).le hp
  have hratio := CoarseIntegralBounds.rare_ratio_of_tilted_bounds hfinite.2.2.2.1 hfinite.2.2.2.2
    (by rw [← hN n]; exact A.N_pos n) hcC hUR.le hcfinite.1 hcfinite.2.2 hR0
  refine ⟨?_,?_,?_,hratio.1,hratio.2.1,hratio.2.2⟩
  · rw [hfinite.2.2.2.1]
    have hh := mul_le_mul_of_nonneg_left hcfinite.1 (Real.exp_pos (-I)).le
    convert! hh using 1
    dsimp [cC,I]
    ring
  · rw [hfinite.2.2.2.1]
    have hh := mul_le_mul_of_nonneg_left hcfinite.2.1 (Real.exp_pos (-I)).le
    convert! hh using 1
    dsimp [UC,I]
    ring
  · rw [hfinite.2.2.2.2]
    have hh := mul_le_mul_of_nonneg_left hcfinite.2.2 (Real.exp_pos (-I)).le
    convert! hh using 1
    dsimp [UR,I]
    ring

end FCAppendix.Affine.Uniform06.SourceCoarseAsymptotics
