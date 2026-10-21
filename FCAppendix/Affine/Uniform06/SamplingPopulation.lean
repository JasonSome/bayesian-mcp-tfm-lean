import FCAppendix.Affine.Uniform06.FullReciprocalMean
import FCAppendix.Affine.Uniform06.FiniteSampledLaplace
import FCAppendix.Affine.Uniform06.EntryEarlySourceLimits

noncomputable section
namespace FCAppendix.Affine.Uniform06.SamplingPopulation

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
open LowBody Uniform07 RawMixedSource RawTiltedSource RawMarkedLaplace
open FCAppendix.Affine.ClippedResidual FiniteGuards PhysicalExposureLimit
open FullJointLaw FullBidGeometry FullReciprocalMean MixedWeakLimits

theorem continuous_eligibility_bid {ξ L r : ℝ} (hξ : 0 < ξ) (hL : 0 < L) :
    Continuous (eligibility ξ L r) :=
  continuous_clip01.comp ((((continuous_exposure hξ hL).const_mul 4).sub continuous_const).div_const r)

theorem eligibility_price_difference {ξ r ell L T : ℝ}
    (hξ : 0 < ξ) (hr : 0 < r) (hell : 0 < ell) (hL : ell ≤ L) (hT : ell ≤ T) (B : ℝ) :
    |eligibility ξ L r B-eligibility ξ T r B| ≤ (4/(r*ξ*ell))*|L-T| := by
  have hh := clip01_lipschitz ((4*exposure ξ L B-r)/r) ((4*exposure ξ T B-r)/r)
  have he : (4*exposure ξ L B-r)/r-(4*exposure ξ T B-r)/r=
      (4/r)*(exposure ξ L B-exposure ξ T B) := by ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 4/r)] at hh
  exact hh.trans (by
    have hx := mul_le_mul_of_nonneg_left (exposure_price_lipschitz hξ hell hL hT B)
      (by positivity : 0 ≤ 4/r)
    convert! hx using 1
    ring)

def bidTest (ξ r b L θ : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-θ*exposure ξ b p.2)*eligibility ξ L r p.2

theorem bidTest_bounds {ξ r b L θ : ℝ} (hξ : 0 < ξ) (hb : 0 < b) (p : ℝ × ℝ) :
    bidTest ξ r b L θ p ∈ Icc (0:ℝ) (Real.exp |θ|) := by
  have hw := eligibility_bounds ξ L r p.2
  have hx0 := exposure_nonneg hξ hb (b:=p.2)
  have hx1 := exposure_le_one ξ b p.2
  have he : Real.exp (-θ*exposure ξ b p.2) ≤ Real.exp |θ| := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right (neg_le_abs θ) hx0).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hx1 (abs_nonneg θ))
  exact ⟨mul_nonneg (Real.exp_pos _).le hw.1,
    (mul_le_mul_of_nonneg_right he hw.1).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hw.2 (Real.exp_pos _).le)⟩

def bidTestBCF {ξ r b L : ℝ} (hξ : 0 < ξ) (hb : 0 < b) (hL : 0 < L) (θ : ℝ) :
    BoundedContinuousFunction (ℝ × ℝ) ℝ where
  toFun := bidTest ξ r b L θ
  continuous_toFun :=
    (Real.continuous_exp.comp (((continuous_exposure hξ hb).comp continuous_snd).const_mul (-θ))).mul
      ((continuous_eligibility_bid hξ hL).comp continuous_snd)
  map_bounded' := by
    refine ⟨2*Real.exp |θ|,?_⟩
    intro p q
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (bidTest_bounds hξ hb p).1,
        abs_of_nonneg (bidTest_bounds hξ hb q).1]
      have hp := (bidTest_bounds (r:=r) (L:=L) (θ:=θ) hξ hb p).2
      have hq := (bidTest_bounds (r:=r) (L:=L) (θ:=θ) hξ hb q).2
      linarith)

theorem bidTest_uniform_limit {ξ r : ℝ} (hξ : 0 < ξ) (hr : 0 < r)
    (b L θ : ℕ → ℝ) (hb : ∀ n,0 < b n) (hL : ∀ n,0 < L n)
    {b0 L0 θ0 : ℝ} (hb0 : 0 < b0) (hL0 : 0 < L0)
    (hblim : Tendsto b atTop (𝓝 b0)) (hLlim : Tendsto L atTop (𝓝 L0))
    (hθlim : Tendsto θ atTop (𝓝 θ0)) :
    TendstoUniformly (fun n => bidTestBCF (r:=r) hξ (hb n) (hL n) (θ n))
      (bidTestBCF (r:=r) hξ hb0 hL0 θ0) atTop := by
  let M : ℝ := |θ0|+1
  let Cb : ℝ := 1/(ξ*(b0/2))
  let CL : ℝ := 4/(r*ξ*(L0/2))
  let err := fun n => Real.exp M*(CL*|L n-L0|+|θ n-θ0|+|θ0| *Cb*|b n-b0|)
  have ht : Tendsto err atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero,mul_zero,zero_add,add_zero] using
      ((((hLlim.sub_const L0).abs.const_mul CL).add ((hθlim.sub_const θ0).abs)).add
        ((hblim.sub_const b0).abs.const_mul (|θ0| *Cb))).const_mul (Real.exp M)
  have hθabs : Tendsto (fun n => |θ n-θ0|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero] using (hθlim.sub_const θ0).abs
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hblim.eventually_const_le (show b0/2 < b0 by linarith),
    hLlim.eventually_const_le (show L0/2 < L0 by linarith),
    hθabs.eventually_lt_const (by norm_num : (0:ℝ) < 1),
    ht.eventually_lt_const hε] with n hbn hLn hθn herr p
  have hθM : |θ n| ≤ M := by
    have hh := abs_sub_le (θ n) θ0 0
    simp only [sub_zero] at hh
    dsimp [M]
    linarith
  have hXn : exposure ξ (b n) p.2 ∈ Icc (0:ℝ) 1 :=
    ⟨exposure_nonneg hξ (hb n) (b:=p.2),exposure_le_one ξ (b n) p.2⟩
  have hX0 : exposure ξ b0 p.2 ∈ Icc (0:ℝ) 1 :=
    ⟨exposure_nonneg hξ hb0 (b:=p.2),exposure_le_one ξ b0 p.2⟩
  have heN : -θ n*exposure ξ (b n) p.2 ≤ M := by
    have hh : |θ n| *exposure ξ (b n) p.2 ≤ |θ n| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hXn.2 (abs_nonneg (θ n))
    exact (mul_le_mul_of_nonneg_right (neg_le_abs (θ n)) hXn.1).trans (hh.trans hθM)
  have he0 : -θ0*exposure ξ b0 p.2 ≤ M := by
    have hh := (mul_le_mul_of_nonneg_right (neg_le_abs θ0) hX0.1).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hX0.2 (abs_nonneg θ0))
    dsimp [M]
    linarith
  have hx := exposure_price_lipschitz hξ (half_pos hb0) hbn (by linarith : b0/2 ≤ b0) p.2
  have hw := eligibility_price_difference hξ hr (half_pos hL0) hLn
    (by linarith : L0/2 ≤ L0) p.2
  have harg : |-θ n*exposure ξ (b n) p.2-(-θ0*exposure ξ b0 p.2)| ≤
      |θ n-θ0|+|θ0| *Cb*|b n-b0| := by
    have he : -θ n*exposure ξ (b n) p.2-(-θ0*exposure ξ b0 p.2)=
        -(θ n-θ0)*exposure ξ (b n) p.2-θ0*(exposure ξ (b n) p.2-exposure ξ b0 p.2) := by ring
    rw [he]
    calc
      _ ≤ |θ n-θ0| *|exposure ξ (b n) p.2|+
          |θ0| *|exposure ξ (b n) p.2-exposure ξ b0 p.2| := by
        simpa only [abs_mul,abs_neg] using abs_sub
          (-(θ n-θ0)*exposure ξ (b n) p.2)
          (θ0*(exposure ξ (b n) p.2-exposure ξ b0 p.2))
      _ ≤ |θ n-θ0| *1+|θ0| *(Cb*|b n-b0|) :=
        add_le_add (mul_le_mul_of_nonneg_left (by simpa [abs_of_nonneg hXn.1] using hXn.2)
          (abs_nonneg _)) (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
      _ = _ := by ring
  have hexp := (exp_difference_upper heN he0).trans
    (mul_le_mul_of_nonneg_left harg (Real.exp_pos _).le)
  have hdif : |bidTest ξ r (b n) (L n) (θ n) p-bidTest ξ r b0 L0 θ0 p| ≤ err n := by
    have hid : bidTest ξ r (b n) (L n) (θ n) p-bidTest ξ r b0 L0 θ0 p=
        Real.exp (-θ n*exposure ξ (b n) p.2)*(eligibility ξ (L n) r p.2-eligibility ξ L0 r p.2)+
        (Real.exp (-θ n*exposure ξ (b n) p.2)-Real.exp (-θ0*exposure ξ b0 p.2))*eligibility ξ L0 r p.2 := by
      unfold bidTest
      ring
    rw [hid]
    have hh := abs_add_le
      (Real.exp (-θ n*exposure ξ (b n) p.2)*(eligibility ξ (L n) r p.2-eligibility ξ L0 r p.2))
      ((Real.exp (-θ n*exposure ξ (b n) p.2)-Real.exp (-θ0*exposure ξ b0 p.2))*eligibility ξ L0 r p.2)
    simp only [abs_mul,abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (eligibility_bounds ξ L0 r p.2).1] at hh
    have hh1 := mul_le_mul (Real.exp_le_exp.mpr heN) hw (abs_nonneg _) (Real.exp_pos _).le
    have hh2 := mul_le_mul hexp (eligibility_bounds ξ L0 r p.2).2
      (eligibility_bounds ξ L0 r p.2).1 (by positivity)
    exact hh.trans (by dsimp [err,CL] at *; nlinarith [hh1,hh2])
  change |bidTest ξ r b0 L0 θ0 p-bidTest ξ r (b n) (L n) (θ n) p| < ε
  simpa only [abs_sub_comm] using hdif.trans_lt herr

theorem bid_integral_tendsto {ξ r : ℝ} (hξ : 0 < ξ) (hr : 0 < r)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0))
    (b L θ : ℕ → ℝ) (hb : ∀ n,0 < b n) (hL : ∀ n,0 < L n)
    {b0 L0 θ0 : ℝ} (hb0 : 0 < b0) (hL0 : 0 < L0)
    (hblim : Tendsto b atTop (𝓝 b0)) (hLlim : Tendsto L atTop (𝓝 L0))
    (hθlim : Tendsto θ atTop (𝓝 θ0)) :
    Tendsto (fun n => ∫ p,bidTest ξ r (b n) (L n) (θ n) p ∂(G n:Measure (ℝ × ℝ))) atTop
      (𝓝 (∫ p,bidTest ξ r b0 L0 θ0 p ∂(G0:Measure (ℝ × ℝ)))) :=
  FCAppendix.PayOnce.KernelLawConvergence.tendsto_integral_varying_test hG
    (fun n => bidTestBCF (r:=r) hξ (hb n) (hL n) (θ n))
    (bidTestBCF (r:=r) hξ hb0 hL0 θ0)
    (bidTest_uniform_limit hξ hr b L θ hb hL hb0 hL0 hblim hLlim hθlim)

def weightMean (i : Row) (G : Measure (ℝ × ℝ)) (b θ : ℝ) (g : LiteralExperiment.GuardData) : ℝ :=
  ∫ r,rawWeight (xi i) g r ∂tiltedSource i G b θ

def selectedMean (i : Row) (G : Measure (ℝ × ℝ)) (b θ : ℝ) (g : LiteralExperiment.GuardData) : ℝ :=
  ∫ r,rawWeight (xi i) g r*Real.exp (-θ*rawH (xi i) b r) ∂tiltedSource i G b θ

theorem weightMean_formula (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (θ : ℝ) (g : LiteralExperiment.GuardData) :
    weightMean i G b θ g=factor i G b θ*
      (∫ p,bidTest (xi i) g.requiredDemand b g.multiplier θ p ∂G) := by
  rw [weightMean]
  have hf : Measurable (eligibility (xi i) g.multiplier g.requiredDemand) := by
    unfold eligibility clip01 exposure
    fun_prop
  exact integral_lowerTest i G hb θ (eligibility (xi i) g.multiplier g.requiredDemand)
    hf
    (by norm_num : (0:ℝ) ≤ 1)
    (fun B => by simpa only [abs_of_nonneg (eligibility_bounds _ _ _ _).1] using
      (eligibility_bounds (xi i) g.multiplier g.requiredDemand B).2)

theorem selectedMean_formula (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (θ : ℝ) (g : LiteralExperiment.GuardData) :
    selectedMean i G b θ g=factor i G b θ*Real.exp (-θ/2)*
      (∫ p,eligibility (xi i) g.multiplier g.requiredDemand p.2 ∂G) := by
  let f : ℝ → ℝ := fun B => eligibility (xi i) g.multiplier g.requiredDemand B*
    Real.exp (-θ*(1/2-exposure (xi i) b B))
  have hf : Measurable f := by unfold f eligibility clip01 exposure; fun_prop
  have hfb (B : ℝ) : |f B| ≤ Real.exp |θ| := by
    have hx0 := exposure_nonneg (xi_pos i) hb (b:=B)
    have hx1 := exposure_le_one (xi i) b B
    have hx : |1/2-exposure (xi i) b B| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have he : Real.exp (-θ*(1/2-exposure (xi i) b B)) ≤ Real.exp |θ| := by
      apply Real.exp_le_exp.mpr
      exact (le_abs_self _).trans (by
        rw [abs_mul,abs_neg]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hx (abs_nonneg θ))
    change |eligibility (xi i) g.multiplier g.requiredDemand B *
      Real.exp (-θ*(1/2-exposure (xi i) b B))| ≤ Real.exp |θ|
    rw [abs_mul,abs_of_nonneg (eligibility_bounds _ _ _ _).1,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left he (eligibility_bounds _ _ _ _).1).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
        (eligibility_bounds (xi i) g.multiplier g.requiredDemand B).2 (Real.exp_pos _).le))
  have heq : (fun r => rawWeight (xi i) g r*Real.exp (-θ*rawH (xi i) b r))=lowerTest f := by
    funext r
    by_cases ht : r.1=0
    · simp only [rawWeight,rawH,RawMixedSource.demand,ht,if_true,lowerTest,f]
    · simp only [rawWeight,if_neg ht,zero_mul,lowerTest]
  rw [selectedMean,heq,integral_lowerTest i G hb θ f hf (Real.exp_pos _).le hfb]
  have hint : (∫ p,Real.exp (-θ*exposure (xi i) b p.2)*f p.2 ∂G)=
      Real.exp (-θ/2)*(∫ p,eligibility (xi i) g.multiplier g.requiredDemand p.2 ∂G) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro p
    dsimp [f]
    rw [mul_left_comm _ (eligibility _ _ _ _),← Real.exp_add,
      show -θ*exposure (xi i) b p.2+-θ*(1/2-exposure (xi i) b p.2)=-θ/2 by ring]
    ring
  rw [hint]
  ring

theorem actual_one_user_means_tendsto (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (G0 : ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 G0)) (b θ : ℕ → ℝ) (g : ℕ → LiteralExperiment.GuardData)
    {b0 θ0 : ℝ} (g0 : LiteralExperiment.GuardData)
    (hb : ∀ n,0 < b n) (hb0 : 0 < b0)
    (hL : ∀ n,0 < (g n).multiplier) (hL0 : 0 < g0.multiplier)
    (hr : 0 < g0.requiredDemand) (hreq : ∀ n,(g n).requiredDemand=g0.requiredDemand)
    (hblim : Tendsto b atTop (𝓝 b0)) (hθlim : Tendsto θ atTop (𝓝 θ0))
    (hLlim : Tendsto (fun n => (g n).multiplier) atTop (𝓝 g0.multiplier)) :
    Tendsto (fun n => weightMean i (G n:Measure (ℝ × ℝ)) (b n) (θ n) (g n)) atTop
      (𝓝 (weightMean i (G0:Measure (ℝ × ℝ)) b0 θ0 g0)) ∧
    Tendsto (fun n => selectedMean i (G n:Measure (ℝ × ℝ)) (b n) (θ n) (g n)) atTop
      (𝓝 (selectedMean i (G0:Measure (ℝ × ℝ)) b0 θ0 g0)) := by
  have hfac := factor_tendsto i G G0 hG b θ hb hb0 hblim hθlim
  have hw := bid_integral_tendsto (xi_pos i) hr G G0 hG b
    (fun n => (g n).multiplier) θ hb hL hb0 hL0 hblim hLlim hθlim
  have hu := bid_integral_tendsto (xi_pos i) hr G G0 hG b
    (fun n => (g n).multiplier) (fun _ => 0) hb hL hb0 hL0 hblim hLlim tendsto_const_nhds
  constructor
  · have hh := hfac.mul hw
    have he (n : ℕ) := weightMean_formula i (G n:Measure (ℝ × ℝ)) (hb n) (θ n) (g n)
    have he0 := weightMean_formula i (G0:Measure (ℝ × ℝ)) hb0 θ0 g0
    simpa only [he,he0,hreq] using hh
  · have hexp := Real.continuous_exp.continuousAt.tendsto.comp (hθlim.neg.div_const 2)
    have hh := (hfac.mul hexp).mul hu
    have he (n : ℕ) := selectedMean_formula i (G n:Measure (ℝ × ℝ)) (hb n) (θ n) (g n)
    have he0 := selectedMean_formula i (G0:Measure (ℝ × ℝ)) hb0 θ0 g0
    simpa only [he,he0,hreq,bidTest,neg_zero,zero_mul,Real.exp_zero,one_mul,Function.comp_def] using hh

theorem full_weight_integral_pos (i : Row) :
    0 < ∫ p,eligibility (xi i) (entry i) (PrefixRoot.requiredDemand i) p.2
      ∂(law i:Measure (ℝ × ℝ)) := by
  let G := (law i:Measure (ℝ × ℝ))
  have hr := (EntryEarlySourceLimits.requiredDemand_bounds i).1
  have hp := EntryEarlySourceLimits.eligibleMass_positive G i Prod.fst measurable_fst
    (full_value_marginal i)
  have ha := EarlyMean.original_entry_exposure i G (full_value_marginal i)
    (full_below_value i) (full_active_graph i)
  have hv := EarlyMean.value_support i G (full_value_marginal i)
  have he : (fun p : ℝ × ℝ => eligibility (xi i) (entry i) (PrefixRoot.requiredDemand i) p.2)
      =ᵐ[G] EntryEarlySourceLimits.eligible i Prod.fst := by
    filter_upwards [ha,hv] with p hp hpv
    rw [EntryEarlySourceLimits.eligibility_eq hr,hp]
    unfold EntryEarlySourceLimits.eligible EntryEarlySourceLimits.entryExposure
    rw [EntryEarlySourceLimits.entryExposure_eq_activeOnly i hpv]
  rw [integral_congr_ae he]
  change 0 < cutoff i*(∫ p,EntryEarlySourceLimits.eligible i Prod.fst p ∂G) at hp
  exact (mul_pos_iff_of_pos_left (cutoff_pos i)).mp hp

theorem full_sampling_means_positive (i : Row) {b : ℝ} (hb : 0 < b) (θ : ℝ)
    (g : LiteralExperiment.GuardData) (hL : g.multiplier=entry i)
    (hr : g.requiredDemand=PrefixRoot.requiredDemand i) :
    0 < weightMean i (law i:Measure (ℝ × ℝ)) b θ g ∧
      0 < selectedMean i (law i:Measure (ℝ × ℝ)) b θ g := by
  have hbase := full_weight_integral_pos i
  have hbase' : 0 < ∫ p,eligibility (xi i) g.multiplier g.requiredDemand p.2
      ∂(law i:Measure (ℝ × ℝ)) := by simpa only [hL,hr] using hbase
  constructor
  · rw [weightMean_formula i _ hb θ g]
    apply mul_pos (factor_pos i _ b θ)
    have hi : Integrable (fun p : ℝ × ℝ => eligibility (xi i) g.multiplier g.requiredDemand p.2)
        (law i:Measure (ℝ × ℝ)) :=
      Integrable.of_mem_Icc 0 1
        ((continuous_eligibility_bid (ξ:=xi i) (L:=g.multiplier) (r:=g.requiredDemand)
          (xi_pos i) (by rw [hL]; exact EarlyMean.entry_pos i)).comp continuous_snd).measurable.aemeasurable
        (ae_of_all _ fun p => eligibility_bounds _ _ _ _)
    have hbi := (bidTestBCF (ξ:=xi i) (b:=b) (L:=g.multiplier) (r:=g.requiredDemand) (xi_pos i) hb
      (by rw [hL]; exact EarlyMean.entry_pos i) θ).integrable
        (μ := (law i:Measure (ℝ × ℝ)))
    have hle := integral_mono_ae (hi.const_mul (Real.exp (-|θ|))) hbi
      (ae_of_all _ fun p => by
        have hx0 := exposure_nonneg (xi_pos i) hb (b:=p.2)
        have hx1 := exposure_le_one (xi i) b p.2
        have habs : |-θ*exposure (xi i) b p.2| ≤ |θ| := by
          rw [abs_mul,abs_neg,abs_of_nonneg hx0]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hx1 (abs_nonneg θ)
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (abs_le.mp habs).1)
          (eligibility_bounds (xi i) g.multiplier g.requiredDemand p.2).1)
    rw [integral_const_mul] at hle
    exact (mul_pos (Real.exp_pos _) hbase').trans_le hle
  · rw [selectedMean_formula i _ hb θ g]
    exact mul_pos (mul_pos (factor_pos i _ b θ) (Real.exp_pos _)) hbase'

section GeometricRatio
variable {Ω : Type*} [MeasurableSpace Ω]

theorem weighted_laplace_ratio (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w h : Ω → ℝ) (hw : Measurable w) (hh : Measurable h)
    (hwb : ∀ᵐ x ∂μ,w x ∈ Icc (0:ℝ) 1) (hhb : ∀ᵐ x ∂μ,|h x| ≤ 1)
    {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η)
    (hgap : ∀ᵐ x ∂μ,w x ≠ 0 → η ≤ h x)
    (hwpos : 0 < ∫ x,w x ∂μ) :
    0 < (∫ x,w x*Real.exp (-θ*h x) ∂μ)/(∫ x,w x ∂μ) ∧
      (∫ x,w x*Real.exp (-θ*h x) ∂μ)/(∫ x,w x ∂μ) ≤ Real.exp (-θ*η) ∧
        Real.exp (-θ*η) < 1 := by
  have hwi : Integrable w μ := Integrable.of_mem_Icc 0 1 hw.aemeasurable hwb
  have hei : Integrable (fun x => w x*Real.exp (-θ*h x)) μ := by
    apply Integrable.of_bound (hw.mul ((hh.const_mul (-θ)).exp)).aestronglyMeasurable (Real.exp θ)
    filter_upwards [hwb,hhb] with x hx hhx
    change ‖w x*Real.exp (-θ*h x)‖ ≤ Real.exp θ
    rw [Real.norm_of_nonneg (mul_nonneg hx.1 (Real.exp_pos _).le)]
    have he : Real.exp (-θ*h x) ≤ Real.exp θ := by
      apply Real.exp_le_exp.mpr
      have hhx' := (abs_le.mp hhx).1
      nlinarith
    exact (mul_le_mul_of_nonneg_left he hx.1).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx.2 (Real.exp_pos _).le)
  have hlo := integral_mono_ae (hwi.const_mul (Real.exp (-θ))) hei (by
    filter_upwards [hwb,hhb] with x hx hhx
    have hex : Real.exp (-θ) ≤ Real.exp (-θ*h x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [(abs_le.mp hhx).2]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hex hx.1)
  have hup := integral_mono_ae hei (hwi.const_mul (Real.exp (-θ*η))) (by
    filter_upwards [hwb,hgap] with x hx hhx
    by_cases hw0 : w x=0
    · simp [hw0]
    · have hex : Real.exp (-θ*h x) ≤ Real.exp (-θ*η) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hhx hw0]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hex hx.1)
  rw [integral_const_mul] at hlo hup
  refine ⟨div_pos ((mul_pos (Real.exp_pos _) hwpos).trans_le hlo) hwpos,?_,?_⟩
  · exact (div_le_iff₀ hwpos).mpr (by simpa only [mul_comm] using hup)
  · exact Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hθ hη])

end GeometricRatio

end FCAppendix.Affine.Uniform06.SamplingPopulation
