import FCAppendix.Affine.Tail04.OrderedSourceCommonMenuError
import FCAppendix.Affine.Tail04.OrderedAtomActiveLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomCommonPayoff
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeNoisySource LatentNoisyPopulation
open OrderedAtomActiveLaw OrderedAtomActiveCompression OrderedOriginalCommonMenuCount
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle
open SourceCommonMoments OrderedSourceCommonMenuError SourceMenuIdentity
open scoped BigOperators

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
  (hcap : D.c=iidCapacity (99/200) N) (hN : 0< N)
  (hF : D.F=Central.B D.ξ) (hflags : ∀ reg,D.e0 reg=baseFlag P reg)
  (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
  (huB : 1+bulkPhysicalWidth D< Central.B D.ξ)
  (hRp : D.V≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : relativeError P.zeta (bulkPhysicalWidth D) (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : D.width≤ γ D.ξ)
  (hθ : (D.regimeShare:ℝ)=P.theta) (hη : D.eta=1-2*D.ξ)

local notation "Ds" => installOriginal D P t ht
local notation "μsrc" => drawLaw D P t ht πL π upperBid hupperBid
local notation "ν" => Measure.pi (fun _ : Fin N => μsrc)
local notation "tag" => NativeActiveCompressedLaw.latentTag D P hdR H hBH
local notation "decode" => NativeActiveCompressedLaw.latentBid D P hdR H hBH
local notation "M" => mixedMean Ds tag decode μsrc
local notation "W" => reciprocalMean Ds tag decode μsrc
local notation "μP" => bidMarginal (Subtype.val (π 2))
local notation "lam" => OrderedSourceCommonMenuError.lambda D P t ht πL π upperBid hupperBid hdR H hBH
local notation "rateN" => SourceMovingMenuRates.rate (commonCoefficient P D.ξ)
  (lowMass P.theta) P.bulkWeight N

include hfloor hrare hF hflags hξh hR huB hRp hsmall hmSmall in
theorem lambda_exposure (reg : Bool) (b : Icc (1:ℝ) D.B) :
    exposure D.ξ (lam reg) b∈Icc (0:ℝ) 1 := by
  have G := source_guard D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    hF hflags hξh hR huB hRp hsmall hmSmall reg
  have hg := G.mean_margins D.hξ.le (integral_nonneg fun x => (indicator_bounds (tagFlag tag 2) x).1)
  have hn : populationNumerator D.ξ (99/200) (activeMean tag μsrc) (M reg) (privateMean0 tag μsrc)
      (keptShare P t reg)=SourceMenuError.meanNumerator P D.ξ (M reg) reg := by
    have ha : activeMean tag μsrc=activeMass P.theta-upperMass P t :=
      active_mean D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    have hp : privateMean0 tag μsrc=(partialMass+upperMass P t)/2 :=
      (private_means D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare).1
    rw [ha,hp]
    exact population_mean_eq P D.ξ t (M reg) ht.le reg
  have hg' : 0<W reg ∧
      (1-D.ξ)*D.B+2*γ D.ξ≤populationNumerator D.ξ (99/200) (activeMean tag μsrc) (M reg)
        (privateMean0 tag μsrc) (keptShare P t reg)/W reg ∧
      populationNumerator D.ξ (99/200) (activeMean tag μsrc) (M reg)
        (privateMean0 tag μsrc) (keptShare P t reg)/W reg+2*γ D.ξ≤1 := hg
  rw [hn] at hg'
  have hγ : 0≤ γ D.ξ := div_nonneg D.hξ.le (by norm_num)
  have hb : (0:ℝ)< b := lt_of_lt_of_le (by norm_num) b.2.1
  have hκ : 0≤1-D.ξ := by linarith [D.hξ1]
  have hlo : (1-D.ξ)*(b:ℝ)≤ lam reg :=
    (mul_le_mul_of_nonneg_left b.2.2 hκ).trans (by dsimp only [OrderedSourceCommonMenuError.lambda];linarith only [hg'.2.1,hγ])
  have hhi : lam reg≤(b:ℝ) := by
    dsimp only [OrderedSourceCommonMenuError.lambda]
    linarith only [hg'.2.2,b.2.1,hγ]
  have hdiv0 : lam reg/(b:ℝ)≤1 := (div_le_one hb).mpr hhi
  have hdiv1 : 1-D.ξ≤ lam reg/(b:ℝ) := (le_div_iff₀ hb).mpr hlo
  unfold exposure
  exact ⟨div_nonneg (by linarith) D.hξ.le,(div_le_one D.hξ).mpr (by linarith)⟩

lemma count_integral_value (reg : Bool) (v : ℝ) (b : Icc (1:ℝ) D.B) :
    (∫ r,ActivePhysicalPayoff.value Ds ((Ds).count (tags tag r) 1)
      (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) (max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) μP v reg
        (decide (0< (Ds).count (tags tag r) 0)) (focalRow Ds (tags tag r) decode b r) ∂ν)=
      (averageCount Ds tag (measurable_latentTag D P hdR H hBH)
        decode (measurable_latentBid D P hdR H hBH) μP N μsrc reg b).expect
          (affineStatistic D.eta v b) := by
  rw [averageCount,FiniteLaw.expect_average]
  apply integral_congr_ae
  exact ae_of_all _ fun r => (affineStatistic_utility
    (count Ds tag decode μP N reg b r) D.eta v b D.heta0 D.heta1 (Schedule.once 2)).symm

lemma integrable_regime_value (reg : Bool) (v : ℝ) (b : Icc (1:ℝ) D.B) :
    Integrable (fun r => ActivePhysicalPayoff.value Ds ((Ds).count (tags tag r) 1)
      (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) (max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) μP v reg
        (decide (0< (Ds).count (tags tag r) 0)) (focalRow Ds (tags tag r) decode b r)) ν := by
  have hi := FiniteLaw.integrable_expect ν (count Ds tag decode μP N reg b)
    (measurable_count_mass Ds tag (measurable_latentTag D P hdR H hBH)
      decode (measurable_latentBid D P hdR H hBH) μP N reg b) (affineStatistic D.eta v b)
  apply hi.congr
  exact ae_of_all _ fun r => affineStatistic_utility
    (count Ds tag decode μP N reg b r) D.eta v b D.heta0 D.heta1 (Schedule.once 2)

include hfloor hrare hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη in
theorem original_physical_payoff_error (v : ℝ) (hv : 0≤ v) (b : Icc (1:ℝ) D.B) :
    |(∫ r,physicalValue D P t ht π hdR H hBH N v b r ∂ν)-
      menuUtility P D.ξ (lam false) (lam true) v b|≤(v+2*D.B)*rateN := by
  let f := affineStatistic D.eta v b
  have hA := original_count_error D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ false b f
  have hR' := original_count_error D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ true b f
  have hmix : (∫ r,physicalValue D P t ht π hdR H hBH N v b r ∂ν)=
      (1-P.theta)*(averageCount Ds tag (measurable_latentTag D P hdR H hBH)
        decode (measurable_latentBid D P hdR H hBH) μP N μsrc false b).expect f+
      P.theta*(averageCount Ds tag (measurable_latentTag D P hdR H hBH)
        decode (measurable_latentBid D P hdR H hBH) μP N μsrc true b).expect f := by
    let regVal : Bool→(Fin N→Draw)→ℝ := fun reg r => ActivePhysicalPayoff.value Ds ((Ds).count (tags tag r) 1)
      (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3))
      (max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) μP v reg
      (decide (0<(Ds).count (tags tag r) 0)) (focalRow Ds (tags tag r) decode b r)
    have hi0 : Integrable (regVal false) ν := integrable_regime_value D P t ht πL π
      upperBid hupperBid hdR H hBH N false v b
    have hi1 : Integrable (regVal true) ν := integrable_regime_value D P t ht πL π
      upperBid hupperBid hdR H hBH N true v b
    have hadd := integral_add (hi0.const_mul (1-P.theta)) (hi1.const_mul P.theta)
    simp only [integral_const_mul] at hadd
    have hp : (∫ r,physicalValue D P t ht π hdR H hBH N v b r ∂ν)=
        (1-P.theta)*(∫r,regVal false r ∂ν)+P.theta*(∫r,regVal true r ∂ν) := by
      simpa only [regVal,physicalValue,rivalValue,caseValue,ActivePhysicalPayoff.regimeValue,
        SourceTailNoisyFixedPoint.installOriginal,hθ] using! hadd
    exact hp.trans (congrArg₂ (fun x y : ℝ=>(1-P.theta)*x+P.theta*y)
      (count_integral_value D P t ht πL π upperBid hupperBid hdR H hBH N false v b)
      (count_integral_value D P t ht πL π upperBid hupperBid hdR H hBH N true v b))
  have hbF : (b:ℝ)∈Icc (1:ℝ) (Central.B D.ξ) := ⟨b.2.1,b.2.2.trans (by simpa only [←hF,Data.B] using D.hUF)⟩
  have hmenu := idealCount_payoff P v D.hξ hbF
    (lambda_exposure D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
      hF hflags hξh hR huB hRp hsmall hmSmall false b)
    (lambda_exposure D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
      hF hflags hξh hR huB hRp hsmall hmSmall true b)
  have hmixIdeal : (1-P.theta)*(idealRegime P D.ξ (M false) (W false) b false).expect f+
      P.theta*(idealRegime P D.ξ (M true) (W true) b true).expect f=
        menuUtility P D.ξ (lam false) (lam true) v b := by
    calc
      _ = (idealCount P D.ξ (M false) (W false) (M true) (W true) b).expect f := by
        simp only [idealCount,Counts.regimeLaw,FiniteLaw.expect_mixture]
        ring
      _ = _ := by simpa only [f,hη,OrderedSourceCommonMenuError.lambda] using! hmenu
  rw [hmix,←hmixIdeal]
  have htθ : 0≤1-P.theta := by linarith [P.theta_small]
  have hsplit := abs_add_le
    ((1-P.theta)*((averageCount Ds tag (measurable_latentTag D P hdR H hBH)
      decode (measurable_latentBid D P hdR H hBH) μP N μsrc false b).expect f-
        (idealRegime P D.ξ (M false) (W false) b false).expect f))
    (P.theta*((averageCount Ds tag (measurable_latentTag D P hdR H hBH)
      decode (measurable_latentBid D P hdR H hBH) μP N μsrc true b).expect f-
        (idealRegime P D.ξ (M true) (W true) b true).expect f))
  rw [abs_mul,abs_mul,abs_of_nonneg htθ,abs_of_nonneg P.theta_pos.le] at hsplit
  have he : MenuError.oscillation f≤ v+2*D.B := by
    have hb0 : 0≤(b:ℝ) := by linarith [b.2.1]
    have ho := oscillation_affineStatistic D.heta0 D.heta1 hv hb0
    have hB0 : 0≤ D.B := hb0.trans b.2.2
    exact ho.trans (by linarith [b.2.2])
  have hrate := SourceMovingMenuRates.rate_nonneg (s:=lowMass P.theta) (commonCoefficient_nonnegative P D.hξ) P.bulkWeight_pos.le N
  have hs := add_le_add (mul_le_mul_of_nonneg_left hA htθ)
    (mul_le_mul_of_nonneg_left hR' P.theta_pos.le)
  have ho := mul_le_mul_of_nonneg_right he hrate
  have hid : ∀ a b c d : ℝ,(1-P.theta)*a+P.theta*b-((1-P.theta)*c+P.theta*d)=
    (1-P.theta)*(a-c)+P.theta*(b-d) := by intros;ring
  rw [hid]
  nlinarith

attribute [local irreducible] OrderedFiniteTailNoisyGame.activeExpected
  OrderedSourceCommonMenuError.lambda OrderedAtomActiveLaw.physicalValue
  OrderedOriginalCommonMenuCount.mixedMean OrderedOriginalCommonMenuCount.reciprocalMean
  SourceMovingMenuRates.rate

include hfloor hrare hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη in
theorem activeExpected_error (v : ℝ) (hv : 0≤ v) (b : Icc (1:ℝ) D.U) :
    |OrderedFiniteTailNoisyGame.activeExpected Ds N (bidLaws D P t ht π,(v,b))-
      ∫ u : unitInterval,menuUtility P D.ξ (lam false) (lam true) v
        (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u):ℝ)|≤
      (v+2*D.B)*rateN := by
  let phy := fun u : unitInterval => noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)
  let actual := fun u : unitInterval => ∫ r,physicalValue D P t ht π hdR H hBH N v (phy u) r ∂ν
  let ideal := fun u : unitInterval => menuUtility P D.ξ (lam false) (lam true) v (phy u)
  have hphy : Measurable phy :=
    (continuous_noisyBid (by norm_num : (0:ℝ)<1) D.heps.le).measurable.comp
      (measurable_const.prodMk measurable_id)
  have hmJoint : Measurable (fun z : unitInterval×(Fin N→ Draw) =>
      physicalValue D P t ht π hdR H hBH N v (phy z.1) z.2) :=
    (measurable_physicalValue_joint D P t ht π hdR H hBH N).comp
      ((measurable_const.prodMk (hphy.comp measurable_fst)).prodMk measurable_snd)
  have hmActual : Measurable actual :=
    hmJoint.stronglyMeasurable.integral_prod_right'.measurable
  have hiActual : Integrable actual volume := Integrable.of_bound hmActual.aestronglyMeasurable
    (v+2*D.B) (ae_of_all _ fun u => by
      have hh := abs_integral_le_integral_abs (μ:=ν) (f:=fun r => physicalValue D P t ht π hdR H hBH N v (phy u) r)
      have hb := integral_mono_of_nonneg (μ:=ν)
        (f:=fun r => |physicalValue D P t ht π hdR H hBH N v (phy u) r|)
        (g:=fun _ => v+2*D.B) (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
        (ae_of_all _ fun r => by simpa only [abs_of_nonneg hv] using (physicalValue_bound D P t ht π hdR H hBH N v (phy u) r))
      rw [Real.norm_eq_abs]
      exact hh.trans (by simpa only [integral_const,probReal_univ,one_smul] using hb))
  have hmIdeal : Measurable ideal := by
    dsimp only [ideal]
    unfold menuUtility payment served duplicates mixedProbability exposure
    fun_prop
  have hiIdeal : Integrable ideal volume := Integrable.of_bound hmIdeal.aestronglyMeasurable
    (v+2*D.B+(v+2*D.B)*rateN) (ae_of_all _ fun u => by
      have he := original_physical_payoff_error D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
        hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη v hv (phy u)
      have hb := (abs_sub_le (ideal u) (actual u) 0)
      rw [Real.norm_eq_abs]
      have ha' : |actual u|≤ v+2*D.B := by
        have h0 := abs_integral_le_integral_abs (μ:=ν) (f:=fun r => physicalValue D P t ht π hdR H hBH N v (phy u) r)
        have h1 := integral_mono_of_nonneg (μ:=ν) (f:=fun r => |physicalValue D P t ht π hdR H hBH N v (phy u) r|)
          (g:=fun _ => v+2*D.B) (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
          (ae_of_all _ fun r => by simpa only [abs_of_nonneg hv] using physicalValue_bound D P t ht π hdR H hBH N v (phy u) r)
        exact h0.trans (by simpa using h1)
      change |actual u-ideal u|≤(v+2*D.B)*rateN at he
      rw [abs_sub_comm] at he
      simp only [sub_zero] at hb
      exact hb.trans (by linarith only [he,ha']))
  rw [←original_noisy_physicalValue D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare v b]
  rw [←integral_sub hiActual hiIdeal]
  have hh := (abs_integral_le_integral_abs).trans
    (integral_mono_of_nonneg (μ:=(volume : Measure unitInterval))
      (f:=fun u => |actual u-ideal u|) (g:=fun _ => (v+2*D.B)*rateN)
      (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
      (ae_of_all _ fun u => original_physical_payoff_error D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
        hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hθ hη v hv (phy u)))
  simpa only [integral_const,probReal_univ,one_smul] using hh

end FCAppendix.Affine.Tail04.OrderedAtomCommonPayoff
