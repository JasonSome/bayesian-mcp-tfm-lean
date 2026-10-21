import FCAppendix.Affine.LowBody.NoisyBidAtomless
import FCAppendix.Probability.L1WeakConvergence

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical Filter Topology
open Existence.Distributional

def baseBid (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (x : LowValue d×unitInterval) : LowValue d:=noisyBid d ε hε hsmall (x,0)

@[simp] theorem baseBid_coe (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (x : LowValue d×unitInterval) : (baseBid d ε hε hsmall x).1=x.1.1*bidRatio ε x.2 := by
  simp [baseBid,noisyBid]

theorem continuous_baseBid (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2) :
    Continuous (baseBid d ε hε hsmall) :=
  (continuous_noisyBid d ε hε hsmall).comp (continuous_id.prodMk continuous_const)

def baseBidLaw (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) : ProbabilityMeasure ℝ :=
  pi.1.map ((continuous_baseBid d ε hε hsmall).subtype_val.measurable.aemeasurable)

def realLowBidLaw {d : ℝ} (pi : ProbabilityMeasure (LowValue d×LowValue d)) :
    ProbabilityMeasure ℝ:=pi.map (measurable_snd.subtype_val.aemeasurable)

theorem continuous_realLowBidLaw (d : ℝ) : Continuous (realLowBidLaw (d:=d)) :=
  ProbabilityMeasure.continuous_map continuous_snd.subtype_val

theorem baseBid_noisyBid_distance {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (x : (LowValue d×unitInterval)×unitInterval) :
    |(baseBid d ε hε hsmall x.1).1-(noisyBid d ε hε hsmall x).1|≤ε*d := by
  have hb:=noisyBid_bounds hε hsmall x.1.1 x.1.2 (0:unitInterval)
  have hb0 : 0≤x.1.1.1*bidRatio ε x.1.2:=by simpa using hb.1
  have hbD : x.1.1.1*bidRatio ε x.1.2≤d:=by
    have hh : x.1.1.1*bidRatio ε x.1.2≤x.1.1.1:=by simpa using hb.2
    exact hh.trans x.1.1.property.2
  have hcost : x.1.1.1*bidRatio ε x.1.2*ε*x.2.1≤ε*d := by
    calc
      _≤x.1.1.1*bidRatio ε x.1.2*ε*1:=mul_le_mul_of_nonneg_left x.2.property.2 (mul_nonneg hb0 hε.le)
      _=ε*(x.1.1.1*bidRatio ε x.1.2):=by ring
      _≤ε*d:=mul_le_mul_of_nonneg_left hbD hε.le
  rw [baseBid_coe]
  change |x.1.1.1*bidRatio ε x.1.2-x.1.1.1*bidRatio ε x.1.2*(1+ε*x.2.1)|≤ε*d
  rw [abs_of_nonpos (by nlinarith [mul_nonneg (mul_nonneg hb0 hε.le) x.2.property.1])]
  nlinarith

theorem baseBidLaw_tendsto {d : ℝ}
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (eps : ℕ→ℝ) (heps : ∀j,0<eps j) (hsmall : ∀j,eps j≤1/2)
    (pi : ℕ→Law (A:=unitInterval) mu) (pi₀ : Law (A:=LowValue d) mu)
    (heps0 : Tendsto eps atTop (𝓝 0))
    (hlim : Tendsto (fun j=>(lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1)
      atTop (𝓝 pi₀.1)) :
    Tendsto (fun j=>baseBidLaw d (eps j) (heps j) (hsmall j) mu (pi j)) atTop (𝓝 (realLowBidLaw pi₀.1)) := by
  let M : ℕ→Measure ((LowValue d×unitInterval)×unitInterval):=fun j=>
    ((pi j).1 : Measure (LowValue d×unitInterval)).prod (volume : Measure unitInterval)
  letI : ∀j,IsProbabilityMeasure (M j):=fun j=>inferInstanceAs
    (IsProbabilityMeasure (((pi j).1 : Measure (LowValue d×unitInterval)).prod (volume : Measure unitInterval)))
  let X : ℕ→((LowValue d×unitInterval)×unitInterval)→ℝ:=
    fun j x=>(baseBid d (eps j) (heps j) (hsmall j) x.1).1
  let Y : ℕ→((LowValue d×unitInterval)×unitInterval)→ℝ:=
    fun j x=>(noisyBid d (eps j) (heps j) (hsmall j) x).1
  let Z : LowValue d×LowValue d→ℝ:=fun x=>x.2.1
  have hX (j : ℕ) : Continuous (X j):=
    ((continuous_baseBid d (eps j) (heps j) (hsmall j)).subtype_val).comp continuous_fst
  have hY (j : ℕ) : Continuous (Y j):=(continuous_noisyBid d (eps j) (heps j) (hsmall j)).subtype_val
  have hphys : TendstoInDistribution Y atTop Z M (pi₀.1 : Measure (LowValue d×LowValue d)) := by
    refine ⟨fun j=>(hY j).measurable.aemeasurable,continuous_snd.subtype_val.measurable.aemeasurable,?_⟩
    have hh:=(continuous_realLowBidLaw d).continuousAt.tendsto.comp hlim
    convert hh using 1
    funext j
    apply Subtype.ext
    change (M j).map (Y j)=(((lowNoisyLaw d (eps j) (heps j) (hsmall j) mu (pi j)).1 :
      Measure (LowValue d×LowValue d)).map (fun x=>x.2.1))
    change (M j).map (Y j)=((M j).map
      (fun x=>(x.1.1,noisyBid d (eps j) (heps j) (hsmall j) x))).map (fun x=>x.2.1)
    have hpsi : Measurable (fun x : (LowValue d×unitInterval)×unitInterval=>
        (x.1.1,noisyBid d (eps j) (heps j) (hsmall j) x)) :=
      (measurable_fst.comp measurable_fst).prodMk (continuous_noisyBid d (eps j) (heps j) (hsmall j)).measurable
    exact (Measure.map_map (μ:=M j) (measurable_snd.subtype_val) hpsi).symm
    all_goals rfl
  have hi (j : ℕ) : Integrable (fun x=>|X j x-Y j x|) (M j) :=
    (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,((hX j).sub (hY j)).abs⟩).integrable _
  have hclose : Tendsto (fun j=>∫x,|X j x-Y j x| ∂M j) atTop (𝓝 0) := by
    apply squeeze_zero (fun j=>integral_nonneg (fun _=>abs_nonneg _))
      (fun j=>?_) (g:=fun j=>eps j*d) (by simpa using heps0.mul_const d)
    have hh:=integral_mono (hi j) (integrable_const (eps j*d))
      (fun x=>baseBid_noisyBid_distance (heps j) (hsmall j) x)
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh
  have hbase:=FCAppendix.Probability.tendstoInDistribution_of_integral_abs_sub M
    (pi₀.1 : Measure (LowValue d×LowValue d)) X Y Z (fun j=>(hX j).measurable) hphys hi hclose
  convert hbase.tendsto using 1
  funext j
  apply Subtype.ext
  change ((pi j).1 : Measure (LowValue d×unitInterval)).map
    (fun x=>(baseBid d (eps j) (heps j) (hsmall j) x).1)=(M j).map (X j)
  have hp:=(measurePreserving_fst (μ:=((pi j).1 : Measure (LowValue d×unitInterval)))
    (ν:=(volume : Measure unitInterval))).map_eq
  rw [←hp,Measure.map_map (continuous_baseBid d (eps j) (heps j) (hsmall j)).subtype_val.measurable measurable_fst]
  rfl
  all_goals rfl

end FCAppendix.Affine.LowBody
