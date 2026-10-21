import FCAppendix.Affine.LowBody.NoisyPurePayoff
import FCAppendix.Affine.EqualCapacityNative

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def equalPayoff (ξ : ℝ) (c : ℕ) (i : ι) (w : ℝ) (b : ι→ℝ) : ℝ :=
  let p:=EqualCapacity.positiveMarginal ξ c b i
  w*(2*p-p^2)-b i*(2*p-2*ξ*p^2)

theorem abs_equalPayoff_le {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (i : ι) (w : ℝ) (b : ι→ℝ) :
    |equalPayoff ξ c i w b|≤|w|+2*|b i| := by
  have hp:=EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 b
  let p:=EqualCapacity.positiveMarginal ξ c b i
  have hp0 : 0≤p:=hp.1 i
  have hp1 : p≤1:=hp.2.1 i
  have hs : |2*p-p^2|≤1 := abs_le.mpr ⟨by nlinarith,by nlinarith [sq_nonneg (p-1)]⟩
  have hp2 : p^2≤p := by nlinarith
  have hξp : ξ*p^2≤p^2 := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hξ1.le (sq_nonneg p)
  have ha : |2*p-2*ξ*p^2|≤2 := abs_le.mpr
    ⟨by nlinarith,by nlinarith [mul_nonneg hξ.le (sq_nonneg p)]⟩
  calc
    _≤|w*(2*p-p^2)|+|b i*(2*p-2*ξ*p^2)|:=abs_sub _ _
    _=|w| *|2*p-p^2|+|b i| *|2*p-2*ξ*p^2|:=by rw [abs_mul,abs_mul]
    _≤|w| *1+|b i| *2:=add_le_add
      (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
      (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
    _=|w|+2*|b i|:=by ring

def equalNoisyPayoff (ξ ε : ℝ) (c : ℕ) (i : ι) (t : ℝ×(ι→ℝ)) (z : ℝ) : ℝ :=
  equalPayoff ξ c i t.1 (noisyFocal i ε t.2 z)

theorem continuousAt_equalNoisyPayoff {ξ ε : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (hε : 0≤ε) (c : ℕ) (i : ι) (t₀ : ℝ×(ι→ℝ))
    (hb : ∀j,0≤t₀.2 j) (hi : 0<t₀.2 i) (z : ℝ) (hz : 0≤z) :
    ContinuousAt (fun t=>equalNoisyPayoff ξ ε c i t z) t₀ := by
  let bids : ℝ×(ι→ℝ)→(ι→ℝ):=fun t=>noisyFocal i ε t.2 z
  have hbc : Continuous bids := (continuous_noisyFocal i ε).comp
    (continuous_snd.prodMk continuous_const)
  have hb0 : ∀j,0≤bids t₀ j := by
    intro j
    by_cases hji : j=i
    · subst j
      simp only [bids,noisyFocal,Function.update_self]
      exact mul_nonneg (hb i) (by nlinarith [mul_nonneg hε hz])
    · simpa only [bids,noisyFocal,Function.update_of_ne hji] using hb j
  have hbi : 0<bids t₀ i := by
    simp only [bids,noisyFocal,Function.update_self]
    exact mul_pos hi (by nlinarith [mul_nonneg hε hz])
  have hp : ContinuousAt (fun t=>EqualCapacity.positiveMarginal ξ c (bids t) i) t₀ :=
    (EqualCapacity.continuousAt_positiveMarginal_focal hξ hξ1 c (bids t₀) hb0 i hbi).comp
      (f:=bids) (x:=t₀) hbc.continuousAt
  have hbid : ContinuousAt (fun t=>bids t i) t₀ := ((continuous_apply i).comp hbc).continuousAt
  exact ((continuous_fst.continuousAt.mul ((continuousAt_const.mul hp).sub (hp.pow 2))).sub
    (hbid.mul ((continuousAt_const.mul hp).sub (continuousAt_const.mul (hp.pow 2)))))

theorem measurable_equalNoisyPayoff {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (ε : ℝ) (c : ℕ) (i : ι) (t : ℝ×(ι→ℝ)) :
    Measurable (equalNoisyPayoff ξ ε c i t) := by
  have hb : Continuous (fun z : ℝ=>noisyFocal i ε t.2 z) :=
    (continuous_noisyFocal i ε).comp (continuous_const.prodMk continuous_id)
  have hp : Measurable (fun z=>EqualCapacity.positiveMarginal ξ c (noisyFocal i ε t.2 z) i) :=
    (measurable_pi_apply i).comp ((EqualCapacity.measurable_positiveMarginal ξ c hξ hξ1).comp hb.measurable)
  unfold equalNoisyPayoff equalPayoff
  exact (measurable_const.mul ((measurable_const.mul hp).sub (hp.pow_const 2))).sub
    (((measurable_pi_apply i).comp hb.measurable).mul
      ((measurable_const.mul hp).sub (measurable_const.mul (hp.pow_const 2))))

def equalSmoothedPayoff (ξ ε : ℝ) (c : ℕ) (i : ι) (t : ℝ×(ι→ℝ)) : ℝ :=
  ∫z,equalNoisyPayoff ξ ε c i t z ∂uniformNoise

theorem continuousAt_equalSmoothedPayoff {ξ ε : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (hε : 0≤ε) (c : ℕ) (i : ι) (t₀ : ℝ×(ι→ℝ))
    (hb : ∀j,0≤t₀.2 j) (hi : 0<t₀.2 i) :
    ContinuousAt (equalSmoothedPayoff ξ ε c i) t₀ := by
  have hw : ∀ᶠt : ℝ×(ι→ℝ) in 𝓝 t₀,|t.1| < |t₀.1|+1 :=
    (show ContinuousAt (fun t : ℝ×(ι→ℝ)=>|t.1|) t₀ from continuous_fst.abs.continuousAt)
      (Iio_mem_nhds (by linarith))
  have hbid : ∀ᶠt : ℝ×(ι→ℝ) in 𝓝 t₀,|t.2 i| < |t₀.2 i|+1 :=
    (show ContinuousAt (fun t : ℝ×(ι→ℝ)=>|t.2 i|) t₀ from
      ((continuous_apply i).comp continuous_snd).abs.continuousAt)
      (Iio_mem_nhds (by linarith))
  let B : ℝ:=(|t₀.1|+1)+2*((|t₀.2 i|+1)*(1+|ε|))
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun t z=>equalNoisyPayoff ξ ε c i t z) (bound:=fun _=>B)
    (Eventually.of_forall (fun t=>(measurable_equalNoisyPayoff hξ hξ1 ε c i t).aestronglyMeasurable))
    ?_ (integrable_const B) ?_
  · filter_upwards [hw,hbid] with t ht ht'
    filter_upwards [uniformNoise_support] with z hz
    change |equalPayoff ξ c i t.1 (noisyFocal i ε t.2 z)|≤B
    calc
      _≤|t.1|+2*|noisyFocal i ε t.2 z i|:=abs_equalPayoff_le hξ hξ1 c i t.1 _
      _≤|t.1|+2*(|t.2 i| * (1+|ε|)):=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (abs_noisyFocal_le i ε t.2 z hz) (by norm_num))
      _≤B:=add_le_add ht.le (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right ht'.le (by positivity)) (by norm_num))
  · exact uniformNoise_support.mono (fun z hz=>continuousAt_equalNoisyPayoff hξ hξ1 hε c i t₀ hb hi z hz.1)

def parameterEqualPayoff (ξ ε : ℝ) (c : ℕ) (i : ι) (t : ℝ×ℝ×(ι→ℝ)) : ℝ :=
  equalSmoothedPayoff ξ ε c i (parameterBids i t)

theorem abs_parameterEqualPayoff_le {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (ε : ℝ) (c : ℕ) (i : ι) (t : ℝ×ℝ×(ι→ℝ)) :
    |parameterEqualPayoff ξ ε c i t|≤|t.1|+2*(|t.1| *|t.2.1|)*(1+|ε|) := by
  have hb : ∀ᵐz ∂uniformNoise,
      ‖equalNoisyPayoff ξ ε c i (parameterBids i t) z‖≤|t.1|+2*(|t.1| *|t.2.1|)*(1+|ε|) := by
    filter_upwards [uniformNoise_support] with z hz
    let b:=(parameterBids i t).2
    have he : |b i|=|t.1| *|t.2.1| := by simp [b,parameterBids,abs_mul]
    have hn:=abs_noisyFocal_le i ε b z hz
    rw [he] at hn
    change |equalPayoff ξ c i t.1 (noisyFocal i ε b z)|≤_
    have hu:=abs_equalPayoff_le hξ hξ1 c i t.1 (noisyFocal i ε b z)
    linarith
  simpa only [parameterEqualPayoff,equalSmoothedPayoff,Real.norm_eq_abs,
    probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hb

theorem parameterEqualPayoff_at_zero (ξ ε : ℝ) (c : ℕ) (i : ι)
    (t : ℝ×ℝ×(ι→ℝ)) (ht : t.1=0) : parameterEqualPayoff ξ ε c i t=0 := by
  unfold parameterEqualPayoff equalSmoothedPayoff equalNoisyPayoff equalPayoff
  simp [parameterBids,noisyFocal,ht]

theorem continuousAt_parameterEqualPayoff_zero {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (ε : ℝ) (c : ℕ) (i : ι) (t₀ : ℝ×ℝ×(ι→ℝ)) (ht : t₀.1=0) :
    ContinuousAt (parameterEqualPayoff ξ ε c i) t₀ := by
  have hcont : Continuous (fun t : ℝ×ℝ×(ι→ℝ)=>|t.1|+2*(|t.1| *|t.2.1|)*(1+|ε|)) := by fun_prop
  have hg : Tendsto (fun t : ℝ×ℝ×(ι→ℝ)=>|t.1|+2*(|t.1| *|t.2.1|)*(1+|ε|))
      (𝓝 t₀) (𝓝 (0:ℝ)) := by simpa only [ht,abs_zero,mul_zero,zero_mul,add_zero] using hcont.tendsto t₀
  change Tendsto _ (𝓝 t₀) (𝓝 (parameterEqualPayoff ξ ε c i t₀))
  rw [parameterEqualPayoff_at_zero ξ ε c i t₀ ht]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _=>norm_nonneg _)
    (fun t=>by simpa only [Real.norm_eq_abs] using abs_parameterEqualPayoff_le hξ hξ1 ε c i t) hg

theorem continuousAt_parameterEqualPayoff {ξ ε : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (hε : 0≤ε) (c : ℕ) (i : ι) (t₀ : ℝ×ℝ×(ι→ℝ))
    (hw : 0≤t₀.1) (hq : 0<t₀.2.1) (hb : ∀j,0≤t₀.2.2 j) :
    ContinuousAt (parameterEqualPayoff ξ ε c i) t₀ := by
  by_cases hw0 : t₀.1=0
  · exact continuousAt_parameterEqualPayoff_zero hξ hξ1 ε c i t₀ hw0
  · have hwpos : 0<t₀.1:=lt_of_le_of_ne hw (Ne.symm hw0)
    have hb' : ∀j,0≤(parameterBids i t₀).2 j := by
      intro j
      by_cases hji : j=i
      · subst j
        simpa only [parameterBids,Function.update_self] using (mul_pos hwpos hq).le
      · simpa only [parameterBids,Function.update_of_ne hji] using hb j
    have hi : 0<(parameterBids i t₀).2 i := by
      simpa only [parameterBids,Function.update_self] using mul_pos hwpos hq
    exact (continuousAt_equalSmoothedPayoff hξ hξ1 hε c i (parameterBids i t₀) hb' hi).comp
      (f:=parameterBids i) (x:=t₀) (continuous_parameterBids i).continuousAt

theorem continuous_parameterEqualPayoff_nonnegative {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0≤ε) (c : ℕ) (i : ι) :
    Continuous (fun t : Ici (0:ℝ)×Ioi (0:ℝ)×(ι→Ici (0:ℝ))=>
      parameterEqualPayoff ξ ε c i (t.1.1,t.2.1.1,fun j=>(t.2.2 j).1)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hmap : Continuous (fun t : Ici (0:ℝ)×Ioi (0:ℝ)×(ι→Ici (0:ℝ))=>
      (t.1.1,t.2.1.1,fun j=>(t.2.2 j).1)) := by fun_prop
  exact (continuousAt_parameterEqualPayoff hξ hξ1 hε c i
    (t.1.1,t.2.1.1,fun j=>(t.2.2 j).1) t.1.2 t.2.1.2 (fun j=>(t.2.2 j).2)).comp
      (f:=fun t : Ici (0:ℝ)×Ioi (0:ℝ)×(ι→Ici (0:ℝ))=>
        (t.1.1,t.2.1.1,fun j=>(t.2.2 j).1)) (x:=t) hmap.continuousAt

end FCAppendix.Affine.LowBody
