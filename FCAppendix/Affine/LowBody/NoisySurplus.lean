import FCAppendix.Affine.LowBody.ResidualOutcomes

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional
open scoped BigOperators
variable {N : ℕ}

def quarterChoice : unitInterval:=⟨1/4,by norm_num,by norm_num⟩

theorem quarterChoice_bid_le_half {ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/4)
    (z : ℝ) (hz : z∈Icc (0:ℝ) 1) : bidRatio ε quarterChoice*(1+ε*z)≤1/2 := by
  have hden : 0<1+ε:=by linarith
  have hr : 0≤bidRatio ε quarterChoice :=
    hε.le.trans (bidRatio_bounds hε (by linarith) quarterChoice).1
  have hn : 1+ε*z≤1+ε:=by nlinarith [hz.2]
  have hp :=mul_le_mul_of_nonneg_left hn hr
  have he : bidRatio ε quarterChoice*(1+ε)≤1/2 := by
    unfold bidRatio quarterChoice
    dsimp only
    field_simp
    nlinarith [mul_nonneg hε.le (show 0≤1/4-ε by linarith)]
  exact hp.trans he

def patternNoisyBids (d ε : ℝ) (kind : Fin N→Fin 4)
    (w : LowValue d) (q : unitInterval) (b : Fin N→LowValue d) (z : ℝ) : Fin (N+1)→ℝ :=
  noisyFocal 0 ε (parameterBids 0 (w.1,bidRatio ε q,patternBids kind d b)).2 z

theorem patternNoisyBids_focal (d ε : ℝ) (kind : Fin N→Fin 4)
    (w : LowValue d) (q : unitInterval) (b : Fin N→LowValue d) (z : ℝ) :
    patternNoisyBids d ε kind w q b z 0=w.1*bidRatio ε q*(1+ε*z) := by
  simp [patternNoisyBids,noisyFocal,parameterBids]

theorem patternNoisyBids_mask (d ε : ℝ) (c : ℕ) (kind : Fin N→Fin 4)
    (w : LowValue d) (q : unitInterval) (b : Fin N→LowValue d) (z : ℝ)
    (i : Fin (N+1)) (hi : i∉(patternTemplate c kind).support) :
    patternNoisyBids d ε kind w q b z i=0 := by
  have hn : i≠0 := by
    intro he
    exact hi (he.symm ▸ focal_mem_patternTemplate c kind)
  simp only [patternNoisyBids,noisyFocal,Function.update_of_ne hn,parameterBids]
  cases i using Fin.cases with
  | zero => exact False.elim (hn rfl)
  | succ j =>
    have hj : kind j≠0 := by
      intro he
      exact hi (by simp [patternTemplate,rowLowList,patternRow,he])
    simp [patternBids,hj]

theorem patternSmoothedPayoff_eq_integral (d ξ ε : ℝ) (c : ℕ) (kind : Fin N→Fin 4)
    (w : LowValue d) (q : unitInterval) (b : Fin N→LowValue d) :
    patternSmoothedPayoff d ξ ε c kind ((w,q),b)=
      ∫z,patternPayoff ξ c kind w.1 (patternNoisyBids d ε kind w q b z) ∂uniformNoise := by
  unfold patternSmoothedPayoff patternPayoff
  dsimp only
  split_ifs with heq
  · rfl
  · rfl

theorem measurable_patternNoisyPayoff (d : ℝ) {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (ε : ℝ) (c : ℕ) (kind : Fin N→Fin 4) (w : LowValue d) (q : unitInterval)
    (b : Fin N→LowValue d) :
    Measurable (fun z=>patternPayoff ξ c kind w.1 (patternNoisyBids d ε kind w q b z)) := by
  unfold patternPayoff
  dsimp only
  split_ifs
  · change Measurable (equalNoisyPayoff ξ ε (patternTemplate c kind).residual₀
      (0:Fin (N+1)) (parameterBids 0 (w.1,bidRatio ε q,patternBids kind d b)))
    exact measurable_equalNoisyPayoff hξ hξ1 ε _ (0:Fin (N+1)) _
  · exact measurable_pureNoisyPayoff
      (fun P : (patternTemplate c kind).Candidate=>P.val) (1-ξ) ε 0 _

theorem integrable_patternNoisyPayoff (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (kind : Fin N→Fin 4) (w : LowValue d) (q : unitInterval)
    (b : Fin N→LowValue d) :
    Integrable (fun z=>patternPayoff ξ c kind w.1 (patternNoisyBids d ε kind w q b z)) uniformNoise := by
  have hξ1 : ξ<1:=by linarith
  apply Integrable.of_bound (measurable_patternNoisyPayoff d hξ hξ1 ε c kind w q b).aestronglyMeasurable
    (3*w.1)
  filter_upwards [uniformNoise_support] with z hz
  have hb:=noisyBid_bounds hε hsmall w q (⟨z,hz⟩ : unitInterval)
  rw [←patternNoisyBids_focal d ε kind w q b z] at hb
  rw [Real.norm_eq_abs,abs_le,patternPayoff_outcomes]
  have hout:=pattern_outcomes_bounds hξ hξ1 c kind (patternNoisyBids d ε kind w q b z)
  have hs:=mul_nonneg (sub_nonneg.mpr hb.2) hout.1
  have hsu:=mul_le_mul_of_nonneg_left hout.2.1 (sub_nonneg.mpr hb.2)
  have hc : 0≤(1-2*ξ)*patternNoisyBids d ε kind w q b z 0 :=
    mul_nonneg (by linarith) hb.1
  have hcu : (1-2*ξ)*patternNoisyBids d ε kind w q b z 0≤w.1 := by
    nlinarith [hb.1,hb.2,mul_nonneg hξ.le hb.1]
  have hd:=mul_nonneg hc hout.2.2.1
  have hdu:=mul_le_mul_of_nonneg_left hout.2.2.2 hc
  constructor <;> nlinarith [w.property.1,hb.1,hb.2]

theorem patternSmoothedPayoff_le_surplus (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (kind : Fin N→Fin 4) (w : LowValue d) (q : unitInterval)
    (b : Fin N→LowValue d) :
    patternSmoothedPayoff d ξ ε c kind ((w,q),b)≤w.1-w.1*bidRatio ε q := by
  rw [patternSmoothedPayoff_eq_integral]
  have hi:=integrable_patternNoisyPayoff d hξ hξh hε hsmall c kind w q b
  suffices hh : ∫z,patternPayoff ξ c kind w.1 (patternNoisyBids d ε kind w q b z) ∂uniformNoise≤
      ∫_z : ℝ,(w.1-w.1*bidRatio ε q) ∂uniformNoise by
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh
  apply integral_mono_ae hi (integrable_const _)
  filter_upwards [uniformNoise_support] with z hz
  have hb:=noisyBid_bounds hε hsmall w q (⟨z,hz⟩ : unitInterval)
  rw [←patternNoisyBids_focal d ε kind w q b z] at hb
  have hbase : w.1*bidRatio ε q≤patternNoisyBids d ε kind w q b z 0 := by
    rw [patternNoisyBids_focal]
    have hr:=hε.le.trans (bidRatio_bounds hε hsmall q).1
    nlinarith [mul_nonneg (mul_nonneg w.property.1 hr) (mul_nonneg hε.le hz.1)]
  unfold patternPayoff
  dsimp only
  split_ifs
  · exact (equalPayoff_le_value_sub_bid hξ hξh _ _ _ hb.1 hb.2).trans (by linarith)
  · exact (purePayoff_le_value_sub_bid (by linarith : 1/2≤1-ξ) _ _ _ hb.1 hb.2).trans (by linarith)

theorem patternSmoothedPayoff_comparison_lower (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (hε : 0<ε) (hsmall : ε≤1/4)
    (c : ℕ) (kind : Fin N→Fin 4) (w : LowValue d) (hw : 0<w.1)
    (b : Fin N→LowValue d) :
    w.1/2*((if LocalUnderflow c 0 kind then 1 else 0)-(if BothUnderflow c kind then 1 else 0))≤
      patternSmoothedPayoff d ξ ε c kind ((w,quarterChoice),b) := by
  rw [patternSmoothedPayoff_eq_integral]
  have hi:=integrable_patternNoisyPayoff d hξ hξh hε (by linarith) c kind w quarterChoice b
  have hh:=integral_mono_ae (integrable_const
    (w.1/2*((if LocalUnderflow c 0 kind then 1 else 0)-(if BothUnderflow c kind then 1 else 0)))) hi
    (show ∀ᵐz ∂uniformNoise,_≤patternPayoff ξ c kind w.1
      (patternNoisyBids d ε kind w quarterChoice b z) from ?_)
  · simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh
  · filter_upwards [uniformNoise_support] with z hz
    apply patternPayoff_comparison_lower hξ hξh c kind
    · rw [patternNoisyBids_focal]
      have hr:=hε.trans_le (bidRatio_bounds hε (by linarith) quarterChoice).1
      exact mul_pos (mul_pos hw hr) (by nlinarith [mul_nonneg hε.le hz.1])
    · rw [patternNoisyBids_focal]
      have hq:=mul_le_mul_of_nonneg_left (quarterChoice_bid_le_half hε hsmall z hz) w.property.1
      nlinarith
    · exact patternNoisyBids_mask d ε c kind w quarterChoice b z

end FCAppendix.Affine.LowBody
