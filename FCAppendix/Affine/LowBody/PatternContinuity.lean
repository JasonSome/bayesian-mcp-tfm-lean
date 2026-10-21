import FCAppendix.Affine.LowBody.NullHyperplanes

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Filter Topology MeasureTheory ProbabilityTheory

variable {N : ℕ}

def patternPurePayoff (d κ : ℝ) (c : ℕ) (kind : Fin N→Fin 4)
    (t : ℝ×ℝ×(Fin N→LowValue d)) : ℝ :=
  let T:=patternTemplate c kind
  let b:=actualPatternBids kind d t.2.1 t.2.2
  purePayoff κ t.1 b (T.selection κ b) 0

def patternActualPayoff (d ξ : ℝ) (c : ℕ) (kind : Fin N→Fin 4)
    (t : ℝ×ℝ×(Fin N→LowValue d)) : ℝ :=
  let T:=patternTemplate c kind
  let b:=actualPatternBids kind d t.2.1 t.2.2
  if T.residual₀=T.residual₁ then equalPayoff ξ T.residual₀ 0 t.1 b
  else patternPurePayoff d (1-ξ) c kind t

theorem ae_continuousAt_patternPurePayoff {d κ b : ℝ} (hκ : 0<κ) (hb : b≠0)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (c : ℕ) (kind : Fin N→Fin 4) :
    ∀ᵐr ∂Measure.pi (fun _ : Fin N=>mu),∀w : ℝ,
      ContinuousAt (patternPurePayoff d κ c kind) (w,b,r) := by
  filter_upwards [ae_pattern_ties_same_focalCopy hκ hb mu kind] with r hr w
  let T:=patternTemplate c kind
  let bids : (ℝ×ℝ×(Fin N→LowValue d))→(Fin (N+1)→ℝ) :=
    fun t=>actualPatternBids kind d t.2.1 t.2.2
  have hbc : Continuous bids := (continuous_actualPatternBids kind d).comp
    (continuous_snd.fst.prodMk continuous_snd.snd)
  apply continuousAt_selected_payoff
    (fun t (P : T.Candidate)=>CompleteInformation.potential κ (bids t) P.val.1 P.val.2)
    (fun P=>(continuous_potential κ P.val).comp hbc)
    (fun P : T.Candidate=>focalCopy P.val 0)
    (fun t (P : T.Candidate)=>purePayoff κ t.1 (bids t) P.val 0)
    (fun P=>by unfold purePayoff; split_ifs <;> fun_prop)
    (fun t P Q h=>purePayoff_eq_of_focalCopy_eq κ t.1 (bids t) P.val Q.val 0 h)
    (w,b,r)
  exact fun P Q he=>hr P.val Q.val he

theorem continuousAt_patternEqualPayoff {d ξ b : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (hb : 0<b)
    (c : ℕ) (kind : Fin N→Fin 4) (r : Fin N→LowValue d) (w : ℝ) :
    ContinuousAt (fun t : ℝ×ℝ×(Fin N→LowValue d)=>
      equalPayoff ξ c (0:Fin (N+1)) t.1 (actualPatternBids kind d t.2.1 t.2.2)) (w,b,r) := by
  let bids : (ℝ×ℝ×(Fin N→LowValue d))→(Fin (N+1)→ℝ) :=
    fun t=>actualPatternBids kind d t.2.1 t.2.2
  have hbc : Continuous bids := (continuous_actualPatternBids kind d).comp
    (continuous_snd.fst.prodMk continuous_snd.snd)
  have hpos (i : Fin (N+1)) : 0≤bids (w,b,r) i := by
    refine Fin.cases hb.le (fun j=>?_) i
    dsimp [bids,actualPatternBids]
    simp only [Fin.cons_succ]
    split_ifs
    · exact (r j).property.1
    · exact le_rfl
  have hp:= (EqualCapacity.continuousAt_positiveMarginal_focal hξ hξ1 c (bids (w,b,r)) hpos
    (0:Fin (N+1)) hb).comp (f:=bids) (x:=(w,b,r)) hbc.continuousAt
  have hbid : ContinuousAt (fun t=>bids t 0) (w,b,r) := ((continuous_apply 0).comp hbc).continuousAt
  exact ((continuous_fst.continuousAt.mul ((continuousAt_const.mul hp).sub (hp.pow 2))).sub
    (hbid.mul ((continuousAt_const.mul hp).sub (continuousAt_const.mul (hp.pow 2)))))

theorem ae_continuousAt_patternActualPayoff {d ξ b : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (hb : 0<b)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (c : ℕ) (kind : Fin N→Fin 4) :
    ∀ᵐr ∂Measure.pi (fun _ : Fin N=>mu),∀w : ℝ,
      ContinuousAt (patternActualPayoff d ξ c kind) (w,b,r) := by
  by_cases heq : (patternTemplate c kind).residual₀=(patternTemplate c kind).residual₁
  · have hfun : patternActualPayoff d ξ c kind=(fun t : ℝ×ℝ×(Fin N→LowValue d)=>
        equalPayoff ξ (patternTemplate c kind).residual₀ 0 t.1 (actualPatternBids kind d t.2.1 t.2.2)) := by
      funext t
      exact if_pos heq
    rw [hfun]
    exact ae_of_all _ (fun r w=>continuousAt_patternEqualPayoff hξ hξ1 hb
      (patternTemplate c kind).residual₀ kind r w)
  · have hfun : patternActualPayoff d ξ c kind=patternPurePayoff d (1-ξ) c kind := by
      funext t
      exact if_neg heq
    rw [hfun]
    exact ae_continuousAt_patternPurePayoff (sub_pos.mpr hξ1) hb.ne' mu c kind

theorem abs_patternActualPayoff_le {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4) (t : ℝ×ℝ×(Fin N→LowValue d)) :
    |patternActualPayoff d ξ c kind t|≤|t.1|+(3+2*|1-ξ|)*|t.2.1| := by
  dsimp only [patternActualPayoff]
  split_ifs
  · have hh:=abs_equalPayoff_le hξ hξ1 (patternTemplate c kind).residual₀ (0:Fin (N+1))
      t.1 (actualPatternBids kind d t.2.1 t.2.2)
    change |equalPayoff ξ (patternTemplate c kind).residual₀ 0 t.1
      (actualPatternBids kind d t.2.1 t.2.2)|≤|t.1|+2*|t.2.1| at hh
    exact hh.trans (by nlinarith [abs_nonneg (1-ξ),abs_nonneg t.2.1])
  · have hh:=abs_purePayoff_le (1-ξ) t.1 (actualPatternBids kind d t.2.1 t.2.2)
      ((patternTemplate c kind).selection (1-ξ) (actualPatternBids kind d t.2.1 t.2.2)) 0
    simp only [actualPatternBids,Fin.cons_zero] at hh
    exact hh.trans (by nlinarith [abs_nonneg t.2.1])

theorem patternSmoothedPayoff_eq_integral_patternActualPayoff (d ξ ε : ℝ) (c : ℕ)
    (kind : Fin N→Fin 4) (t : (LowValue d×unitInterval)×(Fin N→LowValue d)) :
    patternSmoothedPayoff d ξ ε c kind t=
      ∫z,patternActualPayoff d ξ c kind (t.1.1.1,t.1.1.1*bidRatio ε t.1.2*(1+ε*z),t.2) ∂uniformNoise := by
  have he (z : ℝ) :
      noisyFocal (0:Fin (N+1)) ε
        (parameterBids 0 (t.1.1.1,bidRatio ε t.1.2,patternBids kind d t.2)).2 z=
      actualPatternBids kind d (t.1.1.1*bidRatio ε t.1.2*(1+ε*z)) t.2 := by
    ext i
    refine Fin.cases ?_ (fun j=>?_) i <;>
      simp [noisyFocal,parameterBids,actualPatternBids,patternBids]
  unfold patternSmoothedPayoff patternActualPayoff
  dsimp only
  split_ifs with hcap
  · unfold parameterEqualPayoff equalSmoothedPayoff equalNoisyPayoff
    apply integral_congr_ae
    exact ae_of_all _ (fun z=>by dsimp only; rw [he]; rfl)
  · apply integral_congr_ae
    apply ae_of_all
    intro z
    unfold PureTemplate.noisyUserPayoff patternPurePayoff
    rw [he]
    rfl

end FCAppendix.Affine.LowBody
