import FCAppendix.Affine.LowBody.ExactPayoffBounds
import FCAppendix.Affine.LowBody.ZeroClusterLoss

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
variable {N : ℕ}

private theorem pattern_integrable {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4) (G : ProbabilityMeasure (LowValue d)) (w b : ℝ) :
    Integrable (fun r : Fin N→LowValue d=>patternActualPayoff d ξ c kind (w,b,r))
      (Measure.pi (fun _ : Fin N=>(G : Measure (LowValue d)))) := by
  have hm : Measurable (fun r : Fin N→LowValue d=>patternActualPayoff d ξ c kind (w,b,r)) :=
    (measurable_patternActualPayoff hξ hξ1 c kind).comp (by fun_prop)
  exact (integrable_const (|w|+(3+2*|1-ξ|)*|b|)).mono' hm.aestronglyMeasurable
    (ae_of_all _ (fun r=>by simpa only [Real.norm_eq_abs] using
      abs_patternActualPayoff_le hξ hξ1 c kind (w,b,r)))

theorem exactExpectedPayoff_zero_loss {d ξ : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d))
    {w b : ℝ} (hb : 0≤b) (hbw : b≤w) :
    exactExpectedPayoff N d ξ c categories G (w,0)-
      exactExpectedPayoff N d ξ c categories G (w,b)≤2*b := by
  have hξ1 : ξ<1:=by linarith
  have hp (kind : Fin N→Fin 4) : patternExpectedPayoff d ξ c kind G (w,0)-
      patternExpectedPayoff d ξ c kind G (w,b)≤2*b := by
    rw [patternExpectedPayoff,patternExpectedPayoff,
      ←integral_sub (pattern_integrable hξ hξ1 c kind G w 0) (pattern_integrable hξ hξ1 c kind G w b)]
    have hh:=integral_mono ((pattern_integrable hξ hξ1 c kind G w 0).sub
      (pattern_integrable hξ hξ1 c kind G w b)) (integrable_const (2*b))
      (fun r : Fin N→LowValue d=>by
        let omega : Fin N→RowRival:=fun j=>(kind j,(r j).1)
        have hh:=patternPayoff_small_bid_loss c hξ hξh omega (x:=0) le_rfl hb hbw
          (fun j _=>(r j).property.1)
        simpa only [Pi.sub_apply,literalRowPayoff,rowBids,omega,patternActualPayoff_eq_patternPayoff,
          actualPatternBids] using hh)
    simpa only [Pi.sub_apply,integral_const,probReal_univ,smul_eq_mul,one_mul] using hh
  have hh:=(CommonList.iid categories N).expect_le_const hp
  change (CommonList.iid categories N).expect (fun kind=>patternExpectedPayoff d ξ c kind G (w,0))-
    (CommonList.iid categories N).expect (fun kind=>patternExpectedPayoff d ξ c kind G (w,b))≤2*b
  rw [←FiniteLaw.expect_sub]
  exact hh

theorem incumbent_nonneg_of_local_positive_IC {d ξ : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d))
    (pi : Measure (LowValue d×LowValue d))
    (hvalue : ∀ᵐx ∂pi,0<x.1.1)
    (hlocal : ∀b : Ioi (0:ℝ),∀ᵐx ∂pi,b.1<x.1.1→
      exactExpectedPayoff N d ξ c categories G (x.1.1,b.1)≤
        exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1)) :
    ∀ᵐx ∂pi,0≤exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1) := by
  let bidSeq : ℕ→ℝ:=fun k=>1/(k+1)
  have hbid (k : ℕ) : 0<bidSeq k:=by dsimp [bidSeq]; positivity
  have ht : Tendsto bidSeq atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
  have hall : ∀ᵐx ∂pi,∀k : ℕ,bidSeq k<x.1.1→
      exactExpectedPayoff N d ξ c categories G (x.1.1,bidSeq k)≤
        exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1) :=
    ae_all_iff.mpr (fun k=>hlocal ⟨bidSeq k,hbid k⟩)
  filter_upwards [hvalue,hall] with x hx hallx
  have hlo : ∀ᶠk in atTop,-2*bidSeq k≤exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1) :=
    (ht.eventually (Iio_mem_nhds hx)).mono (fun k hk=>
      (exactExpectedPayoff_ge_neg_two_bid hξ hξh c categories G x.1.property.1 (hbid k).le).trans (hallx k hk))
  have hneg : Tendsto (fun k=>-2*bidSeq k) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  exact le_of_tendsto hneg hlo

theorem common_all_bid_IC_of_local_positive_IC {d ξ : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d))
    [NullSingletonClass (G : Measure (LowValue d))]
    (pi : Measure (LowValue d×LowValue d))
    (hvalue : ∀ᵐx ∂pi,0<x.1.1)
    (hlocal : ∀b : Ioi (0:ℝ),∀ᵐx ∂pi,b.1<x.1.1→
      exactExpectedPayoff N d ξ c categories G (x.1.1,b.1)≤
        exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1)) :
    ∀ᵐx ∂pi,∀b : ℝ,0≤b→exactExpectedPayoff N d ξ c categories G (x.1.1,b)≤
      exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1) := by
  have hnonneg:=incumbent_nonneg_of_local_positive_IC hξ hξh c categories G pi hvalue hlocal
  have hfixed (b : Ioi (0:ℝ)) : ∀ᵐx ∂pi,
      exactExpectedPayoff N d ξ c categories G (x.1.1,b.1)≤
        exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1) := by
    filter_upwards [hlocal b,hnonneg] with x hx hn
    by_cases hb : b.1<x.1.1
    · exact hx hb
    · exact (exactExpectedPayoff_nonpos_of_value_le_bid hξ hξh c categories G (le_of_not_gt hb) b.property.le).trans hn
  have hall:=common_positive_bid_IC hξ (by linarith : ξ<1) c categories G pi hfixed
  filter_upwards [hall,hvalue] with x hx hw b hb
  by_cases hbpos : 0<b
  · exact hx b hbpos
  · have hbzero : b=0:=le_antisymm (le_of_not_gt hbpos) hb
    rw [hbzero]
    let bs : ℕ→ℝ:=fun k=>x.1.1/(k+1)
    have hbs (k : ℕ) : 0<bs k := by dsimp [bs]; positivity
    have hbsw (k : ℕ) : bs k≤x.1.1 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<k+1)).mpr
      nlinarith [x.1.property.1,show (0:ℝ)≤k from Nat.cast_nonneg k]
    have hlim : Tendsto bs atTop (𝓝 0) := by
      simpa only [bs,mul_zero,div_eq_mul_inv,one_mul] using
        tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
    have hle (k : ℕ) : exactExpectedPayoff N d ξ c categories G (x.1.1,0)≤
        exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1)+2*bs k := by
      have he:=exactExpectedPayoff_zero_loss (N:=N) hξ hξh c categories G (hbs k).le (hbsw k)
      have hi:=hx (bs k) (hbs k)
      linarith
    have htarget : Tendsto (fun k=>exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1)+2*bs k) atTop
        (𝓝 (exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1))) := by
      simpa only [mul_zero,add_zero] using tendsto_const_nhds.add (tendsto_const_nhds.mul hlim)
    exact ge_of_tendsto htarget (Eventually.of_forall hle)

end FCAppendix.Affine.LowBody
