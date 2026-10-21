import FCAppendix.Affine.LowBody.PatternNullSet

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Filter Topology MeasureTheory ProbabilityTheory
open Existence.Distributional

variable {N : ℕ}

def patternExpectedPayoff (d ξ : ℝ) (c : ℕ) (kind : Fin N→Fin 4)
    (G : ProbabilityMeasure (LowValue d)) (t : ℝ×ℝ) : ℝ :=
  ∫r,patternActualPayoff d ξ c kind (t.1,t.2,r)
    ∂Measure.pi (fun _ : Fin N=>(G : Measure (LowValue d)))

theorem continuousAt_patternExpectedPayoff {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4) (G : ProbabilityMeasure (LowValue d))
    [NullSingletonClass (G : Measure (LowValue d))] (t0 : ℝ×ℝ) (hb : 0<t0.2) :
    ContinuousAt (patternExpectedPayoff d ξ c kind G) t0 := by
  let muR : Measure (Fin N→LowValue d):=Measure.pi (fun _ : Fin N=>(G : Measure (LowValue d)))
  have hw : ∀ᶠt : ℝ×ℝ in 𝓝 t0,|t.1| < |t0.1|+1 :=
    (continuous_fst.abs.continuousAt) (Iio_mem_nhds (by linarith))
  have hbid : ∀ᶠt : ℝ×ℝ in 𝓝 t0,|t.2| < |t0.2|+1 :=
    (continuous_snd.abs.continuousAt) (Iio_mem_nhds (by linarith))
  let C : ℝ:=(|t0.1|+1)+(3+2*|1-ξ|)*(|t0.2|+1)
  have hm (t : ℝ×ℝ) : AEStronglyMeasurable
      (fun r : Fin N→LowValue d=>patternActualPayoff d ξ c kind (t.1,t.2,r)) muR := by
    have hi : Measurable (fun r : Fin N→LowValue d=>(t.1,t.2,r)) := by fun_prop
    exact ((measurable_patternActualPayoff hξ hξ1 c kind).comp hi).aestronglyMeasurable
  have hdom : ∀ᶠt : ℝ×ℝ in 𝓝 t0,∀ᵐr ∂muR,
      ‖patternActualPayoff d ξ c kind (t.1,t.2,r)‖≤C := by
    filter_upwards [hw,hbid] with t ht ht'
    exact ae_of_all _ (fun r=>by
      rw [Real.norm_eq_abs]
      exact (abs_patternActualPayoff_le hξ hξ1 c kind (t.1,t.2,r)).trans
        (by dsimp [C]; nlinarith [abs_nonneg (1-ξ)]))
  have hcont : ∀ᵐr ∂muR,ContinuousAt
      (fun t : ℝ×ℝ=>patternActualPayoff d ξ c kind (t.1,t.2,r)) t0 := by
    filter_upwards [ae_continuousAt_patternActualPayoff hξ hξ1 hb (G : Measure (LowValue d)) c kind] with r hr
    exact (hr t0.1).comp (f:=fun t : ℝ×ℝ=>(t.1,t.2,r)) (x:=t0) (by fun_prop)
  exact MeasureTheory.continuousAt_of_dominated (μ:=muR)
    (F:=fun (t : ℝ×ℝ) (r : Fin N→LowValue d)=>patternActualPayoff d ξ c kind (t.1,t.2,r))
    (bound:=fun _=>C) (Eventually.of_forall hm) hdom (integrable_const C) hcont

def exactExpectedPayoff (N : ℕ) (d ξ : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (G : ProbabilityMeasure (LowValue d)) (t : ℝ×ℝ) : ℝ :=
  ∑kind : Fin N→Fin 4,(CommonList.iid categories N).mass kind*
    patternExpectedPayoff d ξ c kind G t

theorem continuousAt_exactExpectedPayoff {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d))
    [NullSingletonClass (G : Measure (LowValue d))] (t0 : ℝ×ℝ) (hb : 0<t0.2) :
    ContinuousAt (exactExpectedPayoff N d ξ c categories G) t0 := by
  apply tendsto_finsetSum
  intro kind _
  exact continuousAt_const.mul (continuousAt_patternExpectedPayoff hξ hξ1 c kind G t0 hb)

private theorem dense_common_IC {X : Type*} [MeasurableSpace X] (pi : Measure X)
    (u : X→Ioi (0:ℝ)→ℝ) (current : X→ℝ) (hu : ∀x,Continuous (u x))
    (hfixed : ∀b : Ioi (0:ℝ),∀ᵐx ∂pi,u x b≤current x) :
    ∀ᵐx ∂pi,∀b : Ioi (0:ℝ),u x b≤current x := by
  obtain ⟨D,hDc,hDd⟩:=TopologicalSpace.exists_countable_dense (Ioi (0:ℝ))
  have hfixedD : ∀b∈D,∀ᵐx ∂pi,u x b≤current x := fun b _=>hfixed b
  have hall : ∀ᵐx ∂pi,∀b∈D,u x b≤current x := (ae_ball_iff hDc).mpr hfixedD
  filter_upwards [hall] with x hx
  have hclosed : IsClosed {b : Ioi (0:ℝ) | u x b≤current x} := isClosed_le (hu x) continuous_const
  have hs:=closure_minimal (fun b hb=>hx b hb) hclosed
  intro b
  exact hs (hDd.closure_eq ▸ mem_univ b)

theorem common_positive_bid_IC {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d))
    [NullSingletonClass (G : Measure (LowValue d))]
    (pi : Measure (LowValue d×LowValue d))
    (hfixed : ∀b : Ioi (0:ℝ),∀ᵐx ∂pi,
      exactExpectedPayoff N d ξ c categories G (x.1.1,b.1)≤
        exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1)) :
    ∀ᵐx ∂pi,∀b : ℝ,0<b→exactExpectedPayoff N d ξ c categories G (x.1.1,b)≤
      exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1) := by
  have hu (x : LowValue d×LowValue d) : Continuous
      (fun b : Ioi (0:ℝ)=>exactExpectedPayoff N d ξ c categories G (x.1.1,b.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro b
    have hm : ContinuousAt (fun z : Ioi (0:ℝ)=>(x.1.1,z.1)) b := by fun_prop
    simpa only [Function.comp_def] using
      (continuousAt_exactExpectedPayoff (N:=N) hξ hξ1 c categories G (x.1.1,b.1) b.property).comp
        (f:=fun z : Ioi (0:ℝ)=>(x.1.1,z.1)) (x:=b) hm
  have hh:=dense_common_IC pi
    (fun (x : LowValue d×LowValue d) (b : Ioi (0:ℝ))=>exactExpectedPayoff N d ξ c categories G (x.1.1,b.1))
    (fun x=>exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1)) hu hfixed
  exact hh.mono (fun _ hx b hb=>hx ⟨b,hb⟩)

end FCAppendix.Affine.LowBody
