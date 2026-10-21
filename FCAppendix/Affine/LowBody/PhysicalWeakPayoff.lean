import FCAppendix.Affine.LowBody.PatternNullSet

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Filter Topology MeasureTheory ProbabilityTheory
open Existence.Distributional

variable {N : ℕ}

theorem rowLaw_eq_measure_pi {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [CompactSpace X] [TopologicalSpace.MetrizableSpace X] [BorelSpace X]
    (N : ℕ) (mu : ProbabilityMeasure X) :
    (rowLaw N mu : Measure (Fin N→X))=Measure.pi (fun _ : Fin N=>(mu : Measure X)) := by
  induction N with
  | zero => exact (Measure.pi_of_empty _ (fun i=>Fin.elim0 i)).symm
  | succ N ih =>
    let e:=MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1)=>X) (0:Fin (N+1))
    have hp:=MeasurePreserving.symm e (measurePreserving_piFinSuccAbove
      (fun _ : Fin (N+1)=>(mu : Measure X)) (0:Fin (N+1)))
    have he : (fun p : X×(Fin N→X)=>Fin.cons p.1 p.2)=e.symm := by
      funext p
      ext i
      refine Fin.cases ?_ (fun j=>?_) i <;>
        simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
    change (((mu : Measure X).prod (rowLaw N mu : Measure (Fin N→X))).map
      (fun p=>Fin.cons (α:=fun _ : Fin (N+1)=>X) p.1 p.2))=_
    rw [ih,he]
    exact hp.map_eq

def physicalPatternPayoff (d ξ : ℝ) (c : ℕ) (kind : Fin N→Fin 4)
    (t : (LowValue d×LowValue d)×(Fin N→LowValue d)) : ℝ :=
  patternActualPayoff d ξ c kind (physicalPatternInput d t)

def physicalPatternBadSet (d κ : ℝ) (kind : Fin N→Fin 4) :
    Set ((LowValue d×LowValue d)×(Fin N→LowValue d)) :=
  physicalPatternInput d ⁻¹' patternBadSet d κ kind

theorem abs_physicalPatternPayoff_le {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4)
    (t : (LowValue d×LowValue d)×(Fin N→LowValue d)) :
    |physicalPatternPayoff d ξ c kind t|≤(4+2*|1-ξ|)*|d| := by
  have hh:=abs_patternActualPayoff_le hξ hξ1 c kind (physicalPatternInput d t)
  have hw : |t.1.1.1|≤|d| := by
    rw [abs_of_nonneg t.1.1.property.1]
    exact t.1.1.property.2.trans (le_abs_self d)
  have hb : |t.1.2.1|≤|d| := by
    rw [abs_of_nonneg t.1.2.property.1]
    exact t.1.2.property.2.trans (le_abs_self d)
  exact hh.trans (by dsimp only [physicalPatternInput]; nlinarith [abs_nonneg (1-ξ)])

theorem physicalPatternBadSet_null {d κ : ℝ} (hκ : 0<κ)
    (pi0 : ProbabilityMeasure (LowValue d×LowValue d))
    (G0 : ProbabilityMeasure (LowValue d)) [NullSingletonClass (G0 : Measure (LowValue d))]
    (hpos : ∀ᵐx ∂(pi0 : Measure (LowValue d×LowValue d)),0<x.2.1) (kind : Fin N→Fin 4) :
    (productLaw pi0 (rowLaw N G0) : Measure _) (physicalPatternBadSet d κ kind)=0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  change ∀ᵐt ∂((pi0 : Measure (LowValue d×LowValue d)).prod
    ((rowLaw N G0) : Measure (Fin N→LowValue d))),_
  rw [rowLaw_eq_measure_pi]
  exact ae_physicalPattern_not_bad (d:=d) (N:=N) hκ
    (pi0 : Measure (LowValue d×LowValue d)) (G0 : Measure (LowValue d)) hpos kind

theorem tendsto_integral_physicalPatternPayoff {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4)
    (pi0 : ProbabilityMeasure (LowValue d×LowValue d))
    (G0 : ProbabilityMeasure (LowValue d)) [NullSingletonClass (G0 : Measure (LowValue d))]
    (hpos : ∀ᵐx ∂(pi0 : Measure (LowValue d×LowValue d)),0<x.2.1)
    (M : ℕ→ProbabilityMeasure ((LowValue d×LowValue d)×(Fin N→LowValue d)))
    (ht : Tendsto M atTop (𝓝 (productLaw pi0 (rowLaw N G0)))) :
    Tendsto (fun j=>∫t,physicalPatternPayoff d ξ c kind t ∂(M j : Measure _)) atTop
      (𝓝 (∫t,physicalPatternPayoff d ξ c kind t ∂(productLaw pi0 (rowLaw N G0) : Measure _))) := by
  have hs : IsClosed (physicalPatternBadSet d (1-ξ) kind) :=
    (isClosed_patternBadSet d (1-ξ) kind).preimage (continuous_physicalPatternInput d)
  have hnull:=physicalPatternBadSet_null (sub_pos.mpr hξ1) pi0 G0 hpos kind
  apply tendsto_integral_of_closed_null_discontinuities
    (physicalPatternPayoff d ξ c kind)
    ((measurable_patternActualPayoff hξ hξ1 c kind).comp (continuous_physicalPatternInput d).measurable)
    (physicalPatternBadSet d (1-ξ) kind) hs
    (fun t ht=>(continuousAt_patternActualPayoff_of_not_mem_bad hξ hξ1 c kind _ ht).comp
      (continuous_physicalPatternInput d).continuousAt)
    (show 0≤(4+2*|1-ξ|)*|d| by positivity)
    (abs_physicalPatternPayoff_le hξ hξ1 c kind) M _ ht hnull

theorem tendsto_integral_physicalPatternTest {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4)
    (a : C((LowValue d×LowValue d)×(Fin N→LowValue d),ℝ))
    (pi0 : ProbabilityMeasure (LowValue d×LowValue d))
    (G0 : ProbabilityMeasure (LowValue d)) [NullSingletonClass (G0 : Measure (LowValue d))]
    (hpos : ∀ᵐx ∂(pi0 : Measure (LowValue d×LowValue d)),0<x.2.1)
    (M : ℕ→ProbabilityMeasure ((LowValue d×LowValue d)×(Fin N→LowValue d)))
    (ht : Tendsto M atTop (𝓝 (productLaw pi0 (rowLaw N G0)))) :
    Tendsto (fun j=>∫t,a t*physicalPatternPayoff d ξ c kind t ∂(M j : Measure _)) atTop
      (𝓝 (∫t,a t*physicalPatternPayoff d ξ c kind t
        ∂(productLaw pi0 (rowLaw N G0) : Measure _))) := by
  have hs : IsClosed (physicalPatternBadSet d (1-ξ) kind) :=
    (isClosed_patternBadSet d (1-ξ) kind).preimage (continuous_physicalPatternInput d)
  apply tendsto_integral_of_closed_null_discontinuities
    (fun t=>a t*physicalPatternPayoff d ξ c kind t)
    (a.continuous.measurable.mul ((measurable_patternActualPayoff hξ hξ1 c kind).comp
      (continuous_physicalPatternInput d).measurable))
    (physicalPatternBadSet d (1-ξ) kind) hs
    (fun t ht=>a.continuous.continuousAt.mul
      ((continuousAt_patternActualPayoff_of_not_mem_bad hξ hξ1 c kind _ ht).comp
        (continuous_physicalPatternInput d).continuousAt))
    (show 0≤‖a‖*((4+2*|1-ξ|)*|d|) by positivity) ?_ M _ ht
    (physicalPatternBadSet_null (sub_pos.mpr hξ1) pi0 G0 hpos kind)
  intro t
  rw [abs_mul]
  exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm t)
    (abs_physicalPatternPayoff_le hξ hξ1 c kind t) (abs_nonneg _) (norm_nonneg _)

def physicalJointRowLaw (N : ℕ) {d : ℝ} (pi : ProbabilityMeasure (LowValue d×LowValue d)) :
    ProbabilityMeasure ((LowValue d×LowValue d)×(Fin N→LowValue d)) :=
  productLaw pi (rowLaw N (pi.map measurable_snd.aemeasurable))

theorem continuous_physicalJointRowLaw (N : ℕ) (d : ℝ) :
    Continuous (physicalJointRowLaw N (d:=d)) :=
  continuous_productLaw.comp (continuous_id.prodMk
    ((continuous_rowLaw N).comp (ProbabilityMeasure.continuous_map continuous_snd)))

end FCAppendix.Affine.LowBody
