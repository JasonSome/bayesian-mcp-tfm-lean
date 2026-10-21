import FCAppendix.Affine.Tail04.SourceAmbientPartialPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.AmbientLocalizedTests
open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws FixedAmbientNoise
open FiniteTailNoisyGame SourceAmbientLaws AmbientFiniteGame

section Active
variable (D : Data) (A H0 H1 : ℕ) (reg low : Bool)
  {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [MetrizableSpace X]
  (v : C(X,ℝ)) (action : C(X,Icc (1:ℝ) D.U)) (a : C(X,ℝ))
  (e : Noise D.eps) (μP : ProbabilityMeasure (Icc D.R D.Up))
  (μA : ProbabilityMeasure (Icc (1:ℝ) D.U)) (π : ProbabilityMeasure X)

lemma active_test :
    (∫x,a x*active D A H0 H1 reg low e μP μA (v x) (action x) ∂(π : Measure _))=
      ∫z,a z.1*ZeroNoiseActive.payoff D A H0 H1 reg low v action
        ((e,SourceAmbientLaws.privateBayes D H0 e μP),z)
        ∂(ZeroNoiseActive.sampleLaw D A π (SourceAmbientLaws.common D e μA) : Measure _) := by
  let f:=fun z : ZeroNoiseActive.Sample D A (X:=X)=>
    a z.1*ZeroNoiseActive.payoff D A H0 H1 reg low v action
      ((e,SourceAmbientLaws.privateBayes D H0 e μP),z)
  have hf : Measurable f := (a.continuous.measurable.comp measurable_fst).mul
    ((ZeroNoiseActive.measurable_payoff D A H0 H1 reg low v action).comp
      (measurable_const.prodMk measurable_id))
  have hb (z) : |f z|≤‖a‖*(‖v‖+2*D.B) := by
    rw [abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm z.1)
      (ZeroNoiseActive.payoff_bound D A H0 H1 reg low v action _) (abs_nonneg _) (norm_nonneg _)
  symm
  change (∫z,f z ∂(π : Measure _).prod
    ((rowLaw A (SourceAmbientLaws.common D e μA) : Measure _).prod volume))=_
  rw [BoundedProbabilityIntegral.prod _ _ f hf hb]
  apply integral_congr_ae
  refine ae_of_all _ fun x=>?_
  dsimp only
  rw [BoundedProbabilityIntegral.prod _ _ (fun z=> f (x,z))
    (hf.comp (measurable_const.prodMk measurable_id)) (fun z=> hb (x,z))]
  simp only [f,ZeroNoiseActive.payoff,ZeroNoiseActive.count,ZeroNoiseActive.row,
    active,activeValue,activeCount,integral_const_mul,Fin.cons_zero]

lemma integrable_active_test :
    Integrable (fun x=> a x*active D A H0 H1 reg low e μP μA (v x) (action x)) (π : Measure _) := by
  let f:=fun z : ZeroNoiseActive.Sample D A (X:=X)=> a z.1*
    ZeroNoiseActive.payoff D A H0 H1 reg low v action ((e,SourceAmbientLaws.privateBayes D H0 e μP),z)
  have hf : Measurable f := (a.continuous.measurable.comp measurable_fst).mul
    ((ZeroNoiseActive.measurable_payoff D A H0 H1 reg low v action).comp
      (measurable_const.prodMk measurable_id))
  have hb (z) : |f z|≤‖a‖*(‖v‖+2*D.B) := by
    rw [abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm z.1)
      (ZeroNoiseActive.payoff_bound D A H0 H1 reg low v action _) (abs_nonneg _) (norm_nonneg _)
  have hi:=BoundedProbabilityIntegral.integrable
    ((π : Measure _).prod ((rowLaw A (SourceAmbientLaws.common D e μA) : Measure _).prod volume)) f hf hb
  convert! hi.integral_prod_left using 1
  funext x
  rw [BoundedProbabilityIntegral.prod _ _ (fun z=> f (x,z))
    (hf.comp (measurable_const.prodMk measurable_id)) (fun z=> hb (x,z))]
  simp only [f,ZeroNoiseActive.payoff,ZeroNoiseActive.count,ZeroNoiseActive.row,
    active,activeValue,activeCount,integral_const_mul,Fin.cons_zero]

end Active

section Partial
variable (D : Data) (A H0 H1 : ℕ) (side reg low : Bool) (vL vU : ℝ)
  (j : Fin (AllCountAtypical.ownCount H0 H1 side))
  (action : C(EqualZeroNoisePrivate.Own D vL vU,Icc D.R D.Up))
  (a : C(EqualZeroNoisePrivate.Own D vL vU,ℝ))
  (e : Noise D.eps) (μP : ProbabilityMeasure (Icc D.R D.Up))
  (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
  (π : ProbabilityMeasure (EqualZeroNoisePrivate.Own D vL vU))

lemma equal_test (H : ℕ) (j : Fin H) :
    (∫x,a x*(∫b,∫s,∫u : unitInterval,equalPrivateValue D A H j e μP (x.1:ℝ) (action x) b s u
      ∂(volume : Measure unitInterval) ∂(privateRaw D H e μP : Measure _)
      ∂(rowLaw A (SourceAmbientLaws.common D e μA) : Measure _)) ∂(π : Measure _))=
    ∫z,a z.1*EqualZeroNoisePrivate.payoff D A H vL vU j action
      ((e,SourceAmbientLaws.privateBayes D H e μP),z)
      ∂(EqualZeroNoisePrivate.sampleLaw D A H vL vU π (SourceAmbientLaws.common D e μA)
        (privateRaw D H e μP) : Measure _) := by
  let f:=fun z : EqualZeroNoisePrivate.Sample D A H vL vU=>
    a z.1*EqualZeroNoisePrivate.payoff D A H vL vU j action
      ((e,SourceAmbientLaws.privateBayes D H e μP),z)
  have hf : Measurable f := (a.continuous.measurable.comp measurable_fst).mul
    ((EqualZeroNoisePrivate.measurable_payoff D A H vL vU j action).comp
      (measurable_const.prodMk measurable_id))
  have hb (z) : |f z|≤‖a‖*(|vL|+|vU|+|D.V|) := by
    rw [abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm z.1)
      (EqualZeroNoisePrivate.payoff_bound D A H vL vU j action _) (abs_nonneg _) (norm_nonneg _)
  symm
  change (∫z,f z ∂(π : Measure _).prod ((rowLaw A (SourceAmbientLaws.common D e μA) : Measure _).prod
    ((privateRaw D H e μP : Measure _).prod volume)))=_
  rw [BoundedProbabilityIntegral.prod _ _ f hf hb]
  apply integral_congr_ae
  refine ae_of_all _ fun x=>?_
  dsimp only
  rw [BoundedProbabilityIntegral.prod _ _ (fun z=> f (x,z))
    (hf.comp (measurable_const.prodMk measurable_id)) (fun z=> hb (x,z))]
  simp only [←integral_const_mul]
  congr 1
  funext b
  rw [BoundedProbabilityIntegral.prod _ _ (fun z=> f (x,b,z))
    (hf.comp (by fun_prop)) (fun z=> hb (x,b,z))]
  simp only [f,EqualZeroNoisePrivate.payoff,EqualZeroNoisePrivate.input,equalPrivateValue,integral_const_mul]

lemma unequal_test (h : H0≠H1) :
    (∫x,a x*«partial» D A H0 H1 side reg low j e μP μA (x.1:ℝ) (action x) ∂(π : Measure _))=
    ∫z,a z.1*UnequalZeroNoisePrivate.payoff D A H0 H1 side reg low vL vU j action (e,z)
      ∂(EqualZeroNoisePrivate.sampleLaw D A (AllCountAtypical.ownCount H0 H1 side) vL vU π
        (SourceAmbientLaws.common D e μA) (privateRaw D (AllCountAtypical.ownCount H0 H1 side) e μP) : Measure _)
    := by
  let f:=fun z : EqualZeroNoisePrivate.Sample D A (AllCountAtypical.ownCount H0 H1 side) vL vU=>
    a z.1*UnequalZeroNoisePrivate.payoff D A H0 H1 side reg low vL vU j action (e,z)
  have hf : Measurable f := (a.continuous.measurable.comp measurable_fst).mul
    ((UnequalZeroNoisePrivate.measurable_payoff D A H0 H1 side reg low vL vU j action).comp
      (measurable_const.prodMk measurable_id))
  have hb (z) : |f z|≤‖a‖*(|vL|+|vU|+|D.V|) := by
    rw [abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm z.1)
      (UnequalZeroNoisePrivate.payoff_bound D A H0 H1 side reg low vL vU j action _) (abs_nonneg _) (norm_nonneg _)
  symm
  change (∫z,f z ∂(π : Measure _).prod ((rowLaw A (SourceAmbientLaws.common D e μA) : Measure _).prod
    ((privateRaw D (AllCountAtypical.ownCount H0 H1 side) e μP : Measure _).prod volume)))=_
  rw [BoundedProbabilityIntegral.prod _ _ f hf hb]
  apply integral_congr_ae
  refine ae_of_all _ fun x=>?_
  dsimp only
  rw [BoundedProbabilityIntegral.prod _ _ (fun z=> f (x,z))
    (hf.comp (measurable_const.prodMk measurable_id)) (fun z=> hb (x,z))]
  unfold «partial»
  rw [dif_neg h]
  simp only [←integral_const_mul]
  congr 1
  funext b
  rw [BoundedProbabilityIntegral.prod _ _ (fun z=> f (x,b,z))
    (hf.comp (by fun_prop)) (fun z=> hb (x,b,z))]
  simp only [f,UnequalZeroNoisePrivate.payoff,UnequalZeroNoisePrivate.inclusion,
    UnequalZeroNoisePrivate.weight,UnequalZeroNoisePrivate.input,unequalPrivateValue,integral_const_mul]

lemma integrable_partial_test :
    Integrable (fun x=> a x*«partial» D A H0 H1 side reg low j e μP μA (x.1:ℝ) (action x))
      (π : Measure _) := by
  by_cases h : H0=H1
  · subst H1
    let jj : Fin H0:=Fin.cast (by cases side <;> simp [AllCountAtypical.ownCount]) j
    let f:=fun z : EqualZeroNoisePrivate.Sample D A H0 vL vU=> a z.1*
      EqualZeroNoisePrivate.payoff D A H0 vL vU jj action ((e,SourceAmbientLaws.privateBayes D H0 e μP),z)
    have hf : Measurable f := (a.continuous.measurable.comp measurable_fst).mul
      ((EqualZeroNoisePrivate.measurable_payoff D A H0 vL vU jj action).comp
        (measurable_const.prodMk measurable_id))
    have hb (z) : |f z|≤‖a‖*(|vL|+|vU|+|D.V|) := by
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm z.1)
        (EqualZeroNoisePrivate.payoff_bound D A H0 vL vU jj action _) (abs_nonneg _) (norm_nonneg _)
    have hi:=BoundedProbabilityIntegral.iterated_three (π : Measure _)
      (rowLaw A (SourceAmbientLaws.common D e μA) : Measure _)
      (privateRaw D H0 e μP : Measure _) volume f hf hb
    simpa only [«partial»,dif_pos rfl,dite_true,jj,f,EqualZeroNoisePrivate.payoff,EqualZeroNoisePrivate.input,
      equalPrivateValue,integral_const_mul] using! hi
  · let f:=fun z : EqualZeroNoisePrivate.Sample D A (AllCountAtypical.ownCount H0 H1 side) vL vU=> a z.1*
      UnequalZeroNoisePrivate.payoff D A H0 H1 side reg low vL vU j action (e,z)
    have hf : Measurable f := (a.continuous.measurable.comp measurable_fst).mul
      ((UnequalZeroNoisePrivate.measurable_payoff D A H0 H1 side reg low vL vU j action).comp
        (measurable_const.prodMk measurable_id))
    have hb (z) : |f z|≤‖a‖*(|vL|+|vU|+|D.V|) := by
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm z.1)
        (UnequalZeroNoisePrivate.payoff_bound D A H0 H1 side reg low vL vU j action _) (abs_nonneg _) (norm_nonneg _)
    have hi:=BoundedProbabilityIntegral.iterated_three (π : Measure _)
      (rowLaw A (SourceAmbientLaws.common D e μA) : Measure _)
      (privateRaw D (AllCountAtypical.ownCount H0 H1 side) e μP : Measure _) volume f hf hb
    simpa only [«partial»,dif_neg h,f,UnequalZeroNoisePrivate.payoff,UnequalZeroNoisePrivate.input,
      UnequalZeroNoisePrivate.inclusion,UnequalZeroNoisePrivate.weight,unequalPrivateValue,integral_const_mul] using! hi

end Partial
end FCAppendix.Affine.Tail04.AmbientLocalizedTests
