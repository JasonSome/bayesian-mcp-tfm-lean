import FCAppendix.Affine.Tail04.SourceAmbientPartialPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroFiberBounds
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws
open FiniteTailNoisyGame ZeroNoiseFiniteGame

variable (D : Data) (A H0 H1 : ℕ) (reg low : Bool)
  (μP : ProbabilityMeasure (Icc D.R D.Up)) (v : ℝ)

lemma active_measurable (price : Icc (1:ℝ) D.U) :
    Measurable (fun b : Fin A→ Icc (1:ℝ) D.U=> activeFiber D A H0 H1 low reg ((v,price,μP),b)) := by
  have h := (AmbientFiniteGame.measurable_activeValue D A H0 H1 reg low
    (FixedAmbientNoise.zero D.eps D.heps.le) μP v price).comp
      (by
        exact (measurable_pi_lambda _ fun i =>
          (EqualPrivateAmbient.continuous_widen (FixedAmbientNoise.base_le_upper (zero_lt_one : (0:ℝ)<1) D.hU D.heps.le)).measurable.comp
            (measurable_pi_apply i)).prodMk measurable_const
        : Measurable (fun b : Fin A→ Icc (1:ℝ) D.U=>
        ((fun i=> EqualPrivateAmbient.widen (FixedAmbientNoise.base_le_upper (zero_lt_one : (0:ℝ)<1) D.hU D.heps.le) (b i)),
          (0:unitInterval))))
  convert! h using 1
  funext b
  exact (SourceAmbientPayoff.active_value_zero D A H0 H1 reg low μP v price b
    (0:unitInterval)).symm

lemma active_bound (price : Icc (1:ℝ) D.U) (b : Fin A→ Icc (1:ℝ) D.U) :
    |activeFiber D A H0 H1 low reg ((v,price,μP),b)|≤|v|+2*D.B := by
  rw [←SourceAmbientPayoff.active_value_zero D A H0 H1 reg low μP v price b (0:unitInterval)]
  exact AmbientFiniteGame.activeValue_bound D A H0 H1 reg low _ μP v price _ _

lemma active_integrable (price : Icc (1:ℝ) D.U) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U)) :
    Integrable (fun b=> activeFiber D A H0 H1 low reg ((v,price,μP),b)) (rowLaw A μA : Measure _) :=
  BoundedProbabilityIntegral.integrable _ _ (active_measurable D A H0 H1 reg low μP v price)
    (active_bound D A H0 H1 reg low μP v price)

lemma partial_measurable (side : Bool) (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (price : Icc D.R D.Up) :
    Measurable (fun b : Fin A→ Icc (1:ℝ) D.U=> partialFiber D A H0 H1 side low reg j ((v,price,μP),b)) := by
  by_cases h : H0=H1
  · let jj : Fin H0:=Fin.cast (by cases side <;> simp [AllCountAtypical.ownCount,h]) j
    have hm : Measurable (fun z : (Fin A→ Icc (1:ℝ) D.U)×Signal H0 D.R D.Up=>
        equalPartialValue D A H0 jj z.1 μP price z.2) := by
      unfold equalPartialValue
      apply (PrivatePayoffContinuity.measurable_privateValue D.ξ jj).comp
      have hs := SortedAllNoise.continuous_sortedBox (N:=A) (L:=(1:ℝ)) (U:=D.U)
      have hq := continuous_policyMean A H0 D.c D.R D.Up D.ξ 1 D.U D.hξ (by norm_num)
      exact ((continuous_pi (fun i=> continuous_subtype_val.comp
        ((continuous_apply i).comp (hs.comp continuous_fst)))).prodMk
          ((hq.comp ((hs.comp continuous_fst).prodMk continuous_const)).prodMk
            (by fun_prop))).measurable
    have hi:=BoundedProbabilityIntegral.measurable_integral
      (privateRow D H0 μP : Measure _) _ hm
    simpa only [partialFiber,dif_pos h,jj] using! measurable_const.mul hi
  · simp only [partialFiber,dif_neg h]
    have hw : Measurable (fun b : Fin A→ Icc (1:ℝ) D.U =>
        UnequalPartialCountPayoff.rawWeight A H0 H1 D.c D.ξ D.U D.R D.Up
          D.width (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1)
          (fun i=>(b i:ℝ))) :=
      (UnequalPartialCountPayoff.measurable_rawWeight A H0 H1 D.c D.ξ D.U D.R D.Up
        D.width (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1)).comp
          (measurable_pi_lambda _ fun i=> measurable_subtype_coe.comp (measurable_pi_apply i))
    exact measurable_const.mul ((hw.mul measurable_const).add
      ((measurable_const.sub hw).mul measurable_const))

lemma partial_bound (side : Bool) (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (price : Icc D.R D.Up) (b : Fin A→ Icc (1:ℝ) D.U) :
    |partialFiber D A H0 H1 side low reg j ((v,price,μP),b)|≤|v|+D.Up := by
  have hp : |(price:ℝ)|≤ D.Up := by
    rw [abs_of_nonneg (D.hR.le.trans price.2.1)]
    exact price.2.2
  have hsur : |v-(price:ℝ)|≤|v|+D.Up := (abs_sub _ _).trans (add_le_add le_rfl hp)
  unfold partialFiber
  by_cases h : H0=H1
  · rw [dif_pos h,abs_mul]
    let jj : Fin H0 := Fin.cast (by cases side <;> simp [AllCountAtypical.ownCount,h]) j
    have hi1 : |∫s,equalPartialValue D A H0 jj b μP price s
        ∂(privateRow D H0 μP : Measure _)|≤1 :=
      BoundedProbabilityIntegral.bound _ _ (fun s=> by
        unfold equalPartialValue
        rw [abs_of_nonneg (PrivatePayoffContinuity.privateValue_bounds (c:=D.c) D.ξ _ _).1]
        exact (PrivatePayoffContinuity.privateValue_bounds (c:=D.c) D.ξ _ _).2)
    exact (mul_le_of_le_one_right (abs_nonneg _) hi1).trans hsur
  · rw [dif_neg h,abs_mul]
    let w:=UnequalPartialCountPayoff.rawWeight A H0 H1 D.c D.ξ D.U D.R D.Up D.width
      (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1) (fun i=>(b i:ℝ))
    let I:=∫s,AtypicalPartialNoisy.rankInclusion A H0 H1 D.c side j ((price:ℝ),s)
      ∂(ProbabilityMeasure.toMeasure (privateRow D (AllCountAtypical.ownCount H0 H1 side) μP))
    have hw:=UnequalPartialCountPayoff.rawWeight_bounds A H0 H1 D.c D.ξ D.U D.R D.Up D.width
      (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1) (fun i=>(b i:ℝ))
    have hi0 : 0≤∫s,AtypicalPartialNoisy.rankInclusion A H0 H1 D.c side j ((price:ℝ),s)
        ∂(ProbabilityMeasure.toMeasure (privateRow D (AllCountAtypical.ownCount H0 H1 side) μP)) :=
      integral_nonneg (fun s=>(AtypicalPartialNoisy.rankInclusion_bounds A H0 H1 D.c side j _).1)
    have hi1 : (∫s,AtypicalPartialNoisy.rankInclusion A H0 H1 D.c side j ((price:ℝ),s)
        ∂(ProbabilityMeasure.toMeasure (privateRow D (AllCountAtypical.ownCount H0 H1 side) μP)))≤1 :=
      (le_abs_self _).trans (BoundedProbabilityIntegral.bound _ _ (fun s=> by
        rw [abs_of_nonneg (AtypicalPartialNoisy.rankInclusion_bounds A H0 H1 D.c side j _).1]
        exact (AtypicalPartialNoisy.rankInclusion_bounds A H0 H1 D.c side j _).2))
    have hz : w*(if reg then 0 else 1)+(1-w)*I∈Icc (0:ℝ) 1 := by
      change 0≤ w ∧ w≤1 at hw
      change 0≤ I at hi0
      change I≤1 at hi1
      cases reg <;> simp only [Bool.false_eq_true,ite_false,ite_true,mul_zero,mul_one,zero_add] <;>
        constructor <;> nlinarith
    change |v-(price:ℝ)| * |w*(if reg then 0 else 1)+(1-w)*I|≤_
    rw [abs_of_nonneg hz.1]
    exact (mul_le_of_le_one_right (abs_nonneg _) hz.2).trans hsur

lemma partial_integrable (side : Bool) (j : Fin (AllCountAtypical.ownCount H0 H1 side))
    (price : Icc D.R D.Up) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U)) :
    Integrable (fun b=> partialFiber D A H0 H1 side low reg j ((v,price,μP),b))
      (rowLaw A μA : Measure _) :=
  BoundedProbabilityIntegral.integrable _ _ (partial_measurable D A H0 H1 reg low μP v side j price)
    (partial_bound D A H0 H1 reg low μP v side j price)

end FCAppendix.Affine.Tail04.ZeroFiberBounds
