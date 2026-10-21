import FCAppendix.Affine.Tail04.FiniteTailNoisyGame
import FCAppendix.Affine.Tail04.AllCountActiveFiniteGain
import FCAppendix.Affine.Tail04.OriginalNoiseProduct

noncomputable section
namespace FCAppendix.Affine.Tail04.ActivePhysicalPayoff
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal CompactSourceBidLaws SortedAllNoise
open AllCountActiveFiniteGain OriginalNoiseProduct FiniteTailNoisyGame
open scoped BigOperators

lemma utility_bound (C : CountLaw 2) (v b B eta : ℝ)
    (hb0 : 0≤ b) (hbB : b≤ B) (hη0 : 0≤ eta) (hη1 : eta≤1) :
    |affineCountUtility C v b eta hη0 hη1|≤|v|+2*B := by
  rw [affineCountUtility,CountLaw.utility_eq,zero_mul,sub_zero]
  have hq0:=C.charge_nonneg (Schedule.affine 2 eta hη0 hη1)
  have hq1: C.charge (Schedule.affine 2 eta hη0 hη1)≤2 :=
    (C.charge_le_load _).trans C.load_le_n
  calc
    _≤|v*C.success|+|b*C.charge (Schedule.affine 2 eta hη0 hη1)| := abs_sub _ _
    _=|v| * C.success+b*C.charge (Schedule.affine 2 eta hη0 hη1) := by
      rw [abs_mul,abs_mul,abs_of_nonneg C.success_nonneg,abs_of_nonneg hb0,abs_of_nonneg hq0]
    _≤|v|+2*B := by
      have hs:=mul_le_mul_of_nonneg_left C.success_le_one (abs_nonneg v)
      have hq:=mul_le_mul_of_nonneg_left hq1 hb0
      nlinarith

variable (D : Data) (A H0 H1 : ℕ) (μP : ProbabilityMeasure (Icc D.R D.Up))
  (v : ℝ)

def value (reg low : Bool) (b : Fin (A+1) → Icc (1:ℝ) D.B) : ℝ :=
  affineCountUtility (physicalCount H0 H1 D.c D.ξ D.B D.R D.V D.width (D.e0 reg) D.F
    reg low (D.marksLaw H0) (D.marksLaw H1) (D.privateBayes H0 μP) b 0)
    v (b 0) D.eta D.heta0 D.heta1

lemma measurable_mass (reg low : Bool) (r : Fin 3) :
    Measurable (fun b : Fin (A+1) → Icc (1:ℝ) D.B =>
      (physicalCount H0 H1 D.c D.ξ D.B D.R D.V D.width (D.e0 reg) D.F
        reg low (D.marksLaw H0) (D.marksLaw H1) (D.privateBayes H0 μP) b 0).mass r) := by
  have hb : Measurable (fun b : Fin (A+1) → Icc (1:ℝ) D.B => fun j => (b j:ℝ)) :=
    measurable_pi_lambda _ (fun j => (measurable_pi_apply j).subtype_val)
  unfold physicalCount
  split_ifs
  · have hc (j : Fin (A+1)) : Measurable (fun b : Fin (A+1)→Icc (1:ℝ) D.B=>
        (EqualPrivateCountPayoff.countLaw (A+1) H0 D.c D.R D.V D.ξ 1 D.B
          (sortedBox b,WeakProbability.mk (D.privateBayes H0 μP)) j).mass r) :=
      (EqualPrivateCountPayoff.continuous_countLaw_mass (A+1) H0 D.c
        D.R D.V D.ξ 1 D.B D.hξ (by norm_num) j r).measurable.comp
          (continuous_sortedBox.measurable.prodMk measurable_const)
    exact LocalCoordinates.measurable_finite_eval
      (fun b : Fin (A+1)→Icc (1:ℝ) D.B=>focalRank (fun j=>(b j:ℝ)) 0)
      (fun b j=>(EqualPrivateCountPayoff.countLaw (A+1) H0 D.c D.R D.V D.ξ 1 D.B
        (sortedBox b,WeakProbability.mk (D.privateBayes H0 μP)) j).mass r)
      ((measurable_focalRank 0).comp hb) hc
  · exact (UnequalNoisyCountPayoff.measurable_rawCount_mass H0 H1 D.c D.ξ D.B D.R D.V
      D.width (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1) 0 r).comp hb

lemma measurable_value (reg low : Bool) : Measurable (value D A H0 H1 μP v reg low) := by
  unfold value affineCountUtility CountLaw.utility FiniteLaw.expect
  apply Finset.measurable_sum
  intro r _
  apply (measurable_mass D A H0 H1 μP reg low r).mul
  unfold userPayoff
  exact ((measurable_const.mul measurable_const).sub
    (((measurable_pi_apply 0).subtype_val).mul measurable_const)).sub measurable_const

lemma value_bound (reg low : Bool) (b : Fin (A+1) → Icc (1:ℝ) D.B) :
    |value D A H0 H1 μP v reg low b|≤|v|+2*D.B :=
  utility_bound _ v (b 0) D.B D.eta ((by norm_num : (0:ℝ)≤1).trans (b 0).2.1)
    (b 0).2.2 D.heta0 D.heta1

def regimeValue (low : Bool) (b : Fin (A+1) → Icc (1:ℝ) D.B) : ℝ :=
  (1-(D.regimeShare:ℝ))*value D A H0 H1 μP v false low b+
    (D.regimeShare:ℝ)*value D A H0 H1 μP v true low b

lemma measurable_regimeValue (low : Bool) :
    Measurable (regimeValue D A H0 H1 μP v low) :=
  ((measurable_value D A H0 H1 μP v false low).const_mul _).add
    ((measurable_value D A H0 H1 μP v true low).const_mul _)

lemma regimeValue_bound (low : Bool) (b : Fin (A+1) → Icc (1:ℝ) D.B) :
    |regimeValue D A H0 H1 μP v low b|≤|v|+2*D.B := by
  have h0:=value_bound D A H0 H1 μP v false low b
  have h1:=value_bound D A H0 H1 μP v true low b
  unfold regimeValue
  calc
    _≤|(1-(D.regimeShare:ℝ))*value D A H0 H1 μP v false low b|+
        |(D.regimeShare:ℝ)*value D A H0 H1 μP v true low b| := abs_add_le _ _
    _≤(1-(D.regimeShare:ℝ))*(|v|+2*D.B)+(D.regimeShare:ℝ)*(|v|+2*D.B) := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr D.regimeShare.2.2),
        abs_of_nonneg D.regimeShare.2.1]
      exact add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr D.regimeShare.2.2))
        (mul_le_mul_of_nonneg_left h1 D.regimeShare.2.1)
    _=_ := by ring

lemma integrable_regime_comp {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (f : X → Fin (A+1) → Icc (1:ℝ) D.B) (hf : Measurable f)
    (low : Bool) : Integrable (fun x => regimeValue D A H0 H1 μP v low (f x)) μ :=
  Integrable.of_bound ((measurable_regimeValue D A H0 H1 μP v low).comp hf).aestronglyMeasurable
    (|v|+2*D.B) (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using regimeValue_bound D A H0 H1 μP v low (f x)))

theorem activeFiber_integral (low reg : Bool) (b : Icc (1:ℝ) D.U)
    (row : Fin A → Icc (1:ℝ) D.U) :
    D.activeFiber A H0 H1 low reg ((v,b,μP),row)=
      ∫ u : Fin (A+1) → unitInterval,value D A H0 H1 μP v reg low
        (physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (A+1) (Fin.cons b row,u))
          ∂Measure.pi (fun _ : Fin (A+1) => (volume : Measure unitInterval)) := by
  unfold Data.activeFiber
  by_cases h : H0=H1
  · rw [if_pos h,EqualNoisyFiniteLoss.activeUtility_eq_integral D.heps.le D.hξ]
    apply integral_congr_ae
    exact ae_of_all _ fun u => by
      simp only [value,physicalCount,if_pos h,EqualNoisyUtilities.rawCount,
        EqualNoisyUtilities.parameter,EqualNoisyUtilities.physical,EqualNoisyUtilities.physicalReal,physicalRow,
        Data.insertActive,Fin.cons_zero]
      rfl
  · rw [if_neg h,UnequalNoisyCountPayoff.utility_eq_integral H0 H1 D.c D.ξ D.B D.R D.V
      D.width (D.e0 reg) D.F D.eta reg low D.heps D.heta0 D.heta1]
    apply integral_congr_ae
    exact ae_of_all _ fun u => by
      simp only [value,physicalCount,if_neg h,physicalRow,Data.insertActive,
        AllNoiseFiniteSelector.noisyBids,noisyBid,Hybrid.activeNoisyRealBid,Fin.cons_zero]
      rfl

lemma activeRegimeFiber_integral (low : Bool) (b : Icc (1:ℝ) D.U)
    (row : Fin A → Icc (1:ℝ) D.U) :
    D.activeRegimeFiber A H0 H1 low ((v,b,μP),row)=
      ∫ u : Fin (A+1) → unitInterval,regimeValue D A H0 H1 μP v low
        (physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (A+1) (Fin.cons b row,u))
          ∂Measure.pi (fun _ : Fin (A+1) => (volume : Measure unitInterval)) := by
  have hi (reg : Bool) : Integrable (fun u : Fin (A+1) → unitInterval =>
      value D A H0 H1 μP v reg low
        (physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (A+1) (Fin.cons b row,u)))
        (Measure.pi (fun _ : Fin (A+1) => (volume : Measure unitInterval))) :=
    Integrable.of_bound
      (((measurable_value D A H0 H1 μP v reg low).comp
        ((measurable_physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (A+1)).comp
          (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
      (|v|+2*D.B) (ae_of_all _ fun u => by
        simpa only [Real.norm_eq_abs] using value_bound D A H0 H1 μP v reg low _)
  rw [Data.activeRegimeFiber,activeFiber_integral,activeFiber_integral]
  symm
  exact (integral_add ((hi false).const_mul _) ((hi true).const_mul _)).trans (by
    rw [integral_const_mul,integral_const_mul])

lemma integrable_focal_average (low : Bool) (b : Icc (1:ℝ) D.U)
    (μA : ProbabilityMeasure (Icc (1:ℝ) D.U)) :
    Integrable (fun u : unitInterval => ∫ row : Fin A → Icc (1:ℝ) D.B,
      regimeValue D A H0 H1 μP v low
        (Fin.cons (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)) row)
          ∂Measure.pi (fun _ : Fin A => ProbabilityMeasure.toMeasure (noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le μA)))
      (volume : Measure unitInterval) := by
  let f : unitInterval×(Fin A→Icc (1:ℝ) D.B)→Fin (A+1)→Icc (1:ℝ) D.B :=
    fun p=>Fin.cons (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,p.1)) p.2
  have hf : Measurable f := measurable_pi_lambda _ fun j=>by
    refine Fin.cases ?_ (fun k=>?_) j
    · exact (continuous_noisyBid (by norm_num : (0:ℝ)<1) D.heps.le).measurable.comp
        (measurable_const.prodMk measurable_fst)
    · exact (measurable_pi_apply k).comp measurable_snd
  let ν : ProbabilityMeasure (Icc (1:ℝ) D.B) :=
    noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le μA
  exact (integrable_regime_comp D A H0 H1 μP v
    ((volume : Measure unitInterval).prod (Measure.pi fun _ : Fin A=>
      (ν : Measure (Icc (1:ℝ) D.B)))) f hf low).integral_prod_left

theorem split_focal_integral (low : Bool) (b : Icc (1:ℝ) D.U)
    (μA : ProbabilityMeasure (Icc (1:ℝ) D.U)) :
    (∫ u : unitInterval,∫ row : Fin A → Icc (1:ℝ) D.B,
      regimeValue D A H0 H1 μP v low
        (Fin.cons (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)) row)
          ∂Measure.pi (fun _ : Fin A => ProbabilityMeasure.toMeasure (noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le μA)))=
      ∫ row : Fin A → Icc (1:ℝ) D.U,D.activeRegimeFiber A H0 H1 low ((v,b,μP),row)
        ∂Measure.pi (fun _ : Fin A => (μA : Measure (Icc (1:ℝ) D.U))) := by
  let M:=Measure.pi (fun _ : Fin A => (μA : Measure (Icc (1:ℝ) D.U)))
  let Z:=Measure.pi (fun _ : Fin (A+1) => (volume : Measure unitInterval))
  let Y:=Measure.pi (fun _ : Fin A => ProbabilityMeasure.toMeasure (noisyBidLaw (by norm_num : (0:ℝ)<1) D.heps.le μA))
  let f : unitInterval×(Fin A → Icc (1:ℝ) D.B) → Fin (A+1) → Icc (1:ℝ) D.B :=
    fun p => Fin.cons (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,p.1)) p.2
  have hf : Measurable f := measurable_pi_lambda _ fun j => by
    refine Fin.cases ?_ (fun k => ?_) j
    · exact (continuous_noisyBid (by norm_num : (0:ℝ)<1) D.heps.le).measurable.comp
        (measurable_const.prodMk measurable_fst)
    · exact (measurable_pi_apply k).comp measurable_snd
  have hF:=integrable_regime_comp D A H0 H1 μP v ((volume : Measure unitInterval).prod Y) f hf low
  have hp:=splitFocalNoise_preserves (by norm_num : (0:ℝ)<1) D.heps.le A μA
  have hg : Measurable (fun p : (Fin A → Icc (1:ℝ) D.U)×(Fin (A+1) → unitInterval) =>
      physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (A+1) (Fin.cons b p.1,p.2)) := by
    apply (measurable_physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (A+1)).comp
    apply Measurable.prodMk _ measurable_snd
    exact measurable_pi_lambda _ fun j => by
      refine Fin.cases measurable_const (fun k => (measurable_pi_apply k).comp measurable_fst) j
  have hi:=integrable_regime_comp D A H0 H1 μP v (M.prod Z) _ hg low
  calc
    _=∫ p,regimeValue D A H0 H1 μP v low (f p) ∂((volume : Measure unitInterval).prod Y) :=
      (integral_prod _ hF).symm
    _=∫ p,regimeValue D A H0 H1 μP v low (f (splitFocalNoise (by norm_num : (0:ℝ)<1) D.heps.le A p))
        ∂M.prod Z := by
      rw [←hp.map_eq]
      exact integral_map (μ:=M.prod Z) hp.measurable.aemeasurable
        (((measurable_regimeValue D A H0 H1 μP v low).comp hf).aestronglyMeasurable)
    _=∫ row,∫ u : Fin (A+1) → unitInterval,regimeValue D A H0 H1 μP v low
        (physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (A+1) (Fin.cons b row,u)) ∂Z ∂M := by
      calc
        _=∫ p,regimeValue D A H0 H1 μP v low
            (physicalRow (by norm_num : (0:ℝ)<1) D.heps.le (A+1) (Fin.cons b p.1,p.2)) ∂M.prod Z := by
          apply integral_congr_ae
          exact ae_of_all _ fun p=>congrArg (regimeValue D A H0 H1 μP v low)
            (physical_cons_eq (by norm_num : (0:ℝ)<1) D.heps.le A b p).symm
        _=_:=integral_prod _ hi
    _=_ := by
      apply integral_congr_ae
      exact ae_of_all _ fun row=>(activeRegimeFiber_integral D A H0 H1 μP v low b row).symm

end FCAppendix.Affine.Tail04.ActivePhysicalPayoff
