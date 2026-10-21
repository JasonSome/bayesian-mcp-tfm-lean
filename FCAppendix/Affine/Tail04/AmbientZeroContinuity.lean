import FCAppendix.Affine.Tail04.AmbientLocalizedTests
import Mathlib.Topology.Sequences

noncomputable section
namespace FCAppendix.Affine.Tail04.AmbientZeroContinuity
open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws FixedAmbientNoise
open FiniteTailNoisyGame SourceAmbientLaws AmbientFiniteGame

section Active
variable (D : Data) (A H0 H1 : ℕ) (reg low : Bool)
  {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [MetrizableSpace X]
  (v : C(X,ℝ)) (action : C(X,Icc (1:ℝ) D.U))
  (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
  [NullSingletonClass (ProbabilityMeasure.toMeasure (SourceAmbientLaws.common D (zero D.eps D.heps.le) μA))]

theorem active : Continuous (fun x=> AmbientFiniteGame.active D A H0 H1 reg low
    (zero D.eps D.heps.le) μP μA (v x) (action x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro xs hxs
  have hh:=ZeroNoiseActive.tendsto_payoff_test D A H0 H1 reg low v action
    (ContinuousMap.const X (1:ℝ)) (fun _=> zero D.eps D.heps.le) tendsto_const_nhds
    (fun _=> SourceAmbientLaws.privateBayes D H0 (zero D.eps D.heps.le) μP)
    (SourceAmbientLaws.privateBayes D H0 (zero D.eps D.heps.le) μP) tendsto_const_nhds
    (fun _=> SourceAmbientLaws.common D (zero D.eps D.heps.le) μA)
    (SourceAmbientLaws.common D (zero D.eps D.heps.le) μA) tendsto_const_nhds
    (fun n=> diracProba (xs n)) (diracProba x)
    (continuous_diracProba.continuousAt.tendsto.comp hxs)
  have he (y : X) :
      (∫z,ZeroNoiseActive.payoff D A H0 H1 reg low v action
        ((zero D.eps D.heps.le,SourceAmbientLaws.privateBayes D H0 (zero D.eps D.heps.le) μP),z)
        ∂(ZeroNoiseActive.sampleLaw D A (diracProba y)
          (SourceAmbientLaws.common D (zero D.eps D.heps.le) μA) : Measure _))=
      AmbientFiniteGame.active D A H0 H1 reg low (zero D.eps D.heps.le) μP μA (v y) (action y) := by
    simpa only [ContinuousMap.const_apply,one_mul,diracProba,ProbabilityMeasure.coe_mk,integral_dirac] using
      (AmbientLocalizedTests.active_test D A H0 H1 reg low v action (ContinuousMap.const X (1:ℝ))
        (zero D.eps D.heps.le) μP μA (diracProba y)).symm
  simpa only [ContinuousMap.const_apply,one_mul,he,Function.comp_apply] using! hh
end Active

section Partial
variable (D : Data) (A : ℕ) (vL vU : ℝ)
  (action : C(EqualZeroNoisePrivate.Own D vL vU,Icc D.R D.Up))
  (μP : ProbabilityMeasure (Icc D.R D.Up)) (μA : ProbabilityMeasure (Icc (1:ℝ) D.U))
  [NullSingletonClass ((ProbabilityMeasure.toMeasure μP).map
    (fun x : Icc D.R D.Up => (x:ℝ)))]
  [NullSingletonClass (ProbabilityMeasure.toMeasure (SourceAmbientLaws.common D (zero D.eps D.heps.le) μA))]

theorem equal (H : ℕ) (j : Fin H) :
    Continuous (fun x : EqualZeroNoisePrivate.Own D vL vU=>
      ∫b,∫s,∫u : unitInterval,AmbientFiniteGame.equalPrivateValue D A H j
        (zero D.eps D.heps.le) μP (x.1:ℝ) (action x) b s u
        ∂(volume : Measure unitInterval)
        ∂(SourceAmbientLaws.privateRaw D H (zero D.eps D.heps.le) μP : Measure _)
        ∂(rowLaw A (SourceAmbientLaws.common D (zero D.eps D.heps.le) μA) : Measure _)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro xs hxs
  have hh:=EqualZeroNoisePrivate.tendsto_payoff_test D A H vL vU j action
    (ContinuousMap.const _ (1:ℝ)) (fun _=> zero D.eps D.heps.le) tendsto_const_nhds
    (fun _=> SourceAmbientLaws.privateBayes D H (zero D.eps D.heps.le) μP)
    (SourceAmbientLaws.privateBayes D H (zero D.eps D.heps.le) μP) tendsto_const_nhds
    (SourceAmbientLaws.bayes_zero_positiveLevels D H μP)
    (fun _=> SourceAmbientLaws.common D (zero D.eps D.heps.le) μA)
    (SourceAmbientLaws.common D (zero D.eps D.heps.le) μA) tendsto_const_nhds
    (fun _=> SourceAmbientLaws.privateRaw D H (zero D.eps D.heps.le) μP)
    (SourceAmbientLaws.privateRaw D H (zero D.eps D.heps.le) μP) tendsto_const_nhds
    (SourceAmbientLaws.raw_zero_positiveLevels D H μP)
    (fun n=> diracProba (xs n)) (diracProba x)
    (continuous_diracProba.continuousAt.tendsto.comp hxs)
  have he (y : EqualZeroNoisePrivate.Own D vL vU) :=
    (AmbientLocalizedTests.equal_test D A vL vU action (ContinuousMap.const _ (1:ℝ))
      (zero D.eps D.heps.le) μP μA (diracProba y) H j).symm
  have hdirac (y : EqualZeroNoisePrivate.Own D vL vU) :
      ProbabilityMeasure.toMeasure (diracProba y)=Measure.dirac y := rfl
  simp only [ContinuousMap.const_apply,one_mul,hdirac,integral_dirac] at he
  simpa only [ContinuousMap.const_apply,one_mul,he,Function.comp_apply] using! hh

theorem unequal (H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (h : H0≠H1) :
    Continuous (fun x : EqualZeroNoisePrivate.Own D vL vU=>
      AmbientFiniteGame.«partial» D A H0 H1 side reg low j (zero D.eps D.heps.le)
        μP μA (x.1:ℝ) (action x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro xs hxs
  have hh:=UnequalZeroNoisePrivate.tendsto_payoff_test D A H0 H1 side reg low vL vU j action
    (ContinuousMap.const _ (1:ℝ)) (fun _=> zero D.eps D.heps.le) tendsto_const_nhds
    (fun _=> SourceAmbientLaws.common D (zero D.eps D.heps.le) μA)
    (SourceAmbientLaws.common D (zero D.eps D.heps.le) μA) tendsto_const_nhds
    (fun _=> SourceAmbientLaws.privateRaw D (AllCountAtypical.ownCount H0 H1 side)
      (zero D.eps D.heps.le) μP)
    (SourceAmbientLaws.privateRaw D (AllCountAtypical.ownCount H0 H1 side)
      (zero D.eps D.heps.le) μP) tendsto_const_nhds
    (SourceAmbientLaws.raw_zero_positiveLevels D (AllCountAtypical.ownCount H0 H1 side) μP)
    (fun n=> diracProba (xs n)) (diracProba x)
    (continuous_diracProba.continuousAt.tendsto.comp hxs)
  have he (y : EqualZeroNoisePrivate.Own D vL vU) :=
    (AmbientLocalizedTests.unequal_test D A H0 H1 side reg low vL vU j action
      (ContinuousMap.const _ (1:ℝ)) (zero D.eps D.heps.le) μP μA (diracProba y) h).symm
  have hdirac (y : EqualZeroNoisePrivate.Own D vL vU) :
      ProbabilityMeasure.toMeasure (diracProba y)=Measure.dirac y := rfl
  simp only [ContinuousMap.const_apply,one_mul,hdirac,integral_dirac] at he
  simpa only [ContinuousMap.const_apply,one_mul,he,Function.comp_apply] using! hh

theorem «partial» (H0 H1 : ℕ) (side reg low : Bool)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) :
    Continuous (fun x : EqualZeroNoisePrivate.Own D vL vU=>
      AmbientFiniteGame.«partial» D A H0 H1 side reg low j (zero D.eps D.heps.le)
        μP μA (x.1:ℝ) (action x)) := by
  by_cases h : H0=H1
  · let jj : Fin H0:=Fin.cast (by cases side <;> simp [AllCountAtypical.ownCount,h]) j
    simpa only [AmbientFiniteGame.«partial»,dif_pos h,jj] using!
      equal D A vL vU action μP μA H0 jj
  · exact unequal D A vL vU action μP μA H0 H1 side reg low j h
end Partial

end FCAppendix.Affine.Tail04.AmbientZeroContinuity
