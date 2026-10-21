import FCAppendix.Affine.Tail04.NativeLowIntegration
import FCAppendix.Affine.Hybrid.NativeLowPositive

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLowInterim
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid LowBody NativeContinuation NativeLowCoordinates NativeLowSelector
open NativeLowIntegration NativeLowRowPayoff
open scoped BigOperators

variable {N c : ℕ} (D : NativeLocalPolicy.Data (N+1) c)
  (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed)
  (hpolicy : Γ.policy=D.completedPolicy)
  (hprofiles : ∀ᵐp ∂userProfileLaw Γ,∀l,NativeMenuReports.MenuAction D.E (p l).1.2)

include hpolicy hprofiles in
theorem duplicates_le_original_row (i : Fin (N+1))
    (ν : Measure (Fin N→ RowRival))
    (hlaw : (userProfileLaw Γ).map (rowProfile D.E i)=ν)
    (a : JointAction 2) (hk : a.routeCount=2) (hbd : a.bid≤ D.E.d) :
    ((problem Γ i).outcome a).duplicates≤ ν.real (rowBothUnderflow c) := by
  let event : Set (Sample (N+1) 2 NativeLocalPolicy.Seed):=
    {ω|rowProfile D.E i ω.1.1∈rowBothUnderflow c}
  have hrow:=measurable_rowProfile D.E i
  have hE : MeasurableSet event := (measurableSet_rowBothUnderflow c).preimage
    (hrow.comp measurable_fst.fst)
  have hpMP : MeasurePreserving
      (fun ω : Sample (N+1) 2 NativeLocalPolicy.Seed=> ω.1.1)
      (sampleLaw Γ) (userProfileLaw Γ) :=
    (measurePreserving_fst (μ:=userProfileLaw Γ)
      (ν:=Measure.pi (fun _ : Fin 2=> Γ.seedLaw))).comp
        (measurePreserving_fst (μ:=backgroundLaw Γ) (ν:=permLaw 2))
  have hp:=hpMP.quasiMeasurePreserving.ae hprofiles
  rw [problem_outcome,CountLaw.duplicates_eq_expect,CountLaw.expect_ofMeasure]
  have hi:=CountLaw.integrable_comp (sampleLaw Γ) (focalCount Γ i a)
    (measurable_focalCount Γ i a) (fun r : Fin 3=>(r.val:ℝ)-successIndicator r.val)
  have hbound : (∫ω,((focalCount Γ i a ω).val:ℝ)-successIndicator (focalCount Γ i a ω).val
      ∂sampleLaw Γ)≤∫ω,event.indicator (fun _=>(1:ℝ)) ω ∂sampleLaw Γ := by
    apply integral_mono_ae hi ((integrable_const (1:ℝ)).indicator hE)
    filter_upwards [hp] with ω hω
    have hc (r : Fin 3) : (r.val:ℝ)-successIndicator r.val=
        (if r.val=2 then (1:ℝ) else 0) := by
      fin_cases r <;> norm_num [successIndicator]
    rw [hc]
    by_cases hdup : (focalCount Γ i a ω).val=2
    · have he : ω∈event := low_duplicate_implies_underflow D Γ hpolicy i a hk hbd ω
        (fun r=> hω (i.succAbove r)) hdup
      simp only [if_pos hdup,Set.indicator_of_mem he,le_refl]
    · rw [if_neg hdup]
      exact Set.indicator_nonneg (fun _ _=> zero_le_one) ω
  have hind:=integral_indicator_one (μ:=sampleLaw Γ) hE
  change (∫ω,event.indicator (fun _=>(1:ℝ)) ω ∂sampleLaw Γ)=(sampleLaw Γ).real event at hind
  rw [hind] at hbound
  have hmap : (sampleLaw Γ).map
      (fun ω : Sample (N+1) 2 NativeLocalPolicy.Seed=> rowProfile D.E i ω.1.1)=ν := by
    change (sampleLaw Γ).map (rowProfile D.E i∘
      (fun ω : Sample (N+1) 2 NativeLocalPolicy.Seed=> ω.1.1))=ν
    rw [←Measure.map_map hrow hpMP.measurable,hpMP.map_eq,hlaw]
  have hm:=Measure.map_apply (μ:=sampleLaw Γ) (hrow.comp hpMP.measurable)
    (measurableSet_rowBothUnderflow c)
  simp only [Function.comp_def] at hm
  rw [hmap] at hm
  exact hbound.trans_eq (congrArg ENNReal.toReal hm.symm)

variable (hseed : Γ.seedLaw=NativeLocalPolicy.seedLaw)
  (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1) (hcoef : (1-η)/2=D.ξ)
  (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hG : Γ.G=Schedule.once 2) (hg : Γ.g=0)

include hpolicy hprofiles hseed η hη0 hη1 hcoef hA hG hg in
theorem positive_payoff (d : ℝ) (hd : D.E.d=d)
    (s a h : ℝ) (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (G : ProbabilityMeasure (LowValue d)) [NullSingletonClass (G : Measure (LowValue d))]
    (i : Fin (N+1))
    (hlaw : (userProfileLaw Γ).map (rowProfile D.E i)=
      Measure.pi (fun _ : Fin N=> rivalLaw s a h (realLowLaw (G : Measure (LowValue d)))))
    (v : ℝ) (act : JointAction 2) (hk : act.routeCount=2)
    (hb : 0< act.bid) (hbd : act.bid≤ d) :
    (problem Γ i).payoff v act=
      exactExpectedPayoff N d D.ξ c (categoryLaw s a h hs ha hh hsum Gref) G (v,act.bid) := by
  have hrow:=measurable_rowProfile D.E i
  have hgeneric : ∀ᵐp ∂userProfileLaw Γ,rowCopyGeneric (1-D.ξ) act.bid (rowProfile D.E i p) := by
    apply (ae_map_iff hrow.aemeasurable
      (measurableSet_rowCopyGeneric (1-D.ξ) act.bid)).mp
    rw [hlaw]
    exact ae_iid_rowCopyGeneric (sub_pos.mpr D.xi_lt_one) hb.ne'
      s a h hs ha hh hsum (G : Measure (LowValue d))
  have hbd' : act.bid≤ D.E.d := by rwa [hd]
  have hidentity : ∀ᵐp ∂userProfileLaw Γ,
      (∫seed,nativeRealizedPayoff Γ i v act ((p,seed),Equiv.refl (Fin 2))
        ∂Measure.pi (fun _ : Fin 2=> Γ.seedLaw))=
        literalRowPayoff D.ξ c v (act.bid,rowProfile D.E i p) := by
    filter_upwards [hprofiles,hgeneric] with p hp hgen
    rw [native_seed_average D Γ hpolicy hseed η hη0 hη1 hcoef hA hG hg
      i v act hk hbd' p (fun r=> hp (i.succAbove r))]
    exact actual_context_positive_payoff D.ξ D.xi_pos D.xi_lt_one c d
      (by rw [←hd];exact D.E.d_nonneg) i act.bid hb hbd (rowProfile D.E i p)
      (fun r hr=> by simpa only [hd] using rowProfile_low_bounds D.E i p r hr) v hgen
  rw [broadcast_payoff_of_row_identity Γ i v act hk D.xi_pos D.xi_lt_one
    (rowProfile D.E i) hrow _ hlaw hidentity]
  exact integral_literalRowPayoff_eq_exact D.xi_pos D.xi_lt_one s a h hs ha hh hsum Gref G v act.bid

end FCAppendix.Affine.Tail04.NativeLowInterim
