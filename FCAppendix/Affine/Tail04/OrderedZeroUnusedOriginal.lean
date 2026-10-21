import FCAppendix.Affine.Tail04.OrderedZeroUnusedFiberLaw
import FCAppendix.Affine.Tail04.OrderedUnusedRowAverage
import FCAppendix.Affine.Tail04.ZeroOriginalRowCompression
import FCAppendix.Affine.Tail04.OrderedZeroSourceUnusedPublic

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroUnusedOriginal
open MeasureTheory ProbabilityTheory Set Filter Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation CompactSourceBidLaws
open SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeBindings OrderedZeroNativeCategories
open NativeActiveFiberCoordinates NativeFiberEnumerations PartialNativeCoordinates
open NativeHighExperiment NativeLocalPolicy PrivateRowSorting EqualPrivateUpper
open OrderedZeroCommonMenuCount OriginalActiveCompression MenuError UnusedRowAverage
open scoped BigOperators

private lemma fiberRare {n : ℕ} {x y p q : ℝ}
    (h : x+y*((((n+1:ℕ):ℝ))*p)≤q) : x+y*((n+1:ℝ)*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw) (π : JointProfile D P t ht)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀v,t< v→ H≤ upperBid v) (N : ℕ)
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))))≤ D.R)

def commonLaw : ProbabilityMeasure (Icc (1:ℝ) D.U) :=
  OrderedZeroActiveFiberLaw.commonLaw D P t ht hdR H hUH π

lemma count_subtype (kind : Fin N→ Fin 4) (k : Fin 4) :
    (installOriginal D P t ht).count kind k=Fintype.card {r : Fin N // kind r=k} := by
  simp only [FiniteTailNoisyGame.Data.count,Fintype.card_subtype]

lemma count_rivalSet (i : Fin (N+1)) (kind : Fin N→ Fin 4) (k : Fin 4) :
    (installOriginal D P t ht).count kind k=(rivalSet i kind k).card :=
  (rivalSet_card_filter i kind k).symm

variable (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 D.ξ D.c cats P.originalLowLaw)
  (hL : πL=L.joint)

include cats L hL in
theorem fiber_error (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (B0 γ a y : ℝ) (hy0 : 0≤ y) (hy : (regions D P hdR H hUH).localTag (some y)=1)
    (hyo : y∉Icc (1:ℝ) D.U) (target : CountLaw 2) (f : Fin 3→ℝ) :
    |(fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (fiberRare hrare) kind i
        (RawRoutes.action y hy0 2)).expect f-target.expect f|≤
      (∫row : Fin ((installOriginal D P t ht).count kind 1)→ Icc (1:ℝ) D.U,
        totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) ((installOriginal D P t ht).count kind 1) (min ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3),max ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3))
          D.U B0 D.R D.Up D.width γ a y target f row
          ∂Measure.pi (fun _ : Fin ((installOriginal D P t ht).count kind 1)=>(ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hUH π))))+
      2*MenuError.oscillation f*(if (installOriginal D P t ht).count kind 0=0 then 1 else 0) := by
  let A:=commonSize i kind
  let H0:=(localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 2)
  let H1:=(localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare).finiteCount (rivalSet i kind 3)
  let M:=Measure.pi (fun _ : Fin A=>(ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hUH π)))
  haveI hM : IsProbabilityMeasure M := by
    dsimp only [M]
    infer_instance
  let priv:=rawPayloadLaw (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) (OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (fiberRare hrare)) H0 H1
  let T:=(Fin A→ Icc (1:ℝ) D.U)×(unitInterval×RawPayload (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) H0 H1)
  have ho:=oscillation_nonneg f
  by_cases hl : 0< (installOriginal D P t ht).count kind 0
  · have hc : 0< Fintype.card {r : Fin N // kind r=0} := by
      rw [←count_subtype D P t ht N]
      exact hl
    let n:=Fintype.card {r : Fin N // kind r=0}-1
    have hn : n+1=Fintype.card {r : Fin N // kind r=0}:=Nat.sub_add_cancel hc
    let el : Fin (n+1)≃{r : Fin N // kind r=0}:=
      (castEquiv hn).trans (Fintype.equivFin {r : Fin N // kind r=0}).symm
    have hnativ:=OrderedZeroUnusedFiberLaw.original_fiber_count_error D P t ht hdR H hUH πL π
      upperBid hupperBid hfloor N (fiberRare hrare) i kind n el cats L hL y hy0 hy hyo f
    have hbad:=@OrderedUnusedRowAverage.native_failure_integral _ _ _ (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) H0 H1 (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) rfl rfl rfl rfl (OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (fiberRare hrare)) M hM B0 γ a
    have hrow : ∀H' : Fin ((N+1)+1),(localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare).originalPrivateRow H'=
        PrivateRowSorting.sortedOriginalIid (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare).E H'.val (OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (fiberRare hrare)) := fun _=> rfl
    have href:=@OrderedUnusedRowAverage.reference_target_error _ _ _ (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) H0 H1 (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) rfl rfl rfl rfl (OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (fiberRare hrare)) hrow M hM
      B0 γ a y target f
    let actual:=fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (fiberRare hrare) kind i
      (RawRoutes.action y hy0 2)
    let reference:=@OrderedUnusedRowAverage.reference _ _ _ (localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare) H0 H1 (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) (OrderedZeroActiveFiberLaw.privateLaw D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (fiberRare hrare)) M hM y
    let bad:=UnusedRowAverage.failure (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) A (min (H0.val) (H1.val),max (H0.val) (H1.val)) D.U B0 D.R D.Up D.width γ a
    let err:=fun row : Fin A→ Icc (1:ℝ) D.U=>
      |publicValue (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) A (min (H0.val) (H1.val),max (H0.val) (H1.val)) D.U y f row-target.expect f|
    have hib:=integrable_failure (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) A (min (H0.val) (H1.val),max (H0.val) (H1.val)) D.U B0 D.R D.Up D.width γ a M
    have hie:=(integrable_publicValue (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) A (min (H0.val) (H1.val),max (H0.val) (H1.val)) D.U y f M).sub (integrable_const (target.expect f)) |>.abs
    have he : (∫row,totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) A (min (H0.val) (H1.val),max (H0.val) (H1.val)) D.U B0 D.R D.Up D.width γ a y target f row ∂M)=
        (∫row,err row+2*MenuError.oscillation f*bad row ∂M)+2*MenuError.oscillation f*(∫row,bad row ∂M) := by
      have hi4 := integral_add hie (hib.const_mul (4*MenuError.oscillation f))
      have hi2 := integral_add hie (hib.const_mul (2*MenuError.oscillation f))
      have he4 : (∫row,err row+4*MenuError.oscillation f*bad row ∂M)=
          (∫row,err row ∂M)+4*MenuError.oscillation f*(∫row,bad row ∂M) := by
        simpa only [Pi.add_apply,integral_const_mul] using! hi4
      have he2 : (∫row,err row+2*MenuError.oscillation f*bad row ∂M)=
          (∫row,err row ∂M)+2*MenuError.oscillation f*(∫row,bad row ∂M) := by
        simpa only [Pi.add_apply,integral_const_mul] using! hi2
      change (∫row,err row+4*MenuError.oscillation f*bad row ∂M)=_
      rw [he4,he2]
      ring
    have hnb : |actual.expect f-reference.expect f|≤2*MenuError.oscillation f*(∫row,bad row ∂M) := by
      simpa only [actual,reference,OrderedUnusedRowAverage.reference,
        OrderedZeroUnusedFiberLaw.referenceCount,bad] using!
        hnativ.trans (mul_le_mul_of_nonneg_left hbad (by positivity))
    have hall : |actual.expect f-target.expect f|≤
        ∫row : Fin A→ Icc (1:ℝ) D.U,
          totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) A (min (H0.val) (H1.val),max (H0.val) (H1.val)) D.U B0 D.R D.Up D.width γ a y target f row ∂M := by
      have href' : |reference.expect f-target.expect f|≤
          ∫row,err row+2*MenuError.oscillation f*bad row ∂M := by
        simpa only [reference,err,bad] using! href
      have htri:=abs_sub_le (actual.expect f) (reference.expect f) (target.expect f)
      linarith only [htri,hnb,href',he]
    let I (A h0 h1 : ℕ) : ℝ := ∫row : Fin A→Icc (1:ℝ) D.U,
      totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) A
        (min h0 h1,max h0 h1) D.U B0 D.R D.Up D.width γ a y target f row
        ∂Measure.pi (fun _ : Fin A => ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hUH π))
    have hA : A=(installOriginal D P t ht).count kind 1 :=
      (count_rivalSet D P t ht N i kind 1).symm
    have h0 : H0.val=(installOriginal D P t ht).count kind 2 :=
      (count_rivalSet D P t ht N i kind 2).symm
    have h1 : H1.val=(installOriginal D P t ht).count kind 3 :=
      (count_rivalSet D P t ht N i kind 3).symm
    have hindex : I A H0.val H1.val=I ((installOriginal D P t ht).count kind 1)
        ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3) :=
      (congrArg (fun n => I n H0.val H1.val) hA).trans
        ((congrArg (fun n => I ((installOriginal D P t ht).count kind 1) n H1.val) h0).trans
          (congrArg (fun n => I ((installOriginal D P t ht).count kind 1)
            ((installOriginal D P t ht).count kind 2) n) h1))
    change |actual.expect f-target.expect f|≤I A H0.val H1.val at hall
    rw [hindex] at hall
    simpa only [if_neg (Nat.ne_of_gt hl),mul_zero,add_zero] using! hall
  · have hz : (installOriginal D P t ht).count kind 0=0:=Nat.eq_zero_of_not_pos hl
    have hp:=count_expect_difference_bound
      (fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (fiberRare hrare) kind i
        (RawRoutes.action y hy0 2)) target f
    have he : 0≤(∫row : Fin ((installOriginal D P t ht).count kind 1)→ Icc (1:ℝ) D.U,
        totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) ((installOriginal D P t ht).count kind 1) (min ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3),max ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3))
          D.U B0 D.R D.Up D.width γ a y target f row
          ∂Measure.pi (fun _ : Fin ((installOriginal D P t ht).count kind 1)=>(ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hUH π)))) :=
      integral_nonneg fun row=>(totalError_bounds (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) _ _ _ _ _ _ _ _ _ _ target f row).1
    rw [if_pos hz,mul_one]
    linarith

theorem noLow_probability :
    (CommonList.iid (installOriginal D P t ht).categories N).expect (fun kind=> if (installOriginal D P t ht).count kind 0=0 then (1:ℝ) else 0)=
      (Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))).real {r : Fin N→ UserDraw 2 | (installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 0=0} := by
  have hmass:=native_source_category_ne_zero D P t ht hdR H hUH πL π upperBid hupperBid hfloor
    (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare) (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)
  have hcat:=native_source_category_mass D P t ht hdR H hUH πL π upperBid hupperBid hfloor
    (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare) (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)
  have hρ:=ZeroNativeFiberProduct.common_projection_law D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N (fiberRare hrare)
  let g : (kind : Fin N→ Fin 4)→(Fin ((installOriginal D P t ht).count kind 1)→ Icc (1:ℝ) D.U)→ℝ:=
    fun kind _=> if (installOriginal D P t ht).count kind 0=0 then 1 else 0
  have he:=ZeroOriginalRowCompression.original_integral (installOriginal D P t ht) (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)) ((regions D P hdR H hUH).coarseTag) (regions D P hdR H hUH).measurable_coarseTag
    (ZeroNativeFiberProduct.commonProjection D P hdR H hUH) (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH)
    hmass (commonLaw D P t ht hdR H hUH π) hρ hcat g (fun _=> measurable_const) 1 (fun _ _=> by dsimp [g];split_ifs <;> norm_num)
  have hs : MeasurableSet {r : Fin N→ UserDraw 2 | (installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 0=0} :=
    ((Set.to_countable {kind : Fin N→ Fin 4 | (installOriginal D P t ht).count kind 0=0}).measurableSet).preimage
      (measurable_tags ((regions D P hdR H hUH).coarseTag) (regions D P hdR H hUH).measurable_coarseTag)
  have hi : (∫r : Fin N→ UserDraw 2,if (installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 0=0 then (1:ℝ) else 0 ∂(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))))=
      (Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))).real {r : Fin N→ UserDraw 2 | (installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 0=0} := by
    simpa only [Set.indicator,Pi.one_apply,Set.mem_setOf_eq] using! integral_indicator_one (μ:=(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare))))) hs
  simp only [ZeroOriginalRowCompression.rowObservable,g,integral_const,probReal_univ,one_smul] at he
  exact he.symm.trans hi

include cats L hL in
theorem original_error (i : Fin (N+1)) (B0 γ a y : ℝ)
    (hy0 : 0≤ y) (hy : (regions D P hdR H hUH).localTag (some y)=1) (hyo : y∉Icc (1:ℝ) D.U)
    (target : CountLaw 2) (f : Fin 3→ℝ) :
    |((problem (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare) i).outcome (RawRoutes.action y hy0 2)).expect f-target.expect f|≤
      (∫r : Fin N→ UserDraw 2,
        totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) ((installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 1) (min ((installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 2) ((installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 3),max ((installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 2) ((installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 3))
          D.U B0 D.R D.Up D.width γ a y target f (baseCommonRow (installOriginal D P t ht) (ZeroNativeFiberProduct.commonProjection D P hdR H hUH) (tags ((regions D P hdR H hUH).coarseTag) r) r) ∂(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))))+
      2*MenuError.oscillation f*(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))).real {r : Fin N→ UserDraw 2 | (installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 0=0} := by
  have hmass:=native_source_category_ne_zero D P t ht hdR H hUH πL π upperBid hupperBid hfloor
    (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare) (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)
  have hcat:=native_source_category_mass D P t ht hdR H hUH πL π upperBid hupperBid hfloor
    (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare) (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)
  have hρ:=ZeroNativeFiberProduct.common_projection_law D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor N (fiberRare hrare)
  let g : (kind : Fin N→ Fin 4)→(Fin ((installOriginal D P t ht).count kind 1)→ Icc (1:ℝ) D.U)→ℝ:=
    fun kind=> totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) ((installOriginal D P t ht).count kind 1) (min ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3),max ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3))
      D.U B0 D.R D.Up D.width γ a y target f
  have hg : ∀kind,Measurable (g kind):=fun kind=> measurable_totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) _ _ _ _ _ _ _ _ _ _ target f
  have hgb : ∀kind row,‖g kind row‖≤6*MenuError.oscillation f := by
    intro kind row
    have hb : g kind row∈Icc (0:ℝ) (6*MenuError.oscillation f) := totalError_bounds (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) _ _ _ _ _ _ _ _ _ _ target f row
    rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
    exact hb.2
  have he:=ZeroOriginalRowCompression.original_integral (installOriginal D P t ht) (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)) ((regions D P hdR H hUH).coarseTag) (regions D P hdR H hUH).measurable_coarseTag
    (ZeroNativeFiberProduct.commonProjection D P hdR H hUH) (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH)
    hmass (commonLaw D P t ht hdR H hUH π) hρ hcat g hg (6*MenuError.oscillation f) hgb
  let w:=CommonList.iid (installOriginal D P t ht).categories N
  let val:=fun kind=>(fiberCount D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (fiberRare hrare)
    kind i (RawRoutes.action y hy0 2)).expect f
  let err:=fun kind=>∫row : Fin ((installOriginal D P t ht).count kind 1)→ Icc (1:ℝ) D.U,g kind row
    ∂Measure.pi (fun _ : Fin ((installOriginal D P t ht).count kind 1)=>(ProbabilityMeasure.toMeasure (commonLaw D P t ht hdR H hUH π)))
  have hh:=w.abs_expect_le (fun kind=> val kind-target.expect f)
  rw [FiniteLaw.expect_sub,FiniteLaw.expect_const] at hh
  have hb:=w.expect_mono (fun kind=> fiber_error D P t ht hdR H hUH πL π upperBid hupperBid
    hfloor N hrare cats L hL i kind B0 γ a y hy0 hy hyo target f)
  have hb' : w.expect (fun kind=>|val kind-target.expect f|)≤
      w.expect err+2*MenuError.oscillation f*w.expect (fun kind=> if (installOriginal D P t ht).count kind 0=0 then 1 else 0) := by
    simpa only [FiniteLaw.expect_add,FiniteLaw.expect_const_mul,err,g] using! hb
  rw [noLow_probability D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare] at hb'
  have hnative : ((problem (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare) i).outcome (RawRoutes.action y hy0 2)).expect f=w.expect val :=
    native_count_statistic_mixture D P t ht hdR H hUH πL π upperBid hupperBid hfloor N (fiberRare hrare) i _ f
  have herr : w.expect err=∫r : Fin N→ UserDraw 2,
      totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) ((installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 1) (min ((installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 2) ((installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 3),max ((installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 2) ((installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 3))
        D.U B0 D.R D.Up D.width γ a y target f (baseCommonRow (installOriginal D P t ht) (ZeroNativeFiberProduct.commonProjection D P hdR H hUH) (tags ((regions D P hdR H hUH).coarseTag) r) r) ∂(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))) := by
    exact he.symm
  rw [hnative]
  exact hh.trans (by rw [herr] at hb';exact hb')

theorem source_integrable_error (y : ℝ) (target : CountLaw 2) (f : Fin 3→ℝ) :
    Integrable (fun r : Fin N→ UserDraw 2=>
      |(OrderedZeroSourceUnusedPublic.count D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r y).expect f-
          target.expect f|+
        4*MenuError.oscillation f*OrderedZeroSourceUnusedPublic.bad D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r) (Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))) := by
  let g : (kind : Fin N→ Fin 4)→(Fin ((installOriginal D P t ht).count kind 1)→ Icc (1:ℝ) D.U)→ℝ:=
    fun kind=> totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) ((installOriginal D P t ht).count kind 1) (min ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3),max ((installOriginal D P t ht).count kind 2) ((installOriginal D P t ht).count kind 3))
      D.U (Central.B D.ξ) D.R D.Up D.width (SourceMomentRectangle.γ D.ξ) (D.ξ/4) y target f
  have hg : ∀kind,Measurable (g kind):=fun kind=> measurable_totalError (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) _ _ _ _ _ _ _ _ _ _ target f
  have hb : ∀kind row,‖g kind row‖≤6*MenuError.oscillation f := by
    intro kind row
    have hh : g kind row∈Icc (0:ℝ) (6*MenuError.oscillation f) := totalError_bounds (publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor) _ _ _ _ _ _ _ _ _ _ target f row
    rw [Real.norm_eq_abs,abs_of_nonneg hh.1]
    exact hh.2
  exact ZeroOriginalRowCompression.integrable_rowObservable (installOriginal D P t ht) (Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))) ((regions D P hdR H hUH).coarseTag) (regions D P hdR H hUH).measurable_coarseTag
    (ZeroNativeFiberProduct.commonProjection D P hdR H hUH) (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH) g hg
    (6*MenuError.oscillation f) hb

include cats L hL in
theorem source_original_error (i : Fin (N+1)) (y : ℝ)
    (hy0 : 0≤ y) (hy : (regions D P hdR H hUH).localTag (some y)=1) (hyo : y∉Icc (1:ℝ) D.U)
    (target : CountLaw 2) (f : Fin 3→ℝ) :
    |((problem (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare) i).outcome (RawRoutes.action y hy0 2)).expect f-target.expect f|≤
      (∫r : Fin N→ UserDraw 2,
        |(OrderedZeroSourceUnusedPublic.count D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r y).expect f-
            target.expect f|+
          4*MenuError.oscillation f*OrderedZeroSourceUnusedPublic.bad D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r ∂(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))))+
      2*MenuError.oscillation f*(Measure.pi (fun _ : Fin N=> (userLaw (game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)))).real {r : Fin N→ UserDraw 2 | (installOriginal D P t ht).count (tags ((regions D P hdR H hUH).coarseTag) r) 0=0} :=
  original_error D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare cats L hL i
    (Central.B D.ξ) (SourceMomentRectangle.γ D.ξ) (D.ξ/4) y hy0 hy hyo target f

end FCAppendix.Affine.Tail04.OrderedZeroUnusedOriginal
