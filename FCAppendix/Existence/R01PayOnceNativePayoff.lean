import FCAppendix.Existence.R01PayOnceNativeInterim
import FCAppendix.Existence.R01PayOncePhysicalTypes
import FCAppendix.PayOnce.BroadcastRescue

noncomputable section
namespace FCAppendix.Bayes.PayOnceConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.PayOnceBounded Existence.Distributional
open scoped BigOperators
variable {N n c : ℕ} (hn : 2≤n) (F : Measure ℝ) [IsProbabilityMeasure F]
    {W : ℝ} (κ : Kernel ℝ (FloorAction 0 W)) [IsMarkovKernel κ]
    (g : ℝ) (hg : 0≤g)
local notation "Gamma"=>mixedGame (N+1) n c hn F κ (Schedule.once n) g hg

theorem mixedGame_bid_law_of_joint_law (net : ℝ→Value W) (hnet : Measurable net)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hjoint : (F ⊗ₘ κ).map (fun z : ℝ×FloorAction 0 W=>(net z.1,z.2))=
      (π : Measure (Value W × FloorAction 0 W))) :
    realBidLaw Gamma=(π : Measure (Value W × FloorAction 0 W)).map (fun z=>bid z.2) := by
  have hb : Measurable (fun z : Value W × FloorAction 0 W=>bid z.2):=
    continuous_bid.measurable.comp measurable_snd
  have hmap : Measurable (fun z : ℝ×FloorAction 0 W=>(net z.1,z.2)) :=
    (hnet.comp measurable_fst).prodMk measurable_snd
  calc
    realBidLaw Gamma=(F ⊗ₘ κ).map (fun z : ℝ×FloorAction 0 W=>bid z.2) := by
      rw [realBidLaw_eq_action_map,mixedGame_value_action_law]
      have hh:=Measure.map_map ((measurable_bid n).comp measurable_snd)
        (measurable_id.prodMap (measurable_nativeAction n W)) (μ:=F ⊗ₘ κ)
      change Measure.map (fun x : ℝ×JointAction n=>x.2.bid)
        (Measure.map (Prod.map id (nativeAction n)) (F ⊗ₘ κ))=
        Measure.map (fun x : ℝ×FloorAction 0 W=>(nativeAction n x.2).bid) (F ⊗ₘ κ) at hh
      simpa only [nativeAction_bid] using hh
    _=((F ⊗ₘ κ).map (fun z : ℝ×FloorAction 0 W=>(net z.1,z.2))).map (fun z=>bid z.2) :=
      (Measure.map_map hb hmap).symm
    _=_ := congrArg (fun ν : Measure (Value W × FloorAction 0 W)=>ν.map (fun z=>bid z.2)) hjoint

theorem mixedGame_interim_success_of_bid_law
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hbid : realBidLaw Gamma=(π : Measure (Value W × FloorAction 0 W)).map (fun z=>bid z.2))
    (i : Fin (N+1)) (a : JointAction n) :
    ((problem Gamma i).outcome a).success=
      ∫r : Fin N→Value W × FloorAction 0 W,PayOnce.success a.routeCount
        (positiveMarginal n c (Fin.cons a.bid (fun j=>bid (r j).2)) 0)
        ∂(rowLaw N π : Measure (Fin N→Value W × FloorAction 0 W)) := by
  rw [mixedGame_interim_success hn F κ (Schedule.once n) g hg,hbid]
  have hb : Measurable (fun z : Value W × FloorAction 0 W=>bid z.2):=
    continuous_bid.measurable.comp measurable_snd
  have hmap:=Measure.pi_map_pi (μ:=fun _ : Fin N=>(π : Measure (Value W × FloorAction 0 W)))
    (fun _ : Fin N=>hb.aemeasurable)
  rw [←hmap,←rowLaw_eq_pi]
  have hf : Measurable (fun r : Fin N→ℝ=>PayOnce.success a.routeCount
      (positiveMarginal n c (Fin.cons a.bid r) 0)) :=
    (PayOnce.continuous_success a.routeCount).measurable.comp
      ((measurable_pi_apply 0).comp ((measurable_positiveMarginal n c hn).comp
        (measurable_pi_iff.mpr (fun j=>by
          refine Fin.cases ?_ (fun k=>?_) j
          · exact measurable_const
          · exact measurable_pi_apply k))))
  exact integral_map (measurable_pi_iff.mpr (fun j=>hb.comp (measurable_pi_apply j))).aemeasurable
    hf.aestronglyMeasurable

theorem mixedGame_native_success
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hbid : realBidLaw Gamma=(π : Measure (Value W × FloorAction 0 W)).map (fun z=>bid z.2))
    (i : Fin (N+1)) (a : FloorAction 0 W) :
    ((problem Gamma i).outcome (nativeAction n a)).success=positiveQ N n c π a := by
  rw [mixedGame_interim_success_of_bid_law hn F κ g hg π hbid]
  cases a with
  | inl u=>
    cases u
    simp only [nativeAction,Interim.abstain,PayOnce.success,pow_zero,sub_self,integral_zero]
    exact (positiveQ_zero_bid N n c hn π (.inl ()) rfl).symm
  | inr b=>
    unfold positiveQ
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun r=>by
      change PayOnce.success n (positiveMarginal n c (Fin.cons b.1 (fun j=>bid (r j).2)) 0)=_
      have he : (fun j=>bid (insertFocal N (.inr b) r j))=
          Fin.cons b.1 (fun j=>bid (r j).2) := by
        funext j; refine Fin.cases ?_ (fun k=>?_) j <;> simp [insertFocal,bid]
      change PayOnce.success n (positiveMarginal n c (Fin.cons b.1 (fun j=>bid (r j).2)) 0)=
        PayOnce.success n (positiveMarginal n c (fun j=>bid (insertFocal N (.inr b) r j)) 0)
      rw [he])

theorem mixedGame_native_payoff
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hbid : realBidLaw Gamma=(π : Measure (Value W × FloorAction 0 W)).map (fun z=>bid z.2))
    (i : Fin (N+1)) (v : ℝ) (a : FloorAction 0 W) :
    (problem Gamma i).payoff v (nativeAction n a)=(v-g-bid a)*positiveQ N n c π a := by
  rw [payoff_once Gamma rfl rfl,mixedGame_native_success hn F κ g hg π hbid,nativeAction_bid]
  change (v-bid a-g)*positiveQ N n c π a=(v-g-bid a)*positiveQ N n c π a
  ring

theorem success_le_same_bid_broadcast (game : FiniteGame (N+1) n c unitInterval)
    (i : Fin (N+1)) (a : JointAction n) :
    ((problem game i).outcome a).success≤((problem game i).outcome (broadcastAction a)).success := by
  simp only [problem_outcome,CountLaw.success,CountLaw.expect_ofMeasure]
  apply integral_mono
  · exact CountLaw.integrable_comp (sampleLaw game) _ (measurable_focalCount game i a)
      (fun r=>successIndicator r.val)
  · exact CountLaw.integrable_comp (sampleLaw game) _ (measurable_focalCount game i (broadcastAction a))
      (fun r=>successIndicator r.val)
  · exact fun ω=>successIndicator_mono_nat (focalCount_le_broadcast game i a ω)

end FCAppendix.Bayes.PayOnceConstruction
