import FCAppendix.Existence.R01PayOnceNativePayoff

noncomputable section
namespace FCAppendix.Bayes.PayOnceConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.PayOnceBounded

variable {N n c : ℕ} (hn : 2≤n) (F : Measure ℝ) [IsProbabilityMeasure F]
    {W : ℝ} (κ : Kernel ℝ (FloorAction 0 W)) [IsMarkovKernel κ]
    (g : ℝ) (hg : 0≤g)
local notation "Gamma"=>mixedGame (N+1) n c hn F κ (Schedule.once n) g hg

theorem nativeAction_injective (hn : 2≤n) : Function.Injective (nativeAction n (W:=W)) := by
  intro a b hab
  cases a with
  | inl u=>
    cases b with
    | inl v=>cases u; cases v; rfl
    | inr bb=>
      have hr:=congrArg JointAction.routeCount hab
      change 0=n at hr
      omega
  | inr aa=>
    cases b with
    | inl u=>
      have hr:=congrArg JointAction.routeCount hab
      change n=0 at hr
      omega
    | inr bb=>
      congr 1
      exact Subtype.ext (congrArg JointAction.bid hab)

theorem measurableEmbedding_nativeAction (hn : 2≤n) : MeasurableEmbedding (nativeAction n (W:=W)) :=
  (measurable_nativeAction n W).measurableEmbedding (nativeAction_injective hn)

theorem mixedGame_usersOptimal_of_net_IC (net : ℝ→Value W) (hnet : Measurable net)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hjoint : (F ⊗ₘ κ).map (fun z : ℝ×FloorAction 0 W=>(net z.1,z.2))=
      (π : Measure (Value W × FloorAction 0 W)))
    (hneteq : ∀ᵐv ∂F,g<v→(net v).1=v-g)
    (hIC : ∀ᵐv ∂F,∀ᵐb ∂κ v,∀b' : FloorAction 0 W,
      positivePayoff N n c π (net v,b')≤positivePayoff N n c π (net v,b))
    (hinactive : ∀ᵐv ∂F,∀ᵐb ∂κ v,v≤g→present b=false) : UsersOptimal Gamma := by
  have hbid:=mixedGame_bid_law_of_joint_law (N:=N) (c:=c) hn F κ g hg net hnet π hjoint
  intro i
  filter_upwards [hneteq,hIC,hinactive] with v hv hICv hiv
  change ∀ᵐa ∂(κ.map (nativeAction n)) v,(problem Gamma i).BestResponse v a
  rw [Kernel.map_apply _ (measurable_nativeAction n W),
    (measurableEmbedding_nativeAction hn).ae_map_iff]
  filter_upwards [hICv,hiv] with b hb hbi
  intro a
  by_cases hvpos : g<v
  · have hnetv:=hv hvpos
    have hplayed : (problem Gamma i).payoff v (nativeAction n b)=positivePayoff N n c π (net v,b) := by
      rw [mixedGame_native_payoff hn F κ g hg π hbid]
      change (v-g-bid b)*positiveQ N n c π b=((net v).1-bid b)*positiveQ N n c π b
      rw [hnetv]
    have hnonneg : 0≤positivePayoff N n c π (net v,b) := by
      simpa only [positivePayoff_inactive N n c hn π] using hb (.inl ())
    rw [hplayed]
    by_cases ha : a.bid≤v-g
    · have hbw : a.bid≤W := ha.trans (by rw [←hnetv]; exact (net v).2.2)
      let bb : Icc (0:ℝ) W:=⟨a.bid,a.bid_nonneg,hbw⟩
      have he : broadcastAction a=nativeAction n (.inr bb) := rfl
      have hmono:=success_le_same_bid_broadcast Gamma i a
      rw [he] at hmono
      have hmul:=mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr ha)
      have hpay : (problem Gamma i).payoff v a≤
          (problem Gamma i).payoff v (nativeAction n (.inr bb)) := by
        rw [payoff_once Gamma rfl rfl,payoff_once Gamma rfl rfl]
        change (v-a.bid-g)*((problem Gamma i).outcome a).success≤
          (v-a.bid-g)*((problem Gamma i).outcome (nativeAction n (.inr bb))).success
        convert hmul using 1 <;> first | rfl | ring
      have hdev : (problem Gamma i).payoff v (nativeAction n (.inr bb))=
          positivePayoff N n c π (net v,.inr bb) := by
        rw [mixedGame_native_payoff hn F κ g hg π hbid]
        change (v-g-bb.1)*positiveQ N n c π (.inr bb)=((net v).1-bb.1)*positiveQ N n c π (.inr bb)
        rw [hnetv]
      exact hpay.trans (hdev.trans_le (hb (.inr bb)))
    · have hnonpos : (problem Gamma i).payoff v a≤0 := by
        rw [payoff_once Gamma rfl rfl]
        exact mul_nonpos_of_nonpos_of_nonneg (by change v-a.bid-g≤0; linarith)
          (CountLaw.success_nonneg _)
      exact hnonpos.trans hnonneg
  · have hbi0:=hbi (le_of_not_gt hvpos)
    have hplayed : (problem Gamma i).payoff v (nativeAction n b)=0 := by
      cases b with
      | inl u=>
        cases u
        rw [mixedGame_native_payoff hn F κ g hg π hbid,
          positiveQ_zero_bid N n c hn π (.inl ()) rfl,mul_zero]
      | inr bb=>simp [present] at hbi0
    rw [hplayed,payoff_once Gamma rfl rfl]
    exact mul_nonpos_of_nonpos_of_nonneg
      (by change v-a.bid-g≤0; linarith [a.bid_nonneg]) (CountLaw.success_nonneg _)

end FCAppendix.Bayes.PayOnceConstruction
