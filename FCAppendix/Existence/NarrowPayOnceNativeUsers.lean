import FCAppendix.Existence.NarrowPayOnceNativeTransport
import FCAppendix.Existence.NarrowPayOnceSurplus

noncomputable section
namespace FCAppendix.Bayes.PayOnceNarrow
open Set Filter Topology MeasureTheory ProbabilityTheory Game CommonList PayOnce
open Existence.NarrowPayOnce Existence.PayOnceBounded PayOnceConstruction

variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)
  (nu : Measure U.valueBand) [IsProbabilityMeasure nu] (beta : U.strategyBand)

def playedAction (v : U.valueBand) : JointAction n :=
  ⟨beta.val v,(U.lower_pos.trans_le (beta.property v).1).le,n,le_rfl⟩

theorem strategy_at_physical (g : ℝ) (hg : 0≤g) (v : U.valueBand) :
    (game U nu beta g hg).σ ((v:ℝ)+g)=Measure.dirac (playedAction U beta v) := by
  change ((stateKernel U beta g).map (nativeAction n)) ((v:ℝ)+g)=_
  rw [Kernel.map_apply _ (measurable_nativeAction n (U.B+eps)),stateKernel,
    Kernel.deterministic_apply,Measure.map_dirac' (measurable_nativeAction n (U.B+eps))]
  congr 1
  simp only [activeState,activeBid,projectNet_physical,nativeAction,playedAction]

theorem payoff_zero_bid (g : ℝ) (hg : 0≤g) (i : Fin (R+1)) (v : ℝ)
    (a : JointAction n) (hb : a.bid=0) : (problem (game U nu beta g hg) i).payoff v a=0 := by
  rw [payoff_once (game U nu beta g hg) rfl rfl,interim_success U nu beta g hg i a]
  have hz (omega : Fin R→U.valueBand) : positiveMarginal n c (rowBids beta.val a.bid omega) 0=0 := by
    apply onSupport_outside
    rw [mem_positiveSupport]
    simp only [rowBids,Fin.cons_zero,hb,lt_self_iff_false,not_false_eq_true]
  simp only [hz,PayOnce.success,sub_zero,one_pow,sub_self,integral_zero,mul_zero]

theorem played_payoff_positive (g : ℝ) (hg : 0≤g)
    (hroot : ∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0)
    (i : Fin (R+1)) (v : U.valueBand) :
    0<(problem (game U nu beta g hg) i).payoff ((v:ℝ)+g) (playedAction U beta v) := by
  rw [payoff_broadcast U nu beta g hg i v (playedAction U beta v) rfl
    (U.lower_pos.trans_le (beta.property v).1)]
  exact U.stationary_utility_pos nu beta hroot v

theorem bestResponse (g : ℝ) (hg : 0≤g)
    (hroot : ∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0)
    (hglobal : ∀(v : U.valueBand) (z : ℝ),0<z →
      finiteExpectedUtility (R:=R) n c nu beta.val v z≤
        finiteExpectedUtility (R:=R) n c nu beta.val v (beta.val v))
    (i : Fin (R+1)) (v : U.valueBand) :
    (problem (game U nu beta g hg) i).BestResponse ((v:ℝ)+g) (playedAction U beta v) := by
  intro a
  have hplayed:=payoff_broadcast U nu beta g hg i v (playedAction U beta v) rfl
    (U.lower_pos.trans_le (beta.property v).1)
  have hpositive:=played_payoff_positive U nu beta g hg hroot i v
  by_cases hb0 : a.bid=0
  · rw [payoff_zero_bid U nu beta g hg i ((v:ℝ)+g) a hb0]
    exact hpositive.le
  have hb:0<a.bid := lt_of_le_of_ne a.bid_nonneg (Ne.symm hb0)
  by_cases hwb : a.bid≤(v:ℝ)
  · have hmono:=success_le_same_bid_broadcast (game U nu beta g hg) i a
    have hmul:=mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hwb)
    have hpay:(problem (game U nu beta g hg) i).payoff ((v:ℝ)+g) a≤
        (problem (game U nu beta g hg) i).payoff ((v:ℝ)+g) (broadcastAction a) := by
      rw [payoff_once (game U nu beta g hg) rfl rfl,payoff_once (game U nu beta g hg) rfl rfl]
      change ((v:ℝ)+g-a.bid-g)*_≤((v:ℝ)+g-a.bid-g)*_
      convert hmul using 1 <;> first | rfl | ring
    have hdev:=payoff_broadcast U nu beta g hg i v (broadcastAction a) rfl hb
    rw [hplayed]
    exact hpay.trans (hdev.trans_le (hglobal v a.bid hb))
  · have hnonpos:(problem (game U nu beta g hg) i).payoff ((v:ℝ)+g) a≤0 := by
      rw [payoff_once (game U nu beta g hg) rfl rfl]
      apply mul_nonpos_of_nonpos_of_nonneg _ (CountLaw.success_nonneg _)
      change (v:ℝ)+g-a.bid-g≤0
      linarith
    exact hnonpos.trans hpositive.le

theorem usersOptimal (g : ℝ) (hg : 0≤g)
    (hroot : ∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0)
    (hglobal : ∀(v : U.valueBand) (z : ℝ),0<z →
      finiteExpectedUtility (R:=R) n c nu beta.val v z≤
        finiteExpectedUtility (R:=R) n c nu beta.val v (beta.val v)) :
    UsersOptimal (game U nu beta g hg) := by
  intro i
  have hm : MeasurableEmbedding (fun v : U.valueBand=>(v:ℝ)+g) :=
    (measurable_subtype_coe.add_const g).measurableEmbedding (by
      intro v w he
      apply Subtype.ext
      linarith)
  change ∀ᵐv ∂nu.map (fun v : U.valueBand=>(v:ℝ)+g),
    ∀ᵐa ∂(game U nu beta g hg).σ v,(problem (game U nu beta g hg) i).BestResponse v a
  rw [hm.ae_map_iff]
  filter_upwards [] with v
  rw [strategy_at_physical U nu beta g hg v,ae_dirac_eq]
  exact bestResponse U nu beta g hg hroot hglobal i v

theorem fewer_routes_strict (g : ℝ) (hg : 0≤g)
    (hroot : ∀v : U.valueBand,finiteExpectedScore (R:=R) n c nu beta.val v (beta.val v)=0)
    (i : Fin (R+1)) (v : U.valueBand) (a : JointAction n)
    (hbid : a.bid=beta.val v) (hk : a.routeCount<n) :
    (problem (game U nu beta g hg) i).payoff ((v:ℝ)+g) a<
      (problem (game U nu beta g hg) i).payoff ((v:ℝ)+g) (playedAction U beta v) := by
  have hb:0<beta.val v := U.lower_pos.trans_le (beta.property v).1
  have hsurplus:=sub_pos.mpr (U.stationary_bid_lt_value nu beta hroot v)
  let p:=fun omega : Fin R→U.valueBand=>finiteRowMarginal n c beta.val (beta.val v) omega
  let f:=fun k : ℕ=>fun omega : Fin R→U.valueBand=>((v:ℝ)-beta.val v)*PayOnce.success k (p omega)
  have hp (omega : Fin R→U.valueBand) : p omega∈Ioo (0:ℝ) 1 :=
    U.interior _ (U.row_box beta.val beta.property (beta.val v) (beta.property v) omega) 0
  have hcp : Continuous p := by
    rw [continuous_iff_continuousAt]
    intro omega
    have hh:=continuousAt_rowKernel_joint (c:=c) U.n_ge beta.val beta.val.continuous
      (fun v=>U.lower_pos.trans_le (beta.property v).1) (beta.val v,omega) hb
    exact (continuous_apply 0).continuousAt.comp
      (hh.comp (f:=fun omega : Fin R→U.valueBand=>(beta.val v,omega)) (x:=omega)
        (continuous_const.prodMk continuous_id).continuousAt)
  have hi (k : ℕ) : Integrable (f k) (Measure.pi (fun _=>nu)) :=
    (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,continuous_const.mul ((continuous_success k).comp hcp)⟩).integrable _
  have hpositive (omega : Fin R→U.valueBand) : 0<f n omega-f a.routeCount omega := by
    have hpow:=pow_lt_pow_right_of_lt_one₀ (sub_pos.mpr (hp omega).2)
      (show 1-p omega<1 by linarith [(hp omega).1]) hk
    have hs:PayOnce.success a.routeCount (p omega)<PayOnce.success n (p omega) := by
      unfold PayOnce.success
      linarith
    exact sub_pos.mpr (mul_lt_mul_of_pos_left hs hsurplus)
  have hpos : 0<∫omega : Fin R→U.valueBand,f n omega-f a.routeCount omega ∂Measure.pi (fun _=>nu) := by
    apply (integral_pos_iff_support_of_nonneg (fun omega=>(hpositive omega).le) ((hi n).sub (hi a.routeCount))).mpr
    have hs:Function.support (fun omega : Fin R→U.valueBand=>f n omega-f a.routeCount omega)=univ := by
      ext omega
      simp only [Function.mem_support,mem_univ,iff_true]
      exact (hpositive omega).ne'
    rw [hs,measure_univ]
    norm_num
  rw [integral_sub (hi n) (hi a.routeCount)] at hpos
  rw [payoff_positive_bid U nu beta g hg i v a (by rwa [hbid]),
    payoff_positive_bid U nu beta g hg i v (playedAction U beta v) hb]
  simp only [hbid,playedAction]
  exact sub_pos.mp hpos

end FCAppendix.Bayes.PayOnceNarrow
