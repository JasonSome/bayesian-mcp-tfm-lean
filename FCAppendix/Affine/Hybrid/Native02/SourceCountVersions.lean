import FCAppendix.Affine.Hybrid.Native02.PrimitiveInput
import FCAppendix.Affine.Hybrid.Native02.ReferenceMenus
import FCAppendix.Affine.Hybrid.Native02.OriginalBands
import FCAppendix.Affine.Hybrid.Native02.NullActions

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes

namespace FrozenActiveFamily
variable {p : PrimitiveInput} (A : FrozenActiveFamily p)

def targetBid (v : p.Value) : p.Bid := ⟨p.beta v,A.response_boxed v⟩

theorem measurable_targetBid : Measurable A.targetBid := by
  apply Measurable.subtype_mk
  unfold PrimitiveInput.beta
  exact measurable_const.div (measurable_const.sub (measurable_const.mul A.response_measurable))

def targetAction : ℝ→ JointAction 2 := extendActiveAction p.value_order p.L_pos.le A.targetBid
def targetReal (v : ℝ) : ℝ := (A.targetAction v).bid

theorem measurable_targetAction : Measurable A.targetAction :=
  measurable_extendActiveAction p.value_order p.L_pos.le A.targetBid A.measurable_targetBid
theorem measurable_targetReal : Measurable A.targetReal :=
  (measurable_bid 2).comp A.measurable_targetAction
theorem targetReal_box (v : ℝ) : A.targetReal v∈ Icc p.L p.U :=
  A.response_boxed (Set.projIcc p.vlo p.vhi p.value_order v)
theorem targetReal_at_value (v : p.Value) : A.targetReal v.1=p.beta v := by
  unfold targetReal targetAction
  rw [extendActiveAction_at_value]
  rfl

end FrozenActiveFamily

theorem source_common_conull_set (p : PrimitiveInput) (A : FrozenActiveFamily p)
    {M C : ℕ→ℕ} (G : ∀ k,FiniteGame (M k) 2 (C k) unitInterval)
    (F : Measure ℝ) (hF : ∀ k,(G k).F=F) (t : ℝ)
    (hIC : ∀ k,UsersOptimal (G k))
    (hbands : ∀ k,∀ᵐx ∂(G k).F⊗ₘ(G k).σ,
      OriginalBandSupport p.d p.vlo p.vhi t p.L p.U p.R x)
    (hgraph : ∀ eps>0,∀ᶠk in atTop,∀ᵐx ∂(G k).F⊗ₘ(G k).σ,
      x.1∈ Icc p.vlo p.vhi→|x.2.bid-A.targetReal x.1|< eps) :
    ∃S : Set ℝ,MeasurableSet S ∧ (∀ᵐv ∂F,v∈ S) ∧ ∀ v∈ S,
      (∀ k,∀ᵐa ∂(G k).σ v,OriginalBandSupport p.d p.vlo p.vhi t p.L p.U p.R (v,a)) ∧
      (v∈ Icc p.vlo p.vhi→∀ eps>0,∀ᶠk in atTop,∀ᵐa ∂(G k).σ v,
        |a.bid-A.targetReal v|< eps) ∧
      (∀ k,∀ᵐa ∂(G k).σ v,∀ i : Fin (M k),∀ dev : JointAction 2,
        (problem (G k) i).payoff v dev≤(problem (G k) i).payoff v a) := by
  have hb : ∀ᵐv ∂F,∀ k,∀ᵐa ∂(G k).σ v,
      OriginalBandSupport p.d p.vlo p.vhi t p.L p.U p.R (v,a) := by
    apply ae_all_iff.mpr
    intro k
    simpa only [hF k] using original_conditional_band_support (G k)
      p.d p.vlo p.vhi t p.L p.U p.R (hbands k)
  have hg := original_joint_graph_to_conditional_graph G F hF (Icc p.vlo p.vhi) A.targetReal hgraph
  have hi := family_common_conull G F hF hIC
  apply exists_measurable_common_conull F
  filter_upwards [hb,hg,hi] with v hvb hvg hvi
  exact ⟨hvb,hvg,hvi⟩

theorem source_null_completed_count_limits (p : PrimitiveInput) (A : FrozenActiveFamily p)
    {M C : ℕ→ℕ} (G : ∀ k,FiniteGame (M k) 2 (C k) unitInterval)
    (F : Measure ℝ) (hF : ∀ k,(G k).F=F) (t : ℝ) (hvt : p.vhi< t)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂F,v∈ S)
    (hbands : ∀ v∈ S,∀ k,∀ᵐa ∂(G k).σ v,
      OriginalBandSupport p.d p.vlo p.vhi t p.L p.U p.R (v,a))
    (hgraph : ∀ v∈ S,v∈ Icc p.vlo p.vhi→∀ eps>0,∀ᶠk in atTop,
      ∀ᵐa ∂(G k).σ v,|a.bid-A.targetReal v|< eps)
    (lowError : ℕ→ℝ) (hlowError : Tendsto lowError atTop (𝓝 0))
    (hlowRaw : ∀ᶠk in atTop,∀ i : Fin (M k),∀ a : JointAction 2,a.bid≤ p.d→
      ((problem (G k) i).outcome a).success≤ lowError k)
    (hactiveRaw : ∀ eps>0,∀ᶠk in atTop,∀ i : Fin (M k),∀ a : JointAction 2,
      a.bid∈ Icc p.L p.U→ a.routeCount=2→∀ r,
        |((problem (G k) i).outcome a).mass r-
          activeMass p.z (exposure p.xi p.lam a.bid) r|< eps)
    (upperFloor : ℕ→ℝ) (hupperFloor : Tendsto upperFloor atTop (𝓝 1))
    (hupperRaw : ∀ k,∀ i : Fin (M k),∀ a : JointAction 2,p.R≤ a.bid→ a.routeCount=1→
      upperFloor k≤((problem (G k) i).outcome a).success)
    (upperBid : ℕ→ℝ→ℝ) (hupperMeas : ∀ k,Measurable (upperBid k))
    (hupperBid : ∀ k v,t≤ v→ p.R≤ upperBid k v) :
    let action := fun k=> sourceNullAction p.value_order p.L_pos.le p.d t A.targetBid (upperBid k)
    let actionMeas := fun k=> measurable_sourceNullAction p.value_order p.L_pos.le p.d t
      A.targetBid A.measurable_targetBid (upperBid k) (hupperMeas k)
    let G' := fun k=> nullTypeGame (G k) S hS (action k) (actionMeas k)
    (∀ v∈ Icc (0:ℝ) p.d,∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G' k) (i k) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r))) ∧
    (∀ v : p.Value,∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G' k) (i k) v.1).mass r)
        atTop (𝓝 ((activeLimitLaw p.z (p.q v) p.z_nonneg p.z_lt_one.le
          (p.q_mem v).1 (p.q_mem v).2).mass r))) ∧
    (∀ v,p.vhi< v→∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G' k) (i k) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (1:Fin 3)).mass r))) := by
  let action := fun k=> sourceNullAction p.value_order p.L_pos.le p.d t A.targetBid (upperBid k)
  let actionMeas := fun k=> measurable_sourceNullAction p.value_order p.L_pos.le p.d t
    A.targetBid A.measurable_targetBid (upperBid k) (hupperMeas k)
  let G' := fun k=> nullTypeGame (G k) S hS (action k) (actionMeas k)
  have hfullk (k : ℕ) : ∀ᵐv ∂(G k).F,v∈ S := by simpa only [hF k] using hfull
  have hdl : p.d< p.vlo := (p.d_lt_L.trans p.L_lt_U).trans p.value_surplus
  constructor
  · intro v hv i r
    by_cases hs : v∈ S
    · have hsupport (k : ℕ) : ∀ᵐa ∂(G k).σ v,a.bid≤ p.d :=
        (hbands v hs k).mono (fun a ha=>(ha.1 hv.2).1)
      have hlim := conditional_low_limit_of_uniform_raw_bound G v p.d hsupport
        lowError hlowError hlowRaw i r
      simpa only [G',nullTypeGame_typeOutcome_inside (G _) S hS (hfullk _) _ _ _ v hs] using hlim
    · have ha (k : ℕ) : (action k v).bid≤ p.d := by
        simp only [action,sourceNullAction,if_pos hv.2,lowNullAction,max_eq_left hv.1]
        linarith [hv.1,hv.2]
      have hsuc : Tendsto (fun k=>((problem (G k) (i k)).outcome (action k v)).success)
          atTop (𝓝 0) := by
        apply squeeze_zero' (Eventually.of_forall (fun k=>
          ((problem (G k) (i k)).outcome (action k v)).success_nonneg)) _ hlowError
        filter_upwards [hlowRaw] with k hk
        exact hk (i k) (action k v) (ha k)
      have hlim := count_zero_limit_of_success (fun k=>
        ((problem (G k) (i k)).outcome (action k v))) hsuc r
      simpa only [G',nullTypeGame_typeOutcome_outside (G _) S hS (hfullk _) _ _ _ v hs] using hlim
  constructor
  · intro v i r
    have hstar : p.beta v∈ Icc p.L p.U := A.response_boxed v
    have hmass : activeMass p.z (exposure p.xi p.lam (p.beta v)) r=
        (activeLimitLaw p.z (p.q v) p.z_nonneg p.z_lt_one.le
          (p.q_mem v).1 (p.q_mem v).2).mass r := by
      rw [p.exposure_beta,activeLimitLaw_mass]
    by_cases hs : v.1∈ S
    · have hsupport (k : ℕ) : ∀ᵐa ∂(G k).σ v.1,a.bid∈ Icc p.L p.U ∧ a.routeCount=2 :=
        (hbands v.1 hs k).mono (fun a ha=> ha.2.1 v.property)
      have hgr : ∀ delta>0,∀ᶠk in atTop,∀ᵐa ∂(G k).σ v.1,|a.bid-p.beta v|< delta := by
        simpa only [A.targetReal_at_value] using hgraph v.1 hs v.property
      have hlim := conditional_mass_limit_of_graph_and_uniform_raw G v.1 (p.beta v)
        (Icc p.L p.U) hstar hsupport hgr
        (fun b r=> activeMass p.z (exposure p.xi p.lam b) r)
        (fun r=> continuousOn_reference_mass p.xi p.lam p.L p.U p.z p.L_pos r _ hstar)
        hactiveRaw i r
      simpa only [G',hmass,
        nullTypeGame_typeOutcome_inside (G _) S hS (hfullk _) _ _ _ v.1 hs] using hlim
    · have ha (k : ℕ) : action k v.1=activeBroadcast p.L_pos.le (A.targetBid v) :=
        sourceNullAction_active p.value_order p.L_pos.le p.d t hdl hvt A.targetBid (upperBid k) v
      have hlim := raw_mass_limit_of_uniform_raw G (activeBroadcast p.L_pos.le (A.targetBid v))
        (Icc p.L p.U) hstar rfl (fun b r=> activeMass p.z (exposure p.xi p.lam b) r)
        hactiveRaw i r
      have ha' (k : ℕ) : sourceNullAction p.value_order p.L_pos.le p.d t A.targetBid (upperBid k) v.1 =
          activeBroadcast p.L_pos.le (A.targetBid v) := ha k
      have hmass' : activeMass p.z (exposure p.xi p.lam (activeBroadcast p.L_pos.le (A.targetBid v)).bid) r =
          (activeLimitLaw p.z (p.q v) p.z_nonneg p.z_lt_one.le (p.q_mem v).1 (p.q_mem v).2).mass r := hmass
      simpa only [G',nullTypeGame_typeOutcome_outside (G _) S hS (hfullk _) _ _ _ v.1 hs,
        ha',hmass'] using hlim
  · intro v hv i r
    by_cases hs : v∈ S
    · have hsupport (k : ℕ) : ∀ᵐa ∂(G k).σ v,p.R≤ a.bid ∧ a.routeCount=1 :=
        (hbands v hs k).mono (fun a ha=> ha.2.2 hv)
      have hlim := conditional_upper_limit_of_floor G v p.R hsupport upperFloor
        hupperFloor hupperRaw i r
      simpa only [G',nullTypeGame_typeOutcome_inside (G _) S hS (hfullk _) _ _ _ v hs] using hlim
    · have ha (k : ℕ) : action k v=upperAction (upperBid k) (max v t) :=
        sourceNullAction_above_active p.value_order p.L_pos.le p.d t hdl
          A.targetBid (upperBid k) v hv
      have haf (k : ℕ) : p.R≤(action k v).bid := by
        rw [ha]
        exact (hupperBid k (max v t) (le_max_right _ _)).trans (le_max_left _ _)
      have hak (k : ℕ) : (action k v).routeCount=1 := by rw [ha];rfl
      have hsuc : Tendsto (fun k=>((problem (G k) (i k)).outcome (action k v)).success)
          atTop (𝓝 1) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le hupperFloor tendsto_const_nhds
          (fun k=> hupperRaw k (i k) (action k v) (haf k) (hak k))
          (fun k=>((problem (G k) (i k)).outcome (action k v)).success_le_one)
      have hdup : Tendsto (fun k=>((problem (G k) (i k)).outcome (action k v)).duplicates)
          atTop (𝓝 0) := by
        simpa only [singleton_outcome_duplicates_zero (G _) (i _) (action _ v) (hak _)] using
          (tendsto_const_nhds (x:=(0:ℝ)))
      have hlim := count_one_limit_of_success_duplicates (fun k=>
        ((problem (G k) (i k)).outcome (action k v))) hsuc hdup r
      simpa only [G',nullTypeGame_typeOutcome_outside (G _) S hS (hfullk _) _ _ _ v hs] using hlim

end FCAppendix.Affine.Hybrid.Native02
