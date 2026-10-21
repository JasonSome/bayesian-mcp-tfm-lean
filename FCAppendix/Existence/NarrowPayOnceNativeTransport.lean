import FCAppendix.Existence.NarrowPayOnceGlobalOptimal
import FCAppendix.Existence.R01PayOnceNativePayoff

noncomputable section
namespace FCAppendix.Bayes.PayOnceNarrow
open Set Filter Topology MeasureTheory ProbabilityTheory Game CommonList PayOnce
open Existence.NarrowPayOnce Existence.PayOnceBounded PayOnceConstruction

variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)
  (nu : Measure U.valueBand) [IsProbabilityMeasure nu] (beta : U.strategyBand)

def projectNet (g v : ℝ) : U.valueBand :=
  Set.projIcc (w0-delta) (w0+delta) (by have:=U.delta_nonneg; linarith) (v-g)

theorem continuous_projectNet (g : ℝ) : Continuous ((projectNet U) g) :=
  continuous_projIcc.comp (continuous_id.sub continuous_const)

theorem projectNet_physical (g : ℝ) (v : U.valueBand) : (projectNet U) g ((v:ℝ)+g)=v := by
  rw [projectNet,add_sub_cancel_right]
  exact Set.projIcc_val _ v

def activeBid (g v : ℝ) : Icc (0:ℝ) (U.B+eps) :=
  ⟨beta.val ((projectNet U) g v),
    (U.lower_pos.trans_le (beta.property _).1).le,(beta.property _).2⟩

theorem continuous_activeBid (g : ℝ) : Continuous ((activeBid U) beta g) :=
  Continuous.subtype_mk (beta.val.continuous.comp ((continuous_projectNet U) g)) _

def activeState (g v : ℝ) : FloorAction 0 (U.B+eps) := .inr ((activeBid U) beta g v)

theorem measurable_activeState (g : ℝ) : Measurable ((activeState U) beta g) :=
  measurable_inr.comp ((continuous_activeBid U) beta g).measurable

def stateKernel (g : ℝ) : Kernel ℝ (FloorAction 0 (U.B+eps)) :=
  Kernel.deterministic ((activeState U) beta g) ((measurable_activeState U) beta g)

instance stateKernel_markov (g : ℝ) : IsMarkovKernel ((stateKernel U) beta g) := by
  unfold stateKernel
  infer_instance

def physicalLaw (g : ℝ) : ProbabilityMeasure ℝ :=
  ⟨nu.map (fun v : U.valueBand=>(v:ℝ)+g),
    Measure.isProbabilityMeasure_map (measurable_subtype_coe.add_const g).aemeasurable⟩

def game (g : ℝ) (hg : 0≤g) : FiniteGame (R+1) n c unitInterval :=
  mixedGame (R+1) n c U.n_ge ((physicalLaw U) nu g) ((stateKernel U) beta g) (Schedule.once n) g hg

def posterior (g : ℝ) (hg : 0≤g) : PosteriorSystem ((game U) nu beta g hg) :=
  mixedPosterior U.n_ge ((physicalLaw U) nu g) ((stateKernel U) beta g) (Schedule.once n) g hg

theorem proposer_optimal (g : ℝ) (hg : 0≤g) :
    PosteriorProposerOptimalAE ((game U) nu beta g hg) ((posterior U) nu beta g hg) :=
  mixedGame_proposer_optimal U.n_ge ((physicalLaw U) nu g) ((stateKernel U) beta g) (Schedule.once n) g hg

theorem symmetric (g : ℝ) (hg : 0≤g) : SymmetricProposersOnPath ((game U) nu beta g hg) :=
  mixedGame_symmetric U.n_ge ((physicalLaw U) nu g) ((stateKernel U) beta g) (Schedule.once n) g hg

theorem real_bid_law (g : ℝ) (hg : 0≤g) :
    realBidLaw ((game U) nu beta g hg)=nu.map beta.val := by
  let F : Measure ℝ:=(physicalLaw U) nu g
  let K:=(stateKernel U) beta g
  have hstate:=(measurable_activeState U) beta g
  have hpair:Measurable (Prod.map (id : ℝ→ℝ) (nativeAction n (W:=U.B+eps))) :=
    measurable_id.prodMap (measurable_nativeAction n (U.B+eps))
  have hread:Measurable (fun x : ℝ×JointAction n=>x.2.bid) :=
    (measurable_bid n).comp measurable_snd
  have hbid:Measurable (fun x : ℝ×FloorAction 0 (U.B+eps)=>bid x.2) :=
    continuous_bid.measurable.comp measurable_snd
  calc
    _ = ((F ⊗ₘ K).map (Prod.map id (nativeAction n))).map (fun x=>x.2.bid) := by
      rw [realBidLaw_eq_action_map]
      exact congrArg (fun μ : Measure (ℝ×JointAction n)=>μ.map (fun x=>x.2.bid))
        (mixedGame_value_action_law (m:=R+1) (c:=c) U.n_ge ((physicalLaw U) nu g)
          ((stateKernel U) beta g) (Schedule.once n) g hg)
    _ = (F ⊗ₘ K).map (fun x=>bid x.2) := by
      rw [Measure.map_map hread hpair]
      congr 1
      funext x
      exact nativeAction_bid n x.2
    _ = F.map (fun v=>bid ((activeState U) beta g v)) := by
      rw [show F ⊗ₘ K=F.map (fun v=>(v,(activeState U) beta g v)) from
        Measure.compProd_deterministic hstate]
      simpa only [Function.comp_def,id_eq] using Measure.map_map (μ:=F) hbid
        (measurable_id.prodMk hstate)
    _ = nu.map beta.val := by
      change (nu.map (fun v : U.valueBand=>(v:ℝ)+g)).map
        (fun v=>bid ((activeState U) beta g v))=nu.map beta.val
      calc
        _ = nu.map ((fun v=>bid ((activeState U) beta g v)) ∘ (fun v : U.valueBand=>(v:ℝ)+g)) :=
          Measure.map_map (continuous_bid.measurable.comp hstate) (measurable_subtype_coe.add_const g)
        _ = _ := by
          congr 1
          funext v
          simp only [Function.comp_apply,activeState,bid,activeBid,(projectNet_physical U)]

include U in
theorem positiveMarginal_eq_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι→ℝ) (hb : ∀i,0<b i) (i : ι) :
    positiveMarginal n c b i=kernelMarginal n c b i := by
  let e : ι≃↥(positiveSupport b) :=
    { toFun:=fun j=>⟨j,(mem_positiveSupport b j).2 (hb j)⟩
      invFun:=Subtype.val
      left_inv:=fun _=>rfl
      right_inv:=fun _=>Subtype.ext rfl }
  have he:=congrFun (kernel_equiv e n c U.n_ge (fun j : ↥(positiveSupport b)=>b j.1)
    (fun j=>hb j.1)) i
  dsimp only [positiveMarginal,onSupport]
  rw [dif_pos ((mem_positiveSupport b i).2 (hb i))]
  exact he.symm

theorem interim_success (g : ℝ) (hg : 0≤g) (i : Fin (R+1)) (a : JointAction n) :
    ((problem ((game U) nu beta g hg) i).outcome a).success=
      ∫omega : Fin R→U.valueBand,success a.routeCount
        (positiveMarginal n c (rowBids beta.val a.bid omega) 0) ∂Measure.pi (fun _=>nu) := by
  have hsuccess:=mixedGame_interim_success (N:=R) (c:=c) U.n_ge ((physicalLaw U) nu g) ((stateKernel U) beta g)
    (Schedule.once n) g hg i a
  change ((problem ((game U) nu beta g hg) i).outcome a).success=
    ∫r : Fin R→ℝ,success a.routeCount (positiveMarginal n c (Fin.cons a.bid r) 0)
      ∂Measure.pi (fun _=>realBidLaw ((game U) nu beta g hg)) at hsuccess
  rw [hsuccess,(real_bid_law U) nu beta g hg]
  have hmap:=Measure.pi_map_pi (μ:=fun _ : Fin R=>nu)
    (fun _=>beta.val.continuous.measurable.aemeasurable)
  rw [←hmap]
  have hm:Measurable (fun r : Fin R→ℝ=>success a.routeCount
      (positiveMarginal n c (Fin.cons a.bid r) 0)) :=
    (continuous_success a.routeCount).measurable.comp
      ((measurable_pi_apply 0).comp ((measurable_positiveMarginal n c U.n_ge).comp
        (measurable_pi_iff.mpr (fun j=>by
          refine Fin.cases measurable_const (fun k=>measurable_pi_apply k) j))))
  exact integral_map (measurable_pi_iff.mpr (fun j=>beta.val.continuous.measurable.comp (measurable_pi_apply j))).aemeasurable
    hm.aestronglyMeasurable

theorem payoff_positive_bid (g : ℝ) (hg : 0≤g) (i : Fin (R+1)) (v : U.valueBand)
    (a : JointAction n) (hb : 0<a.bid) :
    (problem ((game U) nu beta g hg) i).payoff ((v:ℝ)+g) a=
      ∫omega : Fin R→U.valueBand,((v:ℝ)-a.bid)*success a.routeCount
        (finiteRowMarginal n c beta.val a.bid omega) ∂Measure.pi (fun _=>nu) := by
  rw [payoff_once ((game U) nu beta g hg) rfl rfl,(interim_success U) nu beta g hg i a]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with omega
  have hpos:∀j,0<rowBids beta.val a.bid omega j := by
    intro j
    refine Fin.cases hb (fun k=>U.lower_pos.trans_le (beta.property (omega k)).1) j
  rw [(positiveMarginal_eq_kernel U) _ hpos 0]
  dsimp [finiteRowUtility,finiteRowMarginal]
  congr 1
  change (v:ℝ)+g-a.bid-g=(v:ℝ)-a.bid
  ring

theorem payoff_broadcast (g : ℝ) (hg : 0≤g) (i : Fin (R+1)) (v : U.valueBand)
    (a : JointAction n) (ha : a.routeCount=n) (hb : 0<a.bid) :
    (problem ((game U) nu beta g hg) i).payoff ((v:ℝ)+g) a=
      finiteExpectedUtility (R:=R) n c nu beta.val v a.bid := by
  rw [payoff_positive_bid U nu beta g hg i v a hb,ha]
  rfl

end FCAppendix.Bayes.PayOnceNarrow
