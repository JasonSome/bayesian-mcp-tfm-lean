import FCAppendix.Affine.Tail04.OrderedSourceUpperCompletion
import FCAppendix.Affine.Tail04.UpperCountLimits

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceUpperSpecified
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation LowBody
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedSourceFiniteStartingPoint
open SourceMovingScalarGuards SourceMomentRectangle OrderedSourceRestrictedNative
open OrderedSourceActiveCountData ConditionalVersions

section Kernel

private theorem probability_eq_dirac_of_ae {T : Type*} [MeasurableSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (a : T)
    (h : ∀ᵐx ∂μ,x=a) : μ=Measure.dirac a := by
  apply Measure.ext
  intro S hS
  by_cases ha : a∈S
  · have he : S=ᵐ[μ]univ := by
      filter_upwards [h] with x hx
      subst x
      exact propext ⟨fun _=>mem_univ a,fun _=>ha⟩
    rw [measure_congr he,measure_univ,Measure.dirac_apply' a hS]
    simp only [Set.indicator_of_mem ha,Pi.one_apply]
  · have he : μ S=0 := measure_eq_zero_iff_ae_notMem.mpr
      (h.mono (fun x hx=> by simpa only [hx] using ha))
    rw [he,Measure.dirac_apply' a hS]
    simp only [Set.indicator_of_notMem ha]

def upperKernel (σ : Kernel ℝ (JointAction 2)) (t : ℝ)
    (b : ℝ→ℝ) (hb : Measurable b) : Kernel ℝ (JointAction 2) :=
  Kernel.piecewise (measurableSet_Ioi : MeasurableSet (Ioi t))
    (Kernel.deterministic (Hybrid.upperAction b) (Hybrid.measurable_upperAction b hb)) σ

instance upperKernel_markov (σ : Kernel ℝ (JointAction 2)) [IsMarkovKernel σ]
    (t : ℝ) (b : ℝ→ℝ) (hb : Measurable b) :
    IsMarkovKernel (upperKernel σ t b hb) := by
  unfold upperKernel
  infer_instance

theorem upperKernel_upper (σ : Kernel ℝ (JointAction 2))
    (t : ℝ) (b : ℝ→ℝ) (hb : Measurable b) (v : ℝ) (hv : t< v) :
    upperKernel σ t b hb v=Measure.dirac (Hybrid.upperAction b v) := by
  simp only [upperKernel,Kernel.piecewise_apply,mem_Ioi,if_pos hv,Kernel.deterministic_apply]

theorem upperKernel_lower (σ : Kernel ℝ (JointAction 2))
    (t : ℝ) (b : ℝ→ℝ) (hb : Measurable b) (v : ℝ) (hv : v≤ t) :
    upperKernel σ t b hb v=σ v := by
  simp only [upperKernel,Kernel.piecewise_apply,mem_Ioi,if_neg (not_lt.mpr hv)]

theorem upperKernel_ae (F : Measure ℝ) [IsProbabilityMeasure F]
    (σ : Kernel ℝ (JointAction 2)) [IsMarkovKernel σ]
    (t : ℝ) (b : ℝ→ℝ) (hb : Measurable b)
    (hpure : ∀ᵐx ∂F⊗ₘσ,t< x.1→ x.2=Hybrid.upperAction b x.1) :
    upperKernel σ t b hb=ᵐ[F]σ := by
  filter_upwards [Measure.ae_ae_of_ae_compProd hpure] with v hv
  by_cases htv : t< v
  · rw [upperKernel_upper σ t b hb v htv]
    exact (probability_eq_dirac_of_ae (σ v) (Hybrid.upperAction b v)
      (hv.mono (fun _ h=> h htv))).symm
  · exact upperKernel_lower σ t b hb v (le_of_not_gt htv)

end Kernel

private theorem withStrategy_proposers {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m n c Seed) (τ : Kernel ℝ (JointAction n)) [IsMarkovKernel τ]
    (hτ : τ=ᵐ[Γ.F]Γ.σ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimal Γ B) :
    PosteriorProposerOptimal (withStrategy Γ τ) (withStrategy_posterior Γ τ hτ B) := hB

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {N : ℕ} (A : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N)
  (hlow : P.d0<1-ξ)
local notation "Γ" => A.native hlow
local notation "Γs" => OrderedSourceActiveSpecified.specified A hlow
local notation "tN" => cutoff N

lemma measurable_upper_graph : MeasurableSet
    {x : ℝ×JointAction 2 | tN< x.1→ x.2=Hybrid.upperAction A.upperBid x.1} := by
  have hs := (measurableSet_lt
    (measurable_const : Measurable (fun _ : ℝ×JointAction 2=> tN))
    (measurable_fst : Measurable (fun x : ℝ×JointAction 2=> x.1))).compl.union
      (measurableSet_eq_fun measurable_snd
        ((Hybrid.measurable_upperAction A.upperBid A.upperBid_measurable).comp measurable_fst))
  simp only [imp_iff_not_or,Set.setOf_or]
  exact hs

theorem original_upper_pure :
    ∀ᵐx ∂(Γ).F⊗ₘ(Γ).σ,tN< x.1→ x.2=Hybrid.upperAction A.upperBid x.1 := by
  apply original_joint_ae A hlow
  · apply (ae_map_iff (measurable_fst.subtype_val.prodMk
      ((measurable_lowBroadcast P.d0).comp measurable_snd)).aemeasurable
      (measurable_upper_graph A)).mpr
    exact Eventually.of_forall fun x hx=> by
      exfalso
      linarith [x.1.2.2,A.point.range.cutoff_gt_M,P.low_partial_gap,
        P.partial_active_gap,P.active_tail_gap,P.w_pos]
  · filter_upwards [bandJoint_support (bidLo_pos A.D 2).le 1 (by norm_num)
      (originalValueLaw P tN A.point.range.cutoff_gt_M 2) (A.sequence.limit 2)] with x hx hupper
    exfalso
    dsimp [valueLo,valueHi] at hx
    linarith [hx.1.2,A.point.range.cutoff_gt_M,P.partial_active_gap,P.active_tail_gap,P.w_pos]
  · filter_upwards [bandJoint_support (bidLo_pos A.D 0).le 2 le_rfl
      (originalValueLaw P tN A.point.range.cutoff_gt_M 0) (A.sequence.limit 0)] with x hx hupper
    exfalso
    dsimp [valueLo,valueHi] at hx
    linarith [hx.1.2,A.point.range.cutoff_gt_M,P.active_tail_gap]
  · filter_upwards [bandJoint_support (bidLo_pos A.D 1).le 2 le_rfl
      (originalValueLaw P tN A.point.range.cutoff_gt_M 1) (A.sequence.limit 1)] with x hx hupper
    exfalso
    dsimp [valueLo,valueHi] at hx
    linarith [hx.1.2]
  · apply (ae_map_iff (measurable_id.prodMk
      (measurable_upperAction A.upperBid A.upperBid_measurable)).aemeasurable
      (measurable_upper_graph A)).mpr
    exact Eventually.of_forall (fun _ _=> rfl)

def strategy : Kernel ℝ (JointAction 2) :=
  upperKernel (Γs).σ tN A.upperBid A.upperBid_measurable

instance strategy_markov : IsMarkovKernel (strategy A hlow) := by
  unfold strategy
  infer_instance

def game : FiniteGame (N+1) 2 A.D.c NativeLocalPolicy.Seed :=
  withStrategy Γs (strategy A hlow)

theorem strategy_ae (hwγ : width≤ γ ξ) : strategy A hlow=ᵐ[(Γs).F](Γs).σ := by
  apply upperKernel_ae (Γs).F (Γs).σ tN A.upperBid A.upperBid_measurable
  rw [OrderedSourceActiveSpecified.specified_joint A hlow hwγ]
  exact original_upper_pure A hlow

theorem upper_at_every_value (v : ℝ) (hv : tN< v) :
    (game A hlow).σ v=Measure.dirac (Hybrid.upperAction A.upperBid v) :=
  upperKernel_upper (Γs).σ tN A.upperBid A.upperBid_measurable v hv

theorem lower_at_every_value (v : ℝ) (hv : v≤ tN) :
    (game A hlow).σ v=(Γs).σ v :=
  upperKernel_lower (Γs).σ tN A.upperBid A.upperBid_measurable v hv

theorem value : (game A hlow).F=valueLaw P := rfl

theorem joint_specified (hwγ : width≤ γ ξ) :
    (game A hlow).F⊗ₘ(game A hlow).σ=(Γs).F⊗ₘ(Γs).σ :=
  withStrategy_joint Γs (strategy A hlow) (strategy_ae A hlow hwγ)

theorem joint (hwγ : width≤ γ ξ) :
    (game A hlow).F⊗ₘ(game A hlow).σ=(Γ).F⊗ₘ(Γ).σ := by
  rw [joint_specified A hlow hwγ,OrderedSourceActiveSpecified.specified_joint A hlow hwγ]

theorem problem_specified (hwγ : width≤ γ ξ) (i : Fin (N+1)) :
    problem (game A hlow) i=problem Γs i :=
  withStrategy_problem Γs (strategy A hlow) (strategy_ae A hlow hwγ) i

theorem problem_native (hwγ : width≤ γ ξ) (i : Fin (N+1)) :
    problem (game A hlow) i=problem Γ i := by
  rw [problem_specified A hlow hwγ i,OrderedSourceActiveSpecified.specified_problem A hlow hwγ i]

theorem userLaw_eq (hwγ : width≤ γ ξ) : userLaw (game A hlow)=userLaw Γ := by
  simp only [userLaw,joint A hlow hwγ]

theorem userProfileLaw_eq (hwγ : width≤ γ ξ) : userProfileLaw (game A hlow)=userProfileLaw Γ := by
  simp only [userProfileLaw,userLaw_eq A hlow hwγ]

theorem sampleLaw_eq (hwγ : width≤ γ ξ) : sampleLaw (game A hlow)=sampleLaw Γ := by
  simp only [sampleLaw,backgroundLaw,userLaw_eq A hlow hwγ]
  rfl

theorem typeOutcome_lower (hwγ : width≤ γ ξ) (i : Fin (N+1)) (v : ℝ) (hv : v≤ tN) :
    typeOutcome (game A hlow) i v=typeOutcome Γs i v := by
  apply FiniteLaw.ext
  intro r
  rw [←FiniteLaw.expect_singleton,←FiniteLaw.expect_singleton,typeOutcome_expect,typeOutcome_expect]
  simp only [problem_specified A hlow hwγ i,lower_at_every_value A hlow v hv]

theorem conditional_lower (hwγ : width≤ γ ξ) (v : ℝ) (hv : v≤ tN) :
    conditionalTypeCountLaw (game A hlow) (Nat.succ_pos N) v=
      conditionalTypeCountLaw Γs (Nat.succ_pos N) v := by
  unfold conditionalTypeCountLaw
  congr 1
  funext i
  exact typeOutcome_lower A hlow hwγ i v hv

def posterior (hwγ : width≤ γ ξ) : PosteriorSystem (game A hlow) :=
  withStrategy_posterior Γs (strategy A hlow) (strategy_ae A hlow hwγ)
    (OrderedSourceSpecifiedNative.posterior A hlow hwγ)

theorem proposer_optimal (hwγ : width≤ γ ξ) :
    PosteriorProposerOptimal (game A hlow) (posterior A hlow hwγ) :=
  withStrategy_proposers Γs (strategy A hlow) (strategy_ae A hlow hwγ)
    (OrderedSourceSpecifiedNative.posterior A hlow hwγ)
    (OrderedSourceSpecifiedNative.proposer_optimal A hlow hwγ)

end FCAppendix.Affine.Tail04.OrderedSourceUpperSpecified

namespace FCAppendix.Affine.Tail04.OrderedSourceEndogenousFloor.Envelope
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.RankEnvelope OriginalValues OriginalPopulation OrderedSourceRestrictedNative
open SourceMovingScalarGuards SourceMomentRectangle OrderedSourceUpperCompletion

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {hlow : P.d0<1-ξ} {N : ℕ}
  (E : Envelope P ξ Up u k width hξ hξh hu hRUp hUp hw hlow N)

abbrev fullySpecified := OrderedSourceUpperSpecified.game E.market hlow

theorem fullySpecified_value : E.fullySpecified.F=valueLaw P := rfl

theorem fullySpecified_joint (hwγ : width≤ γ ξ) :
    E.fullySpecified.F⊗ₘE.fullySpecified.σ=(E.market.native hlow).F⊗ₘ(E.market.native hlow).σ :=
  OrderedSourceUpperSpecified.joint E.market hlow hwγ

theorem fullySpecified_problem (hwγ : width≤ γ ξ) (i : Fin (N+1)) :
    problem E.fullySpecified i=problem (E.market.native hlow) i :=
  OrderedSourceUpperSpecified.problem_native E.market hlow hwγ i

theorem fullySpecified_lower (v : ℝ) (hv : v≤ cutoff N) :
    E.fullySpecified.σ v=E.specified.σ v :=
  OrderedSourceUpperSpecified.lower_at_every_value E.market hlow v hv

theorem fullySpecified_lower_count (hwγ : width≤ γ ξ) (v : ℝ) (hv : v≤ cutoff N) :
    conditionalTypeCountLaw E.fullySpecified (Nat.succ_pos N) v=
      conditionalTypeCountLaw E.specified (Nat.succ_pos N) v :=
  OrderedSourceUpperSpecified.conditional_lower E.market hlow hwγ v hv

theorem fullySpecified_upper (v : ℝ) (hv : cutoff N< v) :
    E.fullySpecified.σ v=Measure.dirac (Hybrid.upperAction E.market.upperBid v) :=
  OrderedSourceUpperSpecified.upper_at_every_value E.market hlow v hv

theorem fullySpecified_bid_atomless (hwγ : width≤ γ ξ) :
    NullSingletonClass ((E.fullySpecified.F⊗ₘE.fullySpecified.σ).map (fun x=> x.2.bid)) := by
  rw [OrderedSourceUpperSpecified.joint_specified E.market hlow hwγ]
  exact E.bid_atomless hwγ

theorem fullySpecified_visible_atomless (hwγ : width≤ γ ξ) : VisibleAtomless E.fullySpecified := by
  intro j y
  rw [OrderedSourceUpperSpecified.userLaw_eq E.market hlow hwγ]
  exact OrderedSourceSpecifiedNative.visible_atomless E.market hlow E.upper_atoms j y

def fullySpecified_posterior (hwγ : width≤ γ ξ) : PosteriorSystem E.fullySpecified :=
  OrderedSourceUpperSpecified.posterior E.market hlow hwγ

theorem fullySpecified_proposer_optimal (hwγ : width≤ γ ξ) :
    PosteriorProposerOptimal E.fullySpecified (E.fullySpecified_posterior hwγ) :=
  OrderedSourceUpperSpecified.proposer_optimal E.market hlow hwγ

theorem fullySpecified_upper_count (hwγ : width≤ γ ξ) (v : ℝ) (hv : cutoff N< v)
    (f : Fin 3→ℝ) :
    (conditionalTypeCountLaw E.fullySpecified (Nat.succ_pos N) v).expect f=
      (1-OriginalMovingUpperEnvelope.q P (cutoff N) (N+1) E.market.D.c v)*f 0+
        OriginalMovingUpperEnvelope.q P (cutoff N) (N+1) E.market.D.c v*f 1 := by
  rw [conditionalTypeCountLaw_expect,E.fullySpecified_upper v hv]
  have hterm (i : Fin (N+1)) :
      (∫act,((problem E.fullySpecified i).outcome act).expect f
        ∂Measure.dirac (Hybrid.upperAction E.market.upperBid v))=
      (1-OriginalMovingUpperEnvelope.q P (cutoff N) (N+1) E.market.D.c v)*f 0+
        OriginalMovingUpperEnvelope.q P (cutoff N) (N+1) E.market.D.c v*f 1 := by
    rw [integral_dirac,E.fullySpecified_problem hwγ i]
    exact native_original_upper_count_expect (E.market.native hlow)
      (P.movingUpperMeasure (cutoff N)) (OrderedSourceUpperCompletion.population_two E) (OrderedSourceUpperCompletion.capacity_pos E) (OrderedSourceUpperCompletion.capacity_lt E)
      (OriginalMovingUpperEnvelope.measure_mass_le_one P (cutoff N)) (cutoff N)
      E.market.H (OrderedSourceUpperCompletion.floor_pos E) (OrderedSourceUpperCompletion.floor_lt_cutoff E) (P.movingUpperMeasure_support (cutoff N))
      (OrderedSourceUpperCompletion.actual_mean E) i v hv.le f
  simp_rw [hterm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hN : ((N+1:ℕ):ℝ)≠0 := by exact_mod_cast (Nat.succ_ne_zero N)
  field_simp

theorem fullySpecified_upper_payoff (hwγ : width≤ γ ξ) (i : Fin (N+1))
    (v : ℝ) (hv : cutoff N≤ v) :
    (problem E.fullySpecified i).payoff v (Hybrid.upperAction E.market.upperBid v)=
      OriginalMovingUpperEnvelope.U P (cutoff N) (N+1) E.market.D.c E.market.H v := by
  rw [E.fullySpecified_problem hwγ i]
  exact OrderedSourceEndogenousFloor.final_upper_attainment P ξ Up u k width hξ hξh hu hRUp hUp hw
    E.point hlow E.ready i v hv

end FCAppendix.Affine.Tail04.OrderedSourceEndogenousFloor.Envelope
