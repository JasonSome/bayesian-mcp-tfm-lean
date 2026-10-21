import FCAppendix.Affine.Uniform07Finishing.Native.SourcePlan
import FCAppendix.Affine.Uniform07Finishing.Native.SourcePopulation
import FCAppendix.Affine.Uniform07Finishing.Native.VisibleBids
import FCAppendix.Affine.Uniform07.SourceLaw

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine
open StrictNative

lemma source_xi_lt_one (i : Uniform07.Row) : Uniform07.xi i<1 := by
  cases i <;> norm_num [Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]

lemma source_eta_lt_one (i : Uniform07.Row) : Uniform07.eta i<1 := by
  cases i <;> norm_num [Uniform07.eta,Uniform07.etaQ]

lemma source_xi_exact (i : Uniform07.Row) : Uniform07.xi i=(1-Uniform07.eta i)/2 := by
  linarith [Uniform07.xi_identity i]

def sourceSeedCategory (zs : ℝ) : Set (UserDraw 2) := {u | u.1.2.bid≤ zs}

lemma measurableSet_sourceSeedCategory (zs : ℝ) : MeasurableSet (sourceSeedCategory zs) :=
  measurableSet_le measurable_draw_bid measurable_const

def sourceSeedMeasure (i : Uniform07.Row) (m : ℕ)
    (hc : 1≤ Uniform07.capacity m) (R : ℝ)
    (PL : ProbabilityMeasure (ℝ×JointAction 2)) : Measure ℝ :=
  (cond ((sourcePopulation i m hc R PL : Measure (ℝ×JointAction 2)).prod (permLaw 2))
    (sourceSeedCategory (Uniform07.cutoff i/2))).map (fun u : UserDraw 2=>u.1.2.bid)

variable {m : ℕ} [Nonempty (Fin m)]

def sourceWeightedContext (i : Uniform07.Row) (hc : 1≤ Uniform07.capacity m)
    (R Λ : ℝ) (hΛ:0<Λ) (PL : ProbabilityMeasure (ℝ×JointAction 2))
    (α : ClassifiedContext m→ unitInterval) (hα:Measurable α) :
    ContextPolicy m (Uniform07.capacity m) unitInterval :=
  Weighted.sourceContextPolicy (Uniform07.xi i) Λ (Early.demandRatio i)
    (Early.bidCap i) (Uniform07.cutoff i/2) (Uniform07.xi_pos i)
    (source_xi_lt_one i) hΛ (Uniform07.capacity m) (sourceSeedMeasure i m hc R PL) α hα

def sourceNativeGame (i : Uniform07.Row) (hc : 1≤ Uniform07.capacity m)
    (R Λ : ℝ) (hΛ:0<Λ) (PL : ProbabilityMeasure (ℝ×JointAction 2))
    (α : ClassifiedContext m→ unitInterval) (hα:Measurable α) :
    FiniteGame m 2 (Uniform07.capacity m) unitInterval where
  F:=Uniform07.uniformLaw
  hF:=inferInstance
  σ:=sourcePopulationVersion i m hc R PL
  hσ:=inferInstance
  seedLaw:=volume
  hseed:=inferInstance
  policy:=(sourceWeightedContext i hc R Λ hΛ PL α hα).localPolicy R
  policy_measurable:=(sourceWeightedContext i hc R Λ hΛ PL α hα).measurable_selection R
  A:=Schedule.affine 2 (Uniform07.eta i) (Uniform07.eta_pos i).le (source_eta_lt_one i).le
  G:=Schedule.once 2
  g:=0
  g_nonneg:=le_rfl

variable (i : Uniform07.Row) (hm:2≤ m) (hc:1≤ Uniform07.capacity m)
  {R Λ : ℝ} (hR:0< R) (hUR:Early.bidCap i< R) (hRt:R< Uniform07.cutoff i) (hΛ:0<Λ)
  (PL : ProbabilityMeasure (ℝ×JointAction 2))
  (hLvalue:(PL : Measure (ℝ×JointAction 2)).map Prod.fst=(sourceLowerValueLaw i : Measure ℝ))
  (hLroute:∀ᵐx∂(PL : Measure (ℝ×JointAction 2)),x.2.bid≤ Early.bidCap i ∧ x.2.routeCount=2)
  (α : ClassifiedContext m→ unitInterval) (hα:Measurable α)

include hm hR hRt hLvalue hLroute in
theorem sourceNativeGame_joint_law :
    (sourceNativeGame i hc R Λ hΛ PL α hα).F⊗ₘ
      (sourceNativeGame i hc R Λ hΛ PL α hα).σ=
        (sourcePopulation i m hc R PL : Measure (ℝ×JointAction 2)) :=
  source_population_version_disintegration i m hm hc hR hRt PL hLvalue hLroute

include hm hR hRt hLvalue hLroute in
theorem sourceNativeGame_user_law :
    userLaw (sourceNativeGame i hc R Λ hΛ PL α hα)=
      (sourcePopulation i m hc R PL : Measure (ℝ×JointAction 2)).prod (permLaw 2) := by
  unfold userLaw
  rw [sourceNativeGame_joint_law i hm hc hR hRt hΛ PL hLvalue hLroute α hα]

include hm hR hRt hLvalue hLroute in

theorem sourceNativeGame_seed_measure :
    sourceSeedMeasure i m hc R PL=
      (cond (userLaw (sourceNativeGame i hc R Λ hΛ PL α hα))
        (sourceSeedCategory (Uniform07.cutoff i/2))).map
          (fun u : UserDraw 2=>u.1.2.bid) := by
  rw [sourceNativeGame_user_law i hm hc hR hRt hΛ PL hLvalue hLroute α hα]
  rfl

include hm hR hUR hRt hLvalue hLroute in
theorem sourceNativeGame_profile_support :
    ∀ᵐd∂userProfileLaw (sourceNativeGame i hc R Λ hΛ PL α hα),
      d∈StrictNative.classifiedProfiles m R := by
  let Γ:=sourceNativeGame i hc R Λ hΛ PL α hα
  have hjoint : ∀ᵐx∂Γ.F⊗ₘΓ.σ,
      (x.2.bid< R ∧ x.2.routeCount=2) ∨ (R≤ x.2.bid ∧ x.2.routeCount=1) := by
    rw [sourceNativeGame_joint_law i hm hc hR hRt hΛ PL hLvalue hLroute α hα]
    filter_upwards [source_population_support i m hm hc hR hRt PL hLvalue hLroute]
      with x hx
    rcases hx with hl|hh
    · exact Or.inl ⟨hl.2.2.1.trans_lt hUR,hl.2.2.2⟩
    · exact Or.inr ⟨hh.2.2.2.1,hh.2.2.2.2.2⟩
  have hu : ∀ᵐu∂userLaw Γ,
      (u.1.2.bid< R ∧ u.1.2.routeCount=2) ∨
        (R≤ u.1.2.bid ∧ u.1.2.routeCount=1) :=
    (measurePreserving_fst (μ:=Γ.F⊗ₘΓ.σ) (ν:=permLaw 2)).quasiMeasurePreserving.ae hjoint
  exact ae_all_iff.mpr (fun k=>
    (measurePreserving_eval (fun _ : Fin m=>userLaw Γ) k).quasiMeasurePreserving.ae hu)

include hm hR hUR hRt hLvalue hLroute in

def sourceNativePosterior : PosteriorSystem (sourceNativeGame i hc R Λ hΛ PL α hα) :=
  StrictNative.classifiedPosterior (sourceNativeGame i hc R Λ hΛ PL α hα) (R:=R)
    (sourceNativeGame_profile_support i hm hc hR hUR hRt hΛ PL hLvalue hLroute α hα)

include hm hR hUR hRt hLvalue hLroute in

theorem sourceNativeGame_proposer_optimal_feasible :
    let Γ:=sourceNativeGame i hc R Λ hΛ PL α hα
    let B:=sourceNativePosterior i hm hc hR hUR hRt hΛ PL hLvalue hLroute α hα
    ∀j L,FeasibleObservedList j L→∀s,
      Finite.Optimal (Uniform07.capacity m)
        (beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L) (Γ.policy j L s).val := by
  let Γ:=sourceNativeGame i hc R Λ hΛ PL α hα
  have hfull:=sourceNativeGame_profile_support i hm hc hR hUR hRt hΛ PL hLvalue hLroute α hα
  exact Weighted.completed_native_proposer_optimal (Uniform07.xi i)
    (Uniform07.xi_pos i) (source_xi_lt_one i) (Uniform07.capacity m)
    (Weighted.sourcePlan (Uniform07.xi i) Λ (Early.demandRatio i) (Early.bidCap i)
      (Uniform07.cutoff i/2) (Uniform07.capacity m) (sourceSeedMeasure i m hc R PL) α)
    (Weighted.measurable_sourcePlan (Uniform07.xi i) Λ (Early.demandRatio i)
      (Early.bidCap i) (Uniform07.cutoff i/2) (Uniform07.xi_pos i) hΛ
      (Uniform07.capacity m) (sourceSeedMeasure i m hc R PL) α hα)
    (fun X=>1<(Weighted.exceptionalSet (Early.bidCap i) X.1).card)
    (measurableSet_lt measurable_const ((measurable_of_countable Finset.card).comp
      ((Weighted.measurable_exceptionalSet (Early.bidCap i)).comp measurable_fst)))
    Γ hR (Uniform07.eta_pos i).le (source_eta_lt_one i) (source_xi_exact i)
    rfl rfl hfull

include hm hR hRt hLvalue hLroute in
theorem sourceNativeGame_visible_atomless
    (hLatom:∀y : ℝ,(PL : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0) :
    VisibleAtomless (sourceNativeGame i hc R Λ hΛ PL α hα) :=
  source_population_visible_atomless i m hm hc hR hRt PL hLatom
    (sourceNativeGame i hc R Λ hΛ PL α hα)
    (sourceNativeGame_joint_law i hm hc hR hRt hΛ PL hLvalue hLroute α hα)

theorem sourceNativeGame_fixed_upper (v : ℝ) (hv:Uniform07.cutoff i≤ v) :
    (sourceNativeGame i hc R Λ hΛ PL α hα).σ v=
      Measure.dirac (Hybrid.upperAction (sourceUpperBid i m R) v) :=
  sourcePopulationVersion_upper i m hc R PL hv

end FCAppendix.Affine.Uniform07Finishing
