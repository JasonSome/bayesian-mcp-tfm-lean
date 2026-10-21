import FCAppendix.Affine.Hybrid.Native02.FullContextPolicy
import FCAppendix.Affine.Hybrid.Native02.ClosedPosterior
import FCAppendix.Affine.Hybrid.Native02.ClosedLowTransport
import FCAppendix.Affine.Hybrid.Native02.OriginalPopulation
import FCAppendix.Finite.ReceiptBoundsAE

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Existence.Distributional

def nativeC5Context (m c : ℕ) (eta : ℝ) (he0 : 0≤ eta) (he1 : eta<1)
    (d L U z : ℝ) (muSeed : Measure ℝ) : ContextPolicy m c unitInterval :=
  FullContext.contextPolicy (by linarith : 0<(1-eta)/2)
    (by linarith : (1-eta)/2<1) d L U z c muSeed

def closedUpperContextPolicy (m c : ℕ) (eta : ℝ) (he0 : 0≤ eta) (he1 : eta<1)
    (d L U R z : ℝ) (muSeed : Measure ℝ) : Fin 2→ LocalPolicy m c unitInterval :=
  ClosedPolicy.localPolicy (nativeC5Context m c eta he0 he1 d L U z muSeed) R

theorem closedUpperContextPolicy_measurable (m c : ℕ) (eta : ℝ)
    (he0 : 0≤ eta) (he1 : eta<1) (d L U R z : ℝ) (muSeed : Measure ℝ) (j : Fin 2) :
    Measurable (fun x : LocalList m×unitInterval=>
      (closedUpperContextPolicy m c eta he0 he1 d L U R z muSeed j x.1 x.2).val) :=
  ClosedPolicy.measurable_selection (nativeC5Context m c eta he0 he1 d L U z muSeed) R j

def nativeC5Game (m c : ℕ) (P : ProbabilityMeasure (ℝ×JointAction 2))
    (eta : ℝ) (he0 : 0≤ eta) (he1 : eta<1)
    (d L U R z : ℝ) (muSeed : Measure ℝ) : FiniteGame m 2 c unitInterval :=
  ClosedPolicy.nativeGame (nativeC5Context m c eta he0 he1 d L U z muSeed)
    (PopulationGame.game m c P eta he0 he1 U) R

theorem nativeC5Game_joint_law (m c : ℕ) (P : ProbabilityMeasure (ℝ×JointAction 2))
    (eta : ℝ) (he0 : 0≤ eta) (he1 : eta<1)
    (d L U R z : ℝ) (muSeed : Measure ℝ) :
    (nativeC5Game m c P eta he0 he1 d L U R z muSeed).F⊗ₘ
      (nativeC5Game m c P eta he0 he1 d L U R z muSeed).σ=
      (P : Measure (ℝ×JointAction 2)) :=
  PopulationGame.joint_law m c P eta he0 he1 U

theorem nativeC5Game_source_fields (m c : ℕ) (P : ProbabilityMeasure (ℝ×JointAction 2))
    (eta : ℝ) (he0 : 0≤ eta) (he1 : eta<1)
    (d L U R z : ℝ) (muSeed : Measure ℝ) :
    let G:=nativeC5Game m c P eta he0 he1 d L U R z muSeed
    G.F=(P : Measure (ℝ×JointAction 2)).fst ∧ G.g=0 ∧
      G.A=Schedule.affine 2 eta he0 he1.le ∧ G.G=Schedule.once 2 ∧ G.seedLaw=volume :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem nativeC5Game_profile_support (m c : ℕ)
    (P : ProbabilityMeasure (ℝ×JointAction 2)) (eta : ℝ) (he0 : 0≤ eta) (he1 : eta<1)
    (d L U R z : ℝ) (muSeed : Measure ℝ)
    (hshape : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),
      (x.2.bid< R ∧ x.2.routeCount=2) ∨ (R≤ x.2.bid ∧ x.2.routeCount=1)) :
    ∀ᵐx ∂userProfileLaw (nativeC5Game m c P eta he0 he1 d L U R z muSeed),
      x∈ closedProfiles m R := by
  let G:=nativeC5Game m c P eta he0 he1 d L U R z muSeed
  have hj : ∀ᵐx ∂G.F⊗ₘG.σ,
      (x.2.bid< R ∧ x.2.routeCount=2) ∨ (R≤ x.2.bid ∧ x.2.routeCount=1) := by
    rw [nativeC5Game_joint_law]
    exact hshape
  have hu := (measurePreserving_fst (μ:=G.F⊗ₘG.σ) (ν:=permLaw 2)).quasiMeasurePreserving.ae hj
  exact ae_all_iff.mpr (fun i=>
    (measurePreserving_eval (fun _ : Fin m=> userLaw G) i).quasiMeasurePreserving.ae hu)

def nativeC5Posterior (m c : ℕ) (P : ProbabilityMeasure (ℝ×JointAction 2))
    (eta : ℝ) (he0 : 0≤ eta) (he1 : eta<1)
    (d L U R z : ℝ) (muSeed : Measure ℝ)
    (hshape : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),
      (x.2.bid< R ∧ x.2.routeCount=2) ∨ (R≤ x.2.bid ∧ x.2.routeCount=1)) :
    PosteriorSystem (nativeC5Game m c P eta he0 he1 d L U R z muSeed) :=
  closedUpperPosterior _ R
    (nativeC5Game_profile_support m c P eta he0 he1 d L U R z muSeed hshape)

theorem nativeC5ProposersOptimal (m c : ℕ) (P : ProbabilityMeasure (ℝ×JointAction 2))
    (eta : ℝ) (he0 : 0≤ eta) (he1 : eta<1)
    (d L U R z : ℝ) (hR : 0< R) (muSeed : Measure ℝ)
    (hshape : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),
      (x.2.bid< R ∧ x.2.routeCount=2) ∨ (R≤ x.2.bid ∧ x.2.routeCount=1)) :
    let G:=nativeC5Game m c P eta he0 he1 d L U R z muSeed
    let B:=nativeC5Posterior m c P eta he0 he1 d L U R z muSeed hshape
    ∀ j X,FeasibleObservedList j X→∀ s,
      Finite.Optimal c (beliefReceipts G.A (posteriorCountBelief G B j X) X)
        (G.policy j X s).val := by
  apply ClosedPolicy.nativeGame_proposer_optimal
    (nativeC5Context m c eta he0 he1 d L U z muSeed)
    (PopulationGame.game m c P eta he0 he1 U) hR he0 he1.le rfl
    (nativeC5Game_profile_support m c P eta he0 he1 d L U R z muSeed hshape)
  intro j X hX s
  have hn := nonnegative_observedClosedContext R j X ((feasibleObservedList_iff_nonnegative j X).mp hX)
  have hh := FullContext.contextPolicy_lower_optimal
    (by linarith : 0<(1-eta)/2) (by linarith : (1-eta)/2<1)
    d L U z c muSeed (nativeC5Game m c P eta he0 he1 d L U R z muSeed) rfl
    j (observedClosedContext R j X) hn s
  simpa only [contextUpper_observedClosed, nativeC5Game, nativeC5Context] using hh

theorem nativeC5RationalAtFeasibleLists (m c : ℕ)
    (P : ProbabilityMeasure (ℝ×JointAction 2))
    (eta : ℝ) (he0 : 0≤ eta) (he1 : eta<1)
    (d L U R z : ℝ) (hR : 0< R) (muSeed : Measure ℝ)
    (hshape : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),
      (x.2.bid< R ∧ x.2.routeCount=2) ∨ (R≤ x.2.bid ∧ x.2.routeCount=1)) :
    ∀ j,ProposerRationalAtFeasibleLists
      (nativeC5Game m c P eta he0 he1 d L U R z muSeed) j := by
  let B:=nativeC5Posterior m c P eta he0 he1 d L U R z muSeed hshape
  apply posterior_rationalAtFeasibleLists _ B
  intro j X hX
  exact ae_of_all _ (nativeC5ProposersOptimal m c P eta he0 he1 d L U R z hR muSeed hshape j X hX)

theorem nativeC5LowContextAgreement (m c : ℕ) (eta : ℝ) (he0 : 0≤ eta) (he1 : eta<1)
    (d L U z : ℝ) (muSeed : Measure ℝ) (hgap : d<(1-(1-eta)/2)*L) :
    LowContextAgreement (nativeC5Context m c eta he0 he1 d L U z muSeed)
      (NativeContinuation.contextPolicy (m:=m) ((1-eta)/2)
        (by linarith : 0<(1-eta)/2) (by linarith : (1-eta)/2<1) c) d :=
  FullContext.low_context_agreement (by linarith : 0<(1-eta)/2)
    (by linarith : (1-eta)/2<1) d L U z c muSeed hgap

def actualLowSeedLaw {N c : ℕ} {d xi : ℝ} {categories : FiniteLaw (Fin 4)}
    {mu : Measure (LowBody.LowValue d)} [IsProbabilityMeasure mu]
    (low : LowBody.ActualAtomlessLowLimit N d xi c categories mu) : Measure ℝ :=
  (lowJoint mu low.joint : Measure (ℝ×JointAction 2)).map (fun x=> x.2.bid)

theorem nativeC5LowUsersOptimal {N c : ℕ} {d L U R eta z : ℝ}
    (hd : 0≤ d) (hdU : d≤ U) (hUR : U< R) (hgap : d<(1-(1-eta)/2)*L)
    (s a h : ℝ) (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowBody.LowValue d)) [IsProbabilityMeasure mu]
    (he0 : 0≤ eta) (he1 : eta<1)
    (low : LowBody.ActualAtomlessLowLimit N d ((1-eta)/2) c
      (LowBody.categoryLaw s a h hs ha hh hsum Gref) mu)
    (PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hactive : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),
      d<((1+eta)/2)*x.2.bid ∧ x.2.bid≤ U ∧ x.2.routeCount=2)
    (hupper : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),R≤ x.2.bid ∧ x.2.routeCount=1)
    (hell : 0<(CommonList.iid (LowBody.categoryLaw s a h hs ha hh hsum Gref) N).prob
      (LowBody.LocalUnderflow c 0))
    (hsmall : (CommonList.iid (LowBody.categoryLaw s a h hs ha hh hsum Gref) N).prob
      (LowBody.BothUnderflow c)≤
      (CommonList.iid (LowBody.categoryLaw s a h hs ha hh hsum Gref) N).prob
        (LowBody.LocalUnderflow c 0)/4) (i : Fin (N+1)) :
    let P:=populationLaw s a h hs ha hh hsum (lowJoint mu low.joint) PA PH
    let G:=nativeC5Game (N+1) c P eta he0 he1 d L U R z (actualLowSeedLaw low)
    ∀ᵐx ∂(lowJoint mu low.joint : Measure (ℝ×JointAction 2)),
      (problem G i).BestResponse x.1 x.2 ∧
      ∀ act : JointAction 2,act.routeCount=1→
        (problem G i).payoff x.1 act<(problem G i).payoff x.1 x.2 := by
  exact closed_population_low_actual_strict_one_route hd hdU hUR s a h hs ha hh hsum
    Gref mu he0 he1 low PA PH hactive hupper hell hsmall
    (nativeC5Context (N+1) c eta he0 he1 d L U z (actualLowSeedLaw low))
    (nativeC5LowContextAgreement (N+1) c eta he0 he1 d L U z (actualLowSeedLaw low) hgap) i

end FCAppendix.Affine.Hybrid.Native02
