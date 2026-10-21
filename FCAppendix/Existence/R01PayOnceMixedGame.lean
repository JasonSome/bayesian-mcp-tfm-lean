import FCAppendix.Existence.R01PayOnceGame
import FCAppendix.Existence.R01PayOnceZeroType

noncomputable section
namespace FCAppendix.Bayes.PayOnceConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.PayOnceBounded

def nativeAction (n : ℕ) {W : ℝ} : FloorAction 0 W → JointAction n
  | .inl _=>Interim.abstain n
  | .inr b=>⟨b.1,b.2.1,n,le_rfl⟩

theorem measurable_nativeAction (n : ℕ) (W : ℝ) : Measurable (nativeAction n (W:=W)) := by
  have ha : Measurable (fun b : Icc (0:ℝ) W=>
      (⟨b.1,b.2.1,n,le_rfl⟩ : JointAction n)) := by
    apply Measurable.of_comap_le
    rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
    exact (measurable_subtype_coe.prodMk measurable_const).comap_le
  exact (measurable_const : Measurable (fun _ : Unit=>Interim.abstain n)).sumElim ha

@[simp] theorem nativeAction_bid (n : ℕ) {W : ℝ} (a : FloorAction 0 W) :
    (nativeAction n a).bid=bid a := by cases a <;> rfl

theorem nativeAction_routes (n : ℕ) {W : ℝ} (a : FloorAction 0 W) :
    (nativeAction n a).routeCount=0 ∨ (nativeAction n a).routeCount=n := by
  cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

def mixedGame (m n c : ℕ) (hn : 2≤n) (F : Measure ℝ) [IsProbabilityMeasure F]
    {W : ℝ} (κ : Kernel ℝ (FloorAction 0 W)) [IsMarkovKernel κ]
    (G : Schedule n) (g : ℝ) (hg : 0≤g) : FiniteGame m n c unitInterval where
  F:=F
  hF:=inferInstance
  σ:=κ.map (nativeAction n)
  hσ:=by apply Kernel.IsMarkovKernel.map; exact measurable_nativeAction n W
  seedLaw:=volume
  hseed:=inferInstance
  policy:=fun _=>chosenPolicy m n c hn
  policy_measurable:=fun _=>measurable_chosenPolicy m n c hn
  A:=Schedule.once n
  G:=G
  g:=g
  g_nonneg:=hg

variable {m n c : ℕ} (hn : 2≤n) (F : Measure ℝ) [IsProbabilityMeasure F]
    {W : ℝ} (κ : Kernel ℝ (FloorAction 0 W)) [IsMarkovKernel κ]
    (G : Schedule n) (g : ℝ) (hg : 0≤g)
local notation "Gamma"=>mixedGame m n c hn F κ G g hg

theorem mixedGame_seedLottery (j : Fin n) (L : LocalList m) :
    seedLottery Gamma j L=ExactCapacity.symmetricLottery (listMarginal n c L) :=
  chosenPolicy_law m n c hn L

theorem mixedGame_ae_zero_or_full : ∀ᵐ x ∂((Gamma).F ⊗ₘ (Gamma).σ),
    x.2.routeCount=0 ∨ x.2.routeCount=n := by
  apply Measure.ae_compProd_of_ae_ae
  · exact (measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd) measurable_const).union
      (measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd) measurable_const)
  · apply Filter.Eventually.of_forall
    intro v
    change ∀ᵐ a ∂(κ.map (nativeAction n)) v,a.routeCount=0 ∨ a.routeCount=n
    rw [Kernel.map_apply _ (measurable_nativeAction n W)]
    apply (ae_map_iff (measurable_nativeAction n W).aemeasurable ?_).mpr
    · exact Filter.Eventually.of_forall (nativeAction_routes n)
    · exact (measurableSet_eq_fun (measurable_routeCount n) measurable_const).union
        (measurableSet_eq_fun (measurable_routeCount n) measurable_const)

theorem mixedGame_profile_support : ∀ᵐ d ∂userProfileLaw Gamma,
    d∈ExclusiveConstruction.broadcastProfiles m n := by
  have hu : ∀ᵐ u ∂userLaw Gamma,u.1.2.routeCount=0 ∨ u.1.2.routeCount=n :=
    (measurePreserving_fst (μ:=(Gamma).F ⊗ₘ (Gamma).σ) (ν:=permLaw n)).quasiMeasurePreserving.ae
      (mixedGame_ae_zero_or_full hn F κ G g hg)
  exact ae_all_iff.mpr fun i=>
    (measurePreserving_eval (fun _ : Fin m=>userLaw Gamma) i).quasiMeasurePreserving.ae hu

def mixedPosterior : PosteriorSystem Gamma :=
  ExclusiveConstruction.commonListPosterior Gamma (mixedGame_profile_support hn F κ G g hg)

theorem mixedPosterior_common (j : Fin n) (L : LocalList m) (hL : FeasibleObservedList j L) :
    ∀ᵐ d ∂(mixedPosterior (m:=m) (c:=c) hn F κ G g hg).posterior j L,
      ∀l,observe (drawsRealization d) l=L :=
  ExclusiveConstruction.commonListPosterior_common Gamma _ j L hL

theorem mixedGame_proposer_optimal : PosteriorProposerOptimalAE Gamma
    (mixedPosterior (m:=m) (c:=c) hn F κ G g hg) := by
  cases n with
  | zero=>omega
  | succ k=>
    exact bayesian_policy_optimal (mixedGame m (k+1) c hn F κ G g hg) hn rfl
      (mixedPosterior (m:=m) (c:=c) hn F κ G g hg)
      (mixedPosterior_common (m:=m) (c:=c) hn F κ G g hg)
      (mixedGame_seedLottery (m:=m) (c:=c) hn F κ G g hg)

theorem mixedGame_symmetric_at_list (j : Fin n) (L : LocalList m) :
    SymmetricAtList Gamma L (seedLottery Gamma j L) := fun _=>rfl

theorem mixedGame_symmetric : SymmetricProposersOnPath Gamma :=
  fun j=>Filter.Eventually.of_forall (mixedGame_symmetric_at_list hn F κ G g hg j)

end FCAppendix.Bayes.PayOnceConstruction
