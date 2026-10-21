import FCAppendix.Existence.R01PayOnceBayesianPolicy

noncomputable section
namespace FCAppendix.Bayes.PayOnceConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.PayOnceBounded

def chosenPolicy (m n c : ℕ) (hn : 2 ≤ n) : LocalPolicy m c unitInterval :=
  (exists_payOnce_localPolicy m n c hn).choose

theorem measurable_chosenPolicy (m n c : ℕ) (hn : 2 ≤ n) :
    Measurable (fun x : LocalList m × unitInterval => (chosenPolicy m n c hn x.1 x.2).val) :=
  (exists_payOnce_localPolicy m n c hn).choose_spec.choose

theorem chosenPolicy_law (m n c : ℕ) (hn : 2 ≤ n) (L : LocalList m) :
    FiniteLaw.ofMeasure volume (fun s => (chosenPolicy m n c hn L s).val)
      ((measurable_chosenPolicy m n c hn).comp (measurable_const.prodMk measurable_id)) =
      ExactCapacity.symmetricLottery (listMarginal n c L) :=
  (exists_payOnce_localPolicy m n c hn).choose_spec.choose_spec L

def pureGame (m n c : ℕ) (hn : 2 ≤ n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (G : Schedule n) (g : ℝ) (hg : 0 ≤ g) : FiniteGame m n c unitInterval :=
  ExclusiveConstruction.game m n c F E hE b hb (Schedule.once n) G g hg
    (chosenPolicy m n c hn) (measurable_chosenPolicy m n c hn)

variable {m n c : ℕ} (hn : 2 ≤ n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (G : Schedule n) (g : ℝ) (hg : 0 ≤ g)

local notation "Gamma" => pureGame m n c hn F E hE b hb G g hg

theorem pureGame_seedLottery (j : Fin n) (L : LocalList m) :
    seedLottery Gamma j L = ExactCapacity.symmetricLottery (listMarginal n c L) :=
  chosenPolicy_law m n c hn L

def purePosterior : PosteriorSystem Gamma :=
  ExclusiveConstruction.commonListPosterior Gamma
    (ExclusiveConstruction.ae_profile_zero_or_full hE hb (Schedule.once n) G g hg
      (chosenPolicy m n c hn) (measurable_chosenPolicy m n c hn))

theorem purePosterior_common (j : Fin n) (L : LocalList m) (hL : FeasibleObservedList j L) :
    ∀ᵐ d ∂(purePosterior (m:=m) (c:=c) hn F E hE b hb G g hg).posterior j L,
      ∀ l, observe (drawsRealization d) l = L :=
  ExclusiveConstruction.commonListPosterior_common Gamma _ j L hL

theorem pureGame_proposer_optimal :
    PosteriorProposerOptimalAE Gamma (purePosterior (m:=m) (c:=c) hn F E hE b hb G g hg) := by
  cases n with
  | zero => omega
  | succ k =>
    exact bayesian_policy_optimal (pureGame m (k+1) c hn F E hE b hb G g hg) hn rfl
      (purePosterior (m:=m) (c:=c) hn F E hE b hb G g hg)
      (purePosterior_common (m:=m) (c:=c) hn F E hE b hb G g hg)
      (pureGame_seedLottery (m:=m) (c:=c) hn F E hE b hb G g hg)

theorem pureGame_symmetric_at_list (j : Fin n) (L : LocalList m) :
    SymmetricAtList Gamma L (seedLottery Gamma j L) := fun _ => rfl

end FCAppendix.Bayes.PayOnceConstruction
