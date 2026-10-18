import FCAppendix.Exclusive.CanonicalBayesianConstruction
import FCAppendix.Finite.IdentitySymmetry
import FCAppendix.Exclusive.CompletionExistingSourceFamily

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Set Filter Exclusive

def chosenCanonicalPolicy (m n c : ℕ) (hn : 2 ≤ n) (hc : 0 < c) :
    LocalPolicy m c unitInterval := (exists_canonical_localPolicy m n c hn hc).choose

theorem measurable_chosenCanonicalPolicy (m n c : ℕ) (hn : 2 ≤ n) (hc : 0 < c) :
    Measurable (fun x : LocalList m × unitInterval =>
      (chosenCanonicalPolicy m n c hn hc x.1 x.2).val) :=
  (exists_canonical_localPolicy m n c hn hc).choose_spec.choose

theorem chosenCanonicalPolicy_law (m n c : ℕ) (hn : 2 ≤ n) (hc : 0 < c)
    (L : LocalList m) :
    FiniteLaw.ofMeasure volume (fun u => (chosenCanonicalPolicy m n c hn hc L u).val)
      ((measurable_chosenCanonicalPolicy m n c hn hc).comp
        (measurable_const.prodMk measurable_id)) =
      canonicalLottery n hn c (listBids L) :=
  (exists_canonical_localPolicy m n c hn hc).choose_spec.choose_spec L

def canonicalGame (m n c : ℕ) (hn : 2 ≤ n) (hc : 0 < c)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) : FiniteGame m n c unitInterval :=
  game m n c F E hE b hb A G g hg (chosenCanonicalPolicy m n c hn hc)
    (measurable_chosenCanonicalPolicy m n c hn hc)

variable {m n c : ℕ} (hn : 2 ≤ n) (hc : 0 < c)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)

local notation "Γ" => canonicalGame m n c hn hc F E hE b hb A G g hg

theorem canonicalGame_seedLottery (j : Fin n) (L : LocalList m) :
    seedLottery Γ j L = canonicalLottery n hn c (listBids L) :=
  chosenCanonicalPolicy_law m n c hn hc L

def canonicalPosterior : PosteriorSystem Γ :=
  commonListPosterior Γ (ae_profile_zero_or_full hE hb A G g hg
    (chosenCanonicalPolicy m n c hn hc) (measurable_chosenCanonicalPolicy m n c hn hc))

theorem canonicalPosterior_common (j : Fin n) (L : LocalList m)
    (hL : FeasibleObservedList j L) :
    ∀ᵐ d ∂(canonicalPosterior hn hc F E hE b hb A G g hg).posterior j L,
      ∀ l, observe (drawsRealization d) l = L :=
  commonListPosterior_common Γ _ j L hL

theorem canonicalGame_symmetric : SymmetricProposersOnPath Γ :=
  symmetric_on_path hE hb A G g hg (chosenCanonicalPolicy m n c hn hc)
    (measurable_chosenCanonicalPolicy m n c hn hc)

theorem canonicalGame_broadcast
    (hpos : ∀ᵐ v ∂F, v ∈ E → 0 < b v) : ExclusiveBroadcastOn Γ E :=
  broadcast_on hE hb A G g hg (chosenCanonicalPolicy m n c hn hc)
    (measurable_chosenCanonicalPolicy m n c hn hc) hpos

theorem canonicalGame_equivariant : PolicyLawEquivariant Γ := by
  intro e j L _hL
  let f := fun s => ((Γ).policy j L s).val
  let f' := fun s => ((Γ).policy j (L ∘ e.symm) s).val
  let T := fun S : Finset (Fin m) => S.map e.toEmbedding
  have hf : Measurable f := measurable_policy_at_list Γ j L
  have hf' : Measurable f' := measurable_policy_at_list Γ j (L ∘ e.symm)
  have hT : Measurable T := measurable_of_countable _
  have he : FiniteLaw.ofMeasure (Γ).seedLaw f' hf' =
      FiniteLaw.ofMeasure (Γ).seedLaw (T ∘ f) (hT.comp hf) := by
    rw [← FiniteLaw.ofMeasure_map (Γ).seedLaw f hf T hT]
    change seedLottery Γ j (L ∘ e.symm) = (seedLottery Γ j L).map T
    rw [canonicalGame_seedLottery, canonicalGame_seedLottery]
    have hbids : listBids (L ∘ e.symm) = listBids L ∘ e.symm := rfl
    rw [hbids]
    exact canonicalLottery_relabel n hn c hc (listBids L) e
  have hx := congrArg FiniteLaw.probabilityMeasure he
  simpa only [FiniteLaw.probabilityMeasure_ofMeasure, f, f', T, Function.comp_def] using hx

end FCAppendix.Bayes.ExclusiveConstruction

namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Set Filter Exclusive

theorem canonicalGame_proposer_optimal
    {m k c : ℕ} (hn : 2 ≤ k+1) (hc : 0 < c)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule (k+1)) (g : ℝ) (hg : 0 ≤ g) :
    ExclusivePosteriorOptimalAE (canonicalGame m (k+1) c hn hc F E hE b hb A G g hg)
      (canonicalPosterior hn hc F E hE b hb A G g hg) :=
  canonical_policy_bayesian_optimal _ hn _
    (canonicalPosterior_common hn hc F E hE b hb A G g hg)
    (canonicalGame_seedLottery hn hc F E hE b hb A G g hg)

theorem canonicalGame_rawBandContinuation
    {m k c : ℕ} (hn : 2 ≤ k+1) (hc : 0 < c)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule (k+1)) (g : ℝ) (hg : 0 ≤ g) (lo hi : ℝ) :
    Completion.Exclusive.RawBandContinuation
      (canonicalGame m (k+1) c hn hc F E hE b hb A G g hg)
      (canonicalPosterior hn hc F E hE b hb A G g hg) lo hi where
  common := fun j L hL _ => canonicalPosterior_common hn hc F E hE b hb A G g hg j L hL
  symmetric := fun j L _ _ => symmetric_at_list hE hb A G g hg
    (chosenCanonicalPolicy m (k+1) c hn hc)
    (measurable_chosenCanonicalPolicy m (k+1) c hn hc) j L
  optimal := fun j L hL _ => canonicalGame_proposer_optimal hn hc F E hE b hb A G g hg j L hL

end FCAppendix.Bayes.ExclusiveConstruction
