import FCAppendix.Existence.SingletonAmpleFamily
import FCAppendix.Existence.SingletonNativeAggregates

noncomputable section
namespace FCAppendix.Bayes.SingletonConstruction
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open Existence.Singleton Existence.RankEnvelope

variable {n : ℕ} (hn : 2 ≤ n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ) (hg : 0 ≤ g) [NullSingletonClass (F.restrict (Ioi g))]
    (A G : Schedule n)

local notation "mu" => positiveNetLaw F g

theorem ample_singleton_equilibrium_and_limits (R C : ℕ → ℕ)
    (hR : Tendsto R atTop atTop) (hc : ∀ t, 1 ≤ C t)
    (hcr : ∀ t, C t ≤ R t+1) {rho : ℝ}
    (hDensity : Tendsto (fun t => (C t:ℝ)/((R t:ℝ)+2)) atTop (𝓝 rho))
    (hgap : F.real (Ioi g)/(n:ℝ)<rho) (d H : ℝ) (hd0 : 0<d)
    (hd : ∀ k : ℕ, 2 ≤ k → k ≤ n → d ≤ g*(G.charge k-1))
    (hbound : ∀ᵐ v ∂F, g<v → v-g ≤ H) :
    (∃ T : ℕ, ∀ t, T ≤ t →
      UsersOptimal (ampleGame (R t) n (C t) hn (hc t) F g hg A G) ∧
      IsAEEquilibrium (ampleGame (R t) n (C t) hn (hc t) F g hg A G) ∧
      PosteriorProposerOptimalAE (ampleGame (R t) n (C t) hn (hc t) F g hg A G)
        (gamePosterior (by omega) F (ampleBid F g (R t) (C t) n)
          (ampleBid_measurable F g (hc t) hn) A G g hg) ∧
      VisibleAtomless (ampleGame (R t) n (C t) hn (hc t) F g hg A G) ∧
      (∀ j L, SymmetricAtList (ampleGame (R t) n (C t) hn (hc t) F g hg A G) L
        (seedLottery (ampleGame (R t) n (C t) hn (hc t) F g hg A G) j L)) ∧
      (∀ᵐ w ∂mu, 0<ampleBid F g (R t) (C t) n w)) ∧
    (∀ t (w : ℝ), 0 ≤ w → ampleBid F g (R t) (C t) n w =
      w-(∫ x in 0..w, rank mu (R t+1) (C t) n x)/rank mu (R t+1) (C t) n w) ∧
    Tendsto (fun t => finiteCoverage (ampleGame (R t) n (C t) hn (hc t) F g hg A G))
      atTop (𝓝 (F.real (Ioi g))) ∧
    Tendsto (fun t => finiteLoad (ampleGame (R t) n (C t) hn (hc t) F g hg A G))
      atTop (𝓝 (F.real (Ioi g))) ∧
    (∀ t, finiteLoad (ampleGame (R t) n (C t) hn (hc t) F g hg A G) -
      finiteCoverage (ampleGame (R t) n (C t) hn (hc t) F g hg A G)=0) ∧
    (∀ t v, (conditionalTypeCountLaw
      (ampleGame (R t) n (C t) hn (hc t) F g hg A G) (by omega) v).duplicates=0) ∧
    TendstoUniformlyOn (fun t w => ampleBid F g (R t) (C t) n w)
      (fun _ => 0) atTop (Icc 0 H) := by
  refine ⟨exists_ample_equilibrium_family hn F g hg A G R C hR hc hcr hDensity hgap
    d H hd0 hd hbound, ?_,
    ampleGame_coverage_tendsto hn F g hg A G R C hR hc hcr hDensity hgap,
    ampleGame_load_tendsto hn F g hg A G R C hR hc hcr hDensity hgap,
    ?_, ?_, ample_bids_tendsto_uniformly_zero hn F g R C hR hc hcr H hDensity hgap⟩
  · intro t w hw
    exact ample_bid_formula hn F g (hc t) (hcr t) hw
  · intro t
    exact ampleGame_duplicates_zero hn F g hg A G (R t) (C t) (hc t)
  · intro t v
    exact ampleGame_conditional_duplicates_zero hn (hc t) F g hg A G v

end FCAppendix.Bayes.SingletonConstruction
