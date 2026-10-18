import FCAppendix.Exclusive.SourceStationaryGame

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter
open Exclusive.Narrow.Existence

variable {m n c : ℕ} (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps) (H scale : ℝ)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) (L cutoff : ℝ)
    {delta : ℝ} (hs : 0 ≤ scale) (hband : ∀ u, beta u ∈ Icc (-delta) delta)
    (hcut : cutoff ≤ scale*Real.exp (-delta)) (hroom : n-1 ≤ m-n*c)

def bandSourcePosterior : PosteriorSystem
    (bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff) :=
  sourcePosterior hm hn hc _ _ measurableSet_Icc _
    (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable A G g hg cutoff
    hroom (bandSourceGame_floor hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff
      hs hband hcut)

theorem bandSourceGame_proposer_optimal {k : ℕ} (hnk : n=k+1) :
    ExclusivePosteriorOptimalAE
      (bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff)
      (bandSourcePosterior hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff
        hs hband hcut hroom) := by
  subst n
  exact sourceGame_proposer_optimal hm hn hc _ _ measurableSet_Icc _
    (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable A G g hg cutoff
    hroom (bandSourceGame_floor hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff
      hs hband hcut)

theorem bandSourceGame_rawContinuation {k : ℕ} (hnk : n=k+1)
    (lo hi : ℝ) (hlo : cutoff ≤ lo) :
    Completion.Exclusive.RawBandContinuation
      (bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff)
      (bandSourcePosterior hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff
        hs hband hcut hroom) lo hi := by
  subst n
  exact sourceGame_rawBandContinuation hm hn hc _ _ measurableSet_Icc _
    (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable A G g hg cutoff
    hroom (bandSourceGame_floor hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff
      hs hband hcut) lo hi hlo

end FCAppendix.Bayes.ExclusiveConstruction

namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter
open Exclusive.Narrow.Existence

theorem bandSourceGame_relative_band {m n c : ℕ}
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c)
    (h : unitInterval) {eps : ℝ} (heps : 0 ≤ eps) (H scale : ℝ) (hs : 0 < scale)
    (beta : ValueBand eps → ℝ) (hbeta : Continuous beta)
    (nu : Measure (ValueBand eps)) [IsProbabilityMeasure nu]
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) (L cutoff eta : ℝ)
    (hlog : ∀ u, Real.exp (beta u) ∈ Ioo (1-eta) (1+eta)) :
    let Γ := bandSourceGame m n c hm hn hc h heps H scale beta hbeta nu A G g hg L cutoff
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, v ∈ bandHighSet eps H →
      a.bid ∈ Ioo (scale*(1-eta)) (scale*(1+eta)) := by
  dsimp only
  apply Eventually.of_forall
  intro v
  change ∀ᵐ a ∂Kernel.deterministic
    (pureAction n (bandHighSet eps H) (extendedSourceBid eps heps H scale beta))
    (measurable_pureAction n measurableSet_Icc
      (continuous_extendedSourceBid eps heps H scale beta hbeta).measurable) v, _
  simp only [Kernel.deterministic_apply,ae_dirac_eq,Filter.eventually_pure]
  intro hv
  have hp := extendedSourceBid_pos heps H hs beta v
  have hb : (pureAction n (bandHighSet eps H)
      (extendedSourceBid eps heps H scale beta) v).bid =
      extendedSourceBid eps heps H scale beta v := by
    simp [pureAction,hv,max_eq_left hp.le]
  rw [hb]
  exact ⟨mul_lt_mul_of_pos_left (hlog _).1 hs,mul_lt_mul_of_pos_left (hlog _).2 hs⟩

end FCAppendix.Bayes.ExclusiveConstruction
