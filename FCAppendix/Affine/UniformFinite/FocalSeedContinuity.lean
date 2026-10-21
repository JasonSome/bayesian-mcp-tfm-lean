import FCAppendix.Affine.UniformFinite.SeedPayoffRejection

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

namespace SourceContinuity
open Uniform05

theorem continuousAt_rowPayoff_rival_cut {M : ℕ} [NeZero M]
    (i : Row) (row : Source.CountRow M) (a : Fin M) (ha : a∈row.lower)
    (x : ℝ×State i M) (hpos : 0< bids i x.2 a)
    (hcut : ∀j∈row.lower,j≠a→ bids i x.2 j≠t i/2)
    (hgeneric : ∀P Q : (Source.lowerTemplate row).Candidate,
      LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids row (bids i x.2))
        P.val.1 P.val.2 =
      LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids row (bids i x.2))
        Q.val.1 Q.val.2 → LowBody.focalCopy P.val a=LowBody.focalCopy Q.val a) :
    ContinuousAt (fun y : ℝ×State i M=> rowPayoff i y.2.1 row y.1 (bids i y.2) a) x := by
  by_cases hown : bids i x.2 a=t i/2
  · by_cases he : Source.residual row 0=Source.residual row 1
    · simp only [rowPayoff,continuation_equal i _ row _ he]
      simp_rw [equalPayoff_eq]
      have hb : ContinuousAt (fun y : ℝ×State i M => bids i y.2 a) x :=
        ((continuous_apply a).comp ((continuous_bids i).comp continuous_snd)).continuousAt
      have hp:=(continuousAt_equalMarginal i row a ha x.2 hpos).comp continuousAt_snd
      exact ((continuousAt_fst.sub hb).mul
        ((continuousAt_const.mul hp).sub (hp.pow 2))).sub
          ((continuousAt_const.mul hb).mul (hp.pow 2))
    · have hn : ∀ᶠy : ℝ×State i M in 𝓝 x,
          bids i y.2 a< SeedRejection.cutoffNeighborhood i :=
        (isOpen_lt ((continuous_apply a).comp ((continuous_bids i).comp continuous_snd))
          continuous_const).mem_nhds
            (by change bids i x.2 a < _; rw [hown];
                exact SeedRejection.cutoffNeighborhood_gt_seed i)
      apply (continuousAt_purePayoff i row a x hgeneric).congr_of_eventuallyEq
      filter_upwards [hn] with y hy
      exact SeedRejection.rowPayoff_eq_pure_near_seed i row a ha he y hy.le
  · apply continuousAt_rowPayoff i row a ha x hpos _ hgeneric
    intro j hj
    by_cases hja : j=a
    · simpa only [hja] using hown
    · exact hcut j hj hja

end SourceContinuity

end FCAppendix.Affine.UniformFinite
