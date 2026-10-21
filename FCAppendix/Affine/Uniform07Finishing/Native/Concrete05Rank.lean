import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Family
import FCAppendix.Affine.Uniform07Finishing.Crossover.NativeBroadcastLaw

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open Crossover Crossover.Physical
open FCAppendix.Affine

theorem market_lowerBidMeasure_eq {row : Uniform07.Row} {m : ℕ}
    (D : UniformMarketData row m) (E : UniformFinite.ExactRestrictedLaw row m)
    (hD : D.lower=lowerJoint E) :
    lowerBidMeasure D.native (Uniform07.cutoff row)=
      ENNReal.ofReal (Uniform07.cutoff row) • (E.realBid : Measure ℝ) := by
  unfold lowerBidMeasure
  rw [D.native_lower_restriction,hD,Measure.map_smul,lowerJoint_bid_measure E]

theorem market_rank_eq {row : Uniform07.Row} {m : ℕ}
    (D : UniformMarketData row m) (E : UniformFinite.ExactRestrictedLaw row m)
    (hD : D.lower=lowerJoint E) (b : ℝ) :
    rank D.native (Uniform07.cutoff row) b=
      Uniform06.PureRankCounts.sourceRank (Uniform07.cutoff row)
        ((realJoint E).map Prod.snd) b := by
  rw [rank_eq_lowerBidMeasure,market_lowerBidMeasure_eq D E hD,realJoint_bid E]
  simp only [Uniform06.PureRankCounts.sourceRank,Measure.real,Measure.smul_apply,
    smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Uniform07.cutoff_pos row).le]

theorem LowerFamily.native_rank_eq (F : LowerFamily) (row : Uniform07.Row) (k : ℕ) (b : ℝ) :
    rank (F.marketData row k).native (Uniform07.cutoff row) b=
      Uniform06.PureRankCounts.sourceRank (Uniform07.cutoff row)
        ((realJoint (F.construction row k).finite.restricted).map Prod.snd) b :=
  market_rank_eq (F.marketData row k) (F.construction row k).finite.restricted rfl b

theorem received_native_rank_eq (F : Crossover.Received05.ReadyLowerFamily)
    (row : Uniform07.Row) (k : ℕ) (b : ℝ) :
    rank (F.market row k).native (Uniform07.cutoff row) b=
      Uniform06.PureRankCounts.sourceRank (Uniform07.cutoff row)
        ((Crossover.Received05.G row (F.start+k) (F.law row k) : Measure (ℝ×ℝ)).map Prod.snd) b :=
  F.toLowerFamily.native_rank_eq row k b

end FCAppendix.Affine.Uniform07Finishing.Concrete05
