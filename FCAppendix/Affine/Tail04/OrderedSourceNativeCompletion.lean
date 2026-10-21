import FCAppendix.Affine.Tail04.OrderedSourceAnalyticAdapter
import FCAppendix.Affine.Tail04.OrderedSourceLowerContracts
import FCAppendix.Affine.Tail04.OrderedSourceUpperSpecified

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceNativeCompletion
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open SourceAnalyticContract SourceMovingScalarGuards SourceTailNoisyFixedPoint
open OrderedSourceActiveCountData OrderedSourceGlobalLower OrderedSourceUpperCompletion

variable (S : SourceAnalyticContract.Parameters) {N : ℕ}
  (E : OrderedSourceAnalyticAdapter.Parameters.Envelope S N)

local notation "A" => E.market
local notation "D" => OrderedSourceRestrictedNative.Market.D A
local notation "Γ" => OrderedSourceRestrictedNative.Market.native A S.low_gap

lemma band_value_le_cutoff (q : Fin 3)
    (x : OrderedSourceFinitePayoffTests.Own D S.P (cutoff N) q) : (x.1:ℝ)≤ cutoff N := by
  have hh:=x.1.2.2
  have ht:=(A).point.range.cutoff_gt_M
  fin_cases q
  · dsimp [valueHi] at hh
    linarith [S.P.active_tail_gap]
  · exact hh
  · dsimp [valueHi] at hh
    linarith [S.P.partial_active_gap,S.P.active_tail_gap,S.P.w_pos]

theorem band_full_bestResponse (bud : SourceUpperBudgets.Budget S.P S.ξ S.k N)
    (raw : RawLower E) (q : Fin 3) :
    ∀ᵐx ∂(band A q : Measure (ℝ×JointAction 2)),∀i : Fin (N+1),
      (problem Γ i).BestResponse x.1 x.2 := by
  let f:=fun x : OrderedSourceFinitePayoffTests.Own D S.P (cutoff N) q=>
    ((x.1:ℝ),bandAction (bidLo_pos D q).le (if q=2 then 1 else 2)
      (by split_ifs <;> omega) x.2)
  have hf : Measurable f:=measurable_fst.subtype_val.prodMk
    ((measurable_bandAction _ _ _).comp measurable_snd)
  have hQ : MeasurableSet {x : ℝ×JointAction 2 |
      ∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2} := by
    simpa only [Set.setOf_forall] using MeasurableSet.iInter
      (fun i=> measurableSet_bestResponse Γ i)
  have hband : (band A q : Measure (ℝ×JointAction 2))=
      (ProbabilityMeasure.toMeasure (Subtype.val ((A).sequence.limit q))).map f := rfl
  rw [hband]
  apply (ae_map_iff hf.aemeasurable hQ).mpr
  filter_upwards [raw.band_lower q] with x hx
  intro i
  exact OrderedSourceUpperCompletion.lower_bestResponse E S.k_pos S.bulk_box_lt
    S.partial_width_small.le S.moment_small.le S.width_small bud i (x.1:ℝ)
    (band_value_le_cutoff S E q x) (f x).2 (hx i)

theorem upper_full_bestResponse (bud : SourceUpperBudgets.Budget S.P S.ξ S.k N)
    (raw : RawLower E) :
    ∀ᵐx ∂(upperJoint (OriginalMovingUpperEnvelope.law S.P (cutoff N))
      (A).upperBid (A).upperBid_measurable : Measure (ℝ×JointAction 2)),
      ∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2 := by
  apply OrderedSourceUpperCompletion.upper_joint_bestResponse E bud raw.boundary_all
  simpa only [div_div] using raw.lower_success

theorem original_all_labels (bud : SourceUpperBudgets.Budget S.P S.ξ S.k N)
    (raw : RawLower E) :
    ∀ᵐx ∂(Γ).F⊗ₘ(Γ).σ,∀i : Fin (N+1),(problem Γ i).BestResponse x.1 x.2 :=
  OrderedSourceSpecifiedNative.all_labels_of_components A S.low_gap
    (band_full_bestResponse S E bud raw 2)
    (band_full_bestResponse S E bud raw 0)
    (band_full_bestResponse S E bud raw 1)
    (upper_full_bestResponse S E bud raw)

theorem fullySpecified_all_labels (bud : SourceUpperBudgets.Budget S.P S.ξ S.k N)
    (raw : RawLower E) :
    ∀ᵐx ∂E.fullySpecified.F⊗ₘE.fullySpecified.σ,∀i : Fin (N+1),
      (problem E.fullySpecified i).BestResponse x.1 x.2 := by
  rw [E.fullySpecified_joint S.width_small]
  filter_upwards [original_all_labels S E bud raw] with x hx
  intro i
  rw [E.fullySpecified_problem S.width_small i]
  exact hx i

theorem fullySpecified_equilibrium (bud : SourceUpperBudgets.Budget S.P S.ξ S.k N)
    (raw : RawLower E) : IsBayesianEquilibrium E.fullySpecified := by
  refine ⟨?_,⟨E.fullySpecified_posterior S.width_small,
    E.fullySpecified_proposer_optimal S.width_small⟩⟩
  intro i
  exact Measure.ae_ae_of_ae_compProd
    ((fullySpecified_all_labels S E bud raw).mono (fun _ hx=> hx i))

structure NativeAt (S : SourceAnalyticContract.Parameters) (m : ℕ) where
  c : ℕ
  game : FiniteGame m 2 c NativeLocalPolicy.Seed
  capacity : c=Markets.capacity m
  original_value : game.F=valueLaw S.P
  tariff : game.A=Schedule.affine 2 (1-2*S.ξ) S.coefficient_pos.le S.coefficient_lt_one.le
  base_schedule : game.G=Schedule.once 2
  zero_fee : game.g=0
  posterior : PosteriorSystem game
  proposer_optimal : PosteriorProposerOptimal game posterior
  all_users : ∀ᵐx ∂game.F⊗ₘgame.σ,∀i : Fin m,(problem game i).BestResponse x.1 x.2
  bid_atoms : NullSingletonClass ((game.F⊗ₘgame.σ).map (fun x=> x.2.bid))
  visible_atoms : VisibleAtomless game

namespace NativeAt

def castPopulation {S : SourceAnalyticContract.Parameters} {m n : ℕ}
    (h : m=n) (Z : NativeAt S m) : NativeAt S n := h ▸ Z

theorem equilibrium {S : SourceAnalyticContract.Parameters} {m : ℕ}
    (Z : NativeAt S m) : IsBayesianEquilibrium Z.game := by
  refine ⟨?_,⟨Z.posterior,Z.proposer_optimal⟩⟩
  intro i
  exact Measure.ae_ae_of_ae_compProd (Z.all_users.mono (fun _ hx=> hx i))

end NativeAt

def ofEnvelope (bud : SourceUpperBudgets.Budget S.P S.ξ S.k N)
    (raw : RawLower E) : NativeAt S (N+1) where
  c:=(D).c
  game:=E.fullySpecified
  capacity:=by
    change MenuError.iidCapacity (99/200) N=Markets.capacity (N+1)
    simp only [MenuError.iidCapacity,Markets.capacity,Nat.cast_add,Nat.cast_one]
  original_value:=rfl
  tariff:=rfl
  base_schedule:=rfl
  zero_fee:=rfl
  posterior:=E.fullySpecified_posterior S.width_small
  proposer_optimal:=E.fullySpecified_proposer_optimal S.width_small
  all_users:=fullySpecified_all_labels S E bud raw
  bid_atoms:=E.fullySpecified_bid_atomless S.width_small
  visible_atoms:=E.fullySpecified_visible_atomless S.width_small

end FCAppendix.Affine.Tail04.OrderedSourceNativeCompletion
