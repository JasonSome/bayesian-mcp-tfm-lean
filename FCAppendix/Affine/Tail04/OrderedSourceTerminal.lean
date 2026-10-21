import FCAppendix.Affine.Tail04.OrderedSourceNativeCompletion
import FCAppendix.Affine.Tail04.OrderedSourceGlobalLower
import FCAppendix.Affine.Tail04.OrderedSourceFinalLoad

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceTerminal
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open OriginalValues SourceAnalyticContract OrderedSourceNativeCompletion
open SourceMovingScalarGuards OrderedSourceActiveCountData OrderedSourceOriginalCountFamily
open OrderedSourceOriginalMoments OrderedSourceMomentClearing

variable (S : SourceAnalyticContract.Parameters)

theorem eventually_lower :
    ∀ᶠN in atTop,∀E : OrderedSourceAnalyticAdapter.Parameters.Envelope S N,
      OrderedSourceGlobalLower.RawLower E :=
  OrderedSourceGlobalLower.eventually_all_lower S.P S.ξ S.Up S.u S.k S.width
    S.ξ_pos S.ξ_half S.u_pos.le S.partial_floor_lt S.partial_cap_lt_one
    S.width_pos S.low_gap S.u_pos S.κ_pos S.Amin_pos S.cap_lower S.cap_upper
    S.width_small S.bulk_box_lt S.partial_width_small.le S.moment_small.le
    (OrderedSourceAnalyticAdapter.Parameters.momentInvariant S)
    (OrderedSourceAnalyticAdapter.Parameters.bulkDerivativeBound S)
    (OrderedSourceAnalyticAdapter.Parameters.leadingBounds S) S.moment_tolerance.le
    S.theta_small S.value_width_small S.bulk_center

structure DenseFamily (S : SourceAnalyticContract.Parameters) where
  start : ℕ
  envelope : ∀j,OrderedSourceAnalyticAdapter.Parameters.Envelope S (start+j+1)
  upperBudget : ∀j,SourceUpperBudgets.Budget S.P S.ξ S.k (start+j+1)
  lower : ∀j,OrderedSourceGlobalLower.RawLower (envelope j)

namespace DenseFamily

variable {S} (Y : DenseFamily S)

abbrev rivals (j : ℕ) : ℕ := Y.start+j+1
abbrev population (j : ℕ) : ℕ := Y.start+j+2
abbrev game (j : ℕ) := (Y.envelope j).fullySpecified

def native (j : ℕ) : NativeAt S (Y.population j) :=
  OrderedSourceNativeCompletion.ofEnvelope S (Y.envelope j) (Y.upperBudget j) (Y.lower j)

theorem native_game (j : ℕ) : (Y.native j).game=Y.game j := rfl

theorem rivals_tendsto : Tendsto Y.rivals atTop atTop := by
  change Tendsto (fun j => Y.start+j+1) atTop atTop
  simpa only [rivals,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
    tendsto_add_atTop_nat (Y.start+1)

theorem population_tendsto : Tendsto Y.population atTop atTop := by
  change Tendsto (fun j => Y.start+j+2) atTop atTop
  simpa only [population,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
    tendsto_add_atTop_nat (Y.start+2)

theorem every_large_market (m : ℕ) (hm : Y.start+2≤ m) :
    Nonempty (NativeAt S m) := by
  refine ⟨NativeAt.castPopulation ?_ (Y.native (m-(Y.start+2)))⟩
  dsimp [population]
  omega

include Y in
theorem eventually_native : ∀ᶠm in atTop,Nonempty (NativeAt S m) := by
  filter_upwards [eventually_ge_atTop (Y.start+2)] with m hm
  exact Y.every_large_market m hm

theorem all_labels (j : ℕ) :
    ∀ᵐx ∂(Y.game j).F⊗ₘ(Y.game j).σ,∀i : Fin (Y.population j),
      (problem (Y.game j) i).BestResponse x.1 x.2 := (Y.native j).all_users

theorem equilibrium (j : ℕ) : IsBayesianEquilibrium (Y.game j) :=
  (Y.native j).equilibrium

theorem original_value (j : ℕ) : (Y.game j).F=valueLaw S.P := rfl

theorem value_atomless (j : ℕ) : NullSingletonClass (Y.game j).F := by
  rw [Y.original_value j]
  infer_instance

theorem value_unbounded (j : ℕ) (r : ℝ) : 0<(Y.game j).F (Ioi r) := by
  rw [Y.original_value j]
  exact valueLaw_unbounded S.P r

theorem upper_action (j : ℕ) (v : ℝ) (hv : cutoff (Y.rivals j)< v) :
    (Y.game j).σ v=Measure.dirac (Hybrid.upperAction (Y.envelope j).market.upperBid v) :=
  (Y.envelope j).fullySpecified_upper v hv

theorem upper_count (j : ℕ) (v : ℝ) (hv : cutoff (Y.rivals j)< v) (f : Fin 3→ℝ) :
    (conditionalTypeCountLaw (Y.game j) (Nat.succ_pos (Y.rivals j)) v).expect f=
      (1-OriginalMovingUpperEnvelope.q S.P (cutoff (Y.rivals j)) (Y.population j)
        (Y.envelope j).market.D.c v)*f 0+
      OriginalMovingUpperEnvelope.q S.P (cutoff (Y.rivals j)) (Y.population j)
        (Y.envelope j).market.D.c v*f 1 :=
  (Y.envelope j).fullySpecified_upper_count S.width_small v hv f

theorem expected_unused (j : ℕ) (p : Fin 2) :
    (∫ω,unusedCapacity (Y.game j) p ω ∂backgroundLaw (Y.game j))≤
      ((Y.envelope j).market.D.c:ℝ)*Real.exp (-(Y.population j:ℝ)/50) :=
  OrderedSourceFinalLoad.fullySpecified_unused S (Y.envelope j) p

theorem load_tendsto :
    Tendsto (fun j=> finiteLoad (Y.game j)) atTop (𝓝 (99/100:ℝ)) :=
  OrderedSourceFinalLoad.load_tendsto S Y.rivals Y.rivals_tendsto Y.envelope

end DenseFamily

theorem exists_dense_family : Nonempty (DenseFamily S) := by
  have hU := (tendsto_add_atTop_nat 1).eventually
    (SourceUpperBudgets.eventually_budget S.P S.ξ_pos S.ξ_half S.k_pos)
  have hL := (tendsto_add_atTop_nat 1).eventually (eventually_lower S)
  have hE := OrderedSourceAnalyticAdapter.Parameters.eventually_envelopes S
  have h : ∀ᶠN in atTop,∃E : OrderedSourceAnalyticAdapter.Parameters.Envelope S (N+1),
      SourceUpperBudgets.Budget S.P S.ξ S.k (N+1) ∧ OrderedSourceGlobalLower.RawLower E := by
    filter_upwards [hE,hU,hL] with N hEN hUN hLN
    obtain ⟨E⟩:=hEN
    exact ⟨E,hUN,hLN E⟩
  obtain ⟨K,hK⟩:=eventually_atTop.mp h
  let E (j : ℕ) : OrderedSourceAnalyticAdapter.Parameters.Envelope S (K+j+1) :=
    Classical.choose (hK (K+j) (Nat.le_add_right K j))
  refine ⟨{start:=K,envelope:=E,upperBudget:=?_,lower:=?_}⟩
  · intro j
    exact (Classical.choose_spec (hK (K+j) (Nat.le_add_right K j))).1
  · intro j
    exact (Classical.choose_spec (hK (K+j) (Nat.le_add_right K j))).2

structure TailFiniteAndLimitOutput (S : SourceAnalyticContract.Parameters) where
  family : DenseFamily S
  multipliers : ℝ×ℝ
  multipliers_mem : multipliers∈S.Λ
  subsequence : ℕ→ℕ
  subsequence_strict : StrictMono subsequence
  multiplier_limit : Tendsto
    (fun j=> lambda (family.envelope (subsequence j)).market S.low_gap) atTop (𝓝 multipliers)
  fixed_counts :
    ∀v∈Icc (0:ℝ) S.P.d0∪S.P.partialValues∪S.P.bulkValues∪Ici S.P.M,∀r : Fin 3,
      Tendsto (fun j=>(conditionalTypeCountLaw (family.game (subsequence j))
        (Nat.succ_pos (family.rivals (subsequence j))) v).mass r) atTop
        (𝓝 ((limitLaw S.P S.ξ S.ξ_pos multipliers v).mass r))
  count_tests : ∀f : Fin 3→ℝ,
    Tendsto (fun j=>∫v,(conditionalTypeCountLaw (family.game (subsequence j))
      (Nat.succ_pos (family.rivals (subsequence j))) v).expect f ∂valueLaw S.P) atTop
      (𝓝 (∫v,(limitLaw S.P S.ξ S.ξ_pos multipliers v).expect f ∂valueLaw S.P))
  moments : ∀rec reg : Bool,
    Tendsto (fun j=> actualMoment (family.envelope (subsequence j)).market S.low_gap rec reg)
      atTop (𝓝 (limitMoment S.P S.ξ S.ξ_pos multipliers rec reg))
  clearing : ∀reg : Bool,(if reg then multipliers.2 else multipliers.1)=
    SourceMenuError.meanNumerator S.P S.ξ
      (limitMoment S.P S.ξ S.ξ_pos multipliers false reg) reg/
        limitMoment S.P S.ξ S.ξ_pos multipliers true reg
  limiting_load : (∫v,(limitLaw S.P S.ξ S.ξ_pos multipliers v).load ∂valueLaw S.P)=99/100

namespace TailFiniteAndLimitOutput

variable {S} (Z : TailFiniteAndLimitOutput S)

abbrev game (j : ℕ) := Z.family.game j
abbrev native (j : ℕ) := Z.family.native j

include Z in
theorem eventually_native : ∀ᶠm in atTop,Nonempty (NativeAt S m) :=
  Z.family.eventually_native

theorem equilibrium (j : ℕ) : IsBayesianEquilibrium (Z.game j) := Z.family.equilibrium j

theorem all_labels (j : ℕ) :
    ∀ᵐx ∂(Z.game j).F⊗ₘ(Z.game j).σ,∀i : Fin (Z.family.population j),
      (problem (Z.game j) i).BestResponse x.1 x.2 := Z.family.all_labels j

theorem moment_positive (rec reg : Bool) :
    0< limitMoment S.P S.ξ S.ξ_pos Z.multipliers rec reg :=
  limitMoment_positive S.P S.ξ S.ξ_pos Z.multipliers rec reg

theorem source_moment (rec reg : Bool) :
    limitMoment S.P S.ξ S.ξ_pos Z.multipliers rec reg=
      S.P.bulkWeight*SourceMenuPopulation.baseFlag S.P reg+
        ∫ v in Ici S.P.M,
          (if rec then SourceMenuIdentity.mixedProbability S.P S.ξ reg
            (SourceTailOptimizer.beta S.P S.ξ S.ξ_pos Z.multipliers v)/
              (SourceTailOptimizer.beta S.P S.ξ S.ξ_pos Z.multipliers v:ℝ)
           else SourceMenuIdentity.mixedProbability S.P S.ξ reg
             (SourceTailOptimizer.beta S.P S.ξ S.ξ_pos Z.multipliers v)) ∂valueLaw S.P :=
  limitMoment_eq_source S.P S.ξ S.ξ_pos Z.multipliers rec reg

theorem aggregate_limits :
    Tendsto (fun j=> finiteCoverage (Z.game (Z.subsequence j))) atTop
      (𝓝 (∫v,(limitLaw S.P S.ξ S.ξ_pos Z.multipliers v).success ∂valueLaw S.P)) ∧
    Tendsto (fun j=> finiteLoad (Z.game (Z.subsequence j))) atTop
      (𝓝 (∫v,(limitLaw S.P S.ξ S.ξ_pos Z.multipliers v).load ∂valueLaw S.P)) ∧
    Tendsto (fun j=> finiteLoad (Z.game (Z.subsequence j))-
      finiteCoverage (Z.game (Z.subsequence j))) atTop
      (𝓝 (∫v,(limitLaw S.P S.ξ S.ξ_pos Z.multipliers v).duplicates ∂valueLaw S.P)) :=
  OrderedSourceFinalCountFamily.aggregates S.P S.ξ S.Up S.u S.k S.width
    S.ξ_pos S.ξ_half S.u_pos.le S.partial_floor_lt S.partial_cap_lt_one S.width_pos
    S.low_gap S.width_small (fun j=> Z.family.rivals (Z.subsequence j))
    (Z.family.rivals_tendsto.comp Z.subsequence_strict.tendsto_atTop)
    (fun j=> Z.family.envelope (Z.subsequence j)) S.κ_pos
    (OrderedSourceAnalyticAdapter.Parameters.bulkDerivativeBound S)
    (OrderedSourceAnalyticAdapter.Parameters.derivativeGeometry S)
    Z.multipliers Z.multipliers_mem Z.multiplier_limit

theorem load_tendsto :
    Tendsto (fun j=> finiteLoad (Z.game j)) atTop (𝓝 (99/100:ℝ)) := Z.family.load_tendsto

end TailFiniteAndLimitOutput

theorem exists_finite_and_limit : Nonempty (TailFiniteAndLimitOutput S) := by
  obtain ⟨Y⟩:=exists_dense_family S
  obtain ⟨lam,hlam,φ,hφ,hls,hcounts,htests,hmom,hclear⟩:=
    OrderedSourceFinalCountFamily.exists_common_limit S.P S.ξ S.Up S.u S.k S.width
      S.ξ_pos S.ξ_half S.u_pos.le S.partial_floor_lt S.partial_cap_lt_one S.width_pos
      S.low_gap S.width_small Y.rivals Y.rivals_tendsto Y.envelope S.κ_pos
      S.compact_rectangle (OrderedSourceAnalyticAdapter.Parameters.momentInvariant S)
      S.moment_tolerance.le (OrderedSourceAnalyticAdapter.Parameters.bulkDerivativeBound S)
      (OrderedSourceAnalyticAdapter.Parameters.derivativeGeometry S)
  refine ⟨{
    family := Y
    multipliers := lam
    multipliers_mem := hlam
    subsequence := φ
    subsequence_strict := hφ
    multiplier_limit := hls
    fixed_counts := hcounts
    count_tests := htests
    moments := hmom
    clearing := hclear
    limiting_load := ?_ }⟩
  exact OrderedSourceFinalLoad.limit_load S (fun j=> Y.rivals (φ j))
    (Y.rivals_tendsto.comp hφ.tendsto_atTop) (fun j=> Y.envelope (φ j)) lam hlam hls

theorem eventually_native : ∀ᶠm in atTop,Nonempty (NativeAt S m) := by
  obtain ⟨Z⟩:=exists_finite_and_limit S
  exact Z.eventually_native

def construct : TailFiniteAndLimitOutput S := Classical.choice (exists_finite_and_limit S)

end FCAppendix.Affine.Tail04.OrderedSourceTerminal
