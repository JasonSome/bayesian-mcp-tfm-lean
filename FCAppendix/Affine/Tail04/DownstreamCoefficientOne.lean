import FCAppendix.Affine.Tail04.NativeVersionedLimits
import FCAppendix.Affine.Tail04.OriginalFixedCountFamily
import FCAppendix.Affine.Tail04.CoefficientOneSourceLoad
import FCAppendix.Affine.Tail04.SourcePairContract
import FCAppendix.Affine.Hybrid.Tail03.LowerEarlySource

noncomputable section
namespace FCAppendix.Affine.Tail04.DownstreamCoefficientOne
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Hybrid Hybrid.Native02 OriginalValues CoefficientOne

structure DenseOriginalFamily {P : ValueParameters} (s : BoundedSource P)
    (hs : BoundedSourceGuards s) where
  native : NativeImplementation (NativeSource.input s hs)
  shift : ℕ
  exact_equilibrium : ∀ j,
    IsBayesianEquilibrium (NativeVersionedSource.normalizedGame s hs native (shift+j))

namespace DenseOriginalFamily
variable {P : ValueParameters} {s : BoundedSource P} {hs : BoundedSourceGuards s}
    (Y : DenseOriginalFamily s hs)

def offset : ℕ := Y.shift+200+Y.native.toNativeFamilyData.offset

def population (j : ℕ) : ℕ := Y.native.toNativeFamilyData.M (Y.shift+j+200)

def game (j : ℕ) : FiniteGame (Y.population j) 2
    (marketCapacity (Y.population j)) unitInterval :=
  NativeVersionedSource.normalizedGame s hs Y.native (Y.shift+j)

lemma exact_index (j : ℕ) : Y.population j=Y.offset+j := by
  rw [population,Y.native.toNativeFamilyData.M_eq]
  dsimp only [offset]
  omega

lemma large (j : ℕ) : 200≤Y.population j :=
  NativeVersionedSource.large s hs Y.native (Y.shift+j)

lemma positive (j : ℕ) : 0<Y.population j := by
  have h:=Y.large j
  omega

lemma offset_positive : 0<Y.offset := by
  have h:=Y.positive 0
  simpa only [Y.exact_index,Nat.add_zero] using h

lemma cofinal : Tendsto Y.population atTop atTop := by
  have h : Y.population=(fun j : ℕ=>Y.offset+j) := funext Y.exact_index
  rw [h]
  apply tendsto_atTop_mono (fun j=>Nat.le_add_left j Y.offset) tendsto_id

lemma original_value (j : ℕ) : (Y.game j).F=valueLaw P :=
  NativeVersionedSource.normalized_value s hs Y.native (Y.shift+j)

lemma schedules (j : ℕ) : (Y.game j).g=0 ∧
    (Y.game j).A=Schedule.affine 2 s.scalar.eta
      s.scalar.eta_pos.le s.scalar.eta_lt_one.le ∧
    (Y.game j).G=Schedule.once 2 ∧ (Y.game j).seedLaw=volume :=
  ⟨rfl,rfl,rfl,rfl⟩

lemma equilibrium (j : ℕ) : IsBayesianEquilibrium (Y.game j) :=
  Y.exact_equilibrium j

lemma bid_atomless (j : ℕ) : NullSingletonClass (realBidLaw (Y.game j)) :=
  NativeVersionedSource.normalized_bid_atomless s hs Y.native (Y.shift+j)

lemma visible_atomless (j : ℕ) : VisibleAtomless (Y.game j) :=
  NativeVersionedSource.normalized_visible_atomless s hs Y.native (Y.shift+j)

def posterior (j : ℕ) : PosteriorSystem (Y.game j) :=
  FeasibleListNormalization.posterior
    (NativeVersionedSource.originalGame s hs Y.native (Y.shift+j))
    (NativeVersionedSource.originalPosterior s hs Y.native (Y.shift+j+200)
      (NativeVersionedSource.large s hs Y.native (Y.shift+j)))

lemma proposers (j : ℕ) : PosteriorProposerOptimal (Y.game j) (Y.posterior j) :=
  FeasibleListNormalization.proposers
    (NativeVersionedSource.originalGame s hs Y.native (Y.shift+j))
    (NativeVersionedSource.originalPosterior s hs Y.native (Y.shift+j+200)
      (NativeVersionedSource.large s hs Y.native (Y.shift+j)))
    (NativeVersionedSource.original_proposers s hs Y.native (Y.shift+j+200)
      (NativeVersionedSource.large s hs Y.native (Y.shift+j)))

lemma all_labels (j : ℕ) :
    ∀ᵐx ∂(Y.game j).F⊗ₘ(Y.game j).σ,∀i : Fin (Y.population j),
      (problem (Y.game j) i).BestResponse x.1 x.2 := by
  apply ae_all_iff.mpr
  intro i
  exact ae_bestResponse_compProd (Y.game j) (Y.equilibrium j).users i

lemma common_conull_all_actions :
    ∀ᵐv ∂valueLaw P,∀j : ℕ,∀i : Fin (Y.population j),
      ∀ᵐa ∂(Y.game j).σ v,∀raw : JointAction 2,
        (problem (Y.game j) i).payoff v raw≤(problem (Y.game j) i).payoff v a := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro i
  have h:=(Y.equilibrium j).users i
  rwa [Y.original_value j] at h

lemma upper_finite_test (j : ℕ) (v : ℝ) (hv : P.vA-P.w≤v) (f : Fin 3→ℝ) :
    (conditionalTypeCountLaw (Y.game j) (Y.positive j) v).expect f=
      (1-Existence.RankEnvelope.rank P.fixedUpperMeasure (Y.population j-1)
        (marketCapacity (Y.population j)) 2 v)*f 0+
      Existence.RankEnvelope.rank P.fixedUpperMeasure (Y.population j-1)
        (marketCapacity (Y.population j)) 2 v*f 1 := by
  have he := NativeVersionedSource.normalized_count_eq s hs Y.native (Y.shift+j) v
  calc
    _ = (conditionalTypeCountLaw (NativeVersionedSource.originalGame s hs Y.native (Y.shift+j))
        (by have := NativeVersionedSource.large s hs Y.native (Y.shift+j); omega) v).expect f :=
      congrArg (fun K : CountLaw 2 => K.expect f) he
    _ = _ := by
      exact NativeVersionedSource.upper_count_expect s hs Y.native (Y.shift+j+200)
        (NativeVersionedSource.large s hs Y.native (Y.shift+j)) v hv f

private lemma shift_tendsto : Tendsto (fun j : ℕ=>Y.shift+j) atTop atTop :=
  tendsto_atTop_mono (fun j=>Nat.le_add_left j Y.shift) tendsto_id

lemma low_tests (v : ℝ) (hv : v∈Icc (0:ℝ) P.d0) (f : Fin 3→ℝ) :
    Tendsto (fun j=>(conditionalTypeCountLaw (Y.game j) (Y.positive j) v).expect f)
      atTop (𝓝 (f 0)) :=
  (NativeVersionedSource.normalized_low_tests s hs Y.native v hv f).comp Y.shift_tendsto

lemma partial_tests (v : ℝ) (hv : v∈P.partialValues) (f : Fin 3→ℝ) :
    Tendsto (fun j=>(conditionalTypeCountLaw (Y.game j) (Y.positive j) v).expect f)
      atTop (𝓝 ((s.partialLimit hs v hv).expect f)) :=
  (NativeVersionedSource.normalized_partial_tests s hs Y.native v hv f).comp Y.shift_tendsto

lemma upper_tests (v : ℝ) (hv : P.vA-P.w≤v) (f : Fin 3→ℝ) :
    Tendsto (fun j=>(conditionalTypeCountLaw (Y.game j) (Y.positive j) v).expect f)
      atTop (𝓝 (f 1)) :=
  (NativeVersionedSource.normalized_upper_tests s hs Y.native v hv f).comp Y.shift_tendsto

lemma fixed_counts (v : ℝ)
    (hv : v∈Icc (0:ℝ) P.d0∪P.partialValues∪Ici (P.vA-P.w)) (r : Fin 3) :
    Tendsto (fun j=>(conditionalTypeCountLaw (Y.game j) (Y.positive j) v).mass r)
      atTop (𝓝 ((s.fullLimit hs v).mass r)) :=
  original_fixed_count P s hs Y.population Y.positive Y.game
    Y.low_tests Y.partial_tests Y.upper_tests v hv r

lemma count_tests (f : Fin 3→ℝ) :
    Tendsto (fun j=>∫v,(conditionalTypeCountLaw (Y.game j) (Y.positive j) v).expect f
      ∂valueLaw P) atTop (𝓝 (∫v,(s.fullLimit hs v).expect f ∂valueLaw P)) :=
  original_aggregate_count P s hs Y.population Y.positive Y.game Y.original_value
    Y.low_tests Y.partial_tests Y.upper_tests f

lemma coverage_tendsto :
    Tendsto (fun j=>finiteCoverage (Y.game j)) atTop
      (𝓝 (∫v,(s.fullLimit hs v).success ∂valueLaw P)) :=
  (original_aggregates P s hs Y.population Y.positive Y.game Y.original_value
    Y.low_tests Y.partial_tests Y.upper_tests).1

lemma load_tendsto :
    Tendsto (fun j=>finiteLoad (Y.game j)) atTop (𝓝 (99/100:ℝ)) := by
  have h:=(original_aggregates P s hs Y.population Y.positive Y.game Y.original_value
    Y.low_tests Y.partial_tests Y.upper_tests).2.1
  simpa only [s.fullLimit_load_integral hs] using h

lemma duplicates_tendsto :
    Tendsto (fun j=>finiteLoad (Y.game j)-finiteCoverage (Y.game j)) atTop
      (𝓝 (∫v,(s.fullLimit hs v).duplicates ∂valueLaw P)) :=
  (original_aggregates P s hs Y.population Y.positive Y.game Y.original_value
    Y.low_tests Y.partial_tests Y.upper_tests).2.2

lemma every_large_market (m : ℕ) (hm : Y.offset ≤ m) :
    ∃G : FiniteGame m 2 (marketCapacity m) unitInterval,∃B : PosteriorSystem G,
      G.F=valueLaw P ∧ G.g=0 ∧
      G.A=Schedule.affine 2 s.scalar.eta s.scalar.eta_pos.le s.scalar.eta_lt_one.le ∧
      G.G=Schedule.once 2 ∧ G.seedLaw=volume ∧
      IsBayesianEquilibrium G ∧ PosteriorProposerOptimal G B ∧
      NullSingletonClass (realBidLaw G) ∧ VisibleAtomless G := by
  let j:=m-Y.offset
  have he : Y.population j=m := by
    rw [Y.exact_index]
    dsimp only [j]
    omega
  rw [←he]
  exact ⟨Y.game j,Y.posterior j,Y.original_value j,(Y.schedules j).1,
    (Y.schedules j).2.1,(Y.schedules j).2.2.1,(Y.schedules j).2.2.2,
    Y.equilibrium j,Y.proposers j,Y.bid_atomless j,Y.visible_atomless j⟩

include Y in
lemma eventually_native :
    ∀ᶠm : ℕ in atTop,
      ∃G : FiniteGame m 2 (marketCapacity m) unitInterval,∃B : PosteriorSystem G,
        G.F=valueLaw P ∧ G.g=0 ∧
        G.A=Schedule.affine 2 s.scalar.eta s.scalar.eta_pos.le s.scalar.eta_lt_one.le ∧
        G.G=Schedule.once 2 ∧ G.seedLaw=volume ∧
        IsBayesianEquilibrium G ∧ PosteriorProposerOptimal G B ∧
        NullSingletonClass (realBidLaw G) ∧ VisibleAtomless G := by
  filter_upwards [eventually_ge_atTop Y.offset] with m hm
  exact Y.every_large_market m hm

end DenseOriginalFamily

theorem exists_original_family {P : ValueParameters}
    (s : BoundedSource P) (hs : BoundedSourceGuards s) :
    Nonempty (DenseOriginalFamily s hs) := by
  obtain ⟨V⟩:=NativeSource.exists_native_implementation s hs
  obtain ⟨K,hK⟩:=eventually_atTop.mp
    (NativeVersionedSource.eventually_normalized_equilibrium s hs V)
  exact ⟨{ native := V
           shift := K
           exact_equilibrium := fun j=>hK (K+j) (Nat.le_add_right K j) }⟩

theorem exists_for_pair {eta1 eta2 : ℝ}
    (Q : SourcePairContract.Parameters eta1 eta2) :
    Nonempty (DenseOriginalFamily Q.one Q.one_guards) :=
  exists_original_family Q.one Q.one_guards

theorem exists_of_coefficients (eta1 eta2 : ℝ)
    (h1 : 0<eta1) (h12 : eta1<eta2) (h2 : eta2<1) :
    ∃Q : SourcePairContract.Parameters eta1 eta2,
      Nonempty (DenseOriginalFamily Q.one Q.one_guards) := by
  obtain ⟨Q⟩:=Hybrid.Tail03.LowerEarlySource.exists_pair eta1 eta2 h1 h12 h2
  exact ⟨Q,exists_for_pair Q⟩

theorem exists_for_early {eta1 eta2 : ℝ}
    (p : Hybrid.Tail03.Parameters eta1 eta2) :
    Nonempty (DenseOriginalFamily
      (Hybrid.Tail03.LowerEarlySource.source p)
      (Hybrid.Tail03.LowerEarlySource.guards p)) :=
  exists_original_family (Hybrid.Tail03.LowerEarlySource.source p)
    (Hybrid.Tail03.LowerEarlySource.guards p)

end FCAppendix.Affine.Tail04.DownstreamCoefficientOne
