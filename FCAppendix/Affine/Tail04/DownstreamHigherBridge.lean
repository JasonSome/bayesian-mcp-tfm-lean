import FCAppendix.Affine.Tail04.OrderedSourceTerminalCounts
import FCAppendix.Affine.Tail04.DownstreamLowerBridge

noncomputable section
namespace FCAppendix.Affine.Tail04.DownstreamHigherBridge
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Hybrid.Tail03 OriginalValues

variable {eta1 eta2 : ℝ} (p : Hybrid.Tail03.Parameters eta1 eta2)

abbrev S := Hybrid.Tail03.EarlySourceAdapter.analyticParameters p
abbrev Family := OrderedSourceTerminal.TailFiniteAndLimitOutput (S p)

private def castCapacity {m c d : ℕ} {T : Type*} [MeasurableSpace T]
    (h : c=d) (Γ : FiniteGame m 2 c T) : FiniteGame m 2 d T := h ▸ Γ

private def castPosterior {m c d : ℕ} {T : Type*} [MeasurableSpace T]
    (h : c=d) {Γ : FiniteGame m 2 c T} (B : PosteriorSystem Γ) :
    PosteriorSystem (castCapacity h Γ) := by
  cases h
  exact B

private lemma castCapacity_count {m c d : ℕ} {T : Type*} [MeasurableSpace T]
    (h : c=d) (Γ : FiniteGame m 2 c T) (hm : 0 < m) (v : ℝ) :
    conditionalTypeCountLaw (castCapacity h Γ) hm v=conditionalTypeCountLaw Γ hm v := by
  cases h
  rfl

private lemma castCapacity_load {m c d : ℕ} {T : Type*} [MeasurableSpace T]
    (h : c=d) (Γ : FiniteGame m 2 c T) : finiteLoad (castCapacity h Γ)=finiteLoad Γ := by
  cases h
  rfl

private lemma castCapacity_pred {m c d : ℕ} {T : Type*} [MeasurableSpace T]
    (h : c=d) (Γ : FiniteGame m 2 c T)
    (Q : ∀c, FiniteGame m 2 c T → Prop) (hq : Q c Γ) :
    Q d (castCapacity h Γ) := by
  cases h
  exact hq

private lemma castPosterior_optimal {m c d : ℕ} {T : Type*} [MeasurableSpace T]
    (h : c=d) (Γ : FiniteGame m 2 c T) (B : PosteriorSystem Γ)
    (hb : PosteriorProposerOptimal Γ B) :
    PosteriorProposerOptimal (castCapacity h Γ) (castPosterior h B) := by
  cases h
  exact hb

namespace Family
variable {p} (Z : Family p)

abbrev offset : ℕ := Z.family.start+2
abbrev population (j : ℕ) : ℕ := Z.family.population j

lemma exact_index (j : ℕ) : Z.population j=Z.offset+j := by
  dsimp [population,offset,OrderedSourceTerminal.DenseFamily.population]
  omega

lemma positive (j : ℕ) : 0<Z.population j := by rw [Z.exact_index];dsimp [offset];omega

lemma capacity_eq (j : ℕ) : (Z.family.envelope j).market.D.c=sourceCapacity (Z.population j) := by
  exact (Z.family.native j).capacity.trans (by rfl)

def nativeAt (j : ℕ) : NativeFinite (commonLaw p) eta2 (Z.population j) where
  Seed:=NativeLocalPolicy.Seed
  seedSpace:=inferInstance
  game:=castCapacity (Z.capacity_eq j) (Z.family.game j)
  posterior:=castPosterior (Z.capacity_eq j) (Z.family.native j).posterior
  values:=castCapacity_pred (Z.capacity_eq j) (Z.family.game j)
    (fun _ G=>G.F=(commonLaw p : Measure ℝ))
    ((Z.family.native j).original_value.trans (OriginalLawIdentity.valueLaw_eq_commonLaw p))
  eta_pos:=by
    have he : 1-2*(S p).ξ=eta2 := (LowerEarlySource.pair p).second_coefficient
    rw [←he]
    exact (S p).coefficient_pos
  eta_lt_one:=(LowerEarlySource.pair p).second_lt_one
  bid_rule:=by
    apply castCapacity_pred (Z.capacity_eq j) (Z.family.game j)
      (fun _ G=>G.A=Schedule.affine 2 eta2 _ _)
    have he : 1-2*(S p).ξ=eta2 := (LowerEarlySource.pair p).second_coefficient
    simpa only [he] using! (Z.family.native j).tariff
  base_rule:=castCapacity_pred (Z.capacity_eq j) (Z.family.game j)
    (fun _ G=>G.G=Schedule.once 2) (Z.family.native j).base_schedule
  fee:=castCapacity_pred (Z.capacity_eq j) (Z.family.game j)
    (fun _ G=>G.g=0) (Z.family.native j).zero_fee
  m_pos:=Z.positive j
  capacity_pos:=by
    rw [←Z.capacity_eq j]
    exact (Z.family.envelope j).market.point.range.capacity_positive
  capacity_lt:=by
    rw [←Z.capacity_eq j]
    exact (Z.family.envelope j).market.point.range.capacity_less_population
  users:=castCapacity_pred (Z.capacity_eq j) (Z.family.game j)
    (fun _ G=>UsersOptimal G) (Z.family.native j).equilibrium.users
  proposers:=by
    intro i X _
    exact Eventually.of_forall ((castPosterior_optimal (Z.capacity_eq j) (Z.family.game j)
      (Z.family.native j).posterior (Z.family.native j).proposer_optimal) i X)
  proposers_full:=castPosterior_optimal (Z.capacity_eq j) (Z.family.game j)
    (Z.family.native j).posterior (Z.family.native j).proposer_optimal
  bid_atomless:=by
    apply castCapacity_pred (Z.capacity_eq j) (Z.family.game j)
      (fun _ G=>NullSingletonClass (realBidLaw G))
    rw [realBidLaw_eq_action_map]
    exact (Z.family.native j).bid_atoms
  visible_atomless:=castCapacity_pred (Z.capacity_eq j) (Z.family.game j)
    (fun _ G=>VisibleAtomless G) (Z.family.native j).visible_atoms

lemma nativeAt_count (j : ℕ) (v : ℝ) :
    (Z.nativeAt j).conditionalCount v=
      conditionalTypeCountLaw (Z.family.game j) (Nat.succ_pos (Z.family.rivals j)) v := by
  exact castCapacity_count (Z.capacity_eq j) (Z.family.game j) (Z.positive j) v

lemma nativeAt_load (j : ℕ) : finiteLoad (Z.nativeAt j).game=finiteLoad (Z.family.game j) :=
  castCapacity_load (Z.capacity_eq j) (Z.family.game j)

lemma population_reindex (m : ℕ) (hm : Z.offset ≤ m) : Z.population (m-Z.offset)=m := by
  rw [Z.exact_index]
  omega

def native (m : ℕ) (hm : Z.offset ≤ m) : NativeFinite (commonLaw p) eta2 m :=
  Z.population_reindex m hm ▸ Z.nativeAt (m-Z.offset)

private lemma count_cast {F : ProbabilityMeasure ℝ} {eta : ℝ} {m m' : ℕ}
    (h : m=m') (N : NativeFinite F eta m) (v : ℝ) :
    (show NativeFinite F eta m' from h ▸ N).conditionalCount v=N.conditionalCount v := by
  cases h
  rfl

lemma native_count (m : ℕ) (hm : Z.offset ≤ m) (v : ℝ) :
    (Z.native m hm).conditionalCount v=(Z.nativeAt (m-Z.offset)).conditionalCount v :=
  count_cast (Z.population_reindex m hm) (Z.nativeAt (m-Z.offset)) v

private lemma load_cast {F : ProbabilityMeasure ℝ} {eta : ℝ} {m m' : ℕ}
    (h : m=m') (N : NativeFinite F eta m) :
    finiteLoad (show NativeFinite F eta m' from h ▸ N).game=finiteLoad N.game := by
  cases h
  rfl

lemma native_load (m : ℕ) (hm : Z.offset ≤ m) :
    finiteLoad (Z.native m hm).game=finiteLoad (Z.nativeAt (m-Z.offset)).game :=
  load_cast (Z.population_reindex m hm) (Z.nativeAt (m-Z.offset))

abbrev limitLaw (v : ℝ) : CountLaw 2 := OrderedSourceTerminalCounts.law Z v
abbrev multiplier : Fin 2→ℝ := EarlySourceAdapter.finPair Z.multipliers

lemma multiplier_mem : Z.multiplier∈p.rect.box :=
  EarlySourceAdapter.finPair_mem p Z.multipliers_mem

lemma measurable_limitLaw (r : Fin 3) : Measurable (fun v=>(Z.limitLaw v).mass r) :=
  OrderedSourceOriginalCountFamily.measurable_limit_mass (S p).P (S p).ξ (S p).ξ_pos
    Z.multipliers r

lemma tail_bid_eq (v : ℝ) (hv : p.tailFloor≤v) :
    (OrderedSourceTerminalCounts.activeBid Z v:ℝ)=p.boundary.response Z.multiplier v := by
  let b:=OrderedSourceTerminalCounts.activeBid Z v
  have hspec:=OrderedSourceTerminalCounts.tail_response Z v hv
  have hr:=p.boundary.response_mem Z.multiplier Z.multiplier_mem v
    (p.tail_above_boundary.le.trans hv)
  have he (y : ℝ) : SourceMenuIdentity.menuUtility (S p).P (S p).ξ
      Z.multipliers.1 Z.multipliers.2 v y=utility p.center Z.multiplier v y :=
    congrFun (EarlySourceAdapter.utility_eq p Z.multipliers v) y
  have hopt := p.boundary.response_optimal Z.multiplier Z.multiplier_mem v
    (p.tail_above_boundary.le.trans hv) b ⟨hspec.1.1.le,hspec.1.2.le⟩
  by_contra hn
  have hne : (⟨p.boundary.response Z.multiplier v,hr.1.le,hr.2.le⟩ :
      Icc (1:ℝ) (Central.B (S p).ξ))≠b := by
    intro hh
    exact hn (congrArg (fun x=>x.val) hh).symm
  have hh:=hspec.2.2 ⟨p.boundary.response Z.multiplier v,hr.1.le,hr.2.le⟩ hne
  rw [he,he] at hh
  exact (not_lt_of_ge hopt) hh

lemma limit_tail_failure (v : ℝ) (hv : p.tailFloor≤v) :
    (Z.limitLaw v).mass 0=1-served p.center Z.multiplier (p.boundary.response Z.multiplier v) := by
  have hL : v∉Icc (0:ℝ) (S p).P.d0 := by
    intro h
    have hvM : (S p).P.M≤v := hv
    have hg:=(S p).P.low_partial_gap
    have hp:=(S p).P.partial_active_gap
    have ha:=(S p).P.active_tail_gap
    linarith [h.2,hvM,(S p).P.w_pos]
  have hP : v∉(S p).P.partialValues := by
    intro h
    linarith [h.2,show (S p).P.M≤v from hv,(S p).P.partial_active_gap,(S p).P.active_tail_gap,(S p).P.w_pos]
  rw [(OrderedSourceTerminalCounts.statistics Z v).2.2.2.1]
  simp only [OrderedSourceTerminalCounts.sourceSuccess,if_neg hL,if_neg hP]
  rw [←OrderedSourceAnalyticAdapter.success_eq]
  erw [EarlySourceAdapter.success_eq p Z.multipliers, Z.tail_bid_eq v hv]

lemma limit_tail_duplicates (v : ℝ) (hv : p.tailFloor≤v) :
    (Z.limitLaw v).mass 2=duplicates p.center Z.multiplier (p.boundary.response Z.multiplier v) := by
  have hL : v∉Icc (0:ℝ) (S p).P.d0 := by
    intro h
    linarith [h.2,show (S p).P.M≤v from hv,(S p).P.low_partial_gap,(S p).P.partial_active_gap,
      (S p).P.active_tail_gap,(S p).P.w_pos]
  have hP : v∉(S p).P.partialValues := by
    intro h
    linarith [h.2,show (S p).P.M≤v from hv,(S p).P.partial_active_gap,(S p).P.active_tail_gap,(S p).P.w_pos]
  rw [(OrderedSourceTerminalCounts.statistics Z v).2.2.2.2.2]
  simp only [OrderedSourceTerminalCounts.sourceDuplicates,if_neg hL,if_neg hP]
  rw [←OrderedSourceAnalyticAdapter.duplicates_eq]
  erw [EarlySourceAdapter.duplicates_eq p Z.multipliers,Z.tail_bid_eq v hv]

lemma limit_low_ae : ∀ᵐv ∂bandMeasure 0 p.d0,(Z.limitLaw v).success=0 := by
  filter_upwards [bandMeasure_supported 0 p.d0] with v hv
  change (OrderedSourceTerminalCounts.law Z v).success=0
  rw [OrderedSourceTerminalCounts.low_law Z v hv]
  simp [CountLaw.success,successIndicator]

lemma limit_partial_ae : ∀ᵐv ∂bandMeasure (2-p.valueWidth) (2+p.valueWidth),
    (Z.limitLaw v).success=1-p.center.theta := by
  filter_upwards [bandMeasure_supported (2-p.valueWidth) (2+p.valueWidth)] with v hv
  change (OrderedSourceTerminalCounts.law Z v).success=1-p.center.theta
  rw [OrderedSourceTerminalCounts.partial_law Z v hv]
  exact (Counts.singletonLaw_statistics (1-(S p).P.theta)
    ⟨by linarith [(S p).P.theta_small],by linarith [(S p).P.theta_pos]⟩).1

lemma fixed_counts (v : ℝ)
    (hv : v∈Icc (0:ℝ) (S p).P.d0∪(S p).P.partialValues∪(S p).P.bulkValues∪Ici (S p).P.M)
    (r : Fin 3) :
    Tendsto (fun j=>((Z.nativeAt (Z.subsequence j)).conditionalCount v).mass r) atTop
      (𝓝 ((Z.limitLaw v).mass r)) := by
  simpa only [Z.nativeAt_count] using OrderedSourceTerminal.TailFiniteAndLimitOutput.fixed_counts Z v hv r

lemma underfill_tendsto :
    Tendsto (fun j=>2*(sourceCapacity (Z.population j):ℝ)/(Z.population j:ℝ)-
      finiteLoad (Z.nativeAt j).game) atTop (𝓝 0) := by
  have hc:=(sourceCapacity_ratio_tendsto.comp Z.family.population_tendsto).const_mul 2
  have h:=hc.sub Z.load_tendsto
  simpa only [Function.comp_apply,Z.nativeAt_load,mul_div_assoc,show (2:ℝ)*(99/200)-99/100=0 by norm_num] using! h

end Family

theorem exists_family : Nonempty (Family p) :=
  OrderedSourceTerminal.exists_finite_and_limit (S p)

end FCAppendix.Affine.Tail04.DownstreamHigherBridge
