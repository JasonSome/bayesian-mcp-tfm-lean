import FCAppendix.Affine.Tail04.DownstreamCoefficientOne
import FCAppendix.Affine.Hybrid.Tail03.FiniteInterface
import FCAppendix.Affine.Hybrid.Tail03.OriginalLawIdentity

noncomputable section
namespace FCAppendix.Affine.Tail04.DownstreamLowerBridge
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid.Tail03 OriginalValues CoefficientOne DownstreamCoefficientOne

variable {eta1 eta2 : ℝ} (p : Hybrid.Tail03.Parameters eta1 eta2)

abbrev Family := DenseOriginalFamily
  (LowerEarlySource.source p) (LowerEarlySource.guards p)

namespace Family
variable {p} (Y : Family p)

private lemma count_cast {F : ProbabilityMeasure ℝ} {eta : ℝ} {m m' : ℕ}
    (h : m=m') (N : NativeFinite F eta m) (v : ℝ) :
    (show NativeFinite F eta m' from h ▸ N).conditionalCount v=N.conditionalCount v := by
  cases h
  rfl

def nativeAt (j : ℕ) : NativeFinite (commonLaw p) eta1 (Y.population j) where
  Seed:=unitInterval
  seedSpace:=inferInstance
  game:=Y.game j
  posterior:=Y.posterior j
  values:=(Y.original_value j).trans (OriginalLawIdentity.valueLaw_eq_commonLaw p)
  eta_pos:=(LowerEarlySource.pair p).first_pos
  eta_lt_one:=by
    have h:=(LowerEarlySource.source p).scalar.eta_lt_one
    change (LowerEarlySource.pair p).one.scalar.eta<1 at h
    rwa [(LowerEarlySource.pair p).first_coefficient] at h
  bid_rule:=by
    have h:=(Y.schedules j).2.1
    have he : (LowerEarlySource.source p).scalar.eta=eta1 := (LowerEarlySource.pair p).first_coefficient
    simpa only [he] using! h
  base_rule:=(Y.schedules j).2.2.1
  fee:=(Y.schedules j).1
  m_pos:=Y.positive j
  capacity_pos:=(sourceCapacity_bounds _ (Y.large j)).2.2
  capacity_lt:=by
    have hm : (0:ℝ)<Y.population j:=by exact_mod_cast Y.positive j
    have hc:=(sourceCapacity_bounds _ (Y.large j)).2.1
    have hlt : (sourceCapacity (Y.population j):ℝ)<Y.population j:=by linarith
    exact_mod_cast hlt
  users:=(Y.equilibrium j).users
  proposers:=fun i X _=>Eventually.of_forall (Y.proposers j i X)
  proposers_full:=Y.proposers j
  bid_atomless:=Y.bid_atomless j
  visible_atomless:=Y.visible_atomless j

lemma nativeAt_count (j : ℕ) (v : ℝ) :
    (Y.nativeAt j).conditionalCount v=
      conditionalTypeCountLaw (Y.game j) (Y.positive j) v := rfl

lemma population_reindex (m : ℕ) (hm : Y.offset ≤ m) :
    Y.population (m-Y.offset)=m := by rw [Y.exact_index];omega

def native (m : ℕ) (hm : Y.offset ≤ m) : NativeFinite (commonLaw p) eta1 m :=
  Y.population_reindex m hm ▸ Y.nativeAt (m-Y.offset)

lemma native_count (m : ℕ) (hm : Y.offset ≤ m) (v : ℝ) :
      (Y.native m hm).conditionalCount v=(Y.nativeAt (m-Y.offset)).conditionalCount v :=
  count_cast (Y.population_reindex m hm) (Y.nativeAt (m-Y.offset)) v

private lemma load_cast {F : ProbabilityMeasure ℝ} {eta : ℝ} {m m' : ℕ}
    (h : m=m') (N : NativeFinite F eta m) :
    finiteLoad (show NativeFinite F eta m' from h ▸ N).game=finiteLoad N.game := by
  cases h
  rfl

lemma native_load (m : ℕ) (hm : Y.offset ≤ m) :
    finiteLoad (Y.native m hm).game=finiteLoad (Y.nativeAt (m-Y.offset)).game :=
  load_cast (Y.population_reindex m hm) (Y.nativeAt (m-Y.offset))

lemma original_fixed_counts (v : ℝ)
    (hv : v∈Icc (0:ℝ) p.d0 ∪
      Icc (2-p.valueWidth) (2+p.valueWidth) ∪
      Ici (bulkValue p.center-p.valueWidth)) (r : Fin 3) :
    Tendsto (fun j=>((Y.nativeAt j).conditionalCount v).mass r) atTop
      (𝓝 (((LowerEarlySource.source p).fullLimit (LowerEarlySource.guards p) v).mass r)) :=
  Y.fixed_counts v hv r

lemma upper_counts (v : ℝ) (hv : p.tailFloor≤v) (r : Fin 3) :
    Tendsto (fun j=>((Y.nativeAt j).conditionalCount v).mass r) atTop
      (𝓝 ((FiniteLaw.dirac (1:Fin 3)).mass r)) := by
  have hupper : bulkValue p.center-p.valueWidth≤v:=by
    have hw:=p.valueWidth_pos
    have ht:=p.tail_separation
    linarith
  have h:=Y.upper_tests v hupper (fun k=>if k=r then (1:ℝ) else 0)
  simp only [FiniteLaw.expect_singleton] at h
  have he : (if (1:Fin 3)=r then (1:ℝ) else 0)=(FiniteLaw.dirac (1:Fin 3)).mass r := by
    by_cases hr : r=1
    · simp [FiniteLaw.dirac,hr]
    · simp [FiniteLaw.dirac,hr,Ne.symm hr]
  rw [he] at h
  exact h

lemma original_fixed_counts_on (ι : ℕ→ℕ) (hι : Tendsto ι atTop atTop)
    (hlarge : ∀k,Y.offset ≤ ι k) (v : ℝ)
    (hv : v∈Icc (0:ℝ) p.d0 ∪
      Icc (2-p.valueWidth) (2+p.valueWidth) ∪
      Ici (bulkValue p.center-p.valueWidth)) (r : Fin 3) :
    Tendsto (fun k=>((Y.native (ι k) (hlarge k)).conditionalCount v).mass r) atTop
      (𝓝 (((LowerEarlySource.source p).fullLimit (LowerEarlySource.guards p) v).mass r)) := by
  have hsub : Tendsto (fun k=>ι k-Y.offset) atTop atTop:=
    (tendsto_sub_atTop_nat Y.offset).comp hι
  simpa only [Y.native_count,Function.comp_apply] using! (Y.original_fixed_counts v hv r).comp hsub

def limitLaw (_Y : Family p) (v : ℝ) : CountLaw 2 :=
  (LowerEarlySource.source p).fullLimit (LowerEarlySource.guards p) v

lemma measurable_limitLaw (r : Fin 3) : Measurable (fun v=>(Y.limitLaw v).mass r) :=
  (LowerEarlySource.source p).measurable_fullLimit_mass (LowerEarlySource.guards p) r

lemma limit_tail (v : ℝ) (hv : p.tailFloor≤v) :
    Y.limitLaw v=FiniteLaw.dirac (1:Fin 3) := by
  apply (LowerEarlySource.source p).fullLimit_upper (LowerEarlySource.guards p)
  change bulkValue p.center-p.valueWidth≤v
  linarith [p.tail_separation,p.valueWidth_pos]

lemma limit_low (v : ℝ) (hv : v∈Icc (0:ℝ) p.d0) :
    (Y.limitLaw v).success=0 := by
  rw [limitLaw,(LowerEarlySource.source p).fullLimit_low (LowerEarlySource.guards p) v hv]
  simp [CountLaw.success,successIndicator]

lemma limit_partial (v : ℝ) (hv : v∈Icc (2-p.valueWidth) (2+p.valueWidth)) :
    1-oneMixedMass p.center≤(Y.limitLaw v).success := by
  rw [limitLaw,(LowerEarlySource.source p).fullLimit_partial (LowerEarlySource.guards p) v hv]
  exact (LowerEarlySource.source p).partialLimit_success_lower (LowerEarlySource.guards p) v hv

lemma limit_low_ae :
    ∀ᵐv ∂bandMeasure 0 p.d0,(Y.limitLaw v).success=0 := by
  filter_upwards [bandMeasure_supported 0 p.d0] with v hv
  exact Y.limit_low v hv

lemma limit_partial_ae :
    ∀ᵐv ∂bandMeasure (2-p.valueWidth) (2+p.valueWidth),
      1-oneMixedMass p.center≤(Y.limitLaw v).success := by
  filter_upwards [bandMeasure_supported (2-p.valueWidth) (2+p.valueWidth)] with v hv
  exact Y.limit_partial v hv

lemma limit_fixed_upper_ae :
    ∀ᵐv ∂fixedUpperValueMeasure p.lawInput,(Y.limitLaw v).success=1 := by
  filter_upwards [fixedUpper_supported p.lawInput] with v hv
  rw [limitLaw,(LowerEarlySource.source p).fullLimit_upper (LowerEarlySource.guards p) v hv]
  simp [CountLaw.success,successIndicator]

lemma underfill_tendsto :
    Tendsto (fun j=>2*(sourceCapacity (Y.population j):ℝ)/(Y.population j:ℝ)-
      finiteLoad (Y.nativeAt j).game) atTop (𝓝 0) := by
  have hc:=(sourceCapacity_ratio_tendsto.comp Y.cofinal).const_mul 2
  have h:=hc.sub Y.load_tendsto
  convert! h using 1
  · funext j
    change 2*(sourceCapacity (Y.population j):ℝ)/(Y.population j:ℝ)-finiteLoad (Y.game j)=
      2*((sourceCapacity (Y.population j):ℝ)/(Y.population j:ℝ))-finiteLoad (Y.game j)
    ring
  · norm_num

end Family

theorem exists_family : Nonempty (Family p) :=
  DownstreamCoefficientOne.exists_for_early p

theorem exists_of_coefficients (eta1 eta2 : ℝ)
    (h1 : 0<eta1) (h12 : eta1<eta2) (h2 : eta2<1) :
    ∃p : Hybrid.Tail03.Parameters eta1 eta2,Nonempty (Family p) := by
  obtain ⟨p⟩:=exists_parameters eta1 eta2 h1 h12 h2
  exact ⟨p,exists_family p⟩

end FCAppendix.Affine.Tail04.DownstreamLowerBridge
