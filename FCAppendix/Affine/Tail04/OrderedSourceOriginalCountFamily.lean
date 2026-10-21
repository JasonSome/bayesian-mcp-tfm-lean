import FCAppendix.Affine.Tail04.OrderedSourceFixedCountLaws

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceOriginalCountFamily
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open OriginalValues SourceMenuIdentity SourceTailOptimizer SourceMultiplierRectangle
open SourceBulkAnalyticAdapter SourceMomentRectangle SourceMovingScalarGuards
open OrderedSourceRestrictedNative OrderedSourceActiveCountData OrderedSourceActiveSpecified

def limitLaw (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ) (lam : ℝ×ℝ) (v : ℝ) : CountLaw 2 :=
  if v∈Icc (0:ℝ) P.d0 then FiniteLaw.dirac 0
  else if v∈P.partialValues then Counts.singletonLaw (1-P.theta)
    ⟨by linarith [P.theta_small],by linarith [P.theta_pos]⟩
  else if v∈P.bulkValues then ParametricMenuCount.law P ξ lam 1
  else ParametricMenuCount.law P ξ lam (beta P ξ hξ lam v)

attribute [local irreducible] SourceTailOptimizer.beta ParametricMenuCount.law

lemma measurable_limit_mass (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ)
    (lam : ℝ×ℝ) (r : Fin 3) : Measurable (fun v=>(limitLaw P ξ hξ lam v).mass r) := by
  have hb : Measurable (fun v=> beta P ξ hξ lam v) :=
    (measurable_beta P ξ hξ).comp (measurable_const.prodMk measurable_id)
  have ht : Measurable (fun v=>(ParametricMenuCount.law P ξ lam (beta P ξ hξ lam v)).mass r) :=
    (ParametricMenuCount.continuous_mass P ξ (Central.B ξ) r).measurable.comp
      (measurable_const.prodMk hb)
  have hh : Measurable (fun v : ℝ=>
      if v∈Icc (0:ℝ) P.d0 then (FiniteLaw.dirac (0:Fin 3)).mass r
      else if v∈P.partialValues then (Counts.singletonLaw (1-P.theta)
        ⟨by linarith [P.theta_small],by linarith [P.theta_pos]⟩).mass r
      else if v∈P.bulkValues then (ParametricMenuCount.law P ξ lam 1).mass r
      else (ParametricMenuCount.law P ξ lam (beta P ξ hξ lam v)).mass r) :=
    measurable_const.piecewise measurableSet_Icc
      (measurable_const.piecewise measurableSet_Icc
        (measurable_const.piecewise measurableSet_Icc ht))
  convert hh using 1
  funext v
  unfold limitLaw
  split_ifs <;> rfl

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)
  (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)
  (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
  (A : ∀j,Market P ξ Up u k width hξ hξh hu hRUp hUp hw (N j))

local notation "ls" => fun j=> lambda (A j) hlow
local notation "G" => fun j=> specified (A j) hlow

include Up u k width hξh hu hRUp hUp hw hlow hwγ hN A in
theorem every_fixed_original_value {κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (hgeom : DerivativeGeometry P ξ Λ)
    (lam : ℝ×ℝ) (hlam : lam∈Λ) (hls : Tendsto ls atTop (𝓝 lam)) :
    ∀v∈Icc (0:ℝ) P.d0∪P.partialValues∪P.bulkValues∪Ici P.M,∀r : Fin 3,
      Tendsto (fun j=>(conditionalTypeCountLaw (G j) (Nat.succ_pos (N j)) v).mass r)
        atTop (𝓝 ((limitLaw P ξ hξ lam v).mass r)) := by
  intro v hv r
  by_cases hL : v∈Icc (0:ℝ) P.d0
  · simpa only [limitLaw,if_pos hL] using
      OrderedSourceFixedCountLaws.original_fixed_low_limit P ξ Up u k width hξ hξh hu hRUp hUp hw
        hlow hwγ N hN A v hL r
  by_cases hP : v∈P.partialValues
  · simpa only [limitLaw,if_neg hL,if_pos hP] using
      OrderedSourceFixedCountLaws.original_fixed_partial_limit P ξ Up u k width hξ hξh hu hRUp hUp hw
        hlow hwγ N hN A v hP r
  by_cases hB : v∈P.bulkValues
  · simpa only [limitLaw,if_neg hL,if_neg hP,if_pos hB] using
      OrderedSourceFixedCountLaws.original_fixed_bulk_limit P ξ Up u k width hξ hξh hu hRUp hUp hw
        hlow hwγ N hN A hκ hder lam hlam hls v hB r
  have hT : P.M≤ v := by
    rcases hv with ((hv|hv)|hv)|hv
    · exact (hL hv).elim
    · exact (hP hv).elim
    · exact (hB hv).elim
    · exact hv
  simpa only [limitLaw,if_neg hL,if_neg hP,if_neg hB] using
    OrderedSourceFixedCountLaws.original_fixed_tail_limit P ξ Up u k width hξ hξh hu hRUp hUp hw
      hlow hwγ N hN A hgeom lam hlam hls v hT r

include Up u k width hξh hu hRUp hUp hw hlow hwγ hN A in
theorem every_aggregate_count_test {κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (hgeom : DerivativeGeometry P ξ Λ)
    (lam : ℝ×ℝ) (hlam : lam∈Λ) (hls : Tendsto ls atTop (𝓝 lam)) (f : Fin 3→ℝ) :
    Tendsto (fun j=>∫v,(conditionalTypeCountLaw (G j) (Nat.succ_pos (N j)) v).expect f ∂valueLaw P)
      atTop (𝓝 (∫v,(limitLaw P ξ hξ lam v).expect f ∂valueLaw P)) := by
  apply Counts.native_expect_integral_tendsto (fun j=> N j+1) (fun j=>(A j).D.c)
    (fun _=> NativeLocalPolicy.Seed) G (fun j=> Nat.succ_pos (N j)) (valueLaw P)
    (fun _=> rfl) (limitLaw P ξ hξ lam)
  intro r
  filter_upwards [P.fine_support] with v hv
  exact every_fixed_original_value P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ N hN A
    hκ hder hgeom lam hlam hls v hv r

include Up u k width hξh hu hRUp hUp hw hlow hwγ N hN A in
theorem original_aggregates {κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (hgeom : DerivativeGeometry P ξ Λ)
    (lam : ℝ×ℝ) (hlam : lam∈Λ) (hls : Tendsto ls atTop (𝓝 lam)) :
    Tendsto (fun j=> finiteCoverage (G j)) atTop
        (𝓝 (∫v,(limitLaw P ξ hξ lam v).success ∂valueLaw P)) ∧
      Tendsto (fun j=> finiteLoad (G j)) atTop
        (𝓝 (∫v,(limitLaw P ξ hξ lam v).load ∂valueLaw P)) ∧
      Tendsto (fun j=> finiteLoad (G j)-finiteCoverage (G j)) atTop
        (𝓝 (∫v,(limitLaw P ξ hξ lam v).duplicates ∂valueLaw P)) := by
  have hl : ∀r,∀ᵐv ∂valueLaw P,
      Tendsto (fun j=>(conditionalTypeCountLaw (G j) (Nat.succ_pos (N j)) v).mass r)
        atTop (𝓝 ((limitLaw P ξ hξ lam v).mass r)) := by
    intro r
    filter_upwards [P.fine_support] with v hv
    exact every_fixed_original_value P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ N hN A
      hκ hder hgeom lam hlam hls v hv r
  exact ⟨Counts.native_coverage_tendsto (fun j=> N j+1) (fun j=>(A j).D.c)
      (fun _=> NativeLocalPolicy.Seed) G (fun j=> Nat.succ_pos (N j)) (valueLaw P)
      (fun _=> rfl) (limitLaw P ξ hξ lam) hl,
    Counts.native_load_tendsto (fun j=> N j+1) (fun j=>(A j).D.c)
      (fun _=> NativeLocalPolicy.Seed) G (fun j=> Nat.succ_pos (N j)) (valueLaw P)
      (fun _=> rfl) (limitLaw P ξ hξ lam) hl,
    Counts.native_duplicates_tendsto (fun j=> N j+1) (fun j=>(A j).D.c)
      (fun _=> NativeLocalPolicy.Seed) G (fun j=> Nat.succ_pos (N j)) (valueLaw P)
      (fun _=> rfl) (limitLaw P ξ hξ lam) hl⟩

include hwγ hN in
theorem exists_one_count_subsequence {ρ κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hcompact : IsCompact Λ) (hrect : MomentInvariant P ξ ρ Λ)
    (hρ : relativeError P.zeta u (Central.B ξ)≤ ρ)
    (hder : BulkDerivativeBound P ξ κ Λ) (hgeom : DerivativeGeometry P ξ Λ) :
    ∃lam∈Λ,∃φ : ℕ→ℕ,StrictMono φ ∧ Tendsto (fun j=> lambda (A (φ j)) hlow) atTop (𝓝 lam) ∧
      (∀v∈Icc (0:ℝ) P.d0∪P.partialValues∪P.bulkValues∪Ici P.M,∀r : Fin 3,
        Tendsto (fun j=>(conditionalTypeCountLaw (specified (A (φ j)) hlow)
          (Nat.succ_pos (N (φ j))) v).mass r) atTop (𝓝 ((limitLaw P ξ hξ lam v).mass r))) ∧
      (∀f : Fin 3→ℝ,
        Tendsto (fun j=>∫v,(conditionalTypeCountLaw (specified (A (φ j)) hlow)
          (Nat.succ_pos (N (φ j))) v).expect f ∂valueLaw P) atTop
            (𝓝 (∫v,(limitLaw P ξ hξ lam v).expect f ∂valueLaw P))) := by
  obtain ⟨lam,hlam,φ,hφ,hlim⟩:=hcompact.tendsto_subseq
    (fun j=> lambda_mem (A j) hlow hrect hρ)
  refine ⟨lam,hlam,φ,hφ,hlim,?_,?_⟩
  · exact every_fixed_original_value P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ
      (fun j=> N (φ j)) (hN.comp hφ.tendsto_atTop) (fun j=> A (φ j)) hκ hder hgeom lam hlam hlim
  · intro f
    exact every_aggregate_count_test P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ
      (fun j=> N (φ j)) (hN.comp hφ.tendsto_atTop) (fun j=> A (φ j)) hκ hder hgeom lam hlam hlim f

end FCAppendix.Affine.Tail04.OrderedSourceOriginalCountFamily
