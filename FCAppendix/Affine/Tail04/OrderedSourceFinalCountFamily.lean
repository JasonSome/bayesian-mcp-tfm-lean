import FCAppendix.Affine.Tail04.OrderedSourceMomentClearing
import FCAppendix.Affine.Tail04.OrderedSourceUpperSpecified

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceFinalCountFamily
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open OriginalValues SourceMenuIdentity SourceMenuPopulation SourceMenuError
open SourceMomentRectangle SourceMovingScalarGuards SourceMultiplierRectangle
open OrderedSourceRestrictedNative OrderedSourceEndogenousFloor OrderedSourceActiveCountData
open OrderedSourceOriginalCountFamily OrderedSourceMomentClearing OrderedSourceOriginalMoments
open SourceTailOptimizer SourceBulkAnalyticAdapter

section OneMarket

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {hlow : P.d0<1-ξ} {N : ℕ}
  (E : Envelope P ξ Up u k width hξ hξh hu hRUp hUp hw hlow N)

local notation "R" => OrderedNativeZeroNoiseSource.regions E.market.D P
  (E.market.forget.low_gap hlow) E.market.H E.market.upper_gap

theorem fullySpecified_actualMoment (hwγ : width≤ γ ξ) (rec reg : Bool) :
    (∫x,(if (R).coarseTag x=1 then bidTest P ξ rec reg x.1.2.bid else 0)
      ∂userLaw E.fullySpecified)=actualMoment E.market hlow rec reg := by
  unfold userLaw
  rw [E.fullySpecified_joint hwγ]
  rfl

end OneMarket

section Family

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)
  (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)
  (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
  (E : ∀j,Envelope P ξ Up u k width hξ hξh hu hRUp hUp hw hlow (N j))

include hwγ hN in
theorem every_fixed_value {κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (hgeom : DerivativeGeometry P ξ Λ)
    (lam : ℝ×ℝ) (hlam : lam∈Λ) (hls : Tendsto (fun j=> lambda (E j).market hlow) atTop (𝓝 lam)) :
    ∀v∈Icc (0:ℝ) P.d0∪P.partialValues∪P.bulkValues∪Ici P.M,∀r : Fin 3,
      Tendsto (fun j=>(conditionalTypeCountLaw ((fun j=>(E j).fullySpecified) j) (Nat.succ_pos (N j)) v).mass r)
        atTop (𝓝 ((limitLaw P ξ hξ lam v).mass r)) := by
  intro v hv r
  have hh:=OrderedSourceOriginalCountFamily.every_fixed_original_value P ξ Up u k width
    hξ hξh hu hRUp hUp hw hlow hwγ N hN (fun j=>(E j).market)
    hκ hder hgeom lam hlam hls v hv r
  apply hh.congr'
  filter_upwards [(cutoff_tendsto.comp hN).eventually_ge_atTop v] with j hj
  rw [(E j).fullySpecified_lower_count hwγ v hj]

include hwγ hN in
theorem every_count_test {κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (hgeom : DerivativeGeometry P ξ Λ)
    (lam : ℝ×ℝ) (hlam : lam∈Λ) (hls : Tendsto (fun j=> lambda (E j).market hlow) atTop (𝓝 lam)) (f : Fin 3→ℝ) :
    Tendsto (fun j=>∫v,(conditionalTypeCountLaw ((fun j=>(E j).fullySpecified) j) (Nat.succ_pos (N j)) v).expect f ∂valueLaw P)
      atTop (𝓝 (∫v,(limitLaw P ξ hξ lam v).expect f ∂valueLaw P)) := by
  apply Counts.native_expect_integral_tendsto (fun j=> N j+1) (fun j=>(E j).market.D.c)
    (fun _=> NativeLocalPolicy.Seed) (fun j=>(E j).fullySpecified) (fun j=> Nat.succ_pos (N j)) (valueLaw P)
    (fun _=> rfl) (limitLaw P ξ hξ lam)
  intro r
  filter_upwards [P.fine_support] with v hv
  exact every_fixed_value P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ N hN E
    hκ hder hgeom lam hlam hls v hv r

include hwγ hN in
theorem aggregates {κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (hgeom : DerivativeGeometry P ξ Λ)
    (lam : ℝ×ℝ) (hlam : lam∈Λ) (hls : Tendsto (fun j=> lambda (E j).market hlow) atTop (𝓝 lam)) :
    Tendsto (fun j=> finiteCoverage ((fun j=>(E j).fullySpecified) j)) atTop
        (𝓝 (∫v,(limitLaw P ξ hξ lam v).success ∂valueLaw P)) ∧
      Tendsto (fun j=> finiteLoad ((fun j=>(E j).fullySpecified) j)) atTop
        (𝓝 (∫v,(limitLaw P ξ hξ lam v).load ∂valueLaw P)) ∧
      Tendsto (fun j=> finiteLoad ((fun j=>(E j).fullySpecified) j)-finiteCoverage ((fun j=>(E j).fullySpecified) j)) atTop
        (𝓝 (∫v,(limitLaw P ξ hξ lam v).duplicates ∂valueLaw P)) := by
  have hl : ∀r,∀ᵐv ∂valueLaw P,
      Tendsto (fun j=>(conditionalTypeCountLaw ((fun j=>(E j).fullySpecified) j) (Nat.succ_pos (N j)) v).mass r)
        atTop (𝓝 ((limitLaw P ξ hξ lam v).mass r)) := by
    intro r
    filter_upwards [P.fine_support] with v hv
    exact every_fixed_value P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ N hN E
      hκ hder hgeom lam hlam hls v hv r
  exact ⟨Counts.native_coverage_tendsto (fun j=> N j+1) (fun j=>(E j).market.D.c)
      (fun _=> NativeLocalPolicy.Seed) (fun j=>(E j).fullySpecified) (fun j=> Nat.succ_pos (N j)) (valueLaw P)
      (fun _=> rfl) (limitLaw P ξ hξ lam) hl,
    Counts.native_load_tendsto (fun j=> N j+1) (fun j=>(E j).market.D.c)
      (fun _=> NativeLocalPolicy.Seed) (fun j=>(E j).fullySpecified) (fun j=> Nat.succ_pos (N j)) (valueLaw P)
      (fun _=> rfl) (limitLaw P ξ hξ lam) hl,
    Counts.native_duplicates_tendsto (fun j=> N j+1) (fun j=>(E j).market.D.c)
      (fun _=> NativeLocalPolicy.Seed) (fun j=>(E j).fullySpecified) (fun j=> Nat.succ_pos (N j)) (valueLaw P)
      (fun _=> rfl) (limitLaw P ξ hξ lam) hl⟩

include hwγ hN in
theorem exists_common_limit {ρ κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hcompact : IsCompact Λ) (hrect : MomentInvariant P ξ ρ Λ)
    (hρ : relativeError P.zeta u (Central.B ξ)≤ ρ)
    (hder : BulkDerivativeBound P ξ κ Λ) (hgeom : DerivativeGeometry P ξ Λ) :
    ∃lam∈Λ,∃φ : ℕ→ℕ,StrictMono φ ∧
      Tendsto (fun j=> lambda (E (φ j)).market hlow) atTop (𝓝 lam) ∧
      (∀v∈Icc (0:ℝ) P.d0∪P.partialValues∪P.bulkValues∪Ici P.M,∀r : Fin 3,
        Tendsto (fun j=>(conditionalTypeCountLaw (E (φ j)).fullySpecified
          (Nat.succ_pos (N (φ j))) v).mass r) atTop (𝓝 ((limitLaw P ξ hξ lam v).mass r))) ∧
      (∀f : Fin 3→ℝ,
        Tendsto (fun j=>∫v,(conditionalTypeCountLaw (E (φ j)).fullySpecified
          (Nat.succ_pos (N (φ j))) v).expect f ∂valueLaw P) atTop
            (𝓝 (∫v,(limitLaw P ξ hξ lam v).expect f ∂valueLaw P))) ∧
      (∀rec reg : Bool,
        Tendsto (fun j=> actualMoment (E (φ j)).market hlow rec reg) atTop
          (𝓝 (limitMoment P ξ hξ lam rec reg))) ∧
      (∀reg : Bool,(if reg then lam.2 else lam.1)=
        meanNumerator P ξ (limitMoment P ξ hξ lam false reg) reg/
          limitMoment P ξ hξ lam true reg) := by
  obtain ⟨lam,hlam,φ,hφ,hlim⟩:=hcompact.tendsto_subseq
    (fun j=> lambda_mem (E j).market hlow hrect hρ)
  have hNφ:=hN.comp hφ.tendsto_atTop
  refine ⟨lam,hlam,φ,hφ,hlim,?_,?_,?_,?_⟩
  · exact every_fixed_value P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ
      (fun j=> N (φ j)) hNφ (fun j=> E (φ j)) hκ hder hgeom lam hlam hlim
  · intro f
    exact every_count_test P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ
      (fun j=> N (φ j)) hNφ (fun j=> E (φ j)) hκ hder hgeom lam hlam hlim f
  · intro rec reg
    exact actualMoment_tendsto P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ
      (fun j=> N (φ j)) hNφ (fun j=>(E (φ j)).market) hκ hder hgeom lam hlam hlim rec reg
  · exact actual_clearing P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ
      (fun j=> N (φ j)) hNφ (fun j=>(E (φ j)).market) hκ hder hgeom lam hlam hlim

end Family
end FCAppendix.Affine.Tail04.OrderedSourceFinalCountFamily
