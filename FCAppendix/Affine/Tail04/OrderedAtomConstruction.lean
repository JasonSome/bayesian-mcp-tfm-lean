import FCAppendix.Affine.Tail04.OrderedAtomActiveNoisyCap
import FCAppendix.Affine.Tail04.OrderedAtomStartingPoint
import FCAppendix.Affine.Tail04.OrderedAtomNoiseRates

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomConstruction
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional OriginalValues FiniteTailNoisyGame SourceTailNoisyFixedPoint
open OrderedOriginalNoisySequence NativeNoisySource SourceMovingScalarGuards OrderedSourceFiniteStartingPoint
open OrderedAtomClusterLaws
open MenuError SourceMomentRectangle SourceMenuPopulation SourceBulkAnalyticAdapter
open SourceTailTaylor SourceTailCapGap OrderedAtomMultiplierRectangle OrderedSourceCommonMenuError

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)

section Fixed
variable {N : ℕ} (Z : StartingPoint P ξ Up u k width hξ hξh hu hRUp hUp hw N)
  (hlow : P.d0<1-ξ)

local notation "D" => OrderedSourceFiniteStartingPoint.data P ξ Up u k width
  hξ hξh hu hRUp hUp hw N Z.range
local notation "S" => Z.sequence
local notation "tN" => cutoff N
local notation "htN" => Z.range.cutoff_gt_M

include hlow in
lemma low_lt_partial : P.d0< (D).R := by
  change P.d0< Central.R ξ
  unfold Central.R
  linarith

lemma physical_lt_floor : (D).B< Central.B ξ+1 :=
  (D).hUF.trans_lt (lt_add_of_pos_right _ (by norm_num))

lemma rare_guard : (1-(D).ξ)*(D).B+(D).ξ*(D).B*((N+1:ℕ)*
    (tailMass P tN/(partialMass+tailMass P tN)))≤ (D).R := by
  simpa only [OrderedSourceFiniteStartingPoint.data,SourceNoisyData.data,Data.B,commonPhysical,
    noise,tailMass,upperMass,Nat.cast_add,Nat.cast_one] using Z.range.owner_receipt_guard

lemma bulk_width_le (j : ℕ) : bulkPhysicalWidth ((S).data j)≤ bulkWidth ξ Up u k N := by
  change (1+u)*(1+((S).eps j:ℝ))-1≤(1+u)*(1+(D).eps)-1
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left
    (by linarith [(S).noise_small j]) (by linarith)) 1

lemma relative_error_le (j : ℕ) :
    relativeError P.zeta (bulkPhysicalWidth ((S).data j)) (Central.B ξ)≤
      relativeError P.zeta (bulkWidth ξ Up u k N) (Central.B ξ) := by
  have hcoef : 0≤1+2/(Central.B ξ-1) := by
    have hp : 0< Central.B ξ-1 := by unfold Central.B;linarith
    positivity
  exact add_le_add (le_refl P.zeta) (mul_le_mul_of_nonneg_right
    (bulk_width_le P ξ Up u k width hξ hξh hu hRUp hUp hw Z j) hcoef)

def multiplier (j : ℕ) (reg : Bool) : ℝ :=
  OrderedSourceCommonMenuError.lambda ((S).data j) P tN htN Z.low.joint ((S).law j)
    (fun _ : ℝ=> Central.B ξ+1) measurable_const
    (low_lt_partial P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow)
    (Central.B ξ+1)
    (((S).physical_cap_le j).trans_lt
      (physical_lt_floor P ξ Up u k width hξ hξh hu hRUp hUp hw Z)) reg

theorem multiplier_mem {ρ : ℝ} {Λ : Set (ℝ×ℝ)}
    (hrect : MomentInvariant P ξ ρ Λ)
    (hρ : relativeError P.zeta (bulkWidth ξ Up u k N) (Central.B ξ)≤ ρ) (j : ℕ) :
    (multiplier P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow j false,
      multiplier P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow j true)∈Λ := by
  apply actual_mem ((S).data j) P tN htN Z.low.joint ((S).law j)
    (fun _ : ℝ=> Central.B ξ+1) measurable_const
    (low_lt_partial P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow)
    (Central.B ξ+1)
    (((S).physical_cap_le j).trans_lt (physical_lt_floor P ξ Up u k width hξ hξh hu hRUp hUp hw Z))
    (fun _ _=> le_rfl) N ((S).rare_guard (rare_guard P ξ Up u k width hξ hξh hu hRUp hUp hw Z) j)
    rfl (fun reg=> by cases reg <;> rfl)
    ((add_le_add (le_refl (1:ℝ)) (bulk_width_le P ξ Up u k width hξ hξh hu hRUp hUp hw Z j)).trans_lt Z.range.bulk_below_nominal) hrect
  exact (relative_error_le P ξ Up u k width hξ hξh hu hRUp hUp hw Z j).trans hρ

include hlow in
theorem bulk_strip {ρ κ : ℝ} {Λ : Set (ℝ×ℝ)} (hκ : 0≤ κ)
    (hrect : MomentInvariant P ξ ρ Λ) (hder : BulkDerivativeBound P ξ κ Λ)
    (hρ : relativeError P.zeta (bulkWidth ξ Up u k N) (Central.B ξ)≤ ρ)
    (herror : 2*(tN+2*Central.B ξ)*SourceMovingMenuRates.rate
      (commonCoefficient P ξ) (lowMass P.theta) P.bulkWeight N< κ*u/2)
    (hwγ : width≤ γ ξ) (j : ℕ) :
    (ProbabilityMeasure.toMeasure ((S).law j 0).1) {x | 1+u/2<(x.2:ℝ)}=0 := by
  have hb := bulk_width_le P ξ Up u k width hξ hξh hu hRUp hUp hw Z j
  have he := (relative_error_le P ξ Up u k width hξ hξh hu hRUp hUp hw Z j).trans Z.range.moment_guard
  have hstrip := OrderedAtomActiveNoisyCap.bulk_upper_strip ((S).data j) P tN htN
    Z.low.joint ((S).law j) (fun _ : ℝ=> Central.B ξ+1) measurable_const
    (low_lt_partial P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow) (Central.B ξ+1)
    (((S).physical_cap_le j).trans_lt (physical_lt_floor P ξ Up u k width hξ hξh hu hRUp hUp hw Z))
    (fun _ _=> le_rfl) N ((S).rare_guard (rare_guard P ξ Up u k width hξ hξh hu hRUp hUp hw Z) j)
    rfl Z.range.rivals_positive rfl (fun reg=> by cases reg <;> rfl) hξh rfl
    ((add_le_add (le_refl (1:ℝ)) hb).trans_lt Z.range.bulk_below_nominal)
    (((S).partial_cap_le j).trans Z.range.partial_guard) he Z.range.upper_mass_guard
    hwγ rfl rfl hκ hder
    (multiplier_mem P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hrect hρ j)
    (by simpa only [Sequence.data,atNoise,OrderedSourceFiniteStartingPoint.data,SourceNoisyData.data,mul_assoc] using herror) ((S).optimal j 0)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hstrip] with x hx
  exact not_lt_of_ge hx.le

include hlow in
theorem tail_strip {ρ Amin Amax : ℝ} {Λ : Set (ℝ×ℝ)}
    (hmin : 0< Amin) (hk : k<1/(2*Amax))
    (hrect : MomentInvariant P ξ ρ Λ)
    (hleading : ∀ lam∈Λ,Amin≤ leadingA P ξ lam.1 lam.2 ∧ leadingA P ξ lam.1 lam.2≤ Amax)
    (hρ : relativeError P.zeta (bulkWidth ξ Up u k N) (Central.B ξ)≤ ρ)
    (hleft : endpointRadius Amin/tN≤ Central.B ξ-1)
    (hbudget : 2*taylorConstant ξ (endpointRadius Amin)/tN^2≤
      Amin*(stripWidth Amax k)^2/(4*tN))
    (herror : 2*(tN+2*Central.B ξ)*SourceMovingMenuRates.rate
      (commonCoefficient P ξ) (lowMass P.theta) P.bulkWeight N<
        Amin*(stripWidth Amax k)^2/(2*tN))
    (hwγ : width≤ γ ξ) :
    ∀ᶠ j in atTop,(ProbabilityMeasure.toMeasure ((S).law j 1).1)
      {x | inwardCut (Central.B ξ) Amax k tN<(x.2:ℝ)}=0 := by
  filter_upwards [OrderedAtomNoiseRates.sequence_eventually_tail_noise D P tN htN N S hk]
    with j hnoise
  have hb := bulk_width_le P ξ Up u k width hξ hξh hu hRUp hUp hw Z j
  have he := (relative_error_le P ξ Up u k width hξ hξh hu hRUp hUp hw Z j).trans Z.range.moment_guard
  have hm := hleading _ (multiplier_mem P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hrect hρ j)
  have hstrip := OrderedAtomActiveNoisyCap.tail_upper_strip ((S).data j) P tN htN
    Z.low.joint ((S).law j) (fun _ : ℝ=> Central.B ξ+1) measurable_const
    (low_lt_partial P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow) (Central.B ξ+1)
    (((S).physical_cap_le j).trans_lt (physical_lt_floor P ξ Up u k width hξ hξh hu hRUp hUp hw Z))
    (fun _ _=> le_rfl) N ((S).rare_guard (rare_guard P ξ Up u k width hξ hξh hu hRUp hUp hw Z) j)
    rfl Z.range.rivals_positive rfl (fun reg=> by cases reg <;> rfl) hξh rfl
    ((add_le_add (le_refl (1:ℝ)) hb).trans_lt Z.range.bulk_below_nominal)
    (((S).partial_cap_le j).trans Z.range.partial_guard) he Z.range.upper_mass_guard
    hwγ rfl rfl hmin hm.1 hm.2 hk rfl hleft hbudget hnoise
    (by simpa only [Sequence.data,atNoise,OrderedSourceFiniteStartingPoint.data,SourceNoisyData.data,mul_assoc] using herror) ((S).optimal j 1)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hstrip] with x hx
  exact not_lt_of_ge hx.le

end Fixed

theorem eventually_atomless {ρ κ Amin Amax : ℝ} {Λ : Set (ℝ×ℝ)}
    (hu0 : 0< u) (hk0 : 0< k) (hκ : 0< κ) (hmin : 0< Amin) (hk : k<1/(2*Amax))
    (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)
    (hrect : MomentInvariant P ξ ρ Λ) (hder : BulkDerivativeBound P ξ κ Λ)
    (hleading : ∀ lam∈Λ,Amin≤ leadingA P ξ lam.1 lam.2 ∧ leadingA P ξ lam.1 lam.2≤ Amax)
    (hρ : relativeError P.zeta u (Central.B ξ)< ρ) :
    ∀ᶠ N in atTop,
      ∀ Z : StartingPoint P ξ Up u k width hξ hξh hu hRUp hUp hw (N+1),
      let D := OrderedSourceFiniteStartingPoint.data P ξ Up u k width
        hξ hξh hu hRUp hUp hw (N+1) Z.range
      NullSingletonClass (baseRealLaw D P (cutoff (N+1)) Z.range.cutoff_gt_M Z.sequence.limit : Measure ℝ) ∧
      (∀ q : Fin 3,NullSingletonClass (Sequence.realBaseLaw q Z.sequence.limit : Measure ℝ)) := by
  have hUp0 : 0< Up := by have := hRUp;unfold Central.R at this;nlinarith
  have hB0 : 0≤ Central.B ξ := by unfold Central.B;linarith
  have hK := commonCoefficient_nonnegative P hξ
  have hr := (tendsto_add_atTop_nat 1).eventually
    (eventually_physical_tolerance P (k:=k) hξ hξh hUp0 hUp hρ)
  have hb := (tendsto_add_atTop_nat 1).eventually
    (SourceMovingMenuRates.eventually_bulk_error P.low_mass_pos P.bulkWeight_pos hK hB0 hκ hu0)
  have ht := (tendsto_add_atTop_nat 1).eventually
    (SourceMovingMenuRates.eventually_tail_error P.low_mass_pos P.bulkWeight_pos hK hB0
      (by have := stripWidth_pos hk;positivity : 0< Amin*(stripWidth Amax k)^2/2))
  have hg := (tendsto_add_atTop_nat 1).eventually
    (SourceMovingMenuRates.eventually_tail_geometry hξ hmin hk)
  have ha := OrderedAtomStartingPoint.eventually_active_atomless P ξ Up u k width
    hξ hξh hu hRUp hUp hw hk0 hlow hwγ
  filter_upwards [hr,hb,ht,hg,ha] with N hρN hbulk htail hgeo hatoms
  intro Z
  have hB := bulk_strip P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hκ.le
    hrect hder hρN.le hbulk hwγ
  have hT := tail_strip P ξ Up u k width hξ hξh hu hRUp hUp hw Z hlow hmin hk
    hrect hleading hρN.le hgeo.1 hgeo.2 (by convert! htail using 1; ring) hwγ
  have hh := hatoms Z (1+u/2) (inwardCut (Central.B ξ) Amax k (cutoff (N+1)))
    (by linarith) (SourceMovingMenuRates.inwardCut_lt_cap hk (N+1)) hB hT
  refine ⟨hh.1,?_⟩
  intro q
  fin_cases q
  · exact hh.2.1
  · exact hh.2.2
  · exact Z.partial_atomless

end FCAppendix.Affine.Tail04.OrderedAtomConstruction
