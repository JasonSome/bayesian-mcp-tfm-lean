import FCAppendix.Affine.Tail04.OrderedSourceRestrictedNative
import FCAppendix.Affine.Tail04.OrderedZeroNativeMenuPayoff
import FCAppendix.Affine.Tail04.ActiveFixedValueVersions

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceActiveCountData
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation LowBody
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedSourceFiniteStartingPoint
open SourceMovingScalarGuards SourceMomentRectangle SourceMenuPopulation MenuError
open OrderedSourceRestrictedNative SourceMultiplierRectangle SourceMenuIdentity

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {N : ℕ} (A : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N)
  (hlow : P.d0<1-ξ)

def lambda : ℝ×ℝ :=
  let l:=ZeroSourceCommonMenuError.lambda A.D P (cutoff N) A.point.range.cutoff_gt_M
    A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable
    (A.forget.low_gap hlow) A.H A.upper_gap A.upper_floor N (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare)
  (l false,l true)

def rate (P : ValueParameters) (ξ : ℝ) (N : ℕ) : ℝ :=
  SourceMovingMenuRates.rate (SourceCommonMenuError.commonCoefficient P ξ)
    (lowMass P.theta) P.bulkWeight N

lemma rate_nonnegative (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) (N : ℕ) :
    0≤ rate P ξ N :=
  SourceMovingMenuRates.rate_nonneg (SourceCommonMenuError.commonCoefficient_nonnegative P hξ)
    P.bulkWeight_pos.le N

lemma rate_tendsto_zero (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) :
    Tendsto (rate P ξ) atTop (𝓝 0) := by
  apply squeeze_zero (rate_nonnegative P hξ) _
    (SourceMovingMenuRates.scaled_rate_tendsto (K:=SourceCommonMenuError.commonCoefficient P ξ)
      P.low_mass_pos P.bulkWeight_pos)
  intro N
  have ht : 1≤ cutoff N := movingThreshold_ge_one (N+1) (by omega)
  have hn:=rate_nonnegative P hξ N
  have hh:=mul_le_mul_of_nonneg_right (show 1≤ cutoff N^2 by nlinarith) hn
  simpa only [one_mul,rate] using! hh

lemma lambda_mem {ρ : ℝ} {Λ : Set (ℝ×ℝ)}
    (hrect : MomentInvariant P ξ ρ Λ)
    (hρ : relativeError P.zeta u (Central.B ξ)≤ ρ) : lambda A hlow∈Λ :=
  ZeroSourceMultiplierRectangle.actual_mem A.D P (cutoff N) A.point.range.cutoff_gt_M
    A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable
    (A.forget.low_gap hlow) A.H A.upper_gap A.upper_floor N (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare)
    rfl (by intro reg;cases reg <;> rfl) A.forget.base_bulk_below hrect hρ

lemma tariff : A.D.eta=1-2*ξ := rfl

lemma action_eq_band {U : ℝ} (a : JointAction 2) (hk : a.routeCount=2)
    (hb : a.bid∈Icc (1:ℝ) U) :
    a=bandAction (by norm_num) 2 le_rfl (⟨a.bid,hb⟩ : Icc (1:ℝ) U) := by
  cases a with
  | mk b hb' q hq =>
    dsimp at hk
    subst q
    rfl

theorem count_error (hwγ : width≤ γ ξ) (i : Fin (N+1)) (b : Icc (1:ℝ) A.D.U)
    (f : Fin 3→ℝ) :
    |((problem (A.native hlow) i).outcome (bandAction (by norm_num) 2 le_rfl b)).expect f-
      (ParametricMenuCount.law P ξ (lambda A hlow) b).expect f|≤ MenuError.oscillation f*rate P ξ N := by
  letI:=A.common_compact_atomless
  have hh:=OrderedZeroNativeCommonCount.original_count_error A.D P (cutoff N)
    A.point.range.cutoff_gt_M (A.forget.low_gap hlow) A.H A.upper_gap
    A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable A.upper_floor N (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare)
    (NativeLowSourceIC.categories P (cutoff N) A.point.range.cutoff_gt_M.le) A.point.low rfl
    rfl A.point.range.rivals_positive rfl (by intro reg;cases reg <;> rfl) rfl hξh rfl
    A.forget.base_bulk_below A.forget.base_partial_guard A.forget.base_moment_guard
    A.point.range.upper_mass_guard hwγ i b f
  rw [ParametricMenuCount.idealCount_eq] at hh
  exact hh

theorem count_mass_error (hwγ : width≤ γ ξ) (i : Fin (N+1)) (a : JointAction 2)
    (hk : a.routeCount=2) (hb : a.bid∈Icc (1:ℝ) A.D.U) (r : Fin 3) :
    |((problem (A.native hlow) i).outcome a).mass r-
      (ParametricMenuCount.law P ξ (lambda A hlow) a.bid).mass r|≤ rate P ξ N := by
  have ha : a=bandAction (by norm_num) 2 le_rfl (⟨a.bid,hb⟩ : Icc (1:ℝ) A.D.U) := by
    cases a with | mk b hb q hq => dsimp at hk;subst q;rfl
  rw [ha]
  have hh:=count_error A hlow hwγ i ⟨a.bid,hb⟩ (fun q : Fin 3=> if q=r then 1 else 0)
  have ho : MenuError.oscillation (fun q : Fin 3=> if q=r then 1 else 0)≤1 := by
    unfold MenuError.oscillation
    apply max_le
    · dsimp only
      split_ifs <;> norm_num
    · dsimp only
      split_ifs <;> norm_num
  simp only [FiniteLaw.expect_singleton] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right ho (rate_nonnegative P hξ N)).trans_eq (one_mul _))

theorem payoff_error (hwγ : width≤ γ ξ) (i : Fin (N+1)) (v : ℝ) (hv : 0≤ v)
    (b : Icc (1:ℝ) A.D.U) :
    |(problem (A.native hlow) i).payoff v (bandAction (by norm_num) 2 le_rfl b)-
      menuUtility P ξ (lambda A hlow).1 (lambda A hlow).2 v b|≤
        ActiveFixedValueVersions.error ξ (rate P ξ N) v := by
  letI:=A.common_compact_atomless
  have hh:=OrderedZeroNativeMenuPayoff.original_payoff_error A.D P (cutoff N)
    A.point.range.cutoff_gt_M (A.forget.low_gap hlow) A.H A.upper_gap
    A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable A.upper_floor N (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare)
    (NativeLowSourceIC.categories P (cutoff N) A.point.range.cutoff_gt_M.le) A.point.low rfl
    rfl A.point.range.rivals_positive rfl (by intro reg;cases reg <;> rfl) rfl rfl hξh rfl
    A.forget.base_bulk_below A.forget.base_partial_guard A.forget.base_moment_guard
    A.point.range.upper_mass_guard hwγ i v hv b
  simpa only [ActiveFixedValueVersions.error,max_eq_right hv,rate] using! hh

lemma active_valueLo_nonnegative (q : Fin 3) (hq : q≠2) : 0≤ valueLo P q := by
  fin_cases q
  · dsimp [valueLo]
    linarith [P.low_partial_gap,P.d0_pos,P.partial_active_gap,P.w_pos]
  · exact P.M_pos.le
  · exact (hq rfl).elim

lemma active_bidLo (q : Fin 3) (hq : q≠2) : bidLo A.D q=1 := by
  fin_cases q <;> simp_all [bidLo]

lemma active_bidHi (q : Fin 3) (hq : q≠2) : bidHi A.D q≤ A.D.U := by
  fin_cases q
  · exact A.D.huU
  · exact le_rfl
  · exact (hq rfl).elim

def band (q : Fin 3) : ProbabilityMeasure (ℝ×JointAction 2) :=
  bandJoint (bidLo_pos A.D q).le (if q=2 then 1 else 2) (by split_ifs <;> omega)
    (originalValueLaw P (cutoff N) A.point.range.cutoff_gt_M q) (A.sequence.limit q)

theorem band_regret (hwγ : width≤ γ ξ) (q : Fin 3) (hq : q≠2) :
    ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A q)),
      x.1∈Icc (valueLo P q) (valueHi P (cutoff N) q) ∧
      x.2.routeCount=2 ∧ x.2.bid∈Icc (1:ℝ) (bidHi A.D q) ∧
      ∀y : Icc (1:ℝ) (bidHi A.D q),
        menuUtility P ξ (lambda A hlow).1 (lambda A hlow).2 x.1 y≤
          menuUtility P ξ (lambda A hlow).1 (lambda A hlow).2 x.1 x.2.bid+
            2*ActiveFixedValueVersions.error ξ (rate P ξ N) x.1 := by
  have hs:=bandJoint_support (bidLo_pos A.D q).le (if q=2 then 1 else 2)
    (by split_ifs <;> omega) (originalValueLaw P (cutoff N) A.point.range.cutoff_gt_M q)
    (A.sequence.limit q)
  filter_upwards [A.bandJoint_all_labels hlow q,hs] with x hi hx
  have hlo:=active_bidLo A q hq
  rw [if_neg hq,hlo] at hx
  refine ⟨hx.1,hx.2.2,hx.2.1,?_⟩
  intro y
  let i : Fin (N+1):=⟨0,Nat.succ_pos N⟩
  have hv : 0≤ x.1:=(active_valueLo_nonnegative (P:=P) q hq).trans hx.1.1
  let y' : ActiveBaseBid (bidLo A.D q) (bidHi A.D q):=⟨y,by simpa only [hlo] using y.2⟩
  have hic:=hi i y'
  simp only [if_neg hq] at hic
  have hb : x.2.bid∈Icc (1:ℝ) A.D.U:=⟨hx.2.1.1,hx.2.1.2.trans (active_bidHi A q hq)⟩
  let played : Icc (1:ℝ) A.D.U:=⟨x.2.bid,hb⟩
  let cmp : Icc (1:ℝ) A.D.U:=⟨y,y.2.1,y.2.2.trans (active_bidHi A q hq)⟩
  have hp:=payoff_error A hlow hwγ i x.1 hv played
  have hc:=payoff_error A hlow hwγ i x.1 hv cmp
  have ha : bandAction (by norm_num) 2 le_rfl played=x.2 :=
    (action_eq_band x.2 hx.2.2 hb).symm
  rw [ha] at hp
  have he : bandAction (bidLo_pos A.D q).le 2 (by omega) y'=
      bandAction (by norm_num) 2 le_rfl cmp := rfl
  rw [he] at hic
  dsimp only [played,cmp] at hp hc
  linarith [(abs_le.mp hp).2,(abs_le.mp hc).1]

theorem original_joint_ae (Q : ℝ×JointAction 2→ Prop)
    (hL : ∀ᵐx ∂(lowJoint P.originalLowLaw A.point.low.joint : Measure _),Q x)
    (hP : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 2)),Q x)
    (hB : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 0)),Q x)
    (hT : ∀ᵐx ∂(ProbabilityMeasure.toMeasure (band A 1)),Q x)
    (hH : ∀ᵐx ∂(upperJoint
      ⟨P.originalMovingUpperLaw (cutoff N),P.originalMovingUpperLaw_probability (cutoff N)⟩
        A.upperBid A.upperBid_measurable : Measure _),Q x) :
    ∀ᵐx ∂(A.native hlow).F⊗ₘ(A.native hlow).σ,Q x := by
  rw [A.original_joint hlow]
  letI : IsProbabilityMeasure (P.originalMovingActiveLaw (cutoff N) A.point.range.cutoff_gt_M.le) :=
    P.originalMovingActiveLaw_probability (cutoff N) A.point.range.cutoff_gt_M.le
  change ∀ᵐx ∂fourJoint (lowMass P.theta) partialMass
    (activeMass P.theta-tailMass P (cutoff N)) (tailMass P (cutoff N))
    (lowJoint P.originalLowLaw A.point.low.joint) (band A 2)
    (bandJoint (by norm_num) 2 le_rfl (P.originalMovingActiveLaw (cutoff N)
      A.point.range.cutoff_gt_M.le) (OrderedNativeZeroNoiseSource.active A.D P (cutoff N)
        A.point.range.cutoff_gt_M A.sequence.limit))
    (upperJoint ⟨P.originalMovingUpperLaw (cutoff N),
      P.originalMovingUpperLaw_probability (cutoff N)⟩ A.upperBid A.upperBid_measurable),Q x
  unfold fourJoint
  have hj := OrderedNativeZeroNoiseSource.joint_active_components A.D P (cutoff N)
    A.point.range.cutoff_gt_M A.sequence.limit
  erw [hj]
  exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr
    ⟨ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure hL _,Measure.ae_smul_measure hP _⟩,
      ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure hB _,Measure.ae_smul_measure hT _⟩⟩,
    Measure.ae_smul_measure hH _⟩

end FCAppendix.Affine.Tail04.OrderedSourceActiveCountData
