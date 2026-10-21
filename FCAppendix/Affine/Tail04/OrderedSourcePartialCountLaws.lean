import FCAppendix.Affine.Tail04.OrderedZeroSourcePartialCount
import FCAppendix.Affine.Tail04.PartialFixedValueVersions
import FCAppendix.Affine.Tail04.OrderedSourceLowCountLaws
import FCAppendix.Affine.Tail04.OrderedSourceFiniteStartingPoint

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourcePartialCountLaws
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation LowBody
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedSourceFiniteStartingPoint
open SourceMovingScalarGuards SourceMomentRectangle SourceMenuPopulation MenuError
open scoped BigOperators

theorem original_partialCondition (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
    (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
    (πL : Law (A:=LowValue P.d0) P.originalLowLaw) (π : JointProfile D P t ht)
    (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid) (hfloor : ∀v,t< v→ H≤ upperBid v)
    (m : ℕ) (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((m:ℝ)*
      (tailMass P t/(partialMass+tailMass P t)))≤ D.R) :
    let Γ := OrderedNativeZeroNoiseSource.game D P t ht hdR H hUH πL π upperBid hupperBid hfloor m hrare
    ∀ᵐx ∂Γ.F⊗ₘΓ.σ,PartialFixedValueVersions.condition (2-P.w) (2+P.w) D.R D.Up x := by
  dsimp only
  rw [OrderedNativeZeroNoiseSource.game_original_joint]
  filter_upwards [OrderedNativeZeroNoiseSource.source_bands D P t ht hdR H hUH πL π
    upperBid hupperBid hfloor] with x hx
  intro hv
  rcases hx with hx | hx | hx | hx
  · exfalso
    linarith [hx.1.2,hv.1,P.low_partial_gap]
  · exact ⟨hx.2.2,hx.2.1⟩
  · exfalso
    linarith [hx.1.1,hv.2,P.partial_active_gap]
  · exfalso
    linarith [hx.1,hv.2,ht,P.partial_active_gap,P.active_tail_gap,P.w_pos]

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)

structure Market (N : ℕ) where
  point : StartingPoint P ξ Up u k width hξ hξh hu hRUp hUp hw N
  H : ℝ
  upper_gap : (data P ξ Up u k width hξ hξh hu hRUp hUp hw N point.range).U< H
  upperBid : ℝ→ℝ
  upperBid_measurable : Measurable upperBid
  upper_floor : ∀v,cutoff N< v→ H≤ upperBid v

namespace Market
variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {N : ℕ} (A : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N)
  (hlow : P.d0<1-ξ)

abbrev D : Data := data P ξ Up u k width hξ hξh hu hRUp hUp hw N A.point.range

include hlow in
lemma low_gap : P.d0< A.D.R := by
  change P.d0< Central.R ξ
  unfold Central.R
  linarith only [hlow,hξ]

lemma rare : (1-A.D.ξ)*A.D.U+A.D.ξ*A.D.U*((N+1:ℝ)*
    (tailMass P (cutoff N)/(partialMass+tailMass P (cutoff N))))≤ A.D.R := by
  have hp : (1-A.D.ξ)*A.D.B+A.D.ξ*A.D.B*((N+1:ℕ)*
      (tailMass P (cutoff N)/(partialMass+tailMass P (cutoff N))))≤A.D.R := by
    simpa only [D,data,SourceNoisyData.data,Data.B,commonPhysical,noise,
      tailMass,upperMass,Nat.cast_add,Nat.cast_one] using! A.point.range.owner_receipt_guard
  simpa only [Nat.cast_add,Nat.cast_one] using!
    OrderedNativeZeroNoiseSource.rare_guard_of_physical A.D P (cutoff N)
      A.point.range.cutoff_gt_M (N+1) hp

def lowMarket : OrderedSourceLowCountLaws.Market P N where
  data:=A.D
  cap:=by simp only [D,data,SourceNoisyData.data,Markets.capacity,iidCapacity,
    Nat.cast_add,Nat.cast_one]
  threshold:=A.point.range.cutoff_gt_M
  low_gap:=A.low_gap hlow
  H:=A.H
  upper_gap:=A.upper_gap
  low:=A.point.low
  joint:=A.point.sequence.limit
  upperBid:=A.upperBid
  upperBid_measurable:=A.upperBid_measurable
  upper_floor:=A.upper_floor
  rare:=A.rare

abbrev native : FiniteGame (N+1) 2 A.D.c NativeLocalPolicy.Seed := (A.lowMarket hlow).native
abbrev lowSpecified : FiniteGame (N+1) 2 A.D.c NativeLocalPolicy.Seed := (A.lowMarket hlow).specified

def specified : FiniteGame (N+1) 2 A.D.c NativeLocalPolicy.Seed :=
  PartialFixedValueVersions.game (A.lowSpecified hlow) (2-P.w) (2+P.w)
    A.D.R A.D.Up A.D.hR.le

lemma lowCondition : ∀ᵐx ∂(A.native hlow).F⊗ₘ(A.native hlow).σ,
    LowFixedValueVersions.lowCondition P.d0 x :=
  OrderedSourceLowCountLaws.original_lowCondition A.D P _ A.point.range.cutoff_gt_M
    (A.low_gap hlow) A.H A.upper_gap N A.point.low A.point.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor A.rare

lemma partialCondition : ∀ᵐx ∂(A.lowSpecified hlow).F⊗ₘ(A.lowSpecified hlow).σ,
    PartialFixedValueVersions.condition (2-P.w) (2+P.w) A.D.R A.D.Up x := by
  have hj : (A.lowSpecified hlow).F⊗ₘ(A.lowSpecified hlow).σ=
      (A.native hlow).F⊗ₘ(A.native hlow).σ :=
    LowFixedValueVersions.joint_eq (A.native hlow) P.d0 (A.lowCondition hlow)
  rw [hj]
  exact original_partialCondition A.D P _ A.point.range.cutoff_gt_M
    (A.low_gap hlow) A.H A.upper_gap A.point.low.joint A.point.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor (N+1)
      (by simpa only [Nat.cast_add,Nat.cast_one] using! A.rare)

lemma specified_joint : (A.specified hlow).F⊗ₘ(A.specified hlow).σ=
    (A.native hlow).F⊗ₘ(A.native hlow).σ := by
  exact (PartialFixedValueVersions.joint_eq (A.lowSpecified hlow) (2-P.w) (2+P.w)
    A.D.R A.D.Up A.D.hR.le (A.partialCondition hlow)).trans
      (LowFixedValueVersions.joint_eq (A.native hlow) P.d0 (A.lowCondition hlow))

lemma specified_problem (i : Fin (N+1)) :
    problem (A.specified hlow) i=problem (A.native hlow) i := by
  exact (PartialFixedValueVersions.problem_eq (A.lowSpecified hlow) (2-P.w) (2+P.w)
    A.D.R A.D.Up A.D.hR.le (A.partialCondition hlow) i).trans
      (LowFixedValueVersions.problem_eq (A.native hlow) P.d0 (A.lowCondition hlow) i)

lemma specified_value : (A.specified hlow).F=valueLaw P := rfl

lemma specified_outside_low_partial (v : ℝ)
    (hL : v∉Icc (0:ℝ) P.d0) (hP : v∉P.partialValues) :
    (A.specified hlow).σ v=(A.native hlow).σ v := by
  exact (PartialFixedValueVersions.outside (A.lowSpecified hlow) (2-P.w) (2+P.w)
    A.D.R A.D.Up A.D.hR.le v hP).trans
      (LowFixedValueVersions.strategy_outside_low (A.native hlow) P.d0 v hL)

include A in
lemma base_bulk_width : u≤ bulkWidth ξ Up u k N := by
  have he := A.point.range.budget_positive.le
  have hh := mul_nonneg (show 0≤1+u by linarith only [hu]) he
  dsimp [bulkWidth]
  nlinarith

include A in
lemma base_bulk_below : 1+u< Central.B ξ :=
  (by simpa only [add_comm] using add_le_add_left A.base_bulk_width 1 : 1+u≤1+bulkWidth ξ Up u k N).trans_lt A.point.range.bulk_below_nominal

include A in
lemma base_partial_guard : Up≤ Central.R ξ+ξ/1000 := by
  have hh := OrderedNativeZeroNoiseSource.base_partial_le_physical A.D
  exact hh.trans A.point.range.partial_guard

include A in
lemma base_moment_guard : relativeError P.zeta u (Central.B ξ)≤ ξ/1000 := by
  have hB : 0< Central.B ξ-1 := by unfold Central.B;linarith only [hξ]
  have hc : 0≤1+2/(Central.B ξ-1) := by positivity
  have hh : relativeError P.zeta u (Central.B ξ)≤
      relativeError P.zeta (bulkWidth ξ Up u k N) (Central.B ξ) := by
    unfold relativeError
    linarith only [mul_le_mul_of_nonneg_right A.base_bulk_width hc]
  exact hh.trans A.point.range.moment_guard

theorem partial_raw_error (hwγ : width≤ γ ξ) (i : Fin (N+1)) (a : JointAction 2)
    (hk : a.routeCount=1) (hb : a.bid∈Icc A.D.R A.D.Up) (r : Fin 3) :
    |((problem (A.native hlow) i).outcome a).mass r-
      (Counts.singletonLaw (1-P.theta) ⟨by linarith only [P.theta_small],by linarith only [P.theta_pos]⟩).mass r|≤
      OrderedZeroSourcePartialCount.error P ξ N := by
  have ha : a=RawRoutes.action a.bid a.bid_nonneg 1 := by
    cases a with
    | mk b hb' q hq =>
      dsimp at hk
      subst q
      rfl
  rw [ha]
  exact OrderedZeroSourcePartialCount.original_count_mass_error P ξ u Up (cap ξ k N) width N
    hξ hξh hu A.point.range.base_contains_bulk hRUp.le hUp A.point.range.base_below_nominal hw
    (cutoff N) A.point.range.cutoff_gt_M (A.low_gap hlow) A.H A.upper_gap
    A.point.low.joint A.point.sequence.limit A.upperBid A.upperBid_measurable A.upper_floor (by simpa only [Nat.cast_add,Nat.cast_one] using! A.rare)
    A.point.range.rivals_positive A.base_bulk_below A.base_partial_guard A.base_moment_guard
    A.point.range.upper_mass_guard hwγ A.point.range.room
    (NativeLowSourceIC.categories P (cutoff N) A.point.range.cutoff_gt_M.le)
    A.point.low rfl i ⟨a.bid,hb⟩ r

theorem partial_count_error (hwγ : width≤ γ ξ) (v : ℝ) (hv : v∈P.partialValues) (r : Fin 3) :
    |(conditionalTypeCountLaw (A.specified hlow) (Nat.succ_pos N) v).mass r-
      (Counts.singletonLaw (1-P.theta) ⟨by linarith only [P.theta_small],by linarith only [P.theta_pos]⟩).mass r|≤
      OrderedZeroSourcePartialCount.error P ξ N := by
  refine PartialFixedValueVersions.conditional_from_native (A.lowSpecified hlow)
    (2-P.w) (2+P.w) A.D.R A.D.Up A.D.hR.le (A.partialCondition hlow)
    (Nat.succ_pos N) A.D.hRUp
    (Counts.singletonLaw (1-P.theta) ⟨by linarith only [P.theta_small],by linarith only [P.theta_pos]⟩)
    (OrderedZeroSourcePartialCount.error P ξ N) ?_ v hv r
  intro i a hk hb r
  have he : problem (A.lowSpecified hlow) i=problem (A.native hlow) i :=
    LowFixedValueVersions.problem_eq (A.native hlow) P.d0 (A.lowCondition hlow) i
  rw [he]
  exact A.partial_raw_error hlow hwγ i a hk hb r

lemma specified_low_count (v : ℝ) (hv : v∈Icc (0:ℝ) P.d0) :
    conditionalTypeCountLaw (A.specified hlow) (Nat.succ_pos N) v=
      conditionalTypeCountLaw (A.lowSpecified hlow) (Nat.succ_pos N) v := by
  apply PartialFixedValueVersions.conditional_eq_outside _ _ _ _ _ _ (A.partialCondition hlow)
  intro hp
  linarith [hp.1,hv.2,P.low_partial_gap]

end Market

theorem original_fixed_partial_limit (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (A : ∀j,Market P ξ Up u k width hξ hξh hu hRUp hUp hw (N j)) :
    ∀v∈P.partialValues,∀r : Fin 3,
      Tendsto (fun j=>(conditionalTypeCountLaw ((A j).specified hlow) (Nat.succ_pos (N j)) v).mass r)
        atTop (𝓝 ((Counts.singletonLaw (1-P.theta)
          ⟨by linarith only [P.theta_small],by linarith only [P.theta_pos]⟩).mass r)) := by
  intro v hv r
  have he := (OrderedZeroSourcePartialCount.error_tendsto_zero P hξ).comp hN
  have hn : Tendsto (fun j=>|(conditionalTypeCountLaw ((A j).specified hlow)
      (Nat.succ_pos (N j)) v).mass r-(Counts.singletonLaw (1-P.theta)
        ⟨by linarith only [P.theta_small],by linarith only [P.theta_pos]⟩).mass r|) atTop (𝓝 0) :=
    squeeze_zero (fun _=> abs_nonneg _) (fun j=>(A j).partial_count_error hlow hwγ v hv r) he
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using! hn)

theorem original_fixed_low_limit (hlow : P.d0<1-ξ)
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (A : ∀j,Market P ξ Up u k width hξ hξh hu hRUp hUp hw (N j)) :
    ∀v∈Icc (0:ℝ) P.d0,∀r : Fin 3,
      Tendsto (fun j=>(conditionalTypeCountLaw ((A j).specified hlow) (Nat.succ_pos (N j)) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r)) := by
  intro v hv r
  simpa only [(A _).specified_low_count hlow v hv] using!
    OrderedSourceLowCountLaws.original_fixed_value_count_limit P N hN (fun j=>(A j).lowMarket hlow) v hv r

end FCAppendix.Affine.Tail04.OrderedSourcePartialCountLaws
