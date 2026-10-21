import FCAppendix.Affine.Tail04.OrderedNativeLowSourceIC
import FCAppendix.Affine.Tail04.OrderedSourceFixedMarketIC
import FCAppendix.Affine.Tail04.OrderedAtomConstruction
import FCAppendix.Affine.Tail04.OrderedZeroPartialSourcePayoff
import FCAppendix.Affine.Tail04.OrderedSourcePartialCountLaws

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceRestrictedNative
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation LowBody
open CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedOriginalNoisySequence
open OrderedSourceFiniteStartingPoint SourceMovingScalarGuards OrderedAtomClusterLaws
open SourceMomentRectangle SourceMenuPopulation MenuError
open SourceMultiplierRectangle SourceBulkAnalyticAdapter SourceTailTaylor
open scoped BigOperators

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)

structure AtomlessPoint (N : ℕ) where
  point : StartingPoint P ξ Up u k width hξ hξh hu hRUp hUp hw N
  common_atoms : NullSingletonClass
    (baseRealLaw (data P ξ Up u k width hξ hξh hu hRUp hUp hw N point.range)
      P (cutoff N) point.range.cutoff_gt_M point.sequence.limit : Measure ℝ)
  species_atoms : ∀q : Fin 3,NullSingletonClass
    (Sequence.realBaseLaw q point.sequence.limit : Measure ℝ)

structure Market (N : ℕ) where
  point : StartingPoint P ξ Up u k width hξ hξh hu hRUp hUp hw N
  common_atoms : NullSingletonClass
    (baseRealLaw (data P ξ Up u k width hξ hξh hu hRUp hUp hw N point.range)
      P (cutoff N) point.range.cutoff_gt_M point.sequence.limit : Measure ℝ)
  species_atoms : ∀q : Fin 3,NullSingletonClass
    (Sequence.realBaseLaw q point.sequence.limit : Measure ℝ)
  H : ℝ
  upper_gap : (data P ξ Up u k width hξ hξh hu hRUp hUp hw N point.range).U< H
  upperBid : ℝ→ℝ
  upperBid_measurable : Measurable upperBid
  upper_floor : ∀v,cutoff N< v→ H≤ upperBid v

def complete {N : ℕ} (Z : AtomlessPoint P ξ Up u k width hξ hξh hu hRUp hUp hw N)
    (H : ℝ)
    (hH : (data P ξ Up u k width hξ hξh hu hRUp hUp hw N Z.point.range).U< H)
    (upperBid : ℝ→ℝ) (hb : Measurable upperBid) (hf : ∀v,cutoff N< v→ H≤ upperBid v) :
    Market P ξ Up u k width hξ hξh hu hRUp hUp hw N :=
  ⟨Z.point,Z.common_atoms,Z.species_atoms,H,hH,upperBid,hb,hf⟩

namespace Market
variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {N : ℕ} (A : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N)

def forget : OrderedSourcePartialCountLaws.Market P ξ Up u k width hξ hξh hu hRUp hUp hw N where
  point:=A.point
  H:=A.H
  upper_gap:=A.upper_gap
  upperBid:=A.upperBid
  upperBid_measurable:=A.upperBid_measurable
  upper_floor:=A.upper_floor

abbrev D : Data:=data P ξ Up u k width hξ hξh hu hRUp hUp hw N A.point.range
abbrev sequence : Sequence A.D P (cutoff N) A.point.range.cutoff_gt_M N:=A.point.sequence

lemma species_real_atomless (q : Fin 3) : NullSingletonClass
    ((ProbabilityMeasure.toMeasure (A.sequence.limit q).1).map (fun x=>(x.2:ℝ))) := A.species_atoms q

lemma common_compact_atomless : NullSingletonClass
    (bidMarginal (OrderedNativeZeroNoiseSource.active A.D P (cutoff N) A.point.range.cutoff_gt_M
      A.sequence.limit).1 : Measure (Icc (1:ℝ) A.D.U)) := by
  letI : NullSingletonClass (ProbabilityMeasure.toMeasure
      (((installOriginal A.D P (cutoff N) A.point.range.cutoff_gt_M).commonLaw
        (bidLaws A.D P (cutoff N) A.point.range.cutoff_gt_M A.sequence.limit)).map
          measurable_subtype_coe.aemeasurable)) := A.common_atoms
  exact ZeroCommonRowLaw.original_common_atomless A.D P (cutoff N)
    A.point.range.cutoff_gt_M A.sequence.limit

lemma low_real_atomless : NullSingletonClass (realLowBidLaw A.point.low.joint.1 : Measure ℝ) :=
  A.point.low.real_atomless

lemma tariff_coefficient : (1-A.D.eta)/2=A.D.ξ := by
  change (1-(1-2*ξ))/2=ξ
  ring

lemma rare_nat : (1-A.D.ξ)*A.D.U+A.D.ξ*A.D.U*((N+1:ℕ)*
    (tailMass P (cutoff N)/(partialMass+tailMass P (cutoff N))))≤A.D.R := by
  simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare

variable (hlow : P.d0<1-ξ)

abbrev native := A.forget.native hlow

lemma original_value : (A.native hlow).F=valueLaw P := rfl

lemma original_joint : (A.native hlow).F⊗ₘ(A.native hlow).σ=
    (OrderedNativeZeroNoiseSource.joint A.D P (cutoff N) A.point.range.cutoff_gt_M
      A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable : Measure _) :=
  OrderedNativeZeroNoiseSource.game_original_joint A.D P (cutoff N) A.point.range.cutoff_gt_M
    (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor (N+1) A.rare_nat

lemma original_profile : userProfileLaw (A.native hlow)=
    Measure.pi (fun _ : Fin (N+1)=>
      (OrderedNativeZeroNoiseSource.joint A.D P (cutoff N) A.point.range.cutoff_gt_M
        A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable : Measure _).prod
          (permLaw 2)) :=
  OrderedNativeZeroNoiseSource.game_original_iid A.D P (cutoff N) A.point.range.cutoff_gt_M
    (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor (N+1) A.rare_nat

def posterior : PosteriorSystem (A.native hlow) :=
  OrderedNativeZeroNoiseSource.posterior A.D P (cutoff N) A.point.range.cutoff_gt_M
    (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor (N+1) A.rare_nat A.tariff_coefficient

theorem proposer_optimal : PosteriorProposerOptimal (A.native hlow) (A.posterior hlow) :=
  OrderedNativeZeroNoiseSource.proposer_optimal A.D P (cutoff N) A.point.range.cutoff_gt_M
    (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor (N+1) A.rare_nat A.tariff_coefficient hlow

theorem all_species_payoff (q : Fin 3) (i : Fin (N+1))
    (x : OrderedSourceFinitePayoffTests.Own A.D P (cutoff N) q) :
    (problem (A.native hlow) i).payoff (x.1:ℝ)
      (bandAction (bidLo_pos A.D q).le (if q=2 then 1 else 2) (by split_ifs <;> omega) x.2)=
      OrderedZeroNoiseFiniteGame.sourcePayoff A.D P (cutoff N) A.point.range.cutoff_gt_M N q
        (A.sequence.limit,x) := by
  letI:=A.common_compact_atomless
  letI:=A.species_real_atomless 2
  exact OrderedZeroPartialSourcePayoff.all_species_payoff A.D P (cutoff N) A.point.range.cutoff_gt_M
    (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor N A.rare_nat
    (NativeLowSourceIC.categories P (cutoff N) A.point.range.cutoff_gt_M.le)
    A.point.low rfl q i x

theorem band_all_labels (q : Fin 3) :
    ∀ᵐx ∂(ProbabilityMeasure.toMeasure (A.sequence.limit q).1),∀i : Fin (N+1),
      ∀b : ActiveBaseBid (bidLo A.D q) (bidHi A.D q),
        (problem (A.native hlow) i).payoff (x.1:ℝ)
          (bandAction (bidLo_pos A.D q).le (if q=2 then 1 else 2) (by split_ifs <;> omega) b)≤
        (problem (A.native hlow) i).payoff (x.1:ℝ)
          (bandAction (bidLo_pos A.D q).le (if q=2 then 1 else 2) (by split_ifs <;> omega) x.2) := by
  letI:=A.species_real_atomless 0
  letI:=A.species_real_atomless 1
  letI:=A.species_real_atomless 2
  filter_upwards [OrderedSourceFixedMarketIC.all_action_optimal A.D P (cutoff N)
    A.point.range.cutoff_gt_M N A.sequence q] with x hx
  intro i b
  rw [A.all_species_payoff hlow q i (x.1,b),A.all_species_payoff hlow q i x]
  exact hx b

theorem bandJoint_all_labels (q : Fin 3) :
    ∀ᵐx ∂(bandJoint (bidLo_pos A.D q).le (if q=2 then 1 else 2)
      (by split_ifs <;> omega) (originalValueLaw P (cutoff N) A.point.range.cutoff_gt_M q)
      (A.sequence.limit q) : Measure (ℝ×JointAction 2)),
      ∀i : Fin (N+1),∀b : ActiveBaseBid (bidLo A.D q) (bidHi A.D q),
        (problem (A.native hlow) i).payoff x.1
          (bandAction (bidLo_pos A.D q).le (if q=2 then 1 else 2) (by split_ifs <;> omega) b)≤
        (problem (A.native hlow) i).payoff x.1 x.2 := by
  let T := fun x : OrderedSourceFinitePayoffTests.Own A.D P (cutoff N) q=>
    ((x.1:ℝ),bandAction (bidLo_pos A.D q).le (if q=2 then 1 else 2)
      (by split_ifs <;> omega) x.2)
  have hT : Measurable T := measurable_fst.subtype_val.prodMk
    ((measurable_bandAction _ _ _).comp measurable_snd)
  have hinj : Function.Injective T := by
    intro x y he
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst he)
    · exact Subtype.ext (congrArg (fun z : ℝ×JointAction 2=> z.2.bid) he)
  exact (hT.measurableEmbedding hinj).ae_map_iff.mpr (A.band_all_labels hlow q)

theorem low_all_labels :
    ∀ᵐx ∂(lowJoint P.originalLowLaw A.point.low.joint : Measure (ℝ×JointAction 2)),
      ∀i : Fin (N+1),(problem (A.native hlow) i).BestResponse x.1 x.2 := by
  exact OrderedNativeLowSourceIC.normalized_low_all_labels P (cutoff N) A.point.range.cutoff_gt_M.le
    (OrderedNativeZeroNoiseSource.regions A.D P (A.forget.low_gap hlow) A.H A.upper_gap) rfl
    N A.D.c A.D.ξ A.D.width A.D.regimeShare A.D.eA A.D.eR A.D.F
    A.D.hξ A.D.hξ1 A.D.hw A.D.regimeShare.2.1 A.D.regimeShare.2.2
    A.point.low (OrderedNativeZeroNoiseSource.partialLaw A.D P (cutoff N) A.point.range.cutoff_gt_M A.sequence.limit)
    (OrderedNativeZeroNoiseSource.active A.D P (cutoff N) A.point.range.cutoff_gt_M A.sequence.limit)
    A.upperBid A.upperBid_measurable A.upper_floor A.forget.rare
    (OrderedNativeZeroNoiseSource.base_duplicate_gap A.D) A.D.eta A.D.heta0 A.D.heta1 A.tariff_coefficient
    A.point.underflow_pos A.point.double_underflow

theorem active_payoff (i : Fin (N+1)) (v : ℝ) (b : Icc (1:ℝ) A.D.U) :
    (problem (A.native hlow) i).payoff v (bandAction (by norm_num) 2 le_rfl b)=
      OrderedZeroNoiseFiniteGame.activeExpected
        (installOriginal A.D P (cutoff N) A.point.range.cutoff_gt_M) N
        (bidLaws A.D P (cutoff N) A.point.range.cutoff_gt_M A.sequence.limit,(v,b)) := by
  letI:=A.common_compact_atomless
  exact OrderedZeroActiveSourcePayoff.active_payoff A.D P (cutoff N) A.point.range.cutoff_gt_M
    (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor N A.forget.rare
    (NativeLowSourceIC.categories P (cutoff N) A.point.range.cutoff_gt_M.le)
    A.point.low rfl i v b

theorem active_payoff_continuous (i : Fin (N+1)) (v : ℝ) :
    Continuous (fun b : Icc (1:ℝ) A.D.U=>
      (problem (A.native hlow) i).payoff v (bandAction (by norm_num) 2 le_rfl b)) := by
  letI:=A.species_real_atomless 0
  letI:=A.species_real_atomless 1
  letI:=A.species_real_atomless 2
  letI:=A.common_compact_atomless
  letI:=OrderedSourceAmbientSequence.common_atomless A.D P (cutoff N) A.point.range.cutoff_gt_M N A.sequence
  let Ds:=installOriginal A.D P (cutoff N) A.point.range.cutoff_gt_M
  let μP:=OrderedSourceAmbientSequence.partialLaw A.D P (cutoff N) A.point.range.cutoff_gt_M A.sequence.limit
  let μA:=OrderedSourceAmbientSequence.commonLaw A.D P (cutoff N) A.point.range.cutoff_gt_M A.sequence.limit
  letI : NullSingletonClass (ProbabilityMeasure.toMeasure
      (SourceAmbientLaws.common Ds (FixedAmbientNoise.zero Ds.eps Ds.heps.le) μA)) :=
    OrderedSourceAmbientSequence.common_atomless A.D P (cutoff N) A.point.range.cutoff_gt_M N A.sequence
  have hf (B H0 H1 : ℕ) (reg low : Bool) :
      Continuous (fun b : Icc (1:ℝ) A.D.U=>
        OrderedSourceFiberIntegrals.zeroActive Ds B H0 H1 reg low μP μA v b) := by
    simpa only [SourceAmbientPayoff.active_zero,OrderedSourceFiberIntegrals.zeroActive] using!
      AmbientZeroContinuity.active Ds B H0 H1 reg low (ContinuousMap.const _ v)
        (ContinuousMap.id _) μP μA
  have he (b : Icc (1:ℝ) A.D.U) := A.active_payoff hlow i v b
  simp_rw [he,OrderedSourcePayoffExpansion.zero_active_expected]
  apply continuous_finsetSum
  intro kind _
  exact continuous_const.mul ((continuous_const.mul (hf _ _ _ false _)).add
    (continuous_const.mul (hf _ _ _ true _)))

theorem active_maximizer (i : Fin (N+1)) (v : ℝ) :
    ∃b : Icc (1:ℝ) A.D.U,∀y : Icc (1:ℝ) A.D.U,
      (problem (A.native hlow) i).payoff v (bandAction (by norm_num) 2 le_rfl y)≤
      (problem (A.native hlow) i).payoff v (bandAction (by norm_num) 2 le_rfl b) := by
  letI : Nonempty (Icc (1:ℝ) A.D.U):=⟨⟨1,le_rfl,A.D.hU⟩⟩
  obtain ⟨b,_,hb⟩:=isCompact_univ.exists_isMaxOn univ_nonempty
    (A.active_payoff_continuous hlow i v).continuousOn
  exact ⟨b,fun y=> hb (mem_univ y)⟩

end Market

theorem eventually_points {ρ κ Amin Amax : ℝ} {Λ : Set (ℝ×ℝ)}
    (hu0 : 0< u) (hk0 : 0< k) (hκ : 0< κ) (hmin : 0< Amin) (hk : k<1/(2*Amax))
    (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)
    (hvalue : Up<2-P.w) (huB : 1+u< Central.B ξ)
    (hUpMargin : Up< Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)< ξ/1000)
    (hgap : 2*Ample.binaryKL (99/200) (1-partialMass/2)<
      jointRate (lowMass P.theta) (activeMass P.theta) partialMass (99/200))
    (hrect : MomentInvariant P ξ ρ Λ) (hder : BulkDerivativeBound P ξ κ Λ)
    (hleading : ∀lam∈Λ,Amin≤ leadingA P ξ lam.1 lam.2 ∧ leadingA P ξ lam.1 lam.2≤ Amax)
    (hρ : relativeError P.zeta u (Central.B ξ)< ρ) :
    ∀ᶠN in atTop,Nonempty (AtomlessPoint P ξ Up u k width hξ hξh hu hRUp hUp hw (N+1)) := by
  have hp := (tendsto_add_atTop_nat 1).eventually
    (OrderedSourceFiniteStartingPoint.eventually_construct P ξ Up u k width hξ hξh hu hRUp hUp hw
      hk0 hlow hwγ hvalue huB hUpMargin hsmall hgap)
  have ha := OrderedAtomConstruction.eventually_atomless P ξ Up u k width hξ hξh hu hRUp hUp hw
    hu0 hk0 hκ hmin hk hlow hwγ hrect hder hleading hρ
  filter_upwards [hp,ha] with N hpoint hatoms
  obtain ⟨Z⟩:=hpoint
  have hZ:=hatoms Z
  exact ⟨⟨Z,hZ.1,hZ.2⟩⟩

theorem exists_native_family {ρ κ Amin Amax : ℝ} {Λ : Set (ℝ×ℝ)}
    (hu0 : 0< u) (hk0 : 0< k) (hκ : 0< κ) (hmin : 0< Amin) (hk : k<1/(2*Amax))
    (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)
    (hvalue : Up<2-P.w) (huB : 1+u< Central.B ξ)
    (hUpMargin : Up< Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)< ξ/1000)
    (hgap : 2*Ample.binaryKL (99/200) (1-partialMass/2)<
      jointRate (lowMass P.theta) (activeMass P.theta) partialMass (99/200))
    (hrect : MomentInvariant P ξ ρ Λ) (hder : BulkDerivativeBound P ξ κ Λ)
    (hleading : ∀lam∈Λ,Amin≤ leadingA P ξ lam.1 lam.2 ∧ leadingA P ξ lam.1 lam.2≤ Amax)
    (hρ : relativeError P.zeta u (Central.B ξ)< ρ)
    (H : ℕ→ℝ) (hH : ∀n,cap ξ k n< H n)
    (upperBid : ℕ→ℝ→ℝ) (hb : ∀n,Measurable (upperBid n))
    (hf : ∀n v,cutoff n< v→ H n≤ upperBid n v) :
    ∃K : ℕ,∃A : ∀j,Market P ξ Up u k width hξ hξh hu hRUp hUp hw (K+j+1),
      (∀j,(A j).H=H (K+j+1) ∧ (A j).upperBid=upperBid (K+j+1)) ∧
      Tendsto (fun j=> K+j+1) atTop atTop := by
  obtain ⟨K,hK⟩:=eventually_atTop.mp
    (eventually_points P ξ Up u k width hξ hξh hu hRUp hUp hw hu0 hk0 hκ hmin hk
      hlow hwγ hvalue huB hUpMargin hsmall hgap hrect hder hleading hρ)
  let Z : ∀j,AtomlessPoint P ξ Up u k width hξ hξh hu hRUp hUp hw (K+j+1):=
    fun j=> Classical.choice (hK (K+j) (Nat.le_add_right K j))
  let A : ∀j,Market P ξ Up u k width hξ hξh hu hRUp hUp hw (K+j+1):=
    fun j=> complete P ξ Up u k width hξ hξh hu hRUp hUp hw (Z j)
      (H (K+j+1)) (hH (K+j+1)) (upperBid (K+j+1)) (hb (K+j+1)) (hf (K+j+1))
  refine ⟨K,A,fun j=>⟨rfl,rfl⟩,?_⟩
  simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
    (tendsto_add_atTop_nat (K+1))

end FCAppendix.Affine.Tail04.OrderedSourceRestrictedNative
