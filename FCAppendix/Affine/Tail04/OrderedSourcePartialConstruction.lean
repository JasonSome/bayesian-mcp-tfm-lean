import FCAppendix.Affine.Tail04.OrderedNativePayoffIC
import FCAppendix.Affine.Tail04.OrderedAtomPartialAtomless
import FCAppendix.Affine.Tail04.OrderedSourcePartialNoisyCap

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourcePartialConstruction
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedNativeNoisySource OrderedOriginalNoisySequence
open MenuError SourceMenuPopulation SourceMomentRectangle SourceMenuError
open OrderedSourcePartialNoisyError CompactSourceBidLaws

private lemma castRare {n : ℕ} {x y p q : ℝ}
    (h : x+y*((((n+1:ℕ):ℝ))*p)≤q) : x+y*((n+1:ℝ)*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h

variable (P : ValueParameters) (ξ u Up U width : ℝ) (N : ℕ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u) (huU : 1+u≤ U)
  (hRUp : Central.R ξ≤ Up) (hUp : Up<1) (hUB : U< Central.B ξ) (hw : 0< width)

local notation "cN" => iidCapacity (99/200) N
local notation "D" => SourceNoisyData.data P ξ u Up U width cN
  hξ hξh hu huU hRUp hUp hUB hw

variable (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).R) (H : ℝ) (hBH : (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).B< H)
  (hfloor : ∀ v,t< v→ H≤ upperBid v)
  (hrare : (1-(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).ξ)*(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).B+(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).ξ*(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).R)
  (hN : 0< N) (hc : 0< (iidCapacity (99/200) N)) (hcm : (iidCapacity (99/200) N)< N+1)
  (hlow : P.d0<1-ξ) (hvalue : (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).V<2-P.w)
  (huB : 1+bulkPhysicalWidth (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw)< Central.B ξ)
  (hRp : (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).V≤ Central.R ξ+ξ/1000)
  (hsmall : relativeError P.zeta (bulkPhysicalWidth (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw)) (Central.B ξ)≤ ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : width≤ γ ξ)
  (hroom : ∀ reg,8/(N:ℝ)≤ radius ξ (centerMoment P reg))
  (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 ξ (iidCapacity (99/200) N) cats P.originalLowLaw)
  (hL : πL=L.joint)
  (hgap : Central.R ξ< Up)
  (hmargin : 2*(valueBound P+1)*(2*SourcePartialPublicGuard.badBound P ξ N)<
    ((Up-Central.R ξ)/2)*(1-P.theta))

lemma sequence_bulk_width_le (S : Sequence D P t ht N) (j : ℕ) :
    bulkPhysicalWidth (S.data j)≤ bulkPhysicalWidth D := by
  change (1+u)*(1+(S.eps j:ℝ))-1≤(1+u)*(1+(D).eps)-1
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left
    (by linarith [S.noise_small j]) (by linarith)) 1

include πL upperBid hupperBid hdR H hBH hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL hgap hmargin in
theorem sequence_partial_strip (S : Sequence D P t ht N) (j : ℕ) :
    ∀ᵐ x ∂(ProbabilityMeasure.toMeasure (Subtype.val (S.law j 2))),(x.2:ℝ)<(Central.R ξ+Up)/2 := by
  have huj := sequence_bulk_width_le P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    t ht S j
  have herr : relativeError P.zeta (bulkPhysicalWidth (S.data j)) (Central.B ξ)≤ ξ/1000 := by
    have hcoef : 0≤1+2/(Central.B ξ-1) := by
      have hh : 0< Central.B ξ-1 := by unfold Central.B;linarith
      positivity
    exact (add_le_add (le_refl P.zeta) (mul_le_mul_of_nonneg_right huj hcoef)).trans hsmall
  exact OrderedSourcePartialNoisyCap.partial_upper_strip P ξ u Up U width N
    hξ hξh hu huU hRUp hUp hUB hw (S.eps j) (S.noise_positive j) (S.noise_small j)
    t ht hdR H ((S.physical_cap_le j).trans_lt hBH) πL (S.law j)
    upperBid hupperBid hfloor (S.rare_guard hrare j) hN
    ((add_le_add (le_refl 1) huj).trans_lt huB) ((S.partial_cap_le j).trans hRp)
    herr hmSmall hwγ hroom cats L hL hgap hmargin (S.optimal j 2)

include πL upperBid hupperBid hdR H hBH hfloor hrare hN hc hcm hlow hvalue huB hRp hsmall hmSmall hwγ hroom cats L hL hgap hmargin in
theorem partial_limit_atomless (S : Sequence D P t ht N) :
    NullSingletonClass (Sequence.realBaseLaw 2 S.limit : Measure ℝ) := by
  have hidentity : ∀ (j : ℕ) (i : Fin (N+1)) x,
      (∫ z,(problem (OrderedAtomPartialLimit.gameAt D P t ht πL upperBid hupperBid
        hdR H hBH hfloor N hrare S j) i).payoff (x.1:ℝ)
        (OrderedNativeBandCarrierIC.physicalBandAction (S.data j) P t 2 x z)
          ∂(volume : Measure unitInterval))=
        SourceOrderedNoisyFixedPoint.payoff (S.data j) P t ht N 2 (S.law j,x) := by
    intro j i x
    exact OrderedNativePayoffPartial.partial_carrier_payoff (S.data j) P t ht
      hdR H ((S.physical_cap_le j).trans_lt hBH) πL (S.law j)
      upperBid hupperBid hfloor N (castRare (S.rare_guard hrare j)) cats L hL i x
  have hstrip : ∀ᶠ j in atTop,(ProbabilityMeasure.toMeasure (Subtype.val (S.law j 2)))
      {x | (Central.R ξ+Up)/2<(x.2:ℝ)}=0 := by
    apply Eventually.of_forall
    intro j
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [sequence_partial_strip P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      t ht πL upperBid hupperBid hdR H hBH hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom
      cats L hL hgap hmargin S j] with x hx
    exact not_lt_of_ge hx.le
  exact OrderedAtomPartialAtomless.partial_atomless D P t ht πL upperBid hupperBid
    hdR H hBH hfloor N hrare S
    (SourceNoisyData.data_budget_le_one P ξ u Up U width cN hξ hξh hu huU hRUp hUp hUB hw)
    hlow hc hcm hvalue hidentity ((Central.R ξ+Up)/2) (by change (Central.R ξ+Up)/2< Up;linarith)
    hstrip

include πL upperBid hupperBid hdR H hBH hfloor hrare hN hc hcm hlow hvalue huB hRp hsmall hmSmall hwγ hroom cats L hL hgap hmargin in
theorem exists_original_partial_atomless_sequence :
    ∃ S : Sequence D P t ht N,
      NullSingletonClass (Sequence.realBaseLaw 2 S.limit : Measure ℝ) := by
  obtain ⟨S⟩ := OrderedOriginalNoisySequence.exists_sequence D
    (SourceNoisyData.data_budget_le_one P ξ u Up U width cN hξ hξh hu huU hRUp hUp hUB hw)
    P t ht N
  exact ⟨S,partial_limit_atomless P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    t ht πL upperBid hupperBid hdR H hBH hfloor hrare hN hc hcm hlow hvalue
    huB hRp hsmall hmSmall hwγ hroom cats L hL hgap hmargin S⟩

end FCAppendix.Affine.Tail04.OrderedSourcePartialConstruction
