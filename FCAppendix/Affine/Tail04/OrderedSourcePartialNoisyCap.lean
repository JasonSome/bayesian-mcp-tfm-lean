import FCAppendix.Affine.Tail04.OrderedSourcePartialNoisyError
import FCAppendix.Affine.Tail04.OrderedNativePayoffPartial

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourcePartialNoisyCap
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter Topology
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint SourceOrderedNoisyFixedPoint OrderedNativeNoisySource OrderedNativePayoffBindings
open MenuError SourceMenuPopulation SourceMomentRectangle SourceMenuError
open OrderedNativePartialDeviation OrderedPartialFinitePayoff OrderedSourcePartialNoisyError CompactSourceBidLaws

private lemma castRare {ξ B R mass : ℝ} {N : ℕ}
    (h : (1-ξ)*B+ξ*B*((N+1:ℕ)*mass)≤R) :
    (1-ξ)*B+ξ*B*(((N:ℝ)+1)*mass)≤R := by
  simpa only [Nat.cast_add,Nat.cast_one] using h

variable (P : ValueParameters) (ξ u Up U width : ℝ) (N : ℕ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u) (huU : 1+u≤ U)
  (hRUp : Central.R ξ≤ Up) (hUp : Up<1) (hUB : U< Central.B ξ) (hw : 0< width)

local notation "cN" => iidCapacity (99/200) N
local notation "Dbase" => SourceNoisyData.data P ξ u Up U width cN
  hξ hξh hu huU hRUp hUp hUB hw

variable (eps : ℝ) (heps : 0< eps) (hbudget : eps< (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).eps)
local notation "D" => atNoise Dbase eps heps hbudget

variable (t : ℝ) (ht : P.M< t) (hdR : P.d0< (atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget).R) (H : ℝ) (hBH : (atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget).B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile (atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget) P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v)
  (hrare : (1-(atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget).ξ)*(atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget).B+(atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget).ξ*(atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget).B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ (atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget).R)

local notation "E" => regions D P hdR H hBH
local notation "K" => localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N (castRare hrare)
local notation "Γ₀" => coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N (castRare hrare)
local notation "Γ" => game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare

variable (hN : 0< N)
  (huB : 1+bulkPhysicalWidth (atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)< Central.B ξ)
  (hRp : (atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget).V≤ Central.R ξ+ξ/1000)
  (hsmall : relativeError P.zeta (bulkPhysicalWidth (atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)) (Central.B ξ)≤ ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : width≤ γ ξ)
  (hroom : ∀ reg,8/(N:ℝ)≤ radius ξ (centerMoment P reg))
  (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 ξ (iidCapacity (99/200) N) cats P.originalLowLaw)
  (hL : πL=L.joint)

def bottom : Icc (D).R (D).Up := ⟨(D).R,le_rfl,(D).hRUp⟩

lemma physical_bottom_gap (b : Icc (D).R (D).Up) (κ : ℝ) (hκ : 0≤ κ)
    (hb : (D).R+κ≤(b:ℝ)) (z : unitInterval) :
    κ≤(noisyBid (D).hR (D).heps.le (b,z):ℝ)-
      (noisyBid (D).hR (D).heps.le (bottom P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
        eps heps hbudget,z):ℝ) := by
  change κ≤(b:ℝ)*(1+(D).eps*(z:ℝ))-(D).R*(1+(D).eps*(z:ℝ))
  have he : 0≤ (D).eps*(z:ℝ) := mul_nonneg (D).heps.le z.2.1
  nlinarith [mul_nonneg (show 0≤(b:ℝ)-(D).R by linarith) he]

include cats L hL in
lemma actual_averaged_partial_payoff (i : Fin (N+1))
    (v : Icc (2-P.w) (2+P.w)) (b : Icc (D).R (D).Up) :
    (∫ z : unitInterval,OrderedPartialFinitePayoff.pay K Γ₀ i v (noisyBid (D).hR (D).heps.le (b,z)) 1)=
      SourceOrderedNoisyFixedPoint.payoff D P t ht N 2 (π,(v,b)) := by
  have hh := OrderedNativePayoffPartial.partial_payoff D P t ht hdR H hBH πL π
    upperBid hupperBid hfloor N (castRare hrare) cats L hL i (v:ℝ) b
  rw [sourceGame_problem D P t ht hdR H hBH πL π upperBid hupperBid hfloor N (castRare hrare)] at hh
  exact hh

include hdR H hBH πL upperBid hupperBid hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL in
theorem c1_downward_gain (i : Fin (N+1)) (v : Icc (2-P.w) (2+P.w))
    (b : Icc (D).R (D).Up) (κ : ℝ) (hκ : 0≤ κ) (hb : (D).R+κ≤(b:ℝ)) :
    κ*(1-P.theta)-2*(valueBound P+1)*(2*SourcePartialPublicGuard.badBound P ξ N)≤
      SourceOrderedNoisyFixedPoint.payoff D P t ht N 2
        (π,(v,bottom P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw eps heps hbudget))-
      SourceOrderedNoisyFixedPoint.payoff D P t ht N 2 (π,(v,b)) := by
  let a := bottom P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw eps heps hbudget
  have ha : Measurable (fun z : unitInterval => noisyBid (D).hR (D).heps.le (a,z)) :=
    (continuous_noisyBid (D).hR (D).heps.le).measurable.comp (measurable_const.prodMk measurable_id)
  have hb' : Measurable (fun z : unitInterval => noisyBid (D).hR (D).heps.le (b,z)) :=
    (continuous_noisyBid (D).hR (D).heps.le).measurable.comp (measurable_const.prodMk measurable_id)
  have hh := integral_lower_price_gain K Γ₀ (fun _ => rfl) (D).eta (D).heta0 (D).heta1 rfl rfl
    (volume : Measure unitInterval) i v (valueBound P) (1-P.theta)
      ((2*SourcePartialPublicGuard.badBound P ξ N)) κ (partial_value_abs P v)
    (by linarith [P.theta_small])
    (source_serviceProb P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor (castRare hrare) cats L hL i)
    (source_badMass P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor (castRare hrare)
      hN huB hRp hsmall hmSmall hwγ hroom cats L hL i) hκ
    (fun z => noisyBid (D).hR (D).heps.le (a,z)) (fun z => noisyBid (D).hR (D).heps.le (b,z)) ha hb'
    (physical_bottom_gap P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget b κ hκ hb)
  rw [actual_averaged_partial_payoff P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare cats L hL i v a,
    actual_averaged_partial_payoff P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare cats L hL i v b] at hh
  exact hh

include hdR H hBH πL upperBid hupperBid hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL in
theorem partial_base_below (κ : ℝ) (hκ : 0≤ κ)
    (hmargin : 2*(valueBound P+1)*(2*SourcePartialPublicGuard.badBound P ξ N)< κ*(1-P.theta))
    (hC1 : AllActionOptimal (π 2)
      (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N 2 (π,x))) :
    ∀ᵐ x ∂(ProbabilityMeasure.toMeasure (Subtype.val (π 2))),(x.2:ℝ)< (D).R+κ := by
  let i : Fin (N+1) := 0
  let a := bottom P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw eps heps hbudget
  filter_upwards [hC1] with x hx
  by_contra hn
  have hg := c1_downward_gain P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare
    hN huB hRp hsmall hmSmall hwγ hroom cats L hL i x.1 x.2 κ hκ (le_of_not_gt hn)
  have hi := hx a
  linarith

include hdR H hBH πL upperBid hupperBid hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL in
theorem partial_upper_strip (hgap : (D).R< (D).Up)
    (hmargin : 2*(valueBound P+1)*(2*SourcePartialPublicGuard.badBound P ξ N)<
      (((D).Up-(D).R)/2)*(1-P.theta))
    (hC1 : AllActionOptimal (π 2)
      (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N 2 (π,x))) :
    ∀ᵐ x ∂(ProbabilityMeasure.toMeasure (Subtype.val (π 2))),(x.2:ℝ)<((D).R+(D).Up)/2 := by
  have hh := partial_base_below P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare
    hN huB hRp hsmall hmSmall hwγ hroom cats L hL (((D).Up-(D).R)/2) (by linarith) hmargin hC1
  filter_upwards [hh] with x hx
  linarith

include hdR H hBH πL upperBid hupperBid hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL in
theorem exists_noisy_partial_strip (hgap : (D).R< (D).Up)
    (hmargin : 2*(valueBound P+1)*(2*SourcePartialPublicGuard.badBound P ξ N)<
      (((D).Up-(D).R)/2)*(1-P.theta)) :
    ∃ (π' : JointProfile D P t ht)
      (σ : ∀ k : Fin 3,Kernel
        (Hybrid.ActiveValue (valueLo P k) (valueHi P t k))
        (Hybrid.ActiveBaseBid (bidLo D k) (bidHi D k))),
      (∀ k,IsMarkovKernel (σ k)) ∧
      (∀ k,originalValueLaw P t ht k⊗ₘσ k=(ProbabilityMeasure.toMeasure (Subtype.val (π' k)))) ∧
      (∀ k,AllActionOptimal (π' k)
        (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π',x))) ∧
      (∀ k,∀ᵐ v ∂originalValueLaw P t ht k,∀ᵐ b ∂σ k v,
        ∀ b' : Hybrid.ActiveBaseBid (bidLo D k) (bidHi D k),
          SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π',(v,b'))≤
            SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π',(v,b))) ∧
      (∀ᵐ x ∂(ProbabilityMeasure.toMeasure (Subtype.val (π' 2))),(x.2:ℝ)<((D).R+(D).Up)/2) := by
  obtain ⟨π',σ,hσ,hjoint,hopt,hcond⟩ := SourceOrderedNoisyFixedPoint.exists_original_joint_noisy_law D P t ht N
  refine ⟨π',σ,hσ,hjoint,hopt,hcond,?_⟩
  exact partial_upper_strip P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    eps heps hbudget t ht hdR H hBH πL π' upperBid hupperBid hfloor hrare
    hN huB hRp hsmall hmSmall hwγ hroom cats L hL hgap hmargin (hopt 2)

end FCAppendix.Affine.Tail04.OrderedSourcePartialNoisyCap
