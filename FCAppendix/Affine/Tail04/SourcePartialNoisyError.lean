import FCAppendix.Affine.Tail04.SourcePartialPublicGuard
import FCAppendix.Affine.Tail04.PartialFinitePayoff
import FCAppendix.Affine.Tail04.NativeNoisyBindings

noncomputable section
namespace FCAppendix.Affine.Tail04.SourcePartialNoisyError
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter Topology
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint NativeNoisySource NativeNoisyBindings
open MenuError SourceMenuPopulation SourceMomentRectangle SourceMenuError
open NativePartialDeviation PartialFinitePayoff

private lemma castMarketRare {N : ℕ} {x y p q : ℝ}
    (h : x+y*((N+1:ℝ)*p)≤q) : x+y*((((N+1:ℕ):ℝ))*p)≤q := by
  simpa only [Nat.cast_add,Nat.cast_one] using h

variable (P : ValueParameters) (ξ u Up U width : ℝ) (N : ℕ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u) (huU : 1+u≤ U)
  (hRUp : Central.R ξ≤ Up) (hUp : Up<1) (hUB : U< Central.B ξ) (hw : 0< width)

local notation "cN" => iidCapacity (99/200) N
local notation "Dbase" => SourceNoisyData.data P ξ u Up U width cN
  hξ hξh hu huU hRUp hUp hUB hw

variable (eps : ℝ) (heps : 0< eps) (hbudget : eps< ((SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw)).eps)
local notation "D" => atNoise Dbase eps heps hbudget

variable (t : ℝ) (ht : P.M< t) (hdR : P.d0< ((atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)).R) (H : ℝ) (hBH : ((atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)).B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile (atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget) P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v)
  (hrare : (1-((atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)).ξ)*((atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)).B+((atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)).ξ*((atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)).B*((N+1:ℝ)*
    ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/(partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ ((atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)).R)

local notation "E" => regions D P hdR H hBH
local notation "K" => localData D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
local notation "Γ₀" => coreGame D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
local notation "Γ" => game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)

variable (hN : 0< N)
  (huB : 1+bulkPhysicalWidth (atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)< Central.B ξ)
  (hRp : ((atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)).V≤ Central.R ξ+ξ/1000)
  (hsmall : relativeError P.zeta (bulkPhysicalWidth (atNoise (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) eps heps hbudget)) (Central.B ξ)≤ ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : width≤ γ ξ)
  (hroom : ∀ reg,8/(N:ℝ)≤ radius ξ (centerMoment P reg))
  (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 ξ (iidCapacity (99/200) N) cats P.originalLowLaw)
  (hL : πL=L.joint)

lemma core_joint :
    (Γ₀).F⊗ₘ(Γ₀).σ=ProbabilityMeasure.toMeasure (originalJoint P t ht.le (E).R (E).Rp (E).U
      ((E).d_nonneg.trans (E).d_lt_R.le) πL (partialPhysical D P t ht π)
      (activePhysical D P t ht π) upperBid hupperBid) :=
  game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) (NativeNoisyBindings.rare_cast D P t N hrare)

include hN huB hRp hsmall hmSmall hwγ hroom cats L hL in
theorem source_badMass : ∀ i : Fin (N+1),
    badMass K Γ₀ i≤ SourcePartialPublicGuard.badBound P ξ N := by
  intro i
  exact SourcePartialPublicGuard.source_badMass (N:=N) P E rfl t ht (bulkPhysicalWidth D)
    (bulkPhysicalWidth_nonneg D) (bulkPhysicalWidth_le D) πL
    (partialPhysical D P t ht π) (bulkPhysical D P t ht π) (tailPhysical D P t ht π)
    upperBid hupperBid hfloor ξ width hξ hξh hw
      (by simpa only [upperMass,Nat.cast_add,Nat.cast_one] using! hrare) (duplicate_gap D)
    Γ₀ (core_joint P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare)
    hN huB (D).hUF rfl hRp hsmall hmSmall hwγ hroom cats L hL i

include cats L hL in
theorem source_serviceProb : ∀ i : Fin (N+1),1-P.theta≤ serviceProb K Γ₀ i := by
  intro i
  exact SourcePartialPublicGuard.source_serviceProb (N:=N) P E rfl t ht (bulkPhysicalWidth D)
    (bulkPhysicalWidth_le D) πL (partialPhysical D P t ht π)
    (bulkPhysical D P t ht π) (tailPhysical D P t ht π)
    upperBid hupperBid hfloor ξ width hξ hξh hw
      (by simpa only [upperMass,Nat.cast_add,Nat.cast_one] using! hrare) (duplicate_gap D)
    Γ₀ (core_joint P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare)
    cats L hL i

def valueBound (P : ValueParameters) : ℝ := |2-P.w|+|2+P.w|

lemma partial_value_abs (v : Icc (2-P.w) (2+P.w)) : |(v:ℝ)|≤ valueBound P := by
  apply abs_le.mpr
  constructor
  · dsimp [valueBound]
    linarith [v.2.1,neg_abs_le (2-P.w),abs_nonneg (2+P.w)]
  · dsimp [valueBound]
    linarith [v.2.2,le_abs_self (2+P.w),abs_nonneg (2-P.w)]

include hξ in
theorem eventually_downward_margin (κ : ℝ) (hκ : 0< κ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2*(valueBound P+1)*SourcePartialPublicGuard.badBound P ξ n< κ*(1-P.theta) := by
  have hlim := (SourcePartialPublicGuard.badBound_tendsto_zero P hξ).const_mul
    (2*(valueBound P+1))
  have hpos : 0< κ*(1-P.theta) := mul_pos hκ (by linarith [P.theta_small])
  exact hlim.eventually (gt_mem_nhds (by simpa only [mul_zero] using! hpos))

include hN huB hRp hsmall hmSmall hwγ hroom cats L hL in
theorem source_downward_gain (i : Fin (N+1))
    (v : Icc (2-P.w) (2+P.w)) (κ : ℝ) (hκ : 0≤ κ)
    (a b : Icc (D).R (D).V) (hab : κ≤(b:ℝ)-(a:ℝ)) :
    κ*(1-P.theta)-2*(valueBound P+1)*SourcePartialPublicGuard.badBound P ξ N≤
      (problem Γ i).payoff v (RawRoutes.action a ((D).hR.le.trans a.2.1) 1)-
      (problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) 1) := by
  rw [sourceGame_problem D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare]
  exact uniform_lower_price_gain K Γ₀ (fun _ => rfl) (D).eta (D).heta0 (D).heta1 rfl rfl
    i v (valueBound P) (1-P.theta) (SourcePartialPublicGuard.badBound P ξ N) κ
    (partial_value_abs P v) (by linarith [P.theta_small])
    (source_serviceProb P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare cats L hL i)
    (source_badMass P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare
      hN huB hRp hsmall hmSmall hwγ hroom cats L hL i) hκ a b hab

include hN huB hRp hsmall hmSmall hwγ hroom cats L hL in
theorem source_broadcast_penalty (i : Fin (N+1))
    (v : Icc (2-P.w) (2+P.w)) (b : Icc (D).R (D).V) :
    (problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) 2)-
      (problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) 1)≤
        -(1-2*ξ)*Central.R ξ*(1-P.theta)+
          (2*(valueBound P+1)+(1-2*ξ))*SourcePartialPublicGuard.badBound P ξ N := by
  rw [sourceGame_problem D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare]
  exact uniform_broadcast_penalty K Γ₀ (fun _ => rfl) (D).eta (D).heta0 (D).heta1 rfl rfl
    i v (valueBound P) (1-P.theta) (SourcePartialPublicGuard.badBound P ξ N)
    (partial_value_abs P v) (by linarith [P.theta_small])
    (source_serviceProb P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare cats L hL i)
    (source_badMass P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare
      hN huB hRp hsmall hmSmall hwγ hroom cats L hL i) b

include hN huB hRp hsmall hmSmall hwγ hroom cats L hL in
theorem source_singleton_lower (i : Fin (N+1))
    (v : Icc (2-P.w) (2+P.w)) (b : Icc (D).R (D).V) (hvalue : (D).V≤2-P.w) :
    (2-P.w-(D).V)*(1-P.theta)-(valueBound P+1)*SourcePartialPublicGuard.badBound P ξ N≤
      (problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) 1) := by
  rw [sourceGame_problem D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare]
  exact uniform_singleton_positive_margin K Γ₀ (fun _ => rfl) (D).eta (D).heta0 (D).heta1 rfl rfl
    i v (valueBound P) (2-P.w) (1-P.theta) (SourcePartialPublicGuard.badBound P ξ N)
    (partial_value_abs P v) v.2.1 hvalue (by linarith [P.theta_small])
    (source_serviceProb P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare cats L hL i)
    (source_badMass P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare
      hN huB hRp hsmall hmSmall hwγ hroom cats L hL i) b

include hN huB hRp hsmall hmSmall hwγ hroom cats L hL in
theorem source_partial_routes (i : Fin (N+1))
    (v : Icc (2-P.w) (2+P.w)) (b : Icc (D).R (D).V)
    (hvalue : (D).V≤2-P.w)
    (hempty : (valueBound P+1)*SourcePartialPublicGuard.badBound P ξ N<
      (2-P.w-(D).V)*(1-P.theta))
    (hdouble : (2*(valueBound P+1)+(1-2*ξ))*SourcePartialPublicGuard.badBound P ξ N<
      (1-2*ξ)*Central.R ξ*(1-P.theta)) :
    ∀ k : Fin 3,k≠1 →
      (problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) k)<
        (problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) 1) := by
  intro k hk
  fin_cases k
  · have hz := (RawRoutes.all_route_payoffs Γ i b ((D).hR.le.trans b.2.1)
      (D).eta (D).heta0 (D).heta1 rfl rfl v).1
    have hp := source_singleton_lower P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare
      hN huB hRp hsmall hmSmall hwγ hroom cats L hL i v b hvalue
    change (problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) 0)<_
    exact hz.trans_lt (by linarith only [hp,hempty])
  · exact (hk rfl).elim
  · have hp := source_broadcast_penalty P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
      eps heps hbudget t ht hdR H hBH πL π upperBid hupperBid hfloor hrare
      hN huB hRp hsmall hmSmall hwγ hroom cats L hL i v b
    change (problem Γ i).payoff v (RawRoutes.action b ((D).hR.le.trans b.2.1) 2)<_
    linarith only [hp,hdouble]

end FCAppendix.Affine.Tail04.SourcePartialNoisyError
