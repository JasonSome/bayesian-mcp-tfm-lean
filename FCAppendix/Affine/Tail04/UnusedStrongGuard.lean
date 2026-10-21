import FCAppendix.Affine.Tail04.UnusedPublicPrices
import FCAppendix.Affine.Tail04.UnusedFixedRowGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedStrongGuard
open MeasureTheory ProbabilityTheory Set Classical
open PublicScenario EqualPrivateSignal LocalHighCommon JoinedHighPolicy
open NativeTypicalCount OriginalFlagCompression MenuError SourceMenuPopulation
open UnusedPublicLaw UnusedEmpiricalGuard CommonFixedRowError
open UnusedPublicPrices UnusedMeanPrices

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  (N : ℕ) (hN : 0< N) (active private0 private1 : X→ Bool)
  (hactive : Measurable active) (hprivate0 : Measurable private0) (hprivate1 : Measurable private1)
  (p : Bool→ X→ unitInterval) (hp : ∀ reg,Measurable (p reg))
  (bid : X→ℝ) (hbid : Measurable bid) (r : Fin N→ X)
  (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ))
  (ξ ρ B B0 R Rp width γ : ℝ) (share δ : Bool→ℝ)
  (hξ : ξ∈Icc (0:ℝ) 1) (hρ : ρ∈Icc (0:ℝ) 1) (hB0 : 0≤ B0) (hBB : B≤ B0)
  (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1)

local notation "abar" => ∫ x,indicator active x ∂μ
local notation "mbar" => (fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ)
local notation "hbar" => ∫ x,indicator private0 x ∂μ
local notation "wbar" => (fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)
local notation "H0" => privateCount N (markedRow N r) private0 (fun _ => 0)
local notation "H1" => privateCount N (markedRow N r) private1 (fun _ => 0)
local notation "act" => fun j : Fin N => active (r j)

variable (G : ∀ reg,GuardInterior ξ (share reg) ρ B0 R Rp γ (δ reg)
    (∫ x,indicator active x ∂μ) ((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ) reg) (∫ x,indicator private0 x ∂μ) ((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ) reg) reg)
  (Q : PublicScenario.Data) (hQc : Q.c=iidCapacity ρ N) (hQξ : Q.ξ=ξ)
  (hmean0 : ∀ reg,privateMean (privateCount N (markedRow N r) private0 (fun _ => 0)) reg (Q.marksLaw (privateCount N (markedRow N r) private0 (fun _ => 0)))=share reg*(privateCount N (markedRow N r) private0 (fun _ => 0)))
  (hmean1 : ∀ reg,privateMean (privateCount N (markedRow N r) private1 (fun _ => 0)) reg (Q.marksLaw (privateCount N (markedRow N r) private1 (fun _ => 0)))=share reg*(privateCount N (markedRow N r) private1 (fun _ => 0)))
  (hphysical : ∀ j,active (r j)=true → 1≤ bid (r j))
  (hroom : ∀ reg,2*ξ/((N:ℝ)*((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ) reg))≤ γ)
  {A : ℕ} (e : Fin A≃Active (fun j : Fin N => active (r j)))

local notation "br" => compressedBids act e (fun j => bid (r j))

variable (hflag : ∀ reg j,sourceFlagProb ((PublicScenario.e0 Q) reg) Q.B0 (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j))) j=(p reg (r (e j).val):ℝ))

variable (a : ℝ)
  (hbalanceRoom : ∀reg,4*δ reg≤ (∫ x,indicator active x ∂μ)-(fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ) reg)
  (hceiling : ∀reg,populationNumerator ξ ρ (∫ x,indicator active x ∂μ) ((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ) reg) (∫ x,indicator private0 x ∂μ) (share reg)/((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ) reg)+γ≤1-ξ/2-a)

include hN hactive hprivate0 hprivate1 hp hbid hfair hξ hρ hB0 hBB hw hwγ hγ1 G hQc hQξ hmean0 hmean1 hphysical hroom hbalanceRoom hceiling in
theorem output_strong (reg : Bool) (u : Fin N→ unitInterval)
    (hu : error μ N active private0 private1 (p reg) bid r u< δ reg)
    (target : Fin A) (AB : Finset (Fin A)×Finset (Fin A))
    (hAB : (Hybrid.ownerDivision
      (forcedExclusiveSet target (compressedFlags act e (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)))
      (PublicScenario.ownerQuota Q A (H0,H1) reg (target,compressedFlags act e
        (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)))).mass AB≠0) :
    StrongSafe Q A (H0,H1) B B0 R Rp width γ a br
      (outputScenario reg ((target,compressedFlags act e
        (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)),AB)) := by
  let row:=markedRow N r u
  let flags:=compressedFlags act e (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)
  let I:=targetMixedSet target flags
  let target0 : Fin (N+1):=((e target).val).succ
  let M:=flaggedMixedCount N (fun _ : Unit=> row) (fun _=> target0) active (p reg) false ()
  let W:=flaggedReciprocal N (fun _ : Unit=> row) (fun _=> target0) active (p reg) bid 1 false ()
  let q:=clampedOwner (A-M) (share reg*H0) (share reg*H1)
  have hAeq : privateCount N (fun _ : Unit=> row) active ()=A := active_card act e
  have hM : I.card=M := partial_mixed_compression row active (p reg) e target
  have hW : mixedReciprocalSum I br=(N:ℝ)*W :=
    partial_reciprocal_compression row active (p reg) bid e target hN hphysical
  dsimp only [I] at hM hW
  have hMA : M≤ A := hAeq ▸ partial_mixed_le_active N (fun _ : Unit=> row) (fun _=> target0) active (p reg) ()
  have hZ:=guardError_le_error μ N hN active private0 private1 hactive hprivate0 hprivate1
    (p reg) (hp reg) bid hbid r u target0 hfair
  dsimp only at hZ
  erw [hAeq] at hZ
  have hz : guardError N A M H0 H1 W abar (mbar reg) hbar (wbar reg)< δ reg := hZ.trans_lt hu
  have hc:=owner_cards Q A (H0,H1) reg target flags AB hAB
  have hc0 : AB.1.card=q := by
    simpa only [countParameters,TypicalCountParameters.owner0,hmean0 reg,hmean1 reg,hM,clampedOwner,q] using! hc.1
  have hc1 : AB.2.card=A-M-q := by
    simpa only [countParameters,TypicalCountParameters.owner1,TypicalCountParameters.owner0,
      hmean0 reg,hmean1 reg,hM,clampedOwner,q] using! hc.2
  have hAB' : (Hybrid.ownerDivision (forcedExclusiveSet target flags)
      ((countParameters A H0 H1 (iidCapacity ρ N) ξ reg (Q.marksLaw H0) (Q.marksLaw H1)).owner0 I.card)).mass AB≠0 := by
    simpa only [ownerQuota,hQc,hQξ] using hAB
  have hs:=output_guard μ N hN active private0 private1 hactive hprivate0 hprivate1
    (p reg) (hp reg) bid hbid r hfair ξ (share reg) ρ B B0 R Rp width γ (δ reg)
    hξ hρ hB0 hBB hw hwγ hγ1 reg (G reg) (Q.marksLaw H0) (Q.marksLaw H1)
    (hmean0 reg) (hmean1 reg) hphysical (hroom reg) e u target AB hAB' hu
  have hsafe : Safe Q A (H0,H1) B B0 R Rp width γ br
      (outputScenario reg ((target,flags),AB)) := by
    simpa only [Safe,PublicWeightLaw.weight,outputScenario,regime,mixed,owner0,owner1,hQc,hQξ] using! hs
  have he:=price_errors_le_margin N A M H0 H1 hN hMA ξ (share reg) ρ B0 R Rp γ (δ reg)
    W abar (mbar reg) hbar (wbar reg) reg hξ hρ hB0
    (integral_nonneg fun x=>(indicator_bounds private0 x).1) (hw.le.trans hwγ) (G reg) hz
  have hp0 : price0 Q A (H0,H1) br (outputScenario reg ((target,flags),AB))=
      TypicalGuardEndpoints.lambda (iidCapacity ρ N) q M ξ ((N:ℝ)*W) (share reg*H0) := by
    simp only [price0,outputScenario,owner0,regime,mixed,hQc,hQξ,hmean0 reg,hc0,
      WeightedFlagBound.meanMixedPrice,hM,hW,TypicalGuardEndpoints.lambda]
    congr 1
    ring
  have hp1 : price1 Q A (H0,H1) br (outputScenario reg ((target,flags),AB))=
      TypicalGuardEndpoints.lambda (iidCapacity ρ N) (A-M-q) M ξ ((N:ℝ)*W) (share reg*H1) := by
    simp only [price1,outputScenario,owner1,regime,mixed,hQc,hQξ,hmean1 reg,hc1,
      WeightedFlagBound.meanMixedPrice,hM,hW,TypicalGuardEndpoints.lambda]
    congr 1
    ring
  refine ⟨hsafe,?_,?_,?_⟩
  · simpa only [outputScenario,mixed,regime,hmean0 reg,hmean1 reg,←hM] using!
      private_balance N A M H0 H1 hN hMA (share reg) W abar (mbar reg) hbar (wbar reg)
        (δ reg) (G reg).share_mem (hbalanceRoom reg) hz
  · rw [hp0,hQξ]
    linarith [(abs_le.mp he.1).2,hceiling reg]
  · rw [hp1,hQξ]
    linarith [(abs_le.mp he.2).2,hceiling reg]

include hN hactive hprivate0 hprivate1 hp hbid hfair hξ hρ hB0 hw hwγ G hQc hQξ hmean0 hmean1 hphysical in
theorem output_price_error (reg : Bool) (u : Fin N→ unitInterval)
    (hu : error μ N active private0 private1 (p reg) bid r u< δ reg)
    (target : Fin A) (AB : Finset (Fin A)×Finset (Fin A))
    (hAB : (Hybrid.ownerDivision
      (forcedExclusiveSet target (compressedFlags act e (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)))
      (PublicScenario.ownerQuota Q A (H0,H1) reg (target,compressedFlags act e
        (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)))).mass AB≠0) :
    let s:=outputScenario reg ((target,compressedFlags act e
      (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)),AB)
    let W:=mixedReciprocalSum (mixed s) br
    let L:=populationNumerator ξ ρ abar (mbar reg) hbar (share reg)/(wbar reg)
    0< W ∧ 8/W≤16/((N:ℝ)*(wbar reg)) ∧
      |price0 Q A (H0,H1) br s-L|≤10*error μ N active private0 private1 (p reg) bid r u/(wbar reg) ∧
      |price1 Q A (H0,H1) br s-L|≤10*error μ N active private0 private1 (p reg) bid r u/(wbar reg) := by
  dsimp only
  let row:=markedRow N r u
  let flags:=compressedFlags act e (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)
  let I:=targetMixedSet target flags
  let target0 : Fin (N+1):=((e target).val).succ
  let M:=flaggedMixedCount N (fun _ : Unit=> row) (fun _=> target0) active (p reg) false ()
  let W:=flaggedReciprocal N (fun _ : Unit=> row) (fun _=> target0) active (p reg) bid 1 false ()
  let q:=clampedOwner (A-M) (share reg*H0) (share reg*H1)
  have hAeq : privateCount N (fun _ : Unit=> row) active ()=A := active_card act e
  have hM : I.card=M := partial_mixed_compression row active (p reg) e target
  have hW : mixedReciprocalSum I br=(N:ℝ)*W :=
    partial_reciprocal_compression row active (p reg) bid e target hN hphysical
  dsimp only [I] at hM hW
  have hMA : M≤ A := hAeq ▸ partial_mixed_le_active N (fun _ : Unit=> row) (fun _=> target0) active (p reg) ()
  have hZ:=guardError_le_error μ N hN active private0 private1 hactive hprivate0 hprivate1
    (p reg) (hp reg) bid hbid r u target0 hfair
  dsimp only at hZ
  erw [hAeq] at hZ
  have hz : guardError N A M H0 H1 W abar (mbar reg) hbar (wbar reg)< δ reg := hZ.trans_lt hu
  have hc:=owner_cards Q A (H0,H1) reg target flags AB hAB
  have hc0 : AB.1.card=q := by
    simpa only [countParameters,TypicalCountParameters.owner0,hmean0 reg,hmean1 reg,hM,clampedOwner,q] using! hc.1
  have hc1 : AB.2.card=A-M-q := by
    simpa only [countParameters,TypicalCountParameters.owner1,TypicalCountParameters.owner0,
      hmean0 reg,hmean1 reg,hM,clampedOwner,q] using! hc.2
  have he:=price_errors N A M H0 H1 hN hMA ξ (share reg) ρ B0 R Rp γ (δ reg)
    W abar (mbar reg) hbar (wbar reg) reg hξ hρ hB0
    (integral_nonneg fun x=>(indicator_bounds private0 x).1) (hw.le.trans hwγ) (G reg) hz
  have hp0 : price0 Q A (H0,H1) br (outputScenario reg ((target,flags),AB))=
      TypicalGuardEndpoints.lambda (iidCapacity ρ N) q M ξ ((N:ℝ)*W) (share reg*H0) := by
    simp only [price0,outputScenario,owner0,regime,mixed,hQc,hQξ,hmean0 reg,hc0,
      WeightedFlagBound.meanMixedPrice,hM,hW,TypicalGuardEndpoints.lambda]
    congr 1
    ring
  have hp1 : price1 Q A (H0,H1) br (outputScenario reg ((target,flags),AB))=
      TypicalGuardEndpoints.lambda (iidCapacity ρ N) (A-M-q) M ξ ((N:ℝ)*W) (share reg*H1) := by
    simp only [price1,outputScenario,owner1,regime,mixed,hQc,hQξ,hmean1 reg,hc1,
      WeightedFlagBound.meanMixedPrice,hM,hW,TypicalGuardEndpoints.lambda]
    congr 1
    ring
  have hwbar : 0< wbar reg := by linarith [(G reg).radius_pos,(G reg).radius_reciprocal]
  have hWlo : (wbar reg)/2≤ W := by
    have hh:=(guardError_bounds N A M H0 H1 W abar (mbar reg) hbar (wbar reg)).2.2.2.2.2.1
    linarith [(abs_le.mp hh).1,(G reg).radius_reciprocal]
  have hfrac : 8/((N:ℝ)*W)≤16/((N:ℝ)*(wbar reg)) := by
    calc
      _≤8/((N:ℝ)*((wbar reg)/2)) := div_le_div_of_nonneg_left (by norm_num)
        (mul_pos (Nat.cast_pos.mpr hN) (half_pos hwbar))
        (mul_le_mul_of_nonneg_left hWlo (Nat.cast_nonneg N))
      _=_ := by ring
  have herror:=div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hZ (by norm_num : (0:ℝ)≤10)) hwbar.le
  refine ⟨?_,?_,?_,?_⟩
  · change 0< mixedReciprocalSum I br
    rw [hW]
    exact mul_pos (Nat.cast_pos.mpr hN) he.1
  · change 8/mixedReciprocalSum I br≤_
    rwa [hW]
  · rw [hp0]
    exact he.2.1.trans herror
  · rw [hp1]
    exact he.2.2.trans herror

include hN hactive hprivate0 hprivate1 hp hbid hfair hξ hρ hB0 hBB hw hwγ hγ1 G hQc hQξ hmean0 hmean1 hphysical hroom hflag hbalanceRoom hceiling in
theorem probability_bound :
    (scenarioLaw Q A (H0,H1) br).prob
      (fun s=>¬StrongSafe Q A (H0,H1) B B0 R Rp width γ a br s)≤
        (1-Q.θ)*averageError μ N active private0 private1 (p false) bid r/(δ false)+
          Q.θ*averageError μ N active private0 private1 (p true) bid r/(δ true) := by
  let bads : Bool→ Set (Fin N→ unitInterval):=fun reg=>
    bad μ N active private0 private1 (p reg) bid (δ:=δ reg) r
  have hb (reg : Bool) : MeasurableSet (bads reg) :=
    measurableSet_bad μ N active private0 private1 hactive hprivate0 hprivate1
      (p reg) (hp reg) bid hbid r
  have hpos (reg : Bool) (u : Fin N→ unitInterval) (hu : u∉bads reg) : 0< A := by
    have hh:=positive_active_of_error μ N hN active private0 private1 hactive hprivate0 hprivate1
      (p reg) (hp reg) bid hbid r u hfair (G reg).radius_pos (G reg).radius_mixed
      (lt_of_not_ge hu)
    rwa [active_card act e] at hh
  have hg:=fun reg u hu target AB hAB=>
    output_strong μ N hN active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid r hfair
      ξ ρ B B0 R Rp width γ share δ hξ hρ hB0 hBB hw hwγ hγ1 G Q hQc hQξ
      hmean0 hmean1 hphysical hroom e a hbalanceRoom hceiling reg u (lt_of_not_ge hu) target AB hAB
  have hh:=scenario_probability_le_full_flags Q A (H0,H1) br act e (fun reg j=> p reg (r j)) hflag
    (StrongSafe Q A (H0,H1) B B0 R Rp width γ a br) bads hb hpos hg
  have h0:=bad_probability μ N hN active private0 private1 hactive hprivate0 hprivate1
    (p false) (hp false) bid hbid (G false).radius_pos r
  have h1:=bad_probability μ N hN active private0 private1 hactive hprivate0 hprivate1
    (p true) (hp true) bid hbid (G true).radius_pos r
  apply hh.trans
  have hz0:=mul_le_mul_of_nonneg_left h0 (show 0≤1-Q.θ by linarith [Q.θ_le_one])
  have hz1:=mul_le_mul_of_nonneg_left h1 Q.θ_nonneg
  simpa only [div_eq_mul_inv,mul_assoc] using add_le_add hz0 hz1

end FCAppendix.Affine.Tail04.UnusedStrongGuard
