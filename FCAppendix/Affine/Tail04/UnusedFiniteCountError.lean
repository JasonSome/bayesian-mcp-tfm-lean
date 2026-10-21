import FCAppendix.Affine.Tail04.UnusedPublicExpectation

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedFiniteCountError
open MeasureTheory ProbabilityTheory Set Classical
open PublicScenario EqualPrivateSignal LocalHighCommon JoinedHighPolicy
open NativeTypicalCount OriginalFlagCompression MenuError SourceMenuPopulation
open UnusedPublicLaw UnusedEmpiricalGuard CommonFixedRowError
open UnusedPublicPrices UnusedMeanPrices UnusedFocalCountError
open UnusedStrongGuard UnusedPublicExpectation WeightedFlagBound

def scenarioCount (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (b : Fin A→ℝ) (y : ℝ) (s : Scenario A) : CountLaw 2 :=
  actualCount Q.ξ y (mixedReciprocalSum (mixed s) b)
    (price0 Q A H b s) (price1 Q A H b s)

def publicCount (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (b : Fin A→ℝ) (y : ℝ) : CountLaw 2 :=
  FiniteLaw.finiteMix (scenarioLaw Q A H b) (scenarioCount Q A H b y)

def canonicalMixture (Q : PublicScenario.Data) (lam : Bool→ℝ) (y : ℝ) : CountLaw 2 :=
  FiniteLaw.finiteMix (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one)
    (fun reg=> canonicalCount Q.ξ (lam reg) y)

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

variable (hflag : ∀ reg j,sourceFlagProb (PublicScenario.e0 Q reg) Q.B0 (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j))) j=(p reg (r (e j).val):ℝ))

variable (a : ℝ)
  (hbalanceRoom : ∀reg,4*δ reg≤ (∫ x,indicator active x ∂μ)-(fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ) reg)
  (hceiling : ∀reg,populationNumerator ξ ρ (∫ x,indicator active x ∂μ) ((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ) reg) (∫ x,indicator private0 x ∂μ) (share reg)/((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ) reg)+γ≤1-ξ/2-a)

variable (hξpos : 0< ξ) (hξh : ξ<1/2) (hB01 : 1≤ B0)
local notation "lam" => (fun reg : Bool=> populationNumerator ξ ρ abar (mbar reg) hbar (share reg)/(wbar reg))
local notation "C" => (fun reg : Bool=>80/(ξ*(wbar reg))+2/(δ reg))

include hN hactive hprivate0 hprivate1 hp hbid hfair hξ hρ hB0 hBB hw hwγ hγ1 G hQc hQξ hmean0 hmean1 hphysical hroom hbalanceRoom hceiling hξpos hξh hB01 in
theorem output_error (y : ℝ) (hy : y∈Icc (0:ℝ) B0) (f : Fin 3→ℝ)
    (reg : Bool) (u : Fin N→ unitInterval) (target : Fin A)
    (AB : Finset (Fin A)×Finset (Fin A))
    (hAB : (Hybrid.ownerDivision
      (forcedExclusiveSet target (compressedFlags act e (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)))
      (PublicScenario.ownerQuota Q A (H0,H1) reg (target,compressedFlags act e
        (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)))).mass AB≠0) :
    let s:=outputScenario reg ((target,compressedFlags act e
      (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)),AB)
    |(scenarioCount Q A (H0,H1) br y s).expect f-(canonicalCount Q.ξ (lam reg) y).expect f|-
      2*MenuError.oscillation f*(if Crossed Q A (H0,H1) B B0 R Rp width γ a y br s then 1 else 0)≤
      MenuError.oscillation f*(C reg*error μ N active private0 private1 (p reg) bid r u+
        16/((N:ℝ)*(wbar reg))) := by
  dsimp only
  let s:=outputScenario reg ((target,compressedFlags act e
    (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)),AB)
  let E:=error μ N active private0 private1 (p reg) bid r u
  have he0 : 0≤ E := error_nonnegative μ N active private0 private1 (p reg) bid r u
  have hwbar : 0< wbar reg := by linarith [(G reg).radius_pos,(G reg).radius_reciprocal]
  have hosc:=oscillation_nonneg f
  have hcross0 : 0≤2*MenuError.oscillation f*(if Crossed Q A (H0,H1) B B0 R Rp width γ a y br s then 1 else 0) := by
    split_ifs <;> positivity
  by_cases hg : E< δ reg
  · have hs:=output_strong (μ:=μ) (N:=N) (hN:=hN) (active:=active) (private0:=private0) (private1:=private1)
      (hactive:=hactive) (hprivate0:=hprivate0) (hprivate1:=hprivate1) (p:=p) (hp:=hp) (bid:=bid) (hbid:=hbid)
      (r:=r) (hfair:=hfair) (ξ:=ξ) (ρ:=ρ) (B:=B) (B0:=B0) (R:=R) (Rp:=Rp) (width:=width) (γ:=γ)
      (share:=share) (δ:=δ) (hξ:=hξ) (hρ:=hρ) (hB0:=hB0) (hBB:=hBB) (hw:=hw) (hwγ:=hwγ) (hγ1:=hγ1)
      (G:=G) (Q:=Q) (hQc:=hQc) (hQξ:=hQξ) (hmean0:=hmean0) (hmean1:=hmean1) (hphysical:=hphysical)
      (hroom:=hroom) (e:=e) (a:=a) (hbalanceRoom:=hbalanceRoom) (hceiling:=hceiling) reg u hg target AB hAB
    have hpE:=output_price_error (μ:=μ) (N:=N) (hN:=hN) (active:=active) (private0:=private0) (private1:=private1)
      (hactive:=hactive) (hprivate0:=hprivate0) (hprivate1:=hprivate1) (p:=p) (hp:=hp) (bid:=bid) (hbid:=hbid)
      (r:=r) (hfair:=hfair) (ξ:=ξ) (ρ:=ρ) (B0:=B0) (R:=R) (Rp:=Rp) (width:=width) (γ:=γ)
      (share:=share) (δ:=δ) (hξ:=hξ) (hρ:=hρ) (hB0:=hB0) (hw:=hw) (hwγ:=hwγ)
      (G:=G) (Q:=Q) (hQc:=hQc) (hQξ:=hQξ) (hmean0:=hmean0) (hmean1:=hmean1) (hphysical:=hphysical)
      (e:=e) reg u hg target AB hAB
    have hsmall : 10*E/(wbar reg)≤ γ := (div_le_iff₀ hwbar).mpr (by linarith [(G reg).radius_margin])
    have hL:= (G reg).mean_margins hξ.1 (integral_nonneg fun x=>(indicator_bounds private0 x).1)
    have hγ0 : 0≤ γ := hw.le.trans hwγ
    have h0 : (1-ξ)*B0≤ price0 Q A (H0,H1) br s := by
      linarith [(abs_le.mp hpE.2.2.1).1,hL.2.1]
    have h1 : (1-ξ)*B0≤ price1 Q A (H0,H1) br s := by
      linarith [(abs_le.mp hpE.2.2.2).1,hL.2.1]
    have hz:=all_nonnegative_bid_count_error f hξpos hξh hB01 hy hpE.1 h0 h1
      (show (1-ξ)*B0≤ lam reg by linarith [hL.2.1])
    have hi : (if Crossed Q A (H0,H1) B B0 R Rp width γ a y br s then (1:ℝ) else 0)=
        (if BetweenPrices (price0 Q A (H0,H1) br s) y (price1 Q A (H0,H1) br s) then 1 else 0) := by
      have hsafe : StrongSafe Q A (H0,H1) B B0 R Rp width γ a br s := hs
      simp only [Crossed,hsafe,true_and]
    have hprices : (4/ξ)*(|price0 Q A (H0,H1) br s-lam reg|+
        |price1 Q A (H0,H1) br s-lam reg|)≤80/(ξ*(wbar reg))*E := by
      have hh:=mul_le_mul_of_nonneg_left (add_le_add hpE.2.2.1 hpE.2.2.2)
        (div_nonneg (by norm_num : (0:ℝ)≤4) hξ.1)
      convert! hh using 1
      ring
    have hextra : 0≤2/(δ reg)*E := mul_nonneg (div_nonneg (by norm_num) (G reg).radius_pos.le) he0
    change |_ - _|-_≤_
    rw [scenarioCount,hQξ]
    rw [hi]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hprices hpE.2.1) hosc]
  · have hE : δ reg≤ E := le_of_not_gt hg
    have htwo : 2≤2/(δ reg)*E := by
      have hone : 1≤ E/(δ reg) := (le_div_iff₀ (G reg).radius_pos).mpr (by simpa only [one_mul] using hE)
      have hh := mul_le_mul_of_nonneg_left hone (by norm_num : (0:ℝ)≤2)
      convert! hh using 1 <;> ring
    have hrest : 0≤80/(ξ*(wbar reg))*E+16/((N:ℝ)*(wbar reg)) := by positivity
    have hh:=count_expect_difference_bound (scenarioCount Q A (H0,H1) br y s) (canonicalCount Q.ξ (lam reg) y) f
    nlinarith

include hN hactive hprivate0 hprivate1 hp hbid hfair hξ hρ hB0 hBB hw hwγ hγ1 G hQc hQξ hmean0 hmean1 hphysical hroom hflag hbalanceRoom hceiling hξpos hξh hB01 in
theorem public_count_error (hA : 0< A) (y : ℝ) (hy : y∈Icc (0:ℝ) B0) (f : Fin 3→ℝ) :
    |(publicCount Q A (H0,H1) br y).expect f-(canonicalMixture Q lam y).expect f|≤
      MenuError.oscillation f*((1-Q.θ)*(C false*averageError μ N active private0 private1 (p false) bid r+
          16/((N:ℝ)*(wbar false)))+
        Q.θ*(C true*averageError μ N active private0 private1 (p true) bid r+
          16/((N:ℝ)*(wbar true))))+
      2*MenuError.oscillation f*(scenarioLaw Q A (H0,H1) br).prob
        (Crossed Q A (H0,H1) B B0 R Rp width γ a y br) := by
  let g : Scenario A→ℝ:=fun s=>
    |(scenarioCount Q A (H0,H1) br y s).expect f-(canonicalCount Q.ξ (lam (regime s)) y).expect f|-
      2*MenuError.oscillation f*(if Crossed Q A (H0,H1) B B0 R Rp width γ a y br s then 1 else 0)
  let d : Bool→(Fin N→ unitInterval)→ℝ:=fun reg u=>
    MenuError.oscillation f*(C reg*error μ N active private0 private1 (p reg) bid r u+16/((N:ℝ)*(wbar reg)))
  have hd (reg : Bool) : Measurable (d reg) :=
    ((((measurable_error μ N active private0 private1 hactive hprivate0 hprivate1
      (p reg) (hp reg) bid hbid).comp (measurable_const.prodMk measurable_id)).const_mul _).add_const _).const_mul _
  have hi (reg : Bool) : Integrable (d reg) (Measure.pi (fun _ : Fin N=>(volume:Measure unitInterval))) :=
    (((integrable_error μ N hN active private0 private1 hactive hprivate0 hprivate1
      (p reg) (hp reg) bid hbid r).const_mul _).add (integrable_const _)).const_mul _
  have hb : ∀reg u target AB,
      (Hybrid.ownerDivision (forcedExclusiveSet target (compressedFlags act e
        (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)))
        (PublicScenario.ownerQuota Q A (H0,H1) reg (target,compressedFlags act e
          (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)))).mass AB≠0 →
      g (outputScenario reg ((target,compressedFlags act e
        (OriginalFlagMeasure.flags (fun j=> p reg (r j)) u)),AB))≤ d reg u := by
    intro reg u target AB hAB
    exact output_error (μ:=μ) (N:=N) (hN:=hN) (active:=active) (private0:=private0) (private1:=private1)
      (hactive:=hactive) (hprivate0:=hprivate0) (hprivate1:=hprivate1) (p:=p) (hp:=hp) (bid:=bid) (hbid:=hbid)
      (r:=r) (hfair:=hfair) (ξ:=ξ) (ρ:=ρ) (B:=B) (B0:=B0) (R:=R) (Rp:=Rp) (width:=width) (γ:=γ)
      (share:=share) (δ:=δ) (hξ:=hξ) (hρ:=hρ) (hB0:=hB0) (hBB:=hBB) (hw:=hw) (hwγ:=hwγ) (hγ1:=hγ1)
      (G:=G) (Q:=Q) (hQc:=hQc) (hQξ:=hQξ) (hmean0:=hmean0) (hmean1:=hmean1) (hphysical:=hphysical)
      (hroom:=hroom) (e:=e) (a:=a) (hbalanceRoom:=hbalanceRoom) (hceiling:=hceiling)
      (hξpos:=hξpos) (hξh:=hξh) (hB01:=hB01) y hy f reg u target AB hAB
  have he:=expect_le_full_flags Q A hA (H0,H1) br act e (fun reg j=> p reg (r j)) hflag g d hd hi hb
  have hdI (reg : Bool) : (∫u,d reg u ∂Measure.pi (fun _ : Fin N=>(volume:Measure unitInterval)))=
      MenuError.oscillation f*(C reg*averageError μ N active private0 private1 (p reg) bid r+16/((N:ℝ)*(wbar reg))) := by
    rw [integral_const_mul,integral_add
      ((integrable_error μ N hN active private0 private1 hactive hprivate0 hprivate1
        (p reg) (hp reg) bid hbid r).const_mul _) (integrable_const _),integral_const_mul,
      integral_error μ N hN active private0 private1 hactive hprivate0 hprivate1 (p reg) (hp reg) bid hbid r]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
  have hcan : (scenarioLaw Q A (H0,H1) br).expect
      (fun s=>(canonicalCount Q.ξ (lam (regime s)) y).expect f)=(canonicalMixture Q lam y).expect f := by
    rw [scenario_expect Q A hA (H0,H1) br,canonicalMixture,FiniteLaw.expect_finiteMix]
    apply FiniteLaw.expect_congr
    intro reg
    simp only [outputScenario,regime,FiniteLaw.expect_const]
  have habs:=(scenarioLaw Q A (H0,H1) br).abs_expect_le
    (fun s=>(scenarioCount Q A (H0,H1) br y s).expect f-(canonicalCount Q.ξ (lam (regime s)) y).expect f)
  rw [FiniteLaw.expect_sub,hcan,←FiniteLaw.expect_finiteMix] at habs
  rw [hdI false,hdI true] at he
  simp only [g,FiniteLaw.expect_sub,FiniteLaw.expect_const_mul,←FiniteLaw.prob_eq_expect] at he
  dsimp only [publicCount]
  linarith

end FCAppendix.Affine.Tail04.UnusedFiniteCountError
