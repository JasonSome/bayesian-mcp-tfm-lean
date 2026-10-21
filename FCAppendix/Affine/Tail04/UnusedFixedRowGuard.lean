import FCAppendix.Affine.Tail04.UnusedPublicLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedFixedRowGuard
open MeasureTheory ProbabilityTheory Set Classical
open PublicScenario EqualPrivateSignal LocalHighCommon JoinedHighPolicy
open NativeTypicalCount OriginalFlagCompression MenuError SourceMenuPopulation
open UnusedPublicLaw UnusedEmpiricalGuard CommonFixedRowError

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  (N : ℕ) (hN : 0< N) (active private0 private1 : X→ Bool)
  (hactive : Measurable active) (hprivate0 : Measurable private0) (hprivate1 : Measurable private1)
  (p : Bool→ X→ unitInterval) (hp : ∀ reg,Measurable (p reg))
  (bid : X→ℝ) (hbid : Measurable bid) (r : Fin N→ X)
  (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ))
  (ξ ρ B B0 R Rp width γ : ℝ) (share δ : Bool→ℝ)
  (hξ : ξ∈Icc (0:ℝ) 1) (hρ : ρ∈Icc (0:ℝ) 1) (hB0 : 0≤ B0) (hBB : B≤ B0)
  (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1)

variable (G : ∀ reg,GuardInterior ξ (share reg) ρ B0 R Rp γ (δ reg)
    (∫ x,indicator active x ∂μ) ((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ) reg) (∫ x,indicator private0 x ∂μ) ((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ) reg) reg)
  (Q : PublicScenario.Data) (hQc : Q.c=iidCapacity ρ N) (hQξ : Q.ξ=ξ)
  (hmean0 : ∀ reg,privateMean (privateCount N (markedRow N r) private0 (fun _ => 0)) reg (Q.marksLaw (privateCount N (markedRow N r) private0 (fun _ => 0)))=share reg*(privateCount N (markedRow N r) private0 (fun _ => 0)))
  (hmean1 : ∀ reg,privateMean (privateCount N (markedRow N r) private1 (fun _ => 0)) reg (Q.marksLaw (privateCount N (markedRow N r) private1 (fun _ => 0)))=share reg*(privateCount N (markedRow N r) private1 (fun _ => 0)))
  (hphysical : ∀ j,active (r j)=true → 1≤ bid (r j))
  (hroom : ∀ reg,2*ξ/((N:ℝ)*((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ) reg))≤ γ)
  {A : ℕ} (e : Fin A≃Active (fun j : Fin N => active (r j)))

variable (hflag : ∀ reg j,sourceFlagProb (PublicScenario.e0 Q reg) Q.B0 (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j))) j=(p reg (r (e j).val):ℝ))

include hN hactive hprivate0 hprivate1 hp hbid hfair hξ hρ hB0 hBB hw hwγ hγ1 G hQc hQξ hmean0 hmean1 hphysical hroom hflag in
theorem probability_bound :
    (scenarioLaw Q A ((privateCount N (markedRow N r) private0 (fun _ => 0)),(privateCount N (markedRow N r) private1 (fun _ => 0))) (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j)))).prob
      (fun s => ¬Safe Q A ((privateCount N (markedRow N r) private0 (fun _ => 0)),(privateCount N (markedRow N r) private1 (fun _ => 0))) B B0 R Rp width γ (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j))) s)≤
        (1-Q.θ)*averageError μ N active private0 private1 (p false) bid r/(δ false)+
          Q.θ*averageError μ N active private0 private1 (p true) bid r/(δ true) := by
  let bads : Bool→ Set (Fin N→ unitInterval):=fun reg =>
    bad μ N active private0 private1 (p reg) bid (δ:=δ reg) r
  have hb (reg : Bool) : MeasurableSet (bads reg) :=
    measurableSet_bad μ N active private0 private1 hactive hprivate0 hprivate1
      (p reg) (hp reg) bid hbid r
  have hpos (reg : Bool) (u : Fin N→ unitInterval) (hu : u∉bads reg) : 0< A := by
    have hh:=positive_active_of_error μ N hN active private0 private1 hactive hprivate0 hprivate1
      (p reg) (hp reg) bid hbid r u hfair (G reg).radius_pos (G reg).radius_mixed
      (lt_of_not_ge hu)
    rwa [active_card (fun j : Fin N => active (r j)) e] at hh
  have hg (reg : Bool) (u : Fin N→ unitInterval) (hu : u∉bads reg) (target : Fin A)
      (AB : Finset (Fin A)×Finset (Fin A))
      (hAB : (Hybrid.ownerDivision
        (forcedExclusiveSet target (compressedFlags (fun j : Fin N => active (r j)) e (OriginalFlagMeasure.flags (fun j => p reg (r j)) u)))
        (PublicScenario.ownerQuota Q A ((privateCount N (markedRow N r) private0 (fun _ => 0)),(privateCount N (markedRow N r) private1 (fun _ => 0))) reg (target,compressedFlags (fun j : Fin N => active (r j)) e
          (OriginalFlagMeasure.flags (fun j => p reg (r j)) u)))).mass AB≠0) :
      Safe Q A ((privateCount N (markedRow N r) private0 (fun _ => 0)),(privateCount N (markedRow N r) private1 (fun _ => 0))) B B0 R Rp width γ (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j)))
        (outputScenario reg ((target,compressedFlags (fun j : Fin N => active (r j)) e
          (OriginalFlagMeasure.flags (fun j => p reg (r j)) u)),AB)) := by
    have hAB' : (Hybrid.ownerDivision
        (forcedExclusiveSet target (compressedFlags (fun j : Fin N => active (r j)) e (OriginalFlagMeasure.flags (fun j => p reg (r j)) u)))
        ((countParameters A (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0)) (iidCapacity ρ N) ξ reg (Q.marksLaw (privateCount N (markedRow N r) private0 (fun _ => 0))) (Q.marksLaw (privateCount N (markedRow N r) private1 (fun _ => 0)))).owner0
          (targetMixedSet target (compressedFlags (fun j : Fin N => active (r j)) e
            (OriginalFlagMeasure.flags (fun j => p reg (r j)) u))).card)).mass AB≠0 := by
      simpa only [ownerQuota,hQc,hQξ] using hAB
    have hh:=output_guard μ N hN active private0 private1 hactive hprivate0 hprivate1
      (p reg) (hp reg) bid hbid r hfair ξ (share reg) ρ B B0 R Rp width γ (δ reg)
      hξ hρ hB0 hBB hw hwγ hγ1 reg (G reg) (Q.marksLaw (privateCount N (markedRow N r) private0 (fun _ => 0))) (Q.marksLaw (privateCount N (markedRow N r) private1 (fun _ => 0)))
      (hmean0 reg) (hmean1 reg) hphysical (hroom reg) e u target AB hAB' (lt_of_not_ge hu)
    simpa only [Safe,PublicWeightLaw.weight,outputScenario,regime,mixed,owner0,owner1,hQc,hQξ] using hh
  have hh:=scenario_probability_le_full_flags Q A ((privateCount N (markedRow N r) private0 (fun _ => 0)),(privateCount N (markedRow N r) private1 (fun _ => 0))) (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j))) (fun j : Fin N => active (r j)) e
    (fun reg j => p reg (r j)) hflag
    (Safe Q A ((privateCount N (markedRow N r) private0 (fun _ => 0)),(privateCount N (markedRow N r) private1 (fun _ => 0))) B B0 R Rp width γ (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j)))) bads hb hpos hg
  have h0:=bad_probability μ N hN active private0 private1 hactive hprivate0 hprivate1
    (p false) (hp false) bid hbid (G false).radius_pos r
  have h1:=bad_probability μ N hN active private0 private1 hactive hprivate0 hprivate1
    (p true) (hp true) bid hbid (G true).radius_pos r
  apply hh.trans
  have ht0:=Q.θ_nonneg
  have ht1:=Q.θ_le_one
  have hz0:=mul_le_mul_of_nonneg_left h0 (show 0≤1-Q.θ by linarith)
  have hz1:=mul_le_mul_of_nonneg_left h1 ht0
  simpa only [div_eq_mul_inv,mul_assoc] using add_le_add hz0 hz1

end FCAppendix.Affine.Tail04.UnusedFixedRowGuard
