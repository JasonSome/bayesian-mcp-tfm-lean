import FCAppendix.Affine.Tail04.UnusedFiniteCountError
import FCAppendix.Affine.Tail04.OrderedCommonFixedRowError

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedUnusedEmpirical
open MeasureTheory ProbabilityTheory Set Classical
open PublicScenario EqualPrivateSignal LocalHighCommon JoinedHighPolicy
open NativeTypicalCount OriginalFlagCompression MenuError SourceMenuPopulation
open UnusedPublicLaw UnusedEmpiricalGuard CommonFixedRowError
open UnusedPublicPrices UnusedMeanPrices UnusedFiniteCountError

lemma averageError_swap {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (N : ℕ)
    (active private0 private1 : X→Bool) (p : X→unitInterval)
    (bid : X→ℝ) (r : Fin N→X) :
    averageError μ N active private1 private0 p bid r=
      averageError μ N active private0 private1 p bid r := by
  unfold averageError
  rw [OrderedCommonFixedRowError.empiricalAverage_swap]

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
    (∫ x,indicator active x ∂μ) (((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ)) reg) (∫ x,indicator private0 x ∂μ) (((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) reg) reg)
  (Q : PublicScenario.Data) (hQc : Q.c=iidCapacity ρ N) (hQξ : Q.ξ=ξ)
  (hmean0 : ∀ reg,privateMean (min (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0))) reg (Q.marksLaw (min (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0))))=share reg*(min (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0))))
  (hmean1 : ∀ reg,privateMean (max (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0))) reg (Q.marksLaw (max (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0))))=share reg*(max (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0))))
  (hphysical : ∀ j,active (r j)=true → 1≤ bid (r j))
  (hroom : ∀ reg,2*ξ/((N:ℝ)*(((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) reg))≤ γ)
  {A : ℕ} (e : Fin A≃Active (fun j : Fin N => active (r j)))

variable (hflag : ∀ reg j,sourceFlagProb ((PublicScenario.e0 Q) reg) Q.B0 (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j))) j=(p reg (r (e j).val):ℝ))

variable (a : ℝ)
  (hbalanceRoom : ∀reg,4*δ reg≤ (∫ x,indicator active x ∂μ)-((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ)) reg)
  (hceiling : ∀reg,populationNumerator ξ ρ (∫ x,indicator active x ∂μ) (((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ)) reg) (∫ x,indicator private0 x ∂μ) (share reg)/(((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) reg)+γ≤1-ξ/2-a)

include hN hactive hprivate0 hprivate1 hp hbid hfair hξ hρ hB0 hBB hw hwγ hγ1 G hQc hQξ hmean0 hmean1 hphysical hroom hflag hbalanceRoom hceiling in
theorem probability_bound :
    (scenarioLaw Q A ((min (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0))),(max (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0)))) (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j)))).prob
      (fun s=>¬StrongSafe Q A ((min (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0))),(max (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0)))) B B0 R Rp width γ a (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j))) s)≤
        (1-Q.θ)*averageError μ N active private0 private1 (p false) bid r/(δ false)+
          Q.θ*averageError μ N active private0 private1 (p true) bid r/(δ true) := by
  have meanTransport (n k : ℕ) (h : n=k)
      (hm : ∀reg,privateMean n reg (Q.marksLaw n)=share reg*n) :
      ∀reg,privateMean k reg (Q.marksLaw k)=share reg*k := by
    subst n
    exact hm
  by_cases h : (privateCount N (markedRow N r) private0 (fun _ => 0))≤(privateCount N (markedRow N r) private1 (fun _ => 0))
  · simp only [min_eq_left h,max_eq_right h] at ⊢
    have hm0 := meanTransport _ _ (min_eq_left h) hmean0
    have hm1 := meanTransport _ _ (max_eq_right h) hmean1
    exact UnusedStrongGuard.probability_bound μ N hN active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid r hfair ξ ρ B B0 R Rp width γ share δ
      hξ hρ hB0 hBB hw hwγ hγ1 G Q hQc hQξ hm0 hm1 hphysical hroom e hflag
      a hbalanceRoom hceiling
  · have h' : (privateCount N (markedRow N r) private1 (fun _ => 0))≤(privateCount N (markedRow N r) private0 (fun _ => 0)) := (lt_of_not_ge h).le
    simp only [min_eq_right h',max_eq_left h'] at ⊢
    have hm0 := meanTransport _ _ (min_eq_right h') hmean0
    have hm1 := meanTransport _ _ (max_eq_left h') hmean1
    have G' : ∀reg,GuardInterior ξ (share reg) ρ B0 R Rp γ (δ reg)
        (∫ x,indicator active x ∂μ) (((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ)) reg) (∫x,indicator private1 x ∂μ) (((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) reg) reg := by
      intro reg
      rw [←hfair]
      exact G reg
    have hceil' : ∀reg,populationNumerator ξ ρ (∫ x,indicator active x ∂μ) (((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ)) reg)
        (∫x,indicator private1 x ∂μ) (share reg)/(((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) reg)+γ≤1-ξ/2-a := by
      intro reg
      rw [←hfair]
      exact hceiling reg
    have hh := UnusedStrongGuard.probability_bound μ N hN active private1 private0
      hactive hprivate1 hprivate0 p hp bid hbid r hfair.symm ξ ρ B B0 R Rp width γ share δ
      hξ hρ hB0 hBB hw hwγ hγ1 G' Q hQc hQξ hm0 hm1 hphysical hroom e hflag
      a hbalanceRoom hceil'
    simpa only [averageError_swap,←hfair] using hh

variable (hξpos : 0<ξ) (hξh : ξ<1/2) (hB01 : 1≤B0)
include hN hactive hprivate0 hprivate1 hp hbid hfair hξ hρ hB0 hBB hw hwγ hγ1 G hQc hQξ hmean0 hmean1 hphysical hroom hflag hbalanceRoom hceiling hξpos hξh hB01 in
theorem public_count_error (hA : 0< A) (y : ℝ) (hy : y∈Icc (0:ℝ) B0) (f : Fin 3→ℝ) :
    |(publicCount Q A ((min (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0))),(max (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0)))) (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j))) y).expect f-(canonicalMixture Q ((fun reg : Bool=> populationNumerator ξ ρ (∫ x,indicator active x ∂μ) (((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ)) reg) (∫ x,indicator private0 x ∂μ) (share reg)/(((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) reg))) y).expect f|≤
      MenuError.oscillation f*((1-Q.θ)*(((fun reg : Bool=>80/(ξ*(((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) reg))+2/(δ reg))) false*averageError μ N active private0 private1 (p false) bid r+
          16/((N:ℝ)*(((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) false)))+
        Q.θ*(((fun reg : Bool=>80/(ξ*(((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) reg))+2/(δ reg))) true*averageError μ N active private0 private1 (p true) bid r+
          16/((N:ℝ)*(((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) true))))+
      2*MenuError.oscillation f*(scenarioLaw Q A ((min (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0))),(max (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0)))) (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j)))).prob
        (Crossed Q A ((min (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0))),(max (privateCount N (markedRow N r) private0 (fun _ => 0)) (privateCount N (markedRow N r) private1 (fun _ => 0)))) B B0 R Rp width γ a y (compressedBids (fun j : Fin N => active (r j)) e (fun j => bid (r j)))) := by
  have meanTransport (n k : ℕ) (h : n=k)
      (hm : ∀reg,privateMean n reg (Q.marksLaw n)=share reg*n) :
      ∀reg,privateMean k reg (Q.marksLaw k)=share reg*k := by
    subst n
    exact hm
  by_cases h : (privateCount N (markedRow N r) private0 (fun _ => 0))≤(privateCount N (markedRow N r) private1 (fun _ => 0))
  · simp only [min_eq_left h,max_eq_right h] at ⊢
    have hm0 := meanTransport _ _ (min_eq_left h) hmean0
    have hm1 := meanTransport _ _ (max_eq_right h) hmean1
    exact UnusedFiniteCountError.public_count_error μ N hN active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid r hfair ξ ρ B B0 R Rp width γ share δ
      hξ hρ hB0 hBB hw hwγ hγ1 G Q hQc hQξ hm0 hm1 hphysical hroom e hflag
      a hbalanceRoom hceiling hξpos hξh hB01 hA y hy f
  · have h' : (privateCount N (markedRow N r) private1 (fun _ => 0))≤(privateCount N (markedRow N r) private0 (fun _ => 0)) := (lt_of_not_ge h).le
    simp only [min_eq_right h',max_eq_left h'] at ⊢
    have hm0 := meanTransport _ _ (min_eq_right h') hmean0
    have hm1 := meanTransport _ _ (max_eq_left h') hmean1
    have G' : ∀reg,GuardInterior ξ (share reg) ρ B0 R Rp γ (δ reg)
        (∫ x,indicator active x ∂μ) (((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ)) reg) (∫x,indicator private1 x ∂μ) (((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) reg) reg := by
      intro reg
      rw [←hfair]
      exact G reg
    have hceil' : ∀reg,populationNumerator ξ ρ (∫ x,indicator active x ∂μ) (((fun reg : Bool => ∫ x,(p reg x:ℝ)*indicator active x ∂μ)) reg)
        (∫x,indicator private1 x ∂μ) (share reg)/(((fun reg : Bool => ∫ x,(p reg x:ℝ)*reciprocalWeight active bid x ∂μ)) reg)+γ≤1-ξ/2-a := by
      intro reg
      rw [←hfair]
      exact hceiling reg
    have hh := UnusedFiniteCountError.public_count_error μ N hN active private1 private0
      hactive hprivate1 hprivate0 p hp bid hbid r hfair.symm ξ ρ B B0 R Rp width γ share δ
      hξ hρ hB0 hBB hw hwγ hγ1 G' Q hQc hQξ hm0 hm1 hphysical hroom e hflag
      a hbalanceRoom hceil' hξpos hξh hB01 hA y hy f
    simpa only [averageError_swap,←hfair] using hh

end FCAppendix.Affine.Tail04.OrderedUnusedEmpirical
