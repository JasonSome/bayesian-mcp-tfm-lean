import FCAppendix.Affine.Tail04.CommonFixedRowError

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedCommonFixedRowError
open MeasureTheory ProbabilityTheory Set Classical
open MenuError OriginalFlagCompression CommonFlagCompression CommonFiniteCountError
open CommonFixedRowError NativeTypicalCount EqualPrivateSignal SourceMenuPopulation
open scoped BigOperators

variable {X : Type*} [MeasurableSpace X]

lemma commonEmpiricalError_swap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure X) [IsProbabilityMeasure μ] (N : ℕ)
    (row : Ω→Fin N→X×unitInterval) (active private0 private1 : X→Bool)
    (p : X→unitInterval) (bid : X→ℝ) (x : Ω) :
    commonEmpiricalError μ N row active private1 private0 p bid x=
      commonEmpiricalError μ N row active private0 private1 p bid x := by
  simp only [commonEmpiricalError,Fin.sum_univ_succ,Fin.sum_univ_zero,
    sourceEmpiricalError,sourceBasis,Matrix.cons_val_zero,Matrix.cons_val_succ]
  ring

lemma empiricalAverage_swap (μ : Measure X) [IsProbabilityMeasure μ]
    (N : ℕ) (active private0 private1 : X→Bool)
    (p : X→unitInterval) (bid : X→ℝ) (r : Fin N→X) :
    empiricalAverage μ N active private1 private0 p bid r=
      empiricalAverage μ N active private0 private1 p bid r := by
  unfold empiricalAverage empirical
  apply integral_congr_ae
  exact ae_of_all _ (commonEmpiricalError_swap μ N (markedRow N r)
    active private0 private1 p bid)

section Count
attribute [local irreducible] AllCountActiveFiniteGain.physicalCount FiniteLaw.mixture FiniteLaw.dirac
variable (μ : Measure X) [IsProbabilityMeasure μ] (N : ℕ) (hN : 0<N)
  (active private0 private1 : X→Bool)
  (hactive : Measurable active) (hprivate0 : Measurable private0)
  (hprivate1 : Measurable private1) (p : X→unitInterval) (hp : Measurable p)
  (bid : X→ℝ) (hbid : Measurable bid) (r : Fin N→X)
  (hfair : (∫x,MenuError.indicator private0 x ∂μ)=(∫x,MenuError.indicator private1 x ∂μ))
  (ξ share ρ B R Rp width γ δ : ℝ) (hξ : 0<ξ) (hξ1 : ξ≤1)
  (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤B) (hw : 0<width)
  (hwγ : width≤γ) (hγ1 : γ≤1) (reg : Bool)

local notation "abar" => ∫x,MenuError.indicator active x ∂μ
local notation "mbar" => ∫x,(p x:ℝ)*MenuError.indicator active x ∂μ
local notation "hbar" => ∫x,MenuError.indicator private0 x ∂μ
local notation "wbar" => ∫x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
local notation "H0" => privateCount N (markedRow N r) private0 (fun _=>0)
local notation "H1" => privateCount N (markedRow N r) private1 (fun _=>0)
local notation "K0" => min H0 H1
local notation "K1" => max H0 H1
local notation "act" => Fin.cons true (fun j=>active (r j))

variable (G : GuardInterior ξ share ρ B R Rp γ δ
    (∫x,MenuError.indicator active x ∂μ)
    (∫x,(p x:ℝ)*MenuError.indicator active x ∂μ)
    (∫x,MenuError.indicator private0 x ∂μ)
    (∫x,(p x:ℝ)*reciprocalWeight active bid x ∂μ) reg)
  (ν0 : FiniteLaw (Marks (min (privateCount N (markedRow N r) private0 (fun _=>0)) (privateCount N (markedRow N r) private1 (fun _=>0)))))
  (ν1 : FiniteLaw (Marks (max (privateCount N (markedRow N r) private0 (fun _=>0)) (privateCount N (markedRow N r) private1 (fun _=>0)))))
  (hmean0 : privateMean (min (privateCount N (markedRow N r) private0 (fun _=>0)) (privateCount N (markedRow N r) private1 (fun _=>0))) reg ν0=share*(min (privateCount N (markedRow N r) private0 (fun _=>0)) (privateCount N (markedRow N r) private1 (fun _=>0))))
  (hmean1 : privateMean (max (privateCount N (markedRow N r) private0 (fun _=>0)) (privateCount N (markedRow N r) private1 (fun _=>0))) reg ν1=share*(max (privateCount N (markedRow N r) private0 (fun _=>0)) (privateCount N (markedRow N r) private1 (fun _=>0))))
  {A : ℕ} [Nonempty (Fin A)] (e : Fin A≃Active (Fin.cons true (fun j=>active (r j)))) (i : Fin A)
  (hi : (e i).val=0) (b : ℝ) (hb : 1≤b) (pf : unitInterval)
  (hphysical : ∀j,active (r j)=true→1≤bid (r j))

local notation "br" => compressedBids act e (Fin.cons b (fun j=>bid (r j)))
local notation "pp" => (Fin.cons pf (fun j=>p (r j)) : Fin (N+1)→unitInterval)
local notation "nbar" => populationNumerator ξ ρ abar mbar hbar share
local notation "ideal" => clippedCount ξ b nbar nbar wbar

include hN hactive hprivate0 hprivate1 hp hbid hfair γ hξ hξ1 hρ hB hw hwγ hγ1
  G hmean0 hmean1 hi hb hphysical in

theorem physical_error (e0 F : ℝ) (low : Bool)
    (σ : ProbabilityMeasure (Signal K0 R Rp))
    (bb : Fin A→Icc (1:ℝ) B) (hbb : ∀j,(bb j:ℝ)=br j)
    (hflag : ∀j,sourceFlagProb e0 F (fun k=>(bb k:ℝ)) j=(pp (e j).val:ℝ))
    (f : Fin 3→ℝ) :
    |(AllCountActiveFiniteGain.physicalCount K0 K1 (iidCapacity ρ N) ξ B R Rp width e0 F
      reg low ν0 ν1 σ bb i).expect f-
      (FiniteLaw.mixture ideal (FiniteLaw.dirac 1) pf pf.2.1 pf.2.2).expect f|≤
      MenuError.oscillation f*coefficient ξ b wbar δ*empiricalAverage μ N active private0 private1 p bid r+
        4*MenuError.oscillation f/(A:ℝ)+2*MenuError.oscillation f*(if H0=H1 then 1 else 0)+
          2*MenuError.oscillation f*(if low then 0 else 1) := by
  revert σ ν0 ν1
  by_cases h : H0≤H1
  · rw [min_eq_left h,max_eq_right h]
    intro ν0 ν1 hmean0 hmean1 σ
    exact CommonFixedRowError.physical_error μ N hN active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid r hfair ξ share ρ B R Rp width γ δ
      hξ hξ1 hρ hB hw hwγ hγ1 reg G ν0 ν1 hmean0 hmean1 e i hi b hb pf hphysical
      e0 F low σ bb hbb hflag f
  · have h' : H1≤H0 := (lt_of_not_ge h).le
    rw [min_eq_right h',max_eq_left h']
    intro ν0 ν1 hmean0 hmean1 σ
    have G' : GuardInterior ξ share ρ B R Rp γ δ abar mbar
        (∫x,MenuError.indicator private1 x ∂μ) wbar reg := by
      rw [←hfair]
      exact G
    have hh := CommonFixedRowError.physical_error μ N hN active private1 private0
      hactive hprivate1 hprivate0 p hp bid hbid r hfair.symm ξ share ρ B R Rp width γ δ
      hξ hξ1 hρ hB hw hwγ hγ1 reg G' ν0 ν1 hmean0 hmean1 e i hi b hb pf hphysical
      e0 F low σ bb hbb hflag f
    rw [empiricalAverage_swap μ N active private0 private1 p bid r,←hfair] at hh
    simpa only [eq_comm] using hh

end Count
end FCAppendix.Affine.Tail04.OrderedCommonFixedRowError
