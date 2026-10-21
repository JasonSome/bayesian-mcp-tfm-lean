import FCAppendix.Affine.Tail04.CommonRankAverage

noncomputable section
namespace FCAppendix.Affine.Tail04.CommonFixedRowError
open MeasureTheory ProbabilityTheory Set Classical
open MenuError OriginalFlagCompression CommonFlagCompression CommonFiniteCountError
open NativeTypicalCount EqualPrivateSignal SourceMenuPopulation
open scoped BigOperators

private lemma integral_upper {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] (g : Y→ℝ) (C : ℝ)
    (hg0 : ∀ y,0≤ g y) (hg1 : ∀ y,g y≤ C) : (∫ y,g y ∂ν)≤ C := by
  have hh := integral_mono_of_nonneg (μ:=ν) (f:=g) (g:=fun _ => C)
    (ae_of_all _ hg0) (integrable_const C) (ae_of_all _ hg1)
  simpa only [integral_const,probReal_univ,one_smul] using hh

variable {X : Type*} [MeasurableSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ] (N : ℕ) (hN : 0< N)
  (active private0 private1 : X→ Bool)
  (hactive : Measurable active) (hprivate0 : Measurable private0) (hprivate1 : Measurable private1)
  (p : X→ unitInterval) (hp : Measurable p) (bid : X→ℝ) (hbid : Measurable bid)

def markedRow (r : Fin N→ X) (u : Fin N→ unitInterval) : Fin N→ X×unitInterval := fun j => (r j,u j)

def empirical (r : Fin N→ X) (u : Fin N→ unitInterval) : ℝ :=
  commonEmpiricalError μ N (markedRow N r) active private0 private1 p bid u

def empiricalAverage (r : Fin N→ X) : ℝ :=
  ∫ u,empirical μ N active private0 private1 p bid r u
    ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

omit [IsProbabilityMeasure μ] in
lemma empirical_nonnegative (r : Fin N→ X) (u : Fin N→ unitInterval) :
    0≤ empirical μ N active private0 private1 p bid r u :=
  commonEmpiricalError_nonnegative μ N (markedRow N r) active private0 private1 p bid u

include hN in
lemma empirical_bound (r : Fin N→ X) (u : Fin N→ unitInterval) :
    empirical μ N active private0 private1 p bid r u≤5+4/(N:ℝ) := by
  have hk (k : Fin 5) : sourceEmpiricalError μ N (markedRow N r)
      active private0 private1 p bid k u≤1 := by
    have he := empiricalMean_bounds N hN (sourceBasis active private0 private1 p bid k)
      (sourceBasis_bounds active private0 private1 p bid k) (markedRow N r u)
    have hm : (∫ z,sourceBasis active private0 private1 p bid k z
        ∂μ.prod (volume : Measure unitInterval))∈Icc (0:ℝ) 1 :=
      ⟨integral_nonneg fun z => (sourceBasis_bounds active private0 private1 p bid k z).1,
        integral_upper (μ.prod (volume : Measure unitInterval)) _ 1
          (fun z => (sourceBasis_bounds active private0 private1 p bid k z).1)
          (fun z => (sourceBasis_bounds active private0 private1 p bid k z).2)⟩
    exact abs_le.mpr ⟨by linarith [he.1,hm.2],by linarith [he.2,hm.1]⟩
  have hs := Finset.sum_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin 5))) => hk k)
  simpa only [empirical,commonEmpiricalError,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_ofNat,add_comm] using add_le_add_right hs (4/(N:ℝ))

omit [IsProbabilityMeasure μ] in
include hactive hprivate0 hprivate1 hp hbid in
lemma measurable_empirical :
    Measurable (Function.uncurry (empirical μ N active private0 private1 p bid)) := by
  unfold Function.uncurry empirical commonEmpiricalError
  apply Measurable.add_const
  apply Finset.measurable_sum
  intro k _
  apply Measurable.abs
  apply Measurable.sub_const
  exact (measurable_empiricalMean N (sourceBasis active private0 private1 p bid k)
    (measurable_sourceBasis active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid k)).comp
      (OriginalNoiseProduct.measurable_zipRow N)

include hN hactive hprivate0 hprivate1 hp hbid in
lemma integrable_empirical (r : Fin N→ X) :
    Integrable (empirical μ N active private0 private1 p bid r)
      (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))) := by
  apply Integrable.of_bound
    (((measurable_empirical μ N active private0 private1 hactive hprivate0 hprivate1
      p hp bid hbid).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (5+4/(N:ℝ))
  exact ae_of_all _ fun u => by
    change ‖empirical μ N active private0 private1 p bid r u‖≤5+4/(N:ℝ)
    rw [Real.norm_eq_abs,abs_of_nonneg (empirical_nonnegative μ N active private0 private1 p bid r u)]
    exact empirical_bound μ N hN active private0 private1 p bid r u

omit [IsProbabilityMeasure μ] in
include hactive hprivate0 hprivate1 hp hbid in
lemma measurable_empiricalAverage : Measurable (empiricalAverage μ N active private0 private1 p bid) :=
  (measurable_empirical μ N active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid).stronglyMeasurable.integral_prod_right'.measurable

omit [IsProbabilityMeasure μ] in
lemma empiricalAverage_nonnegative (r : Fin N→ X) :
    0≤ empiricalAverage μ N active private0 private1 p bid r :=
  integral_nonneg (empirical_nonnegative μ N active private0 private1 p bid r)

include hN hactive hprivate0 hprivate1 hp hbid in
lemma integrable_empiricalAverage :
    Integrable (empiricalAverage μ N active private0 private1 p bid)
      (Measure.pi (fun _ : Fin N => μ)) := by
  apply Integrable.of_bound (measurable_empiricalAverage μ N active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid).aestronglyMeasurable (5+4/(N:ℝ))
  exact ae_of_all _ fun r => by
    rw [Real.norm_eq_abs,abs_of_nonneg (empiricalAverage_nonnegative μ N active private0 private1 p bid r)]
    exact integral_upper _ _ _ (empirical_nonnegative μ N active private0 private1 p bid r)
      (empirical_bound μ N hN active private0 private1 p bid r)

include hN hactive hprivate0 hprivate1 hp hbid in
theorem empiricalAverage_L1 :
    (∫ r,empiricalAverage μ N active private0 private1 p bid r
      ∂Measure.pi (fun _ : Fin N => μ))≤5/Real.sqrt N+4/(N:ℝ) := by
  let ν := (Measure.pi (fun _ : Fin N => μ)).prod
    (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)))
  have hzip := OriginalNoiseProduct.zipRow_preserves μ (volume : Measure unitInterval) N
  have hi := integrable_commonEmpiricalError μ ν N hN (OriginalNoiseProduct.zipRow N) hzip
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid
  have hh := commonEmpiricalError_L1 μ ν N hN (OriginalNoiseProduct.zipRow N) hzip
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid
  rw [integral_prod _ hi] at hh
  exact hh

section Count
attribute [local irreducible] empirical typicalRankCount FiniteLaw.mixture FiniteLaw.dirac
variable (r : Fin N→ X)
  (hfair : (∫ x,MenuError.indicator private0 x ∂μ)=(∫ x,MenuError.indicator private1 x ∂μ))
  (ξ share ρ B R Rp width γ δ : ℝ) (hξ : 0< ξ) (hξ1 : ξ≤1)
  (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B) (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1)
  (reg : Bool)

local notation "abar" => ∫ x,MenuError.indicator active x ∂μ
local notation "mbar" => ∫ x,(p x:ℝ)*MenuError.indicator active x ∂μ
local notation "hbar" => ∫ x,MenuError.indicator private0 x ∂μ
local notation "wbar" => ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
local notation "H0" => privateCount N (markedRow N r) private0 (fun _ => 0)
local notation "H1" => privateCount N (markedRow N r) private1 (fun _ => 0)
local notation "act" => Fin.cons true (fun j => active (r j))

variable (G : GuardInterior ξ share ρ B R Rp γ δ
    (∫ x,MenuError.indicator active x ∂μ)
    (∫ x,(p x:ℝ)*MenuError.indicator active x ∂μ)
    (∫ x,MenuError.indicator private0 x ∂μ)
    (∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ) reg)
  (ν0 : FiniteLaw (Marks (privateCount N (markedRow N r) private0 (fun _ => 0))))
  (ν1 : FiniteLaw (Marks (privateCount N (markedRow N r) private1 (fun _ => 0))))
  (hmean0 : privateMean (privateCount N (markedRow N r) private0 (fun _ => 0)) reg ν0=
    share*(privateCount N (markedRow N r) private0 (fun _ => 0)))
  (hmean1 : privateMean (privateCount N (markedRow N r) private1 (fun _ => 0)) reg ν1=
    share*(privateCount N (markedRow N r) private1 (fun _ => 0)))
  {A : ℕ} [Nonempty (Fin A)] (e : Fin A≃Active (Fin.cons true (fun j => active (r j)))) (i : Fin A) (hi : (e i).val=0)
  (b : ℝ) (hb : 1≤ b) (pf : unitInterval)
  (hphysical : ∀ j,active (r j)=true → 1≤ bid (r j))

local notation "br" => compressedBids act e (Fin.cons b (fun j => bid (r j)))
local notation "pp" => (Fin.cons pf (fun j => p (r j)) : Fin (N+1)→unitInterval)
local notation "Pnum" => countParameters A H0 H1 (iidCapacity ρ N) ξ reg ν0 ν1
local notation "phi" => TypicalGuardStatistics.phi A H0 H1 (iidCapacity ρ N) ξ B R Rp width reg ν0 ν1
local notation "nbar" => populationNumerator ξ ρ abar mbar hbar share
local notation "ideal" => clippedCount ξ b nbar nbar wbar

include hN hactive hprivate0 hprivate1 hp hbid hfair γ hξ hξ1 hρ hB hw hwγ hγ1 G hmean0 hmean1 hi hb hphysical in
theorem typical_error (fallback : CountLaw 2) (f : Fin 3→ℝ) :
    |(typicalRankCount (Pnum).mixedCount phi br (fun j => (pp (e j).val:ℝ))
      (fun j => (pp (e j).val).2.1) (fun j => (pp (e j).val).2.2) i fallback).expect f-
      (FiniteLaw.mixture ideal (FiniteLaw.dirac 1) pf pf.2.1 pf.2.2).expect f|≤
        MenuError.oscillation f*coefficient ξ b wbar δ*empiricalAverage μ N active private0 private1 p bid r+
          4*MenuError.oscillation f/(A:ℝ) := by
  have hg := guard_numerator_bound G ⟨hξ.le,hξ1⟩
    (integral_nonneg fun x => (indicator_bounds private0 x).1) hB (hw.le.trans hwγ)
  have hZ : Measurable (empirical μ N active private0 private1 p bid r) := by
    exact (measurable_empirical μ N active private0 private1 hactive hprivate0 hprivate1
      p hp bid hbid).comp ((show Measurable
        (fun _ : Fin N→unitInterval => r) from measurable_const).prodMk measurable_id)
  have hZi := integrable_empirical μ N hN active private0 private1 hactive hprivate0 hprivate1
    p hp bid hbid r
  apply CommonRankAverage.rank_error act e pp br i (Pnum).mixedCount phi fallback ideal f
    (MenuError.oscillation f*coefficient ξ b wbar δ)
    (empirical μ N active private0 private1 p bid r)
    hZ hZi
  intro target u
  let ru := markedRow N r (CommonRankAverage.suffix N u)
  have hh := target_count_error μ N hN ru active private0 private1 hactive hprivate0 hprivate1
    p hp bid hbid hfair ξ share ρ B R Rp width γ δ hξ hξ1 hρ hB hw hwγ hγ1 reg G
    ν0 ν1 hmean0 hmean1 e i hi target b hb (Empirical.flag pf (u 0)) hphysical fallback f
  have hflags : OriginalFlagMeasure.flags pp u=
      flagsPrefix ru p (Empirical.flag pf (u 0)) := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  simp only [hflags,Fin.cons_zero]
  convert! hh using 1
  unfold empirical
  rfl

include hN hactive hprivate0 hprivate1 hp hbid hfair γ hξ hξ1 hρ hB hw hwγ hγ1 G hmean0 hmean1 hi hb hphysical in
theorem physical_error (e0 F : ℝ) (low : Bool)
    (σ : ProbabilityMeasure (Signal H0 R Rp))
    (bb : Fin A→ Icc (1:ℝ) B) (hbb : ∀ j,(bb j:ℝ)=br j)
    (hflag : ∀ j,sourceFlagProb e0 F (fun k => (bb k:ℝ)) j=(pp (e j).val:ℝ))
    (f : Fin 3→ℝ) :
    |(AllCountActiveFiniteGain.physicalCount H0 H1 (iidCapacity ρ N) ξ B R Rp width e0 F
      reg low ν0 ν1 σ bb i).expect f-
      (FiniteLaw.mixture ideal (FiniteLaw.dirac 1) pf pf.2.1 pf.2.2).expect f|≤
      MenuError.oscillation f*coefficient ξ b wbar δ*empiricalAverage μ N active private0 private1 p bid r+
        4*MenuError.oscillation f/(A:ℝ)+2*MenuError.oscillation f*(if H0=H1 then 1 else 0)+
          2*MenuError.oscillation f*(if low then 0 else 1) := by
  have hg := guard_numerator_bound G ⟨hξ.le,hξ1⟩
    (integral_nonneg fun x => (indicator_bounds private0 x).1) hB (hw.le.trans hwγ)
  have hbase : 0≤ MenuError.oscillation f*coefficient ξ b wbar δ*
      empiricalAverage μ N active private0 private1 p bid r+4*MenuError.oscillation f/(A:ℝ) := by
    have hK := coefficient_nonnegative hξ hb hg.1 G.radius_pos
    have hZ := empiricalAverage_nonnegative μ N active private0 private1 p bid r
    have ho := oscillation_nonneg f
    positivity
  by_cases heq : H0=H1
  · have hh := count_expect_difference_bound
      (AllCountActiveFiniteGain.physicalCount H0 H1 (iidCapacity ρ N) ξ B R Rp width e0 F
        reg low ν0 ν1 σ bb i)
      (FiniteLaw.mixture ideal (FiniteLaw.dirac 1) pf pf.2.1 pf.2.2) f
    simp only [if_pos heq]
    cases low <;> simp only [ite_true,Bool.false_eq_true,ite_false,mul_zero,mul_one] <;>
      linarith [oscillation_nonneg f]
  · cases low
    · have hh := count_expect_difference_bound
        (AllCountActiveFiniteGain.physicalCount H0 H1 (iidCapacity ρ N) ξ B R Rp width e0 F
          reg false ν0 ν1 σ bb i)
        (FiniteLaw.mixture ideal (FiniteLaw.dirac 1) pf pf.2.1 pf.2.2) f
      simp only [if_neg heq,Bool.false_eq_true,ite_false,mul_zero,mul_one,add_zero]
      linarith
    · simp only [AllCountActiveFiniteGain.physicalCount,if_neg heq,
        UnequalNoisyCountPayoff.rawCount,ite_true,mul_zero,add_zero]
      have hbfun : (fun j => (bb j:ℝ))=br := funext hbb
      have hpfun : sourceFlagProb e0 F (fun k => (bb k:ℝ))=(fun j => (pp (e j).val:ℝ)) := funext hflag
      simp only [hpfun]
      simp only [hbfun]
      exact typical_error μ N hN active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid
        r hfair ξ share ρ B R Rp width γ δ hξ hξ1 hρ hB hw hwγ hγ1 reg G ν0 ν1 hmean0 hmean1
        e i hi b hb pf hphysical _ f

end Count
end FCAppendix.Affine.Tail04.CommonFixedRowError
