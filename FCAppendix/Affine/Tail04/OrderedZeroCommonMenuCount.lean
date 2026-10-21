import FCAppendix.Affine.Tail04.OrderedCommonFixedRowError
import FCAppendix.Affine.Tail04.OriginalActiveTwoPrefix
import FCAppendix.Affine.Tail04.ZeroNoiseFiniteGame
import FCAppendix.Affine.Tail04.ZeroNoiseGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroCommonMenuCount
open MeasureTheory ProbabilityTheory Set Classical
open MenuError SourceMenuPopulation CommonFiniteCountError CommonFixedRowError
open FiniteTailNoisyGame OriginalActiveCompression OriginalActiveTwoPrefix
open OriginalFlagCompression EqualPrivateSignal NativeTypicalCount
open scoped BigOperators

section Carrier
variable (D : Data) {X : Type*} [MeasurableSpace X]
  (tag : X→ Fin 4) (htag : Measurable tag)
  (decode : X→ Icc (1:ℝ) D.U) (hdecode : Measurable decode)
  (μP : ProbabilityMeasure (Icc D.R D.Up)) (N : ℕ)

def baseCommonRow {n : ℕ} (kind : Fin n→ Fin 4) (r : Fin n→ X) :
    Fin (D.count kind 1)→ Icc (1:ℝ) D.U :=
  fun j => decode (r (enumeration D kind 1 j).val)

include hdecode in
lemma measurable_baseCommonRow {n : ℕ} (kind : Fin n→ Fin 4) :
    Measurable (baseCommonRow D decode kind) :=
  measurable_pi_lambda _ (fun j => hdecode.comp
    (measurable_pi_apply (enumeration D kind 1 j).val))

def baseFocalRow {n : ℕ} (kind : Fin n→ Fin 4) (decode : X→ Icc (1:ℝ) D.U) (b : Icc (1:ℝ) D.U) (r : Fin n→ X) :
    Fin (D.count kind 1+1)→ Icc (1:ℝ) D.U := Fin.cons b (baseCommonRow D decode kind r)

lemma measurable_baseFocalRow {n : ℕ} (kind : Fin n→ Fin 4)
    (decode : X→ Icc (1:ℝ) D.U) (hdecode : Measurable decode) :
    Measurable (fun z : Icc (1:ℝ) D.U×(Fin n→ X) => baseFocalRow D kind decode z.1 z.2) := by
  apply measurable_pi_lambda
  intro j
  refine Fin.cases measurable_fst (fun k => ?_) j
  exact ((measurable_pi_apply k).comp
    (measurable_baseCommonRow D decode hdecode kind)).comp measurable_snd

lemma measurable_physical_mass (A H0 H1 : ℕ) (reg low : Bool) (k : Fin 3) :
    Measurable (fun row : Fin (A+1)→ Icc (1:ℝ) D.U =>
      (AllCountActiveFiniteGain.physicalCount H0 H1 D.c D.ξ D.U D.R D.Up D.width
        (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1)
        (ZeroNoiseFiniteGame.privateBayes D H0 μP).val row 0).mass k) := by
  by_cases heq : H0=H1
  · simp only [AllCountActiveFiniteGain.physicalCount,if_pos heq,
      EqualPrivateActiveRelabel.countLaw_sorted D.hξ]
    exact (EqualPrivateCountPayoff.continuous_countLaw_mass (A+1) H0 D.c D.R D.Up
      D.ξ 1 D.U D.hξ (by norm_num) 0 k).measurable.comp
        (measurable_id.prodMk measurable_const)
  · simp only [AllCountActiveFiniteGain.physicalCount,if_neg heq]
    have hb : Measurable (fun row : Fin (A+1)→Icc (1:ℝ) D.U =>
        fun j => (row j:ℝ)) :=
      measurable_pi_lambda _ (fun j => (measurable_pi_apply j).subtype_val)
    have hh := ZeroNoiseGuard.measurable_rawCount_mass (N:=A+1)
      H0 H1 D.c D.ξ D.R D.width
      (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1)
      (fun _ : Fin (A+1)→Icc (1:ℝ) D.U => D.U) (fun _ => D.Up)
      (fun row j => (row j:ℝ)) measurable_const measurable_const hb 0 k
    exact hh

def tagFlag (k : Fin 4) (x : X) : Bool := decide (tag x=k)

include htag in
lemma measurable_tagFlag (k : Fin 4) : Measurable (tagFlag tag k) :=
  (measurable_of_countable (fun k' : Fin 4 => decide (k'=k))).comp htag

def activeEnumeration (r : Fin N→ X) :
    Fin (D.count (tags tag r) 1+1)≃Active (Fin.cons true (fun j => tagFlag tag 1 (r j))) :=
  consEnumeration _ ((enumeration D (tags tag r) 1).trans
    (predicateEquiv (Equiv.refl _) (fun j => tag (r j)=1)
      (fun j => tagFlag tag 1 (r j)=true) (fun j => by simp [tagFlag])))

omit [MeasurableSpace X] in
lemma activeEnumeration_zero (r : Fin N→ X) : (activeEnumeration D tag N r 0).val=0 := rfl

omit [MeasurableSpace X] in
lemma compressed_focal (r : Fin N→ X) (b : Icc (1:ℝ) D.U) :
    compressedBids _ (activeEnumeration D tag N r)
      (Fin.cons (b:ℝ) (fun j => (decode (r j):ℝ)))=
        fun j => (baseFocalRow D (tags tag r) decode b r j:ℝ) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> rfl

omit [MeasurableSpace X] in
lemma count_privateCount (r : Fin N→ X) (k : Fin 4) :
    D.count (tags tag r) k=privateCount N (markedRow N r) (tagFlag tag k) (fun _ => 0) := by
  simp only [Data.count,privateCount,boolCount,markedRow,tagFlag,tags,Function.comp_apply,
    decide_eq_true_eq,Finset.sum_boole]
  norm_cast

def count (reg : Bool) (b : Icc (1:ℝ) D.U) (r : Fin N→ X) : CountLaw 2 :=
  let kind := tags tag r
  AllCountActiveFiniteGain.physicalCount (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3)) D.c D.ξ D.U D.R D.Up
    D.width (D.e0 reg) D.F reg (decide (0< D.count kind 0))
    (D.marksLaw (min (D.count kind 2) (D.count kind 3))) (D.marksLaw (max (D.count kind 2) (D.count kind 3)))
    (ZeroNoiseFiniteGame.privateBayes D (min (D.count kind 2) (D.count kind 3)) μP).val (baseFocalRow D kind decode b r) 0

include htag hdecode in
lemma measurable_count_mass (reg : Bool) (b : Icc (1:ℝ) D.U) (k : Fin 3) :
    Measurable (fun r => (count D tag decode μP N reg b r).mass k) := by
  unfold count
  refine LocalCoordinates.measurable_finite_eval (tags tag)
    (fun r kind => (AllCountActiveFiniteGain.physicalCount (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3)) D.c D.ξ D.U D.R D.Up
      D.width (D.e0 reg) D.F reg (decide (0< D.count kind 0))
      (D.marksLaw (min (D.count kind 2) (D.count kind 3))) (D.marksLaw (max (D.count kind 2) (D.count kind 3)))
      (ZeroNoiseFiniteGame.privateBayes D (min (D.count kind 2) (D.count kind 3)) μP).val (baseFocalRow D kind decode b r) 0).mass k)
    (measurable_tags tag htag) ?_
  intro kind
  exact (measurable_physical_mass D μP (D.count kind 1) (min (D.count kind 2) (D.count kind 3))
    (max (D.count kind 2) (D.count kind 3)) reg (decide (0< D.count kind 0)) k).comp
      ((measurable_baseFocalRow D kind decode hdecode).comp (measurable_const.prodMk measurable_id))

def averageCount (μ : Measure X) [IsProbabilityMeasure μ]
    (reg : Bool) (b : Icc (1:ℝ) D.U) : CountLaw 2 :=
  FiniteLaw.average (Measure.pi (fun _ : Fin N => μ)) (count D tag decode μP N reg b)
    (measurable_count_mass D tag htag decode hdecode μP N reg b)

def flag (reg : Bool) (x : X) : unitInterval := sourceProbability (D.e0 reg) D.F (decode x)

include hdecode in
lemma measurable_flag (reg : Bool) : Measurable (flag D decode reg) :=
  (measurable_sourceProbability (D.e0 reg) D.F).comp hdecode.subtype_val

def activeMean (μ : Measure X) : ℝ := ∫ x,indicator (tagFlag tag 1) x ∂μ
def mixedMean (μ : Measure X) (reg : Bool) : ℝ :=
  ∫ x,(flag D decode reg x:ℝ)*indicator (tagFlag tag 1) x ∂μ
def privateMean0 (μ : Measure X) : ℝ := ∫ x,indicator (tagFlag tag 2) x ∂μ
def reciprocalMean (μ : Measure X) (reg : Bool) : ℝ :=
  ∫ x,(flag D decode reg x:ℝ)*reciprocalWeight (tagFlag tag 1) (fun y => (decode y:ℝ)) x ∂μ

variable (μ : Measure X) [IsProbabilityMeasure μ]
  (hN : 0< N) (ρ share γ δ : ℝ) (reg : Bool)
  (hcap : D.c=iidCapacity ρ N) (hρ : ρ∈Icc (0:ℝ) 1) (hξ1 : D.ξ≤1)
  (hwγ : D.width≤ γ) (hγ1 : γ≤1)
  (hfair : privateMean0 tag μ=∫ x,indicator (tagFlag tag 3) x ∂μ)
  (hmarks : ∀ K,NativeTypicalCount.privateMean K reg (D.marksLaw K)=share*K)
  (G : GuardInterior D.ξ share ρ D.U D.R D.Up γ δ (activeMean tag μ)
    (mixedMean D tag decode μ reg) (privateMean0 tag μ) (reciprocalMean D tag decode μ reg) reg)

local notation "Abar" => activeMean tag μ
local notation "Mbar" => mixedMean D tag decode μ reg
local notation "Hbar" => privateMean0 tag μ
local notation "Wbar" => reciprocalMean D tag decode μ reg
local notation "num" => populationNumerator D.ξ ρ Abar Mbar Hbar share

def benchmark (b : Icc (1:ℝ) D.U) : CountLaw 2 :=
  FiniteLaw.mixture (clippedCount D.ξ b num num Wbar) (FiniteLaw.dirac 1)
    (sourceProbability (D.e0 reg) D.F b)
    (sourceProbability (D.e0 reg) D.F b).2.1 (sourceProbability (D.e0 reg) D.F b).2.2

def rowError (b : Icc (1:ℝ) D.U) (r : Fin N→ X) : ℝ :=
  coefficient D.ξ b Wbar δ * empiricalAverage μ N
    (tagFlag tag 1) (tagFlag tag 2) (tagFlag tag 3) (flag D decode reg) (fun x => (decode x:ℝ)) r+
    4/((D.count (tags tag r) 1+1:ℕ):ℝ)+
    2*(if D.count (tags tag r) 2=D.count (tags tag r) 3 then 1 else 0)+
    2*(if D.count (tags tag r) 0=0 then 1 else 0)

include htag hdecode hN γ hcap hρ hξ1 hwγ hγ1 hfair hmarks G in
theorem pointwise_count_error (b : Icc (1:ℝ) D.U) (f : Fin 3→ℝ) (r : Fin N→ X) :
    |(count D tag decode μP N reg b r).expect f-
      (benchmark D tag decode μ ρ share reg b).expect f|≤
        MenuError.oscillation f*rowError D tag decode N μ δ reg b r := by
  let e := activeEnumeration D tag N r
  have hh := OrderedCommonFixedRowError.physical_error μ N hN
    (tagFlag tag 1) (tagFlag tag 2) (tagFlag tag 3)
    (measurable_tagFlag tag htag 1) (measurable_tagFlag tag htag 2) (measurable_tagFlag tag htag 3)
    (flag D decode reg) (measurable_flag D decode hdecode reg) (fun x => (decode x:ℝ)) hdecode.subtype_val
    r hfair D.ξ share ρ D.U D.R D.Up D.width γ δ D.hξ hξ1 hρ
    (by linarith [D.hU] : 0≤ D.U) D.hw hwγ hγ1 reg G
    (D.marksLaw _) (D.marksLaw _) (hmarks _) (hmarks _) e 0 rfl b b.2.1
    (sourceProbability (D.e0 reg) D.F b) (fun j _ => (decode (r j)).2.1)
    (D.e0 reg) D.F (decide (0< D.count (tags tag r) 0))
    (ZeroNoiseFiniteGame.privateBayes D _ μP).val (baseFocalRow D (tags tag r) decode b r)
    (fun j => (congrFun (compressed_focal D tag decode N r b) j).symm)
    (fun j => by
      refine Fin.cases ?_ (fun k => ?_) j <;> rfl) f
  rw [←count_privateCount D tag N r 2,←count_privateCount D tag N r 3,←hcap] at hh
  have hz : (if decide (0< D.count (tags tag r) 0) then (0:ℝ) else 1)=
      if D.count (tags tag r) 0=0 then 1 else 0 := by
    by_cases hc : D.count (tags tag r) 0=0
    · simp [hc]
    · simp [hc,show 0< D.count (tags tag r) 0 from by omega]
  rw [hz] at hh
  convert! hh using 1
  dsimp only [count,benchmark,rowError,activeMean,mixedMean,privateMean0,reciprocalMean]
  ring

include htag in
lemma integrable_tagStatistic (q : (Fin N→ Fin 4)→ℝ) :
    Integrable (fun r : Fin N→ X => q (tags tag r)) (Measure.pi (fun _ : Fin N => μ)) := by
  apply Integrable.of_bound
    (((measurable_of_countable q).comp (measurable_tags tag htag)).aestronglyMeasurable)
    (∑ kind : Fin N→ Fin 4,‖q kind‖)
  exact ae_of_all _ fun r => Finset.single_le_sum (fun k _ => norm_nonneg (q k)) (Finset.mem_univ _)

include htag hdecode hN in
theorem integrable_rowError (b : Icc (1:ℝ) D.U) :
    Integrable (rowError D tag decode N μ δ reg b) (Measure.pi (fun _ : Fin N => μ)) := by
  have hi := integrable_empiricalAverage μ N hN (tagFlag tag 1) (tagFlag tag 2) (tagFlag tag 3)
    (measurable_tagFlag tag htag 1) (measurable_tagFlag tag htag 2) (measurable_tagFlag tag htag 3)
    (flag D decode reg) (measurable_flag D decode hdecode reg) (fun x => (decode x:ℝ)) hdecode.subtype_val
  have hfin := integrable_tagStatistic tag htag N μ
  exact (((hi.const_mul _).add (hfin (fun k => 4/((D.count k 1+1:ℕ):ℝ)))).add
    (hfin (fun k => 2*(if D.count k 2=D.count k 3 then 1 else 0)))).add
      (hfin (fun k => 2*(if D.count k 0=0 then 1 else 0)))

include hN γ hcap hρ hξ1 hwγ hγ1 hfair hmarks G in
theorem integrated_count_error (b : Icc (1:ℝ) D.U) (f : Fin 3→ℝ) :
    |(averageCount D tag htag decode hdecode μP N μ reg b).expect f-
      (benchmark D tag decode μ ρ share reg b).expect f|≤
    MenuError.oscillation f*(coefficient D.ξ b Wbar δ*(5/Real.sqrt N+4/(N:ℝ))+
      4*(∫ r,1/((D.count (tags tag r) 1+1:ℕ):ℝ) ∂Measure.pi (fun _ : Fin N => μ))+
      2*(Measure.pi (fun _ : Fin N => μ)).real {r | D.count (tags tag r) 2=D.count (tags tag r) 3}+
      2*(Measure.pi (fun _ : Fin N => μ)).real {r | D.count (tags tag r) 0=0}) := by
  let ν := Measure.pi (fun _ : Fin N => μ)
  have hi := FiniteLaw.integrable_expect ν (count D tag decode μP N reg b)
    (measurable_count_mass D tag htag decode hdecode μP N reg b) f
  have hR := integrable_rowError D tag htag decode hdecode N μ hN δ reg b
  have hc : (∫ _ : Fin N→X,(benchmark D tag decode μ ρ share reg b).expect f ∂ν)=
      (benchmark D tag decode μ ρ share reg b).expect f := by simp
  rw [averageCount,FiniteLaw.expect_average,←hc,←integral_sub hi (integrable_const _)]
  have hh := (abs_integral_le_integral_abs).trans
    (integral_mono (hi.sub (integrable_const _)).abs (hR.const_mul _)
      (pointwise_count_error D tag htag decode hdecode μP N μ hN ρ share γ δ reg hcap hρ hξ1
        hwγ hγ1 hfair hmarks G b f))
  rw [integral_const_mul] at hh
  have he := empiricalAverage_L1 μ N hN (tagFlag tag 1) (tagFlag tag 2) (tagFlag tag 3)
    (measurable_tagFlag tag htag 1) (measurable_tagFlag tag htag 2) (measurable_tagFlag tag htag 3)
    (flag D decode reg) (measurable_flag D decode hdecode reg) (fun x => (decode x:ℝ)) hdecode.subtype_val
  have hg := guard_numerator_bound G ⟨D.hξ.le,hξ1⟩
    (integral_nonneg fun x => (indicator_bounds (tagFlag tag 2) x).1)
    (by linarith [D.hU]) (D.hw.le.trans hwγ)
  have hK := coefficient_nonnegative D.hξ b.2.1 hg.1 G.radius_pos
  have hEq : MeasurableSet {r : Fin N→ X | D.count (tags tag r) 2=D.count (tags tag r) 3} :=
    ((Set.to_countable {kind : Fin N→Fin 4 | D.count kind 2=D.count kind 3}).measurableSet).preimage (measurable_tags tag htag)
  have hNo : MeasurableSet {r : Fin N→ X | D.count (tags tag r) 0=0} :=
    ((Set.to_countable {kind : Fin N→Fin 4 | D.count kind 0=0}).measurableSet).preimage (measurable_tags tag htag)
  have hiE := (integrable_empiricalAverage μ N hN (tagFlag tag 1) (tagFlag tag 2) (tagFlag tag 3)
    (measurable_tagFlag tag htag 1) (measurable_tagFlag tag htag 2) (measurable_tagFlag tag htag 3)
    (flag D decode reg) (measurable_flag D decode hdecode reg)
    (fun x => (decode x:ℝ)) hdecode.subtype_val).const_mul (coefficient D.ξ b Wbar δ)
  have hiR := integrable_tagStatistic tag htag N μ (fun k => 4/((D.count k 1+1:ℕ):ℝ))
  have hiQ := integrable_tagStatistic tag htag N μ (fun k => 2*(if D.count k 2=D.count k 3 then 1 else 0))
  have hiL := integrable_tagStatistic tag htag N μ (fun k => 2*(if D.count k 0=0 then 1 else 0))
  have hInt : (∫ r,rowError D tag decode N μ δ reg b r ∂ν)=
      coefficient D.ξ b Wbar δ*(∫ r,empiricalAverage μ N (tagFlag tag 1) (tagFlag tag 2)
        (tagFlag tag 3) (flag D decode reg) (fun x => (decode x:ℝ)) r ∂ν)+
      4*(∫ r,1/((D.count (tags tag r) 1+1:ℕ):ℝ) ∂ν)+
      2*ν.real {r | D.count (tags tag r) 2=D.count (tags tag r) 3}+
      2*ν.real {r | D.count (tags tag r) 0=0} := by
    unfold rowError
    erw [integral_add ((hiE.add hiR).add hiQ) hiL,integral_add (hiE.add hiR) hiQ,
      integral_add hiE hiR]
    simp_rw [show ∀ r : Fin N→ X,4/((D.count (tags tag r) 1+1:ℕ):ℝ)=
        4*(1/((D.count (tags tag r) 1+1:ℕ):ℝ)) by intro r;ring]
    simp only [integral_const_mul]
    have hq : (∫ r : Fin N→X,if D.count (tags tag r) 2=D.count (tags tag r) 3 then (1:ℝ) else 0 ∂ν)=
        ν.real {r | D.count (tags tag r) 2=D.count (tags tag r) 3} := by
      simpa only [Set.indicator,Pi.one_apply,Set.mem_setOf_eq] using integral_indicator_one (μ:=ν) hEq
    have hl : (∫ r : Fin N→X,if D.count (tags tag r) 0=0 then (1:ℝ) else 0 ∂ν)=
        ν.real {r | D.count (tags tag r) 0=0} := by
      simpa only [Set.indicator,Pi.one_apply,Set.mem_setOf_eq] using integral_indicator_one (μ:=ν) hNo
    rw [hq,hl]
  rw [hInt] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (by gcongr) (oscillation_nonneg f))

end Carrier
section OriginalConditioning
variable (D : Data) {N : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (tag : X→ Fin 4) (htag : Measurable tag)
    (decode : X→ Icc (1:ℝ) D.U) (hdecode : Measurable decode)
    (hmass : ∀k,μ (tag ⁻¹' {k})≠0)
    (ρ : ProbabilityMeasure (Icc (1:ℝ) D.U))
    (hρ : (cond μ (tag ⁻¹' {1})).map decode=(ρ : Measure _))
    (μP : ProbabilityMeasure (Icc D.R D.Up))

include hdecode hmass hρ in
lemma baseCommonRow_law (kind : Fin N→ Fin 4) :
    (Measure.pi (fun i=> cond μ (tag ⁻¹' {kind i}))).map (baseCommonRow D decode kind)=
      Measure.pi (fun _ : Fin (D.count kind 1)=>(ρ : Measure _)) := by
  classical
  let ν : Fin N→ Measure X := fun i=> cond μ (tag ⁻¹' {kind i})
  letI (i : Fin N) : Decidable (kind i=1) := Classical.propDecidable _
  haveI (i : Fin N) : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure (hmass (kind i))
  have hh := PrivateConditionalRows.blockSplit_law ν (fun i=> kind i=1)
    (D.count kind 1) (enumeration D kind 1) decode hdecode (ρ:Measure _)
    (fun j=> by simpa only [ν,(enumeration D kind 1 j).property] using hρ)
  have hp := congrArg (fun η=> η.map Prod.fst) hh
  rw [Measure.map_map measurable_fst (PrivateConditionalRows.measurable_blockSplit _ _ _ _ hdecode)] at hp
  have hf : MeasurePreserving
      (Prod.fst : ((Fin (D.count kind 1)→Icc (1:ℝ) D.U)×
        ({i : Fin N // ¬kind i=1}→X))→(Fin (D.count kind 1)→Icc (1:ℝ) D.U))
      ((Measure.pi (fun _ : Fin (D.count kind 1)=>(ρ : Measure (Icc (1:ℝ) D.U)))).prod
        (Measure.pi (fun i : {i : Fin N // ¬kind i=1}=> ν i)))
      (Measure.pi (fun _ : Fin (D.count kind 1)=>(ρ : Measure (Icc (1:ℝ) D.U)))) :=
    measurePreserving_fst
  exact hp.trans hf.map_eq

lemma physical_expect_measurable (A H0 H1 : ℕ) (reg low : Bool) (b : Icc (1:ℝ) D.U)
    (f : Fin 3→ℝ) :
    Measurable (fun row : Fin A→ Icc (1:ℝ) D.U=>
      (AllCountActiveFiniteGain.physicalCount H0 H1 D.c D.ξ D.U D.R D.Up D.width
        (D.e0 reg) D.F reg low (D.marksLaw H0) (D.marksLaw H1)
        (ZeroNoiseFiniteGame.privateBayes D H0 μP).val (Fin.cons b row) 0).expect f) := by
  have hrow : Measurable (fun row : Fin A→ Icc (1:ℝ) D.U=>
      (Fin.cons b row : Fin (A+1)→Icc (1:ℝ) D.U)) := by
    apply measurable_pi_lambda
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · change Measurable (fun _ : Fin A→Icc (1:ℝ) D.U => b)
      exact measurable_const
    · change Measurable (fun row : Fin A→Icc (1:ℝ) D.U => row k)
      exact measurable_pi_apply k
  exact Finset.measurable_sum _ (fun r _=>
    ((measurable_physical_mass D μP A H0 H1 reg low r).comp hrow).mul_const (f r))

include htag hdecode hmass hρ in
lemma conditional_count_integral (kind : Fin N→ Fin 4) (reg : Bool)
    (b : Icc (1:ℝ) D.U) (f : Fin 3→ℝ) :
    (∫r,(count D tag decode μP N reg b r).expect f
      ∂Measure.pi (fun i=> cond μ (tag ⁻¹' {kind i})))=
      ∫row : Fin (D.count kind 1)→ Icc (1:ℝ) D.U,
        (AllCountActiveFiniteGain.physicalCount (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3))
          D.c D.ξ D.U D.R D.Up D.width (D.e0 reg) D.F reg (decide (0< D.count kind 0))
          (D.marksLaw (min (D.count kind 2) (D.count kind 3))) (D.marksLaw (max (D.count kind 2) (D.count kind 3)))
          (ZeroNoiseFiniteGame.privateBayes D (min (D.count kind 2) (D.count kind 3)) μP).val (Fin.cons b row) 0).expect f
        ∂Measure.pi (fun _ : Fin (D.count kind 1)=>(ρ:Measure _)) := by
  have hf := physical_expect_measurable D μP (D.count kind 1) (min (D.count kind 2) (D.count kind 3))
    (max (D.count kind 2) (D.count kind 3)) reg (decide (0< D.count kind 0)) b f
  rw [←baseCommonRow_law D μ tag decode hdecode hmass ρ hρ kind,
    integral_map (measurable_baseCommonRow D decode hdecode kind).aemeasurable hf.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_tags_conditional μ tag htag hmass kind] with r hr
  exact congrArg (fun kind' : Fin N→Fin 4 =>
    (AllCountActiveFiniteGain.physicalCount (min (D.count kind' 2) (D.count kind' 3)) (max (D.count kind' 2) (D.count kind' 3))
      D.c D.ξ D.U D.R D.Up D.width (D.e0 reg) D.F reg (decide (0< D.count kind' 0))
      (D.marksLaw (min (D.count kind' 2) (D.count kind' 3))) (D.marksLaw (max (D.count kind' 2) (D.count kind' 3)))
      (ZeroNoiseFiniteGame.privateBayes D (min (D.count kind' 2) (D.count kind' 3)) μP).val
      (baseFocalRow D kind' decode b r) 0).expect f) hr

include hmass hρ in
lemma original_count_integral
    (hcat : ∀k,μ (tag ⁻¹' {k})=ENNReal.ofReal (D.categories.mass k))
    (reg : Bool) (b : Icc (1:ℝ) D.U) (f : Fin 3→ℝ) :
    (averageCount D tag htag decode hdecode μP N μ reg b).expect f=
      ∑kind : Fin N→ Fin 4,(CommonList.iid D.categories N).mass kind*
        ∫row : Fin (D.count kind 1)→ Icc (1:ℝ) D.U,
          (AllCountActiveFiniteGain.physicalCount (min (D.count kind 2) (D.count kind 3)) (max (D.count kind 2) (D.count kind 3))
            D.c D.ξ D.U D.R D.Up D.width (D.e0 reg) D.F reg (decide (0< D.count kind 0))
            (D.marksLaw (min (D.count kind 2) (D.count kind 3))) (D.marksLaw (max (D.count kind 2) (D.count kind 3)))
            (ZeroNoiseFiniteGame.privateBayes D (min (D.count kind 2) (D.count kind 3)) μP).val (Fin.cons b row) 0).expect f
          ∂Measure.pi (fun _ : Fin (D.count kind 1)=>(ρ:Measure _)) := by
  haveI (kind : Fin N→ Fin 4) (i : Fin N) : IsProbabilityMeasure (cond μ (tag ⁻¹' {kind i})) :=
    cond_isProbabilityMeasure (hmass (kind i))
  have hw (kind : Fin N→ Fin 4) : (∏i,μ (tag ⁻¹' {kind i}))=
      ENNReal.ofReal ((CommonList.iid D.categories N).mass kind) := by
    simp_rw [hcat]
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _=> D.categories.nonneg (kind i))).symm
  have hi (kind : Fin N→ Fin 4) : Integrable
      (fun r=>(count D tag decode μP N reg b r).expect f)
      (Measure.pi (fun i=> cond μ (tag ⁻¹' {kind i}))) :=
    FiniteLaw.integrable_expect _ _ (measurable_count_mass D tag htag decode hdecode μP N reg b) f
  rw [averageCount,FiniteLaw.expect_average,OriginalFiniteFibers.iid_finite_disintegration μ tag htag]
  simp_rw [hw]
  rw [integral_finsetSum_measure (fun kind _=>(hi kind).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr (M:=ℝ) ?_ ?_
  · ext kind
    simp only [Finset.mem_univ]
  · intro kind _
    rw [integral_smul_measure,ENNReal.toReal_ofReal ((CommonList.iid D.categories N).nonneg kind),
      conditional_count_integral D μ tag htag decode hdecode hmass ρ hρ μP kind reg b f]
    rfl

end OriginalConditioning
end FCAppendix.Affine.Tail04.OrderedZeroCommonMenuCount
