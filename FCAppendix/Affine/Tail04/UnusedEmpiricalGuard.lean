import FCAppendix.Affine.Tail04.UnusedInsertionGuard
import FCAppendix.Affine.Tail04.CommonFixedRowError
import FCAppendix.Affine.Tail04.PublicWeightLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedEmpiricalGuard
open MeasureTheory ProbabilityTheory Set Classical
open MenuError OriginalFlagCompression NativeTypicalCount EqualPrivateSignal
open SourceMenuPopulation TypicalGuardEndpoints PublicScenario
open CommonFixedRowError UnusedInsertionGuard
open scoped BigOperators

section Error
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  (N : ℕ) (hN : 0< N) (active private0 private1 : X→ Bool)
  (hactive : Measurable active) (hprivate0 : Measurable private0)
  (hprivate1 : Measurable private1) (p : X→ unitInterval) (hp : Measurable p)
  (bid : X→ℝ) (hbid : Measurable bid)

def error (r : Fin N→ X) (u : Fin N→ unitInterval) : ℝ :=
  empirical μ N active private0 private1 p bid r u+1/(N:ℝ)

def averageError (r : Fin N→ X) : ℝ :=
  empiricalAverage μ N active private0 private1 p bid r+1/(N:ℝ)

omit [IsProbabilityMeasure μ] in
lemma error_nonnegative (r : Fin N→ X) (u : Fin N→ unitInterval) :
    0≤ error μ N active private0 private1 p bid r u :=
  add_nonneg (empirical_nonnegative μ N active private0 private1 p bid r u) (by positivity)

omit [IsProbabilityMeasure μ] in
include hactive hprivate0 hprivate1 hp hbid in
lemma measurable_error : Measurable (Function.uncurry (error μ N active private0 private1 p bid)) :=
  (measurable_empirical μ N active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid).add_const _

include hN hactive hprivate0 hprivate1 hp hbid in
lemma integrable_error (r : Fin N→ X) :
    Integrable (error μ N active private0 private1 p bid r)
      (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))) :=
  (integrable_empirical μ N hN active private0 private1 hactive hprivate0 hprivate1
    p hp bid hbid r).add (integrable_const _)

include hN hactive hprivate0 hprivate1 hp hbid in
lemma integral_error (r : Fin N→ X) :
    (∫ u,error μ N active private0 private1 p bid r u
      ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)))=
        averageError μ N active private0 private1 p bid r := by
  unfold error
  rw [integral_add (integrable_empirical μ N hN active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid r) (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul,
    averageError,empiricalAverage]

omit [IsProbabilityMeasure μ] in
include hactive hprivate0 hprivate1 hp hbid in
lemma measurable_averageError : Measurable (averageError μ N active private0 private1 p bid) :=
  (measurable_empiricalAverage μ N active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid).add_const _

include hN hactive hprivate0 hprivate1 hp hbid in
lemma integrable_averageError : Integrable (averageError μ N active private0 private1 p bid)
    (Measure.pi (fun _ : Fin N => μ)) :=
  (integrable_empiricalAverage μ N hN active private0 private1 hactive hprivate0 hprivate1
    p hp bid hbid).add (integrable_const _)

include hN hactive hprivate0 hprivate1 hp hbid in
theorem averageError_L1 :
    (∫ r,averageError μ N active private0 private1 p bid r
      ∂Measure.pi (fun _ : Fin N => μ))≤5/Real.sqrt N+5/(N:ℝ) := by
  have he:=empiricalAverage_L1 μ N hN active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid
  unfold averageError
  rw [integral_add (integrable_empiricalAverage μ N hN active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid) (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  have hd : (4:ℝ)/N+1/N=5/N := by ring
  linarith

local notation "abar" => ∫ x,MenuError.indicator active x ∂μ
local notation "mbar" => ∫ x,(p x:ℝ)*MenuError.indicator active x ∂μ
local notation "hbar" => ∫ x,MenuError.indicator private0 x ∂μ
local notation "wbar" => ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ

include hN hactive hprivate0 hprivate1 hp hbid in
theorem guardError_le_error (r : Fin N→ X) (u : Fin N→ unitInterval)
    (target : Fin (N+1))
    (hfair : (∫ x,MenuError.indicator private0 x ∂μ)=(∫ x,MenuError.indicator private1 x ∂μ)) :
    let row:=markedRow N r u
    guardError N (privateCount N (fun _ : Unit => row) active ())
      (flaggedMixedCount N (fun _ : Unit => row) (fun _ => target) active p false ())
      (privateCount N (fun _ : Unit => row) private0 ())
      (privateCount N (fun _ : Unit => row) private1 ())
      (flaggedReciprocal N (fun _ : Unit => row) (fun _ => target) active p bid 1 false ())
      abar mbar hbar wbar≤ error μ N active private0 private1 p bid r u := by
  dsimp only
  let row:=markedRow N r u
  have hh:=flaggedGuardError_le_common μ N hN (fun _ : Unit => row)
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid
    1 (by norm_num) false (fun _ => target) hfair ()
  have hc : activeCount N (fun _ : Unit => row) active ()=
      privateCount N (fun _ : Unit => row) active ()+1 := by
    simp only [activeCount,privateCount,boolCount,Fin.sum_univ_succ,
      Fin.cases_zero,Fin.cases_succ,ite_true]
    apply Eq.trans ?_ (Nat.add_comm 1 _)
    congr 1
  have he := abs_sub_le
    ((privateCount N (fun _ : Unit => row) active ():ℝ)/(N:ℝ))
    ((activeCount N (fun _ : Unit => row) active ():ℝ)/(N:ℝ)) abar
  have hdiff : |(privateCount N (fun _ : Unit => row) active ():ℝ)/(N:ℝ)-
      (activeCount N (fun _ : Unit => row) active ():ℝ)/(N:ℝ)|=1/(N:ℝ) := by
    rw [hc,Nat.cast_add,Nat.cast_one,add_div]
    rw [show (privateCount N (fun _ : Unit => row) active ():ℝ)/N-
      ((privateCount N (fun _ : Unit => row) active ():ℝ)/N+1/N)=-(1/(N:ℝ)) by ring,
      abs_neg,abs_of_nonneg (by positivity)]
  rw [hdiff] at he
  dsimp only [flaggedGuardError,guardError] at hh
  change _≤commonEmpiricalError μ N (markedRow N r) active private0 private1 p bid u at hh
  dsimp only [guardError,error,empirical]
  linarith

include hN hactive hprivate0 hprivate1 hp hbid in
lemma positive_active_of_error (r : Fin N→ X) (u : Fin N→ unitInterval)
    (hfair : (∫ x,MenuError.indicator private0 x ∂μ)=(∫ x,MenuError.indicator private1 x ∂μ))
    {δ : ℝ} (hδ : 0< δ) (hδm : δ≤ mbar/2)
    (hg : error μ N active private0 private1 p bid r u< δ) :
    0< boolCount (fun j : Fin N => active (r j)) := by
  have he:=guardError_le_error μ N hN active private0 private1 hactive hprivate0 hprivate1
    p hp bid hbid r u 0 hfair
  by_contra ha
  have ha0 : privateCount N (fun _ : Unit => markedRow N r u) active ()=0 :=
    Nat.eq_zero_of_not_pos ha
  have hm0 : flaggedMixedCount N (fun _ : Unit => markedRow N r u)
      (fun _ => 0) active p false ()=0 :=
    Nat.eq_zero_of_le_zero (ha0 ▸ partial_mixed_le_active N
      (fun _ : Unit => markedRow N r u) (fun _ => 0) active p ())
  dsimp only at he
  rw [hm0] at he
  have hb:=(guardError_bounds N
    (privateCount N (fun _ : Unit => markedRow N r u) active ())
    (flaggedMixedCount N (fun _ : Unit => markedRow N r u) (fun _ => 0) active p false ())
    (privateCount N (fun _ : Unit => markedRow N r u) private0 ())
    (privateCount N (fun _ : Unit => markedRow N r u) private1 ())
    (flaggedReciprocal N (fun _ : Unit => markedRow N r u) (fun _ => 0) active p bid 1 false ())
    abar mbar hbar wbar).2.2.1
  rw [hm0,Nat.cast_zero,zero_div,zero_sub,abs_neg] at hb
  have hh : |mbar|< δ := (hb.trans he).trans_lt hg
  linarith [le_abs_self mbar]

attribute [local irreducible] error

def bad {δ : ℝ} (r : Fin N→ X) : Set (Fin N→ unitInterval) :=
  {u | δ≤ error μ N active private0 private1 p bid r u}

omit [IsProbabilityMeasure μ] in
include hactive hprivate0 hprivate1 hp hbid in
lemma measurableSet_bad {δ : ℝ} (r : Fin N→ X) :
    MeasurableSet (bad μ N active private0 private1 p bid (δ:=δ) r) :=
  measurableSet_le measurable_const ((measurable_error μ N active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid).comp
      ((show Measurable (fun _ : Fin N→unitInterval => r)
        from measurable_const).prodMk measurable_id))

include hN hactive hprivate0 hprivate1 hp hbid in
theorem bad_probability {δ : ℝ} (hδ : 0< δ) (r : Fin N→ X) :
    (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))).real
      (bad μ N active private0 private1 p bid (δ:=δ) r)≤
        averageError μ N active private0 private1 p bid r/δ := by
  let Z:=Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))
  let B:=bad μ N active private0 private1 p bid (δ:=δ) r
  have hB:=measurableSet_bad μ N active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid
    (δ:=δ) r
  have hiB : Integrable (fun u => if u∈B then (1:ℝ) else 0) Z :=
    Integrable.of_bound (Measurable.ite hB measurable_const measurable_const).aestronglyMeasurable 1
      (ae_of_all _ fun u => by split_ifs <;> norm_num)
  have hpoint (u : Fin N→ unitInterval) :
      (if u∈B then (1:ℝ) else 0)≤ error μ N active private0 private1 p bid r u/δ := by
    by_cases hu : u∈B
    · rw [if_pos hu]
      change δ≤error μ N active private0 private1 p bid r u at hu
      exact (le_div_iff₀ hδ).mpr (by simpa only [one_mul] using hu)
    · rw [if_neg hu]
      exact div_nonneg (error_nonnegative μ N active private0 private1 p bid r u) hδ.le
  calc
    _=∫ u,if u∈B then (1:ℝ) else 0 ∂Z := by
      symm
      simpa only [Set.indicator,Pi.one_apply] using integral_indicator_one (μ:=Z) hB
    _≤∫ u,error μ N active private0 private1 p bid r u/δ ∂Z :=
      integral_mono_ae hiB ((integrable_error μ N hN active private0 private1
        hactive hprivate0 hprivate1 p hp bid hbid r).div_const δ) (ae_of_all _ hpoint)
    _=_ := by
      simp only [div_eq_mul_inv,integral_mul_const]
      rw [integral_error μ N hN active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid]

end Error

section ActualOwners
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  (N : ℕ) (hN : 0< N) (active private0 private1 : X→ Bool)
  (hactive : Measurable active) (hprivate0 : Measurable private0)
  (hprivate1 : Measurable private1) (p : X→ unitInterval) (hp : Measurable p)
  (bid : X→ℝ) (hbid : Measurable bid) (r : Fin N→ X)
  (hfair : (∫ x,MenuError.indicator private0 x ∂μ)=(∫ x,MenuError.indicator private1 x ∂μ))
  (ξ share ρ B B0 R Rp width γ δ : ℝ)
  (hξ : ξ∈Icc (0:ℝ) 1) (hρ : ρ∈Icc (0:ℝ) 1)
  (hB0 : 0≤ B0) (hBB : B≤ B0) (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1)
  (reg : Bool)

local notation "abar" => ∫ x,MenuError.indicator active x ∂μ
local notation "mbar" => ∫ x,(p x:ℝ)*MenuError.indicator active x ∂μ
local notation "hbar" => ∫ x,MenuError.indicator private0 x ∂μ
local notation "wbar" => ∫ x,(p x:ℝ)*reciprocalWeight active bid x ∂μ
local notation "H0" => privateCount N (markedRow N r) private0 (fun _ => 0)
local notation "H1" => privateCount N (markedRow N r) private1 (fun _ => 0)
local notation "act" => fun j : Fin N => active (r j)

variable (G : GuardInterior ξ share ρ B0 R Rp γ δ
    (∫x,MenuError.indicator active x ∂μ)
    (∫x,(p x:ℝ)*MenuError.indicator active x ∂μ)
    (∫x,MenuError.indicator private0 x ∂μ)
    (∫x,(p x:ℝ)*reciprocalWeight active bid x ∂μ) reg)
  (ν0 : FiniteLaw (Marks (privateCount N (markedRow N r) private0 (fun _=>0))))
  (ν1 : FiniteLaw (Marks (privateCount N (markedRow N r) private1 (fun _=>0))))
  (hmean0 : privateMean (privateCount N (markedRow N r) private0 (fun _=>0)) reg ν0=
    share*(privateCount N (markedRow N r) private0 (fun _=>0)))
  (hmean1 : privateMean (privateCount N (markedRow N r) private1 (fun _=>0)) reg ν1=
    share*(privateCount N (markedRow N r) private1 (fun _=>0)))
  (hphysical : ∀ j,active (r j)=true → 1≤ bid (r j))
  (hroom : 2*ξ/((N:ℝ)*(∫x,(p x:ℝ)*reciprocalWeight active bid x ∂μ))≤ γ)
  {A : ℕ} (e : Fin A≃Active (fun j : Fin N=>active (r j)))

local notation "br" => compressedBids act e (fun j => bid (r j))
local notation "Pnum" => countParameters A H0 H1 (iidCapacity ρ N) ξ reg ν0 ν1

include hN hactive hprivate0 hprivate1 hp hbid hfair hξ hρ hB0 hBB hw hwγ hγ1 G hmean0 hmean1 hphysical hroom in
theorem output_guard (u : Fin N→ unitInterval) (target : Fin A)
    (AB : Finset (Fin A)×Finset (Fin A))
    (hAB : (Hybrid.ownerDivision
      (forcedExclusiveSet target (compressedFlags act e (OriginalFlagMeasure.flags (fun j => p (r j)) u)))
      ((Pnum).owner0 (targetMixedSet target
        (compressedFlags act e (OriginalFlagMeasure.flags (fun j => p (r j)) u))).card)).mass AB≠0)
    (hgood : error μ N active private0 private1 p bid r u< δ) :
    let flags:=compressedFlags act e (OriginalFlagMeasure.flags (fun j => p (r j)) u)
    let I:=targetMixedSet target flags
    FocalInsertion.Guard A H0 H1 (iidCapacity ρ N) ξ B R Rp reg I AB.1 AB.2 br ν0 ν1 ∧
      TypicalGuard.weight A H0 H1 (iidCapacity ρ N) ξ B R Rp width reg I AB.1 AB.2 br ν0 ν1=1 ∧
      γ≤ TypicalGuard.margin A H0 H1 (iidCapacity ρ N) ξ B0 R Rp reg I AB.1 AB.2 br ν0 ν1 := by
  dsimp only
  let row:=markedRow N r u
  let flags:=compressedFlags act e (OriginalFlagMeasure.flags (fun j => p (r j)) u)
  let I:=targetMixedSet target flags
  let target0 : Fin (N+1):=((e target).val).succ
  let M:=flaggedMixedCount N (fun _ : Unit => row) (fun _ => target0) active p false ()
  let W:=flaggedReciprocal N (fun _ : Unit => row) (fun _ => target0) active p bid 1 false ()
  have hAeq : privateCount N (fun _ : Unit => row) active ()=A := active_card act e
  have hM : I.card=M := partial_mixed_compression row active p e target
  have hW : mixedReciprocalSum I br=(N:ℝ)*W :=
    partial_reciprocal_compression row active p bid e target hN hphysical
  have hMA : M≤ A := hAeq ▸ partial_mixed_le_active N (fun _ : Unit => row) (fun _ => target0) active p ()
  have hZ := guardError_le_error μ N hN active private0 private1 hactive hprivate0 hprivate1
    p hp bid hbid r u target0 hfair
  dsimp only at hZ
  rw [hAeq] at hZ
  have hstrict : guardError N A M H0 H1 W abar mbar hbar wbar< δ := hZ.trans_lt hgood
  have hγ : 0< γ := hw.trans_le hwγ
  have hs:=source_weight_eq_one_of_guardError N A M H0 H1 hN hMA
    ξ share ρ B0 R Rp γ γ δ W abar mbar hbar wbar reg ν0 ν1
    hξ G.share_mem G.share_lower hρ hB0 (integral_nonneg fun x => (indicator_bounds private0 x).1)
    hγ le_rfl hγ1 G.radius_pos G.radius_mixed G.radius_reciprocal G.radius_capacity
    G.radius_margin hmean0 hmean1 G.lower_endpoint G.upper_endpoint G.private_mean hstrict
  have hquota : (Pnum).owner0 I.card=clampedOwner (A-M) (share*H0) (share*H1) := by
    simp only [TypicalCountParameters.owner0,countParameters,hmean0,hmean1,hM,clampedOwner]
  have hquotaLe : (Pnum).owner0 I.card≤(forcedExclusiveSet target flags).card := by
    rw [OriginalOwnerCount.exclusive_card]
    exact (Pnum).owner0_le I.card
  obtain ⟨hsub,hcard0,hcard1,hdis,hcover⟩:=Hybrid.ownerDivision_support
    (forcedExclusiveSet_nonempty target flags) hquotaLe AB.1 AB.2 hAB
  have hcard1' : AB.2.card=A-M-clampedOwner (A-M) (share*H0) (share*H1) := by
    rw [hcard1,Finset.card_sdiff_of_subset hsub,hcard0,OriginalOwnerCount.exclusive_card,hquota,hM]
  have hdisI : Disjoint I (AB.1∪AB.2) := by
    rw [hcover]
    exact Finset.sdiff_disjoint.symm
  have hfull : I∪(AB.1∪AB.2)=Finset.univ := by
    rw [hcover]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hone : TypicalGuard.weight A H0 H1 (iidCapacity ρ N) ξ B0 R Rp γ
      reg I AB.1 AB.2 br ν0 ν1=1 := by
    rw [TypicalGuardStatistics.actual_weight A H0 H1 (iidCapacity ρ N)
      ξ B0 R Rp γ reg I AB.1 AB.2 br ν0 ν1 hdis hdisI hfull,hcard0,hquota,hcard1',hM,hW]
    exact hs
  have hstep := insertion_step hN hξ.1 G.radius_pos G.radius_reciprocal
    (guardError_bounds N A M H0 H1 W abar mbar hbar wbar).2.2.2.2.2.1 hstrict hroom
  have hg:=guard_of_wide_weight A H0 H1 (iidCapacity ρ N) ξ B B0 R Rp width γ reg
    I AB.1 AB.2 br ν0 ν1 hξ.1 hξ.2 hBB hw hwγ hγ1 (by rw [hW];exact hstep.2) hone
  exact ⟨hg.1,hg.2,(weight_one_margin A H0 H1 (iidCapacity ρ N)
    ξ B0 R Rp γ reg I AB.1 AB.2 br ν0 ν1 hγ hone).2⟩

end ActualOwners
end FCAppendix.Affine.Tail04.UnusedEmpiricalGuard
