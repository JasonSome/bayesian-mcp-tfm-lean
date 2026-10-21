import FCAppendix.Affine.Tail04.CommonFiniteCountError
import FCAppendix.Affine.Tail04.BidDependentFlags

noncomputable section
namespace FCAppendix.Affine.Tail04.CommonRankAverage
open MeasureTheory ProbabilityTheory Set Classical
open OriginalFlagCompression OriginalFlagMeasure MenuError
open scoped BigOperators

def suffix {X : Type*} (N : ℕ) (u : Fin (N+1)→ X) : Fin N→ X := fun j => u j.succ

lemma suffix_preserving (N : ℕ) :
    MeasurePreserving (suffix (X:=unitInterval) N)
      (Measure.pi (fun _ : Fin (N+1) => (volume : Measure unitInterval)))
      (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))) := by
  convert! measurePreserving_snd.comp
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (N+1) => (volume : Measure unitInterval)) 0) using 1

lemma flag_coordinate_expect {ι : Type*} [Fintype ι]
    (p : ι→ unitInterval) (i : ι) (a d : ℝ) :
    (independentFlagLaw (fun j => (p j:ℝ))
      (fun j => (p j).2.1) (fun j => (p j).2.2)).expect
      (fun z => if z i then a else d)=(p i:ℝ)*a+(1-(p i:ℝ))*d := by
  have hp : independentFlagLaw (fun j => (p j:ℝ))
      (fun j => (p j).2.1) (fun j => (p j).2.2)=
      BidDependentFlags.product (fun j => IndependentCounts.bernoulli (p j) (p j).2.1 (p j).2.2) := rfl
  calc
    _ = (IndependentCounts.bernoulli (p i) (p i).2.1 (p i).2.2).expect
        (fun z : Bool => if z then a else d) :=
      BidDependentFlags.expect_coordinate
        (fun j => IndependentCounts.bernoulli (p j) (p j).2.1 (p j).2.2)
        i (fun z : Bool => if z then a else d)
    _ = _ := by
      simp only [FiniteLaw.expect,Fintype.sum_bool,IndependentCounts.bernoulli,ite_true,Bool.false_eq_true,ite_false]

private lemma flag_expect_dec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι→unitInterval) (f : (ι→Bool)→ℝ) :
    (independentFlagLaw (fun i=>(p i:ℝ)) (fun i=>(p i).2.1) (fun i=>(p i).2.2)).expect f=
      ∫u,f (flags p u) ∂Measure.pi (fun _ : ι=>(volume : Measure unitInterval)) := by
  have hlaw : FiniteLaw.ofMeasure (Measure.pi fun _ : ι=>(volume : Measure unitInterval))
      (flags p) (measurable_flags p)=
      independentFlagLaw (fun i=>(p i:ℝ)) (fun i=>(p i).2.1) (fun i=>(p i).2.2) := by
    apply FiniteLaw.ext
    intro z
    rw [FiniteLaw.ofMeasure_mass]
    have he : {u : ι→unitInterval | flags p u=z}=
        Set.univ.pi (fun i=>{v : unitInterval | Empirical.flag (p i) v=z i}) := by
      ext u
      simp only [flags,Set.mem_setOf_eq,Set.mem_univ_pi,funext_iff]
    rw [he,Measure.pi_pi,ENNReal.toReal_prod]
    change (∏ i,_) = ∏ i,(IndependentCounts.bernoulli (p i) (p i).2.1 (p i).2.2).mass (z i)
    apply Finset.prod_congr rfl
    intro i _
    rw [←FiniteLaw.ofMeasure_mass (volume : Measure unitInterval) (Empirical.flag (p i))
      (Empirical.measurable_flag_fixed (p i)),Empirical.uniform_flag_law]
  exact (congrArg (fun law : FiniteLaw (ι→Bool)=>law.expect f) hlaw.symm).trans
    (FiniteLaw.expect_ofMeasure _ _ (measurable_flags p) f)

section Prefix
variable {N A : ℕ} [Nonempty (Fin A)]
  (active : Fin (N+1)→ Bool) (e : Fin A≃Active active)
  (p : Fin (N+1)→ unitInterval) (b : Fin A→ℝ) (i : Fin A)
  (hi : (e i).val=0) (Q : ℕ→ℝ→ℝ→ CountLaw 2)
  (phi : ℕ→ℝ→ unitInterval) (fallback ideal : CountLaw 2)
  (f : Fin 3→ℝ) (K : ℝ) (hK : 0≤ K)
  (Z : (Fin N→ unitInterval)→ℝ)
  (hZ : Measurable Z)
  (hZi : Integrable Z (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))))

local notation "Zmean" => ∫ u,Z u ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

omit [Nonempty (Fin A)] in
include hZ hZi in
theorem conditional_error
    (hpoint : ∀ target : Fin A,∀ u : Fin (N+1)→ unitInterval,
      |(FiniteLaw.mixture
          (targetStateCount Q b target (compressedFlags active e (flags p u)) i) fallback
          (targetTypicalWeight phi b target (compressedFlags active e (flags p u)))
          (targetTypicalWeight_bounds phi b target _).1
          (targetTypicalWeight_bounds phi b target _).2).expect f-
        (if Empirical.flag (p 0) (u 0) then ideal else FiniteLaw.dirac 1).expect f|≤
          K*Z (suffix N u)+2*MenuError.oscillation f*(if i=target then 1 else 0)) (target : Fin A) :
    |(conditionalTargetCount Q phi b (fun j : Fin A => (p (e j).val:ℝ)) (fun j => (p (e j).val).2.1) (fun j => (p (e j).val).2.2) target i fallback).expect f-
      (FiniteLaw.mixture ideal (FiniteLaw.dirac 1) (p 0) (p 0).2.1 (p 0).2.2).expect f|≤
        K*Zmean+2*MenuError.oscillation f*(if i=target then 1 else 0) := by
  let C : (Fin A→ Bool)→ CountLaw 2 := fun z => FiniteLaw.mixture
    (targetStateCount Q b target z i) fallback (targetTypicalWeight phi b target z)
    (targetTypicalWeight_bounds phi b target z).1 (targetTypicalWeight_bounds phi b target z).2
  let ν := Measure.pi (fun _ : Fin (N+1) => (volume : Measure unitInterval))
  let actual := fun u : Fin (N+1)→ unitInterval => (C (compressedFlags active e (flags p u))).expect f
  let bench := fun u : Fin (N+1)→ unitInterval =>
    (if Empirical.flag (p 0) (u 0) then ideal else FiniteLaw.dirac 1).expect f
  have hactual : Integrable actual ν := FiniteLaw.integrable_expect ν
    (fun u => C (compressedFlags active e (flags p u)))
    (fun k => (measurable_of_countable
      (fun z : Fin (N+1)→ Bool => (C (compressedFlags active e z)).mass k)).comp (measurable_flags p)) f
  have hbench : Integrable bench ν := FiniteLaw.integrable_expect ν
    (fun u => if Empirical.flag (p 0) (u 0) then ideal else FiniteLaw.dirac 1)
    (fun k => (measurable_of_countable (fun z : Bool =>
      (if z then ideal else FiniteLaw.dirac 1).mass k)).comp
        ((Empirical.measurable_flag_fixed (p 0)).comp (measurable_pi_apply 0))) f
  have heActual : (conditionalTargetCount Q phi b (fun j : Fin A => (p (e j).val:ℝ)) (fun j => (p (e j).val).2.1) (fun j => (p (e j).val).2.2) target i fallback).expect f=
      ∫ u,actual u ∂ν := by
    simp only [conditionalTargetCount,FiniteLaw.expect_finiteMix]
    rw [flag_expect_compression active e p]
    exact flag_expect_dec p (fun z => (C (compressedFlags active e z)).expect f)
  have heBench : (FiniteLaw.mixture ideal (FiniteLaw.dirac 1) (p 0)
      (p 0).2.1 (p 0).2.2).expect f=∫ u,bench u ∂ν := by
    rw [FiniteLaw.expect_mixture]
    have he := flag_coordinate_expect p 0 (ideal.expect f) ((FiniteLaw.dirac 1).expect f)
    rw [flag_expect p] at he
    refine he.symm.trans ?_
    apply integral_congr_ae
    refine ae_of_all _ fun u => ?_
    dsimp [bench,flags]
    split <;> rfl
  have hiZ : Integrable (fun u => Z (suffix N u)) ν :=
    (suffix_preserving N).integrable_comp_of_integrable hZi
  have hiB : Integrable (fun u => K*Z (suffix N u)+
      2*MenuError.oscillation f*(if i=target then 1 else 0)) ν :=
    (hiZ.const_mul K).add (integrable_const _)
  rw [heActual,heBench,←integral_sub hactual hbench]
  have hb := (abs_integral_le_integral_abs (f:=fun u => actual u-bench u)).trans
    (integral_mono (hactual.sub hbench).abs hiB (fun u => hpoint target u))
  have hz := integral_map (μ:=ν) (suffix_preserving N).measurable.aemeasurable hZ.aestronglyMeasurable
  rw [(suffix_preserving N).map_eq] at hz
  rw [integral_add (hiZ.const_mul K) (integrable_const _),integral_const_mul,
    integral_const,probReal_univ,one_smul] at hb
  have hz' : (∫ u,Z (suffix N u) ∂ν)=Zmean := hz.symm
  rw [hz'] at hb
  exact hb

include hZ hZi in
theorem rank_error
    (hpoint : ∀ target : Fin A,∀ u : Fin (N+1)→ unitInterval,
      |(FiniteLaw.mixture
          (targetStateCount Q b target (compressedFlags active e (flags p u)) i) fallback
          (targetTypicalWeight phi b target (compressedFlags active e (flags p u)))
          (targetTypicalWeight_bounds phi b target _).1
          (targetTypicalWeight_bounds phi b target _).2).expect f-
        (if Empirical.flag (p 0) (u 0) then ideal else FiniteLaw.dirac 1).expect f|≤
          K*Z (suffix N u)+2*MenuError.oscillation f*(if i=target then 1 else 0)) :
    |(typicalRankCount Q phi b (fun j : Fin A => (p (e j).val:ℝ)) (fun j => (p (e j).val).2.1) (fun j => (p (e j).val).2.2) i fallback).expect f-
      (FiniteLaw.mixture ideal (FiniteLaw.dirac 1) (p 0) (p 0).2.1 (p 0).2.2).expect f|≤
        K*Zmean+4*MenuError.oscillation f/(A:ℝ) := by
  let T := (FiniteLaw.mixture ideal (FiniteLaw.dirac 1) (p 0) (p 0).2.1 (p 0).2.2).expect f
  rw [typicalRankCount,FiniteLaw.expect_finiteMix]
  have he : (Hybrid.rankLaw b).expect
      (fun target => (conditionalTargetCount Q phi b (fun j : Fin A => (p (e j).val:ℝ)) (fun j => (p (e j).val).2.1) (fun j => (p (e j).val).2.2) target i fallback).expect f)-T=
      (Hybrid.rankLaw b).expect
        (fun target => (conditionalTargetCount Q phi b (fun j : Fin A => (p (e j).val:ℝ)) (fun j => (p (e j).val).2.1) (fun j => (p (e j).val).2.2) target i fallback).expect f-T) := by
    rw [FiniteLaw.expect_sub,FiniteLaw.expect_const]
  rw [he]
  have hh := ((Hybrid.rankLaw b).abs_expect_le _).trans
    ((Hybrid.rankLaw b).expect_mono (fun target =>
      conditional_error active e p b i Q phi fallback ideal f K Z hZ hZi hpoint target))
  have hsingle : (Hybrid.rankLaw b).expect
      (fun target => if i=target then (1:ℝ) else 0)=(Hybrid.rankLaw b).mass i := by
    simp [FiniteLaw.expect]
  rw [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_const_mul,hsingle] at hh
  have ht := mul_le_mul_of_nonneg_left (Hybrid.rankLaw_mass_le b i)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (oscillation_nonneg f))
  simp only [Fintype.card_fin] at ht
  exact hh.trans (by nlinarith [show 2*MenuError.oscillation f*(2/(A:ℝ))=4*MenuError.oscillation f/(A:ℝ) by ring])

end Prefix
end FCAppendix.Affine.Tail04.CommonRankAverage
