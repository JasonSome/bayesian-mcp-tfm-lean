import FCAppendix.Affine.Hybrid.PopulationRows
import FCAppendix.Affine.Hybrid.NativeUpperRank
import FCAppendix.Finite.SingletonDeviation

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Game Bayes Set

theorem upper_contact_measure {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (j : Fin 2) (B : Set ℝ)
    (hroute : ∀ᵐx ∂Gamma.F⊗ₘGamma.σ,x.2.bid∈B→x.2.routeCount=1) :
    userLaw Gamma {d | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid∈B}=
      (Gamma.F⊗ₘGamma.σ) {x | x.2.bid∈B}*(permLaw 2) {tau | j∈firstK tau 1} := by
  let E : Set (ℝ×JointAction 2):={x | x.2.bid∈B}
  let R : Set (Equiv.Perm (Fin 2)):={tau | j∈firstK tau 1}
  have hr : ∀ᵐd ∂userLaw Gamma,d.1.2.bid∈B→d.1.2.routeCount=1:=
    (measurePreserving_fst (μ:=Gamma.F⊗ₘGamma.σ) (ν:=permLaw 2)).quasiMeasurePreserving.ae hroute
  have he : {d : UserDraw 2 | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid∈B}=ᵐ[userLaw Gamma] E×ˢR:=by
    filter_upwards [hr] with d hd
    apply propext
    change (j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid∈B) ↔
      (d.1.2.bid∈B ∧ j∈firstK d.2 1)
    by_cases hb : d.1.2.bid∈B
    · simp only [hb,and_true,true_and,hd hb]
    · simp only [hb,and_false,false_and]
  rw [measure_congr he,userLaw,Measure.prod_prod]

theorem upper_alphaGt {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (j : Fin 2) (y : ℝ)
    (hroute : ∀ᵐx ∂Gamma.F⊗ₘGamma.σ,y<x.2.bid→x.2.routeCount=1) :
    alphaGt Gamma j y=(Gamma.F⊗ₘGamma.σ).real {x | y<x.2.bid}/2 := by
  have he:=congrArg ENNReal.toReal (upper_contact_measure Gamma j (Ioi y) hroute)
  rw [ENNReal.toReal_mul] at he
  change alphaGt Gamma j y=(Gamma.F⊗ₘGamma.σ).real {x | y<x.2.bid}*
    (permLaw 2).real {tau | j∈firstK tau 1} at he
  rw [permLaw_mem_firstK 2 1 (by norm_num) (by norm_num) j] at he
  norm_num at he
  simpa only [div_eq_mul_inv,one_mul] using he

theorem population_measure_above (U s a h : ℝ)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hL : ∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),x.2.bid ≤ U)
    (hA : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),x.2.bid ≤ U)
    (B : Set ℝ) (hBU : B⊆Ioi U) :
    populationJoint s a h PL PA PH {x | x.2.bid∈B}=
      ENNReal.ofReal h*(PH : Measure (ℝ×JointAction 2)) {x | x.2.bid∈B} := by
  have hzero (P : ProbabilityMeasure (ℝ×JointAction 2))
      (hP : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),x.2.bid ≤ U) :
      (P : Measure (ℝ×JointAction 2)) {x | x.2.bid∈B}=0:=by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hP] with x hx hmem
    exact (not_lt.mpr hx) (hBU hmem)
  simp only [populationJoint,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
    hzero PL hL,hzero PA hA,mul_zero,zero_add]

theorem upper_visible_atomless_of_joint {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (U : ℝ)
    (hzero : ∀b : ℝ,U<b→(Gamma.F⊗ₘGamma.σ) {x | x.2.bid=b}=0) :
    ∀(j : Fin 2)(b : ℝ),U<b→
      userLaw Gamma {d | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid=b}=0 := by
  intro j b hb
  have hz : userLaw Gamma {d : UserDraw 2 | d.1.2.bid=b}=0:=by
    have he : {d : UserDraw 2 | d.1.2.bid=b}={x : ℝ×JointAction 2 | x.2.bid=b}×ˢuniv:=by ext d;simp
    rw [he,userLaw]
    rw [Measure.prod_prod,hzero b hb,zero_mul]
  exact measure_mono_null (fun _ hx=>hx.2) hz

theorem population_upper_alphaGt (m c : ℕ) (U s a h : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hL : ∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),x.2.bid ≤ U)
    (hA : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),x.2.bid ≤ U)
    (hH : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),x.2.routeCount=1)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η<1) (j : Fin 2) (y : ℝ) (hy : U<y) :
    let P:=populationLaw s a h hs ha hh hsum PL PA PH
    let Gamma:=PopulationGame.game m c P η hη0 hη1 U
    alphaGt Gamma j y=h*(PH : Measure (ℝ×JointAction 2)).real {x | y<x.2.bid}/2 := by
  dsimp only
  let P:=populationLaw s a h hs ha hh hsum PL PA PH
  let Gamma:=PopulationGame.game m c P η hη0 hη1 U
  have hrL : ∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),y<x.2.bid→x.2.routeCount=1:=
    hL.mono (fun _ hx hb=>(not_lt.mpr (hx.trans hy.le) hb).elim)
  have hrA : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),y<x.2.bid→x.2.routeCount=1:=
    hA.mono (fun _ hx hb=>(not_lt.mpr (hx.trans hy.le) hb).elim)
  have hrH : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),y<x.2.bid→x.2.routeCount=1:=
    hH.mono (fun _ hx _=>hx)
  have hr : ∀ᵐx ∂Gamma.F⊗ₘGamma.σ,y<x.2.bid→x.2.routeCount=1:=by
    rw [PopulationGame.joint_law]
    exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr
      ⟨Measure.ae_smul_measure hrL _,Measure.ae_smul_measure hrA _⟩,Measure.ae_smul_measure hrH _⟩
  rw [upper_alphaGt Gamma j y hr]
  congr 1
  change ((Gamma.F⊗ₘGamma.σ) {x | y<x.2.bid}).toReal=_
  rw [PopulationGame.joint_law]
  have he:=population_measure_above U s a h PL PA PH hL hA (Ioi y)
    (fun _ hx=>hy.trans hx)
  change (populationJoint s a h PL PA PH {x | y<x.2.bid}).toReal=_
  change populationJoint s a h PL PA PH {x | y<x.2.bid}=
    ENNReal.ofReal h*(PH : Measure (ℝ×JointAction 2)) {x | y<x.2.bid} at he
  rw [he,ENNReal.toReal_mul,ENNReal.toReal_ofReal hh]
  rfl

theorem population_upper_visible_atomless (m c : ℕ) (U s a h : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hL : ∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),x.2.bid ≤ U)
    (hA : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),x.2.bid ≤ U)
    (hH : ∀b : ℝ,(PH : Measure (ℝ×JointAction 2)) {x | x.2.bid=b}=0)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η<1) :
    let P:=populationLaw s a h hs ha hh hsum PL PA PH
    let Gamma:=PopulationGame.game m c P η hη0 hη1 U
    ∀(j : Fin 2)(b : ℝ),U<b→
      userLaw Gamma {d | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid=b}=0 := by
  dsimp only
  apply upper_visible_atomless_of_joint
  intro b hb
  rw [PopulationGame.joint_law]
  have he:=population_measure_above U s a h PL PA PH hL hA {b}
    (fun x hx=>show U<x from by rw [mem_singleton_iff.mp hx];exact hb)
  change populationJoint s a h PL PA PH {x | x.2.bid∈({b}:Set ℝ)}=0
  rw [he]
  simp only [mem_singleton_iff,hH b,mul_zero]

theorem population_upper_singleton_payoff (m c : ℕ) (U s a h : ℝ) (hU : 0 ≤ U)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hL : ∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),x.2.bid ≤ U)
    (hA : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),x.2.bid ≤ U)
    (hH : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),x.2.routeCount=1)
    (hnull : ∀b : ℝ,(PH : Measure (ℝ×JointAction 2)) {x | x.2.bid=b}=0)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η<1) (i : Fin m) (v : ℝ)
    (act : JointAction 2) (hk : act.routeCount=1) (hb : U<act.bid) :
    let P:=populationLaw s a h hs ha hh hsum PL PA PH
    let Gamma:=PopulationGame.game m c P η hη0 hη1 U
    (problem Gamma i).payoff v act=(v-act.bid)*
      binomBelow (m-1) (h*(PH : Measure (ℝ×JointAction 2)).real {x | act.bid<x.2.bid}/2) c := by
  dsimp only
  let P:=populationLaw s a h hs ha hh hsum PL PA PH
  let Gamma:=PopulationGame.game m c P η hη0 hη1 U
  let C:=NativeContinuation.contextPolicy (m:=m) ((1-η)/2) (by linarith) (by linarith) c
  have hgame : C.nativeGame Gamma U=Gamma:=by rfl
  have hn:=population_upper_visible_atomless m c U s a h hs ha hh hsum PL PA PH hL hA hnull η hη0 hη1
  have hr:=C.native_upper_meanAcceptProb Gamma hU (by simpa only [hgame] using hn) i act.bid hb
  rw [hgame] at hr
  have ht:=population_upper_alphaGt m c U s a h hs ha hh hsum PL PA PH hL hA hH η hη0 hη1 0 act.bid hb
  rw [ht] at hr
  rw [singleton_payoff Gamma (by norm_num) i act hk,hr]
  change (v-0-act.bid)*_=(v-act.bid)*_
  rw [sub_zero]

end FCAppendix.Affine.Hybrid
