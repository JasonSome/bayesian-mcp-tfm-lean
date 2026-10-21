import FCAppendix.Affine.Tail04.AllNoiseFiniteSelector
import FCAppendix.Affine.Tail04.EqualReceiptLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroNoiseAffine
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open AllNoiseFiniteSelector
open scoped BigOperators

lemma ae_affine_ne {L U : ℝ} (μ : Measure (Icc L U)) [NullSingletonClass μ]
    (a b t : ℝ) (ha : a≠0) : ∀ᵐ (x : Icc L U) ∂μ, a*(x:ℝ)+b≠t := by
  apply EqualReceiptLaw.ae_ne_of_injective (X := Icc L U) μ (fun x : Icc L U=> a*(x:ℝ)+b) _ t
  intro x y hxy
  apply Subtype.ext
  have hz : a*((x:ℝ)-(y:ℝ))=0 := by nlinarith [hxy]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha)

theorem ae_iid_linear_ne {N : ℕ} {L U : ℝ} (μ : Measure (Icc L U))
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (a : Fin N→ℝ) (j : Fin N) (hj : a j≠0) (t : ℝ) :
    ∀ᵐ (x : Fin N → Icc L U) ∂Measure.pi (fun _ : Fin N=> μ),(∑ i,a i*(x i:ℝ))≠t := by
  cases N with
  | zero => exact Fin.elim0 j
  | succ M =>
    let e:=MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M+1)=> Icc L U) j
    let f : (Fin (M+1)→ Icc L U)→ℝ:=fun x=>∑ i,a i*(x i:ℝ)
    have hfm : Measurable f := by dsimp [f];fun_prop
    have he (x : Icc L U) (r : Fin M→ Icc L U) :
        f (e.symm (x,r))=a j*(x:ℝ)+∑ k,a (j.succAbove k)*(r k:ℝ) := by
      dsimp only [f]
      rw [Fin.sum_univ_succAbove _ j]
      simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
    have hS : MeasurableSet {y : Icc L U×(Fin M→ Icc L U) | f (e.symm y)≠t} :=
      (measurableSet_eq_fun (hfm.comp e.symm.measurable) measurable_const).compl
    have hp : ∀ᵐ y ∂μ.prod (Measure.pi (fun _ : Fin M=> μ)),f (e.symm y)≠t := by
      apply (Measure.ae_prod_iff_ae_ae hS).mpr
      apply (Measure.ae_ae_comm hS).mpr
      apply ae_of_all
      intro r
      filter_upwards [ae_affine_ne μ (a j) (∑ k,a (j.succAbove k)*(r k:ℝ)) t hj] with x hx
      rwa [he]
    have hm:=measurePreserving_piFinSuccAbove (fun _ : Fin (M+1)=> μ) j
    have h:=hm.quasiMeasurePreserving.ae hp
    simpa only [e,MeasurableEquiv.symm_apply_apply] using h

lemma homogeneous_cons_difference {N : ℕ} {A : Type*} (a : A→ Fin (N+1)→ℝ)
    (b : ℝ) (r : Fin N→ℝ) (x y : A) :
    score (fun _=>0) a (Fin.cons b r) x-score (fun _=>0) a (Fin.cons b r) y=
      (a x 0-a y 0)*b+∑ i,(a x i.succ-a y i.succ)*r i := by
  have hs : (∑ i,a x i.succ*r i)-(∑ i,a y i.succ*r i)=
      ∑ i,(a x i.succ-a y i.succ)*r i := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [score,zero_add,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  linear_combination hs

theorem ae_cons_score_ties_identical {N : ℕ} {L U : ℝ} {A : Type*} [Fintype A]
    (μ : Measure (Icc L U)) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (a : A→ Fin (N+1)→ℝ) (b : ℝ) (hb : b≠0) :
    ∀ᵐ (r : Fin N → Icc L U) ∂Measure.pi (fun _ : Fin N=> μ),∀ x y,
      score (fun _=>0) a (Fin.cons b (fun i=>(r i:ℝ))) x=
        score (fun _=>0) a (Fin.cons b (fun i=>(r i:ℝ))) y→ a x=a y := by
  apply ae_all_iff.mpr
  intro x
  apply ae_all_iff.mpr
  intro y
  by_cases ha : a x=a y
  · exact ae_of_all _ fun _ _=> ha
  · by_cases hr : ∃ i : Fin N,a x i.succ≠a y i.succ
    · obtain ⟨i,hi⟩:=hr
      filter_upwards [ae_iid_linear_ne μ (fun k=> a x k.succ-a y k.succ) i
        (sub_ne_zero.mpr hi) (-(a x 0-a y 0)*b)] with r hr he
      apply False.elim (hr ?_)
      have hh:=homogeneous_cons_difference a b (fun k=>(r k:ℝ)) x y
      rw [he,sub_self] at hh
      linarith
    · have htail : ∀ i : Fin N,a x i.succ=a y i.succ := by
        simpa only [not_exists,not_not] using hr
      have hhead : a x 0≠a y 0 := by
        intro h
        apply ha
        funext i
        exact Fin.cases h htail i
      apply ae_of_all
      intro r he
      apply False.elim
      have hh:=homogeneous_cons_difference a b (fun k=>(r k:ℝ)) x y
      rw [he,sub_self] at hh
      simp only [htail,sub_self,zero_mul,Finset.sum_const_zero,add_zero] at hh
      exact (mul_ne_zero (sub_ne_zero.mpr hhead) hb) hh.symm

theorem ae_cons_distinct {N : ℕ} {L U : ℝ} (μ : Measure (Icc L U))
    [IsProbabilityMeasure μ] [NullSingletonClass μ] (b : ℝ) (hb : b≠0) :
    ∀ᵐ (r : Fin N → Icc L U) ∂Measure.pi (fun _ : Fin N=> μ),∀ i j : Fin (N+1),i≠j→
      (Fin.cons b (fun k=>(r k:ℝ)) : Fin (N+1) → ℝ) i ≠
        (Fin.cons b (fun k=>(r k:ℝ)) : Fin (N+1) → ℝ) j := by
  let a : Fin (N+1)→ Fin (N+1)→ℝ:=fun i j=> if j=i then 1 else 0
  have hs (v : Fin (N+1)→ℝ) (i : Fin (N+1)) : score (fun _=>0) a v i=v i := by
    simp [score,a,ite_mul]
  filter_upwards [ae_cons_score_ties_identical μ a b hb] with r hr
  intro i j hij he
  have heq : score (fun _ => 0) a (Fin.cons b (fun k => (r k:ℝ))) i =
      score (fun _ => 0) a (Fin.cons b (fun k => (r k:ℝ))) j := by
    rw [hs, hs]
    exact he
  have ha:=congrFun (hr i j heq) i
  simp [a,hij] at ha

end FCAppendix.Affine.Tail04.ZeroNoiseAffine
