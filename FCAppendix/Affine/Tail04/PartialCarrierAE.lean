import FCAppendix.Affine.Tail04.PartialAtomCarrier

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialCarrierAE
open MeasureTheory ProbabilityTheory Set Classical
open PartialAtomCarrier
open scoped BigOperators

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Z) [IsProbabilityMeasure ν]
  (m c : ℕ)

omit [MeasurableSpace X] [MeasurableSpace Z] in
include Z m c in
theorem summed_gain_lower_on_profile (eligible E : Set X) (hsub : E⊆eligible)
    (v b b' q q' : Experiment (X:=X) (Z:=Z) m → Fin m → ℝ)
    (A d : ℝ) (hA : 0≤ A) (hd : 0≤ d)
    (ω : Experiment (X:=X) (Z:=Z) m)
    (huser : ∀ i,ω.1 i∈eligible →
      q ω i∈Icc (0:ℝ) 1 ∧ q' ω i∈Icc (0:ℝ) 1 ∧ q ω i≤ q' ω i ∧
        A≤ v ω i-b' ω i ∧ b ω i≤ b' ω i ∧ b' ω i-b ω i≤ d)
    (hnew : ω∈allEvent (Z:=Z) m E → ∀ i,q' ω i=1)
    (hcapacity : ω∈allEvent (Z:=Z) m E → ∑ i,q ω i≤(c:ℝ)) :
    A*((m:ℝ)-c)*(allEvent (Z:=Z) m E).indicator (fun _ => (1:ℝ)) ω-
      d*(∑ i : Fin m,if ω.1 i∈eligible then (1:ℝ) else 0) ≤
      ∑ i : Fin m,if ω.1 i∈eligible then
        (v ω i-b' ω i)*q' ω i-(v ω i-b ω i)*q ω i else 0 := by
  have hs (i : Fin m) :
      (if ω.1 i∈eligible then A*(q' ω i-q ω i)-d else 0)≤
        if ω.1 i∈eligible then (v ω i-b' ω i)*q' ω i-(v ω i-b ω i)*q ω i else 0 := by
    by_cases hi : ω.1 i∈eligible
    · rw [if_pos hi,if_pos hi]
      obtain ⟨hq,hq',hm,hv,hb,hstep⟩ := huser i hi
      exact private_gain_lower hA hv hd hb hstep hq hq' hm
    · simp only [if_neg hi,le_refl]
  apply le_trans _ (Finset.sum_le_sum (fun i _ => hs i))
  by_cases he : ω∈allEvent (Z:=Z) m E
  · have hell (i : Fin m) : ω.1 i∈eligible := hsub (he.1 i (mem_univ i))
    simp only [Set.indicator_of_mem he,hell,ite_true,mul_one]
    simp_rw [hnew he]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    have hm := mul_le_mul_of_nonneg_left (hcapacity he) hA
    nlinarith
  · rw [Set.indicator_of_notMem he,mul_zero,zero_sub,Finset.mul_sum,←Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : ω.1 i∈eligible
    · simp only [if_pos hi]
      have hm := mul_nonneg hA (sub_nonneg.mpr (huser i hi).2.2.1)
      linarith
    · simp only [if_neg hi,mul_zero,neg_zero,le_refl]

include Z μ ν m c in
theorem finite_noisy_cluster_bound_ae (eligible E : Set X)
    (he : MeasurableSet eligible) (hE : MeasurableSet E) (hsub : E⊆eligible)
    (v b b' q q' : Experiment (X:=X) (Z:=Z) m → Fin m → ℝ)
    (A d : ℝ) (hA : 0≤ A) (hd : 0≤ d)
    (hpoint : ∀ᵐ ω ∂experiment μ ν m,
      (∀ i,ω.1 i∈eligible →
        q ω i∈Icc (0:ℝ) 1 ∧ q' ω i∈Icc (0:ℝ) 1 ∧ q ω i≤ q' ω i ∧
          A≤ v ω i-b' ω i ∧ b ω i≤ b' ω i ∧ b' ω i-b ω i≤ d) ∧
      (ω∈allEvent (Z:=Z) m E → ∀ i,q' ω i=1) ∧
      (ω∈allEvent (Z:=Z) m E → ∑ i,q ω i≤(c:ℝ)))
    (hgain : ∀ i,Integrable (fun ω => if ω.1 i∈eligible then
      (v ω i-b' ω i)*q' ω i-(v ω i-b ω i)*q ω i else 0) (experiment μ ν m))
    (hIC : ∀ i,(∫ ω,if ω.1 i∈eligible then
      (v ω i-b' ω i)*q' ω i-(v ω i-b ω i)*q ω i else 0 ∂experiment μ ν m)≤0) :
    A*((m:ℝ)-c)*(μ.real E)^m≤ d*(m:ℝ)*μ.real eligible := by
  let e : Experiment (X:=X) (Z:=Z) m → Fin m → ℝ :=
    fun ω i => if ω.1 i∈eligible then 1 else 0
  have hei (i : Fin m) : Integrable (fun ω => e ω i) (experiment μ ν m) := by
    exact (integrable_const (1:ℝ)).indicator
      (he.preimage ((measurable_pi_apply i).comp measurable_fst))
  have hei_mass (i : Fin m) : (∫ ω,e ω i ∂experiment μ ν m)=μ.real eligible := by
    have hp : MeasurePreserving (fun ω : Experiment (X:=X) (Z:=Z) m => ω.1 i)
        (experiment μ ν m) μ :=
      (measurePreserving_eval (fun _ : Fin m => μ) i).comp
        (measurePreserving_fst (μ:=Measure.pi (fun _ : Fin m => μ)) (ν:=ν))
    change (∫ ω,eligible.indicator (fun _ => (1:ℝ)) (ω.1 i) ∂experiment μ ν m)=_
    rw [←integral_map hp.measurable.aemeasurable
      (measurable_const.indicator he).aestronglyMeasurable,hp.map_eq]
    change (∫ y,eligible.indicator (1 : X → ℝ) y ∂μ) = _
    rw [integral_indicator_one he]
  have hsumint : Integrable (fun ω => ∑ i : Fin m,e ω i) (experiment μ ν m) :=
    integrable_finsetSum _ (fun i _ => hei i)
  have hfirst : Integrable (fun ω => A*((m:ℝ)-c)*
      (allEvent (Z:=Z) m E).indicator (fun _ => (1:ℝ)) ω) (experiment μ ν m) :=
    ((integrable_const (1:ℝ)).indicator (measurableSet_allEvent m E hE)).const_mul _
  have hsecond := hsumint.const_mul d
  have hh := integral_mono_ae (hfirst.sub hsecond)
    (integrable_finsetSum Finset.univ (fun i _ => hgain i))
    (hpoint.mono fun ω hω => summed_gain_lower_on_profile m c eligible E hsub v b b' q q'
      A d hA hd ω hω.1 hω.2.1 hω.2.2)
  change (∫ ω,A*((m:ℝ)-c)*(allEvent (Z:=Z) m E).indicator (fun _ => (1:ℝ)) ω-
    d*(∑ i : Fin m,e ω i) ∂experiment μ ν m) ≤ _ at hh
  rw [integral_sub hfirst hsecond] at hh
  simp only [integral_const_mul] at hh
  have hfirst_mass : (∫ ω,(allEvent (Z:=Z) m E).indicator (fun _ => (1:ℝ)) ω
      ∂experiment μ ν m) = (μ.real E)^m := by
    change (∫ ω,(allEvent (Z:=Z) m E).indicator
      (1 : Experiment (X:=X) (Z:=Z) m → ℝ) ω ∂experiment μ ν m) = _
    rw [integral_indicator_one (measurableSet_allEvent m E hE),allEvent_mass μ ν m E hE]
  rw [hfirst_mass] at hh
  rw [integral_finsetSum _ (fun i _ => hei i),integral_finsetSum _ (fun i _ => hgain i)] at hh
  simp_rw [hei_mass] at hh
  have hi := Finset.sum_nonpos (s:=Finset.univ) (fun i _ => hIC i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  nlinarith

end FCAppendix.Affine.Tail04.PartialCarrierAE
