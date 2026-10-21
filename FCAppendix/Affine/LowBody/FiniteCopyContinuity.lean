import FCAppendix.Affine.ResidualPotential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Filter Topology
open scoped BigOperators

section FiniteLabels
variable {X A D : Type*} [TopologicalSpace X] [Fintype A] [Nonempty A]

theorem selected_label_eventually_eq (f : X→A→ℝ) (hf : ∀a,Continuous (fun x=>f x a))
    (label : A→D)
    (x₀ : X) (hgeneric : ∀a b,f x₀ a=f x₀ b→label a=label b) :
    ∀ᶠx in 𝓝 x₀,label (FiniteSelector.select (f x))=label (FiniteSelector.select (f x₀)) := by
  classical
  let a₀:=FiniteSelector.select (f x₀)
  have he : ∀a,∀ᶠx in 𝓝 x₀,label a≠label a₀→f x a<f x a₀ := by
    intro a
    by_cases ha : label a=label a₀
    · exact Eventually.of_forall (fun _ h=>False.elim (h ha))
    · have hlt : f x₀ a<f x₀ a₀ := by
        have hle:=FiniteSelector.select_max (f x₀) a
        exact lt_of_le_of_ne hle (fun heq=>ha (hgeneric a a₀ heq))
      have hh : ∀ᶠx in 𝓝 x₀,f x a<f x a₀ := (isOpen_lt (hf a) (hf a₀)).mem_nhds hlt
      exact hh.mono (fun _ h _=>h)
  filter_upwards [Filter.eventually_all.mpr he] with x hx
  by_contra hn
  have hh:=hx (FiniteSelector.select (f x)) hn
  exact (not_lt_of_ge (FiniteSelector.select_max (f x) a₀)) hh

theorem continuousAt_selected_payoff (f : X→A→ℝ) (hf : ∀a,Continuous (fun x=>f x a))
    (label : A→D)
    (u : X→A→ℝ) (hu : ∀a,Continuous (fun x=>u x a))
    (hulabel : ∀x a b,label a=label b→u x a=u x b)
    (x₀ : X) (hgeneric : ∀a b,f x₀ a=f x₀ b→label a=label b) :
    ContinuousAt (fun x=>u x (FiniteSelector.select (f x))) x₀ := by
  apply (hu (FiniteSelector.select (f x₀))).continuousAt.congr
  exact (selected_label_eventually_eq f hf label x₀ hgeneric).mono
    (fun x hx=>(hulabel x _ _ hx).symm)

end FiniteLabels
end FCAppendix.Affine.LowBody

namespace FCAppendix.Affine.LowBody
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem ae_affine_ne (mu : Measure ℝ) [NullSingletonClass mu]
    (a b t : ℝ) (ha : a≠0) : ∀ᵐz ∂mu,a*z+b≠t := by
  filter_upwards [mu.ae_ne ((t-b)/a)] with z hz he
  apply hz
  apply (eq_div_iff ha).mpr
  linarith

section Copies
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def focalCopy (P : Finset ι × Finset ι) (i : ι) : Fin 3 :=
  if i∈P.1∩P.2 then 2 else if i∈P.1∪P.2 then 1 else 0

def copyCoefficient (κ : ℝ) (P : Finset ι × Finset ι) (i : ι) : ℝ :=
  (if i∈P.1∪P.2 then 1 else 0)+κ*(if i∈P.1∩P.2 then 1 else 0)

omit [Fintype ι] in
theorem copyCoefficient_eq (κ : ℝ) (P : Finset ι × Finset ι) (i : ι) :
    copyCoefficient κ P i=
      if focalCopy P i=2 then 1+κ else if focalCopy P i=1 then 1 else 0 := by
  by_cases hS : i∈P.1 <;> by_cases hT : i∈P.2 <;>
    simp [copyCoefficient,focalCopy,hS,hT]

omit [Fintype ι] in
theorem copyCoefficient_ne_of_focalCopy_ne {κ : ℝ} (hκ : 0<κ)
    (P Q : Finset ι × Finset ι) (i : ι) (hne : focalCopy P i≠focalCopy Q i) :
    copyCoefficient κ P i≠copyCoefficient κ Q i := by
  rw [copyCoefficient_eq,copyCoefficient_eq]
  generalize focalCopy P i=x at *
  generalize focalCopy Q i=y at *
  fin_cases x <;> fin_cases y <;> simp_all [Fin.ext_iff] <;> linarith

theorem potential_eq_copyCoefficient (κ : ℝ) (b : ι→ℝ) (P : Finset ι × Finset ι) :
    CompleteInformation.potential κ b P.1 P.2=∑i,copyCoefficient κ P i*b i := by
  unfold copyCoefficient CompleteInformation.potential
  simp_rw [add_mul,mul_assoc,ite_mul,one_mul,zero_mul]
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  have hs (U : Finset ι) : (∑i,if i∈U then b i else 0)=∑i∈U,b i := by simp
  rw [hs,hs]

def noisyFocal (i : ι) (ε : ℝ) (b : ι→ℝ) (z : ℝ) : ι→ℝ :=
  Function.update b i (b i*(1+ε*z))

theorem potential_noisyFocal (κ ε : ℝ) (b : ι→ℝ) (z : ℝ)
    (P : Finset ι × Finset ι) (i : ι) :
    CompleteInformation.potential κ (noisyFocal i ε b z) P.1 P.2=
      copyCoefficient κ P i*b i*ε*z+CompleteInformation.potential κ b P.1 P.2 := by
  rw [potential_eq_copyCoefficient,potential_eq_copyCoefficient]
  rw [←Finset.add_sum_erase Finset.univ (fun j=>copyCoefficient κ P j*noisyFocal i ε b z j)
    (Finset.mem_univ i),
    ←Finset.add_sum_erase Finset.univ (fun j=>copyCoefficient κ P j*b j) (Finset.mem_univ i)]
  have hh : (∑j∈Finset.univ.erase i,copyCoefficient κ P j*noisyFocal i ε b z j)=
      ∑j∈Finset.univ.erase i,copyCoefficient κ P j*b j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [noisyFocal,Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hh]
  simp only [noisyFocal,Function.update_self]
  ring

theorem ae_potential_ties_same_focalCopy (mu : Measure ℝ) [NullSingletonClass mu]
    {κ ε : ℝ} (hκ : 0<κ) (hε : ε≠0) (b : ι→ℝ) (i : ι) (hb : b i≠0) :
    ∀ᵐz ∂mu,∀P Q : Finset ι × Finset ι,
      CompleteInformation.potential κ (noisyFocal i ε b z) P.1 P.2=
        CompleteInformation.potential κ (noisyFocal i ε b z) Q.1 Q.2→
      focalCopy P i=focalCopy Q i := by
  classical
  apply ae_all_iff.mpr
  intro P
  apply ae_all_iff.mpr
  intro Q
  by_cases hcopy : focalCopy P i=focalCopy Q i
  · exact Eventually.of_forall (fun _ _=>hcopy)
  · have hdiff : copyCoefficient κ P i-copyCoefficient κ Q i≠0 :=
      sub_ne_zero.mpr (copyCoefficient_ne_of_focalCopy_ne hκ P Q i hcopy)
    have hn : (copyCoefficient κ P i-copyCoefficient κ Q i)*b i*ε≠0 :=
      mul_ne_zero (mul_ne_zero hdiff hb) hε
    filter_upwards [ae_affine_ne mu ((copyCoefficient κ P i-copyCoefficient κ Q i)*b i*ε)
      (CompleteInformation.potential κ b P.1 P.2-CompleteInformation.potential κ b Q.1 Q.2) 0 hn]
      with z hz he
    apply False.elim (hz ?_)
    rw [potential_noisyFocal,potential_noisyFocal] at he
    nlinarith

def purePayoff (κ w : ℝ) (b : ι→ℝ) (P : Finset ι × Finset ι) (i : ι) : ℝ :=
  if focalCopy P i=2 then w-2*κ*b i
  else if focalCopy P i=1 then w-b i else 0

omit [Fintype ι] in
theorem purePayoff_eq_of_focalCopy_eq (κ w : ℝ) (b : ι→ℝ)
    (P Q : Finset ι × Finset ι) (i : ι) (h : focalCopy P i=focalCopy Q i) :
    purePayoff κ w b P i=purePayoff κ w b Q i := by
  simp only [purePayoff,h]

omit [Fintype ι] in
theorem continuous_noisyFocal (i : ι) (ε : ℝ) :
    Continuous (fun t : (ι→ℝ)×ℝ=>noisyFocal i ε t.1 t.2) := by
  apply continuous_pi
  intro j
  by_cases hji : j=i
  · subst j
    simp only [noisyFocal,Function.update_self]
    fun_prop
  · simp only [noisyFocal,Function.update_of_ne hji]
    fun_prop

theorem continuous_potential (κ : ℝ) (P : Finset ι × Finset ι) :
    Continuous (fun b : ι→ℝ=>CompleteInformation.potential κ b P.1 P.2) := by
  simp_rw [potential_eq_copyCoefficient]
  fun_prop

section Candidates
variable {A : Type*} [Fintype A] [Nonempty A]

def pureNoisyPayoff (pair : A→Finset ι × Finset ι) (κ ε : ℝ) (i : ι)
    (t : ℝ×(ι→ℝ)) (z : ℝ) : ℝ :=
  let bids:=noisyFocal i ε t.2 z
  purePayoff κ t.1 bids
    (pair (FiniteSelector.select (fun a=>CompleteInformation.potential κ bids (pair a).1 (pair a).2))) i

theorem ae_continuousAt_pureNoisyPayoff (pair : A→Finset ι × Finset ι)
    (mu : Measure ℝ) [NullSingletonClass mu] {κ ε : ℝ} (hκ : 0<κ) (hε : ε≠0)
    (i : ι) (t₀ : ℝ×(ι→ℝ)) (hb : t₀.2 i≠0) :
    ∀ᵐz ∂mu,ContinuousAt (fun t=>pureNoisyPayoff pair κ ε i t z) t₀ := by
  have hgen:=ae_potential_ties_same_focalCopy mu hκ hε t₀.2 i hb
  filter_upwards [hgen] with z hz
  let bids : ℝ×(ι→ℝ)→(ι→ℝ):=fun t=>noisyFocal i ε t.2 z
  have hbc : Continuous bids := (continuous_noisyFocal i ε).comp
    (continuous_snd.prodMk continuous_const)
  apply continuousAt_selected_payoff
    (fun t a=>CompleteInformation.potential κ (bids t) (pair a).1 (pair a).2)
    (fun a=>(continuous_potential κ (pair a)).comp hbc)
    (fun a=>focalCopy (pair a) i)
    (fun t a=>purePayoff κ t.1 (bids t) (pair a) i)
    (fun a=>by
      unfold purePayoff
      split_ifs <;> fun_prop)
    (fun t a b h=>purePayoff_eq_of_focalCopy_eq κ t.1 (bids t) (pair a) (pair b) i h)
    t₀
  exact fun a b he=>hz (pair a) (pair b) he

theorem measurable_pureNoisyPayoff (pair : A→Finset ι × Finset ι)
    (κ ε : ℝ) (i : ι) (t : ℝ×(ι→ℝ)) :
    Measurable (pureNoisyPayoff pair κ ε i t) := by
  classical
  letI : MeasurableSpace A:=⊤
  let bids : ℝ→(ι→ℝ):=fun z=>noisyFocal i ε t.2 z
  have hbc : Continuous bids := (continuous_noisyFocal i ε).comp
    (continuous_const.prodMk continuous_id)
  have hs : Measurable (fun z=>FiniteSelector.select
      (fun a=>CompleteInformation.potential κ (bids z) (pair a).1 (pair a).2)) :=
    FiniteSelector.measurable_select _ (fun a=>((continuous_potential κ (pair a)).comp hbc).measurable)
  have hl : Measurable (fun z=>focalCopy (pair (FiniteSelector.select
      (fun a=>CompleteInformation.potential κ (bids z) (pair a).1 (pair a).2))) i) :=
    (measurable_of_countable (fun a : A=>focalCopy (pair a) i)).comp hs
  exact Measurable.ite (measurableSet_eq_fun hl measurable_const)
    (by simp only [noisyFocal,Function.update_self]; fun_prop)
    (Measurable.ite (measurableSet_eq_fun hl measurable_const)
      (by simp only [noisyFocal,Function.update_self]; fun_prop) measurable_const)

end Candidates

omit [Fintype ι] in
theorem abs_purePayoff_le (κ w : ℝ) (b : ι→ℝ) (P : Finset ι × Finset ι) (i : ι) :
    |purePayoff κ w b P i|≤|w|+(1+2*|κ|)*|b i| := by
  unfold purePayoff
  split_ifs
  · have hh:=abs_sub w (2*κ*b i)
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
    nlinarith [abs_nonneg (b i)]
  · have hh:=abs_sub w (b i)
    nlinarith [abs_nonneg κ,abs_nonneg (b i)]
  · simp only [abs_zero]
    positivity

omit [Fintype ι] in
theorem abs_noisyFocal_le (i : ι) (ε : ℝ) (b : ι→ℝ) (z : ℝ) (hz : z∈Icc (0:ℝ) 1) :
    |noisyFocal i ε b z i|≤|b i| * (1+|ε|) := by
  simp only [noisyFocal,Function.update_self,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hh:=abs_add_le (1:ℝ) (ε*z)
  rw [abs_one,abs_mul,abs_of_nonneg hz.1] at hh
  nlinarith [abs_nonneg ε,hz.2]

section Smoothed
variable {A : Type*} [Fintype A] [Nonempty A]

def pureSmoothedPayoff (pair : A→Finset ι × Finset ι) (mu : Measure ℝ)
    (κ ε : ℝ) (i : ι) (t : ℝ×(ι→ℝ)) : ℝ :=
  ∫z,pureNoisyPayoff pair κ ε i t z ∂mu

theorem continuousAt_pureSmoothedPayoff (pair : A→Finset ι × Finset ι)
    (mu : Measure ℝ) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (hmu : ∀ᵐz ∂mu,z∈Icc (0:ℝ) 1) {κ ε : ℝ} (hκ : 0<κ) (hε : ε≠0)
    (i : ι) (t₀ : ℝ×(ι→ℝ)) (hb : t₀.2 i≠0) :
    ContinuousAt (pureSmoothedPayoff pair mu κ ε i) t₀ := by
  have hw : ∀ᶠt : ℝ×(ι→ℝ) in 𝓝 t₀,|t.1| < |t₀.1|+1 :=
    (show ContinuousAt (fun t : ℝ×(ι→ℝ)=>|t.1|) t₀ from continuous_fst.abs.continuousAt)
      (Iio_mem_nhds (by linarith))
  have hbid : ∀ᶠt : ℝ×(ι→ℝ) in 𝓝 t₀,|t.2 i| < |t₀.2 i|+1 :=
    (show ContinuousAt (fun t : ℝ×(ι→ℝ)=>|t.2 i|) t₀ from
      ((continuous_apply i).comp continuous_snd).abs.continuousAt)
      (Iio_mem_nhds (by linarith))
  let B : ℝ:=(|t₀.1|+1)+(1+2*|κ|)*((|t₀.2 i|+1)*(1+|ε|))
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun t z=>pureNoisyPayoff pair κ ε i t z) (bound:=fun _=>B)
    (Eventually.of_forall (fun t=>(measurable_pureNoisyPayoff pair κ ε i t).aestronglyMeasurable))
    ?_ (integrable_const B) (ae_continuousAt_pureNoisyPayoff pair mu hκ hε i t₀ hb)
  filter_upwards [hw,hbid] with t ht ht'
  filter_upwards [hmu] with z hz
  let bids:=noisyFocal i ε t.2 z
  let P:=pair (FiniteSelector.select (fun a=>CompleteInformation.potential κ bids (pair a).1 (pair a).2))
  change |purePayoff κ t.1 bids P i|≤B
  calc
    _≤|t.1|+(1+2*|κ|)*|bids i|:=abs_purePayoff_le κ t.1 bids P i
    _≤|t.1|+(1+2*|κ|)*(|t.2 i| * (1+|ε|)):=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (abs_noisyFocal_le i ε t.2 z hz)
        (by positivity : 0≤1+2*|κ|))
    _≤B:=add_le_add ht.le (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right ht'.le (by positivity)) (by positivity))

end Smoothed

end Copies
end FCAppendix.Affine.LowBody
