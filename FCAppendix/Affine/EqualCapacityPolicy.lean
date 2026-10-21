import FCAppendix.Affine.EqualCapacityContinuity
import FCAppendix.Existence.R01PayOnceCanonicalPolicy

noncomputable section
namespace FCAppendix.Affine.EqualCapacity
open Set MeasureTheory ProbabilityTheory Game Classical
open Existence.PayOnceBounded (positiveSupport mem_positiveSupport positiveStratum
  isOpen_positiveStratum measurable_positiveSupport listBids measurable_listBids)
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def onSupport (ξ : ℝ) (c : ℕ) (S : Finset ι) (b : ι→ℝ) (i : ι) : ℝ :=
  if hi : i∈S then kernelMarginal ξ c (fun j : S=>b j.1) ⟨i,hi⟩ else 0

omit [Fintype ι] in
lemma onSupport_outside (ξ : ℝ) (c : ℕ) (S : Finset ι) (b : ι→ℝ) (i : ι) (hi : i∉S) :
    onSupport ξ c S b i=0 := by simp [onSupport,hi]

omit [Fintype ι] in
lemma onSupport_inside (ξ : ℝ) (c : ℕ) (S : Finset ι) (b : ι→ℝ) (i : S) :
    onSupport ξ c S b i.1=kernelMarginal ξ c (fun j : S=>b j.1) i := by simp [onSupport,i.2]

theorem onSupport_spec (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1)
    (S : Finset ι) (b : ι→ℝ) (hb : ∀i∈S,0<b i) :
    (∀i,0≤onSupport ξ c S b i) ∧ (∀i,onSupport ξ c S b i≤1) ∧
      (∑i,onSupport ξ c S b i=(min c S.card:ℕ)) := by
  have hs := kernelMarginal_spec hξ hξ1 c (fun i : S=>b i.1) (fun i=>hb i.1 i.2)
  refine ⟨?_,?_,?_⟩
  · intro i
    by_cases hi : i∈S
    · simpa [onSupport,hi] using hs.1 ⟨i,hi⟩
    · simp [onSupport,hi]
  · intro i
    by_cases hi : i∈S
    · simpa [onSupport,hi] using hs.2.1 ⟨i,hi⟩
    · simp [onSupport,hi]
  · calc
      (∑i,onSupport ξ c S b i)=∑i∈S,onSupport ξ c S b i :=
        (Finset.sum_subset (Finset.subset_univ S)
          (fun i _ hi=>onSupport_outside ξ c S b i hi)).symm
      _ = ∑i : S,onSupport ξ c S b i := (Finset.sum_attach S _).symm
      _ = (min c S.card:ℕ) := by
        simp only [onSupport_inside]
        simpa using hs.2.2.1

omit [Fintype ι] in
theorem continuousAt_onSupport (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1)
    (S : Finset ι) (b : ι→ℝ) (hb : ∀i∈S,0<b i) :
    ContinuousAt (onSupport ξ c S) b := by
  rw [continuousAt_pi]
  intro i
  by_cases hi : i∈S
  · have hc := (continuousAt_kernelMarginal hξ hξ1 c
      (fun j : S=>b j.1) (fun j=>hb j.1 j.2)).comp
      (continuous_pi (fun j : S=>continuous_apply j.1)).continuousAt
    convert (continuous_apply (⟨i,hi⟩ : S)).continuousAt.comp hc using 1
    funext y
    simp only [onSupport,dif_pos hi,Function.comp_apply]
  · simpa [onSupport,hi] using (continuousAt_const : ContinuousAt (fun _ : ι→ℝ=>(0:ℝ)) b)

def stratumKernel (ξ : ℝ) (c : ℕ) (S : Finset ι) : (ι→ℝ)→ι→ℝ :=
  (positiveStratum S).piecewise (onSupport ξ c S) (fun _ _=>0)

theorem measurable_stratumKernel (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1) (S : Finset ι) :
    Measurable (stratumKernel ξ c S) := by
  apply ContinuousOn.measurable_piecewise _ continuousOn_const
    (isOpen_positiveStratum S).measurableSet
  intro b hb
  exact (continuousAt_onSupport ξ c hξ hξ1 S b (fun i hi=>hb ⟨i,hi⟩)).continuousWithinAt

def positiveMarginal (ξ : ℝ) (c : ℕ) (b : ι→ℝ) : ι→ℝ :=
  onSupport ξ c (positiveSupport b) b

theorem measurable_positiveMarginal (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1) :
    Measurable (positiveMarginal (ι:=ι) ξ c) := by
  have he : positiveMarginal (ι:=ι) ξ c=
      fun b=>∑S : Finset ι,if positiveSupport b=S then stratumKernel ξ c S b else 0 := by
    funext b i
    simp only [Finset.sum_apply,ite_apply,Pi.zero_apply]
    rw [Finset.sum_eq_single (positiveSupport b)]
    · have hpos : b∈positiveStratum (positiveSupport b) :=
        fun j=>(mem_positiveSupport b j.1).mp j.2
      simp [positiveMarginal,stratumKernel,Set.piecewise,hpos]
    · intro S _ hS
      simp only [if_neg (Ne.symm hS)]
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
  rw [he]
  apply Finset.measurable_sum
  intro S _
  exact Measurable.ite (measurableSet_eq_fun measurable_positiveSupport measurable_const)
    (measurable_stratumKernel ξ c hξ hξ1 S) measurable_const

theorem positiveMarginal_spec (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1) (b : ι→ℝ) :
    (∀i,0≤positiveMarginal ξ c b i) ∧ (∀i,positiveMarginal ξ c b i≤1) ∧
      (∑i,positiveMarginal ξ c b i=(min c (positiveSupport b).card:ℕ)) :=
  onSupport_spec ξ c hξ hξ1 _ b (fun i hi=>(mem_positiveSupport b i).mp hi)

def listMarginal {m : ℕ} (ξ : ℝ) (c : ℕ) (L : LocalList m) : Fin m→ℝ :=
  positiveMarginal ξ c (listBids L)

theorem measurable_listMarginal (m : ℕ) (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1) :
    Measurable (listMarginal (m:=m) ξ c) :=
  (measurable_positiveMarginal ξ c hξ hξ1).comp measurable_listBids

theorem exists_affine_localPolicy (m : ℕ) (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1) :
    ∃ (policy : LocalPolicy m c unitInterval)
      (hpolicy : Measurable (fun z : LocalList m×unitInterval=>(policy z.1 z.2).val)),
      ∀L,FiniteLaw.ofMeasure volume (fun s=>(policy L s).val)
        (hpolicy.comp (measurable_const.prodMk measurable_id))=
          ExactCapacity.symmetricLottery (listMarginal ξ c L) := by
  apply exists_measurable_localPolicy_finiteLaw (listMarginal ξ c)
    (measurable_listMarginal m ξ c hξ hξ1) (fun L=>min c (positiveSupport (listBids L)).card)
    (fun _=>min_le_left _ _)
  · intro L i; exact (positiveMarginal_spec ξ c hξ hξ1 (listBids L)).1 i
  · intro L i; exact (positiveMarginal_spec ξ c hξ hξ1 (listBids L)).2.1 i
  · intro L; exact (positiveMarginal_spec ξ c hξ hξ1 (listBids L)).2.2
  · intro L i hi
    apply onSupport_outside
    rw [mem_positiveSupport]
    simp only [listBids,hi,Option.getD_none,lt_self_iff_false,not_false_eq_true]
end FCAppendix.Affine.EqualCapacity
