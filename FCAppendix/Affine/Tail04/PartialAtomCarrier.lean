import FCAppendix.Finite.ReceiptOrder
import FCAppendix.Probability.EmpiricalConcentration
import FCAppendix.Affine.LowBody.ClusterMassLimits

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialAtomCarrier
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators

section Finite
variable {ι : Type*} [DecidableEq ι]

lemma sum_update (S : Finset ι) (r : ι → ℝ) (i : ι) (b : ℝ) :
    (∑ j∈S,Function.update r i b j)=
      (∑ j∈S,r j)+(if i∈S then b-r i else 0) := by
  have he (j : ι) : Function.update r i b j=r j+(if j=i then b-r i else 0) := by
    by_cases h : j=i
    · subst j;simp
    · simp [h]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  congr 1
  by_cases hi : i∈S
  · rw [if_pos hi,Finset.sum_eq_single i]
    · simp
    · intro j hj hji;simp [hji]
    · exact fun h => (h hi).elim
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j≠i := fun h => hi (h ▸ hj)
    simp [hji]

theorem optimal_inclusion_mono (c : ℕ) (r : ι → ℝ) (S T : Finset ι)
    (i : ι) (b : ℝ) (hb : r i< b)
    (hS : Finite.Optimal c r S) (hT : Finite.Optimal c (Function.update r i b) T)
    (hi : i∈S) : i∈T := by
  by_contra hn
  have h0 := hS.2 T hT.1
  have h1 := hT.2 S hS.1
  rw [sum_update,sum_update,if_pos hi,if_neg hn,add_zero] at h1
  linarith

theorem included_above_every_receipt [Fintype ι] (c : ℕ) (hc : 0< c)
    (r : ι → ℝ) (S : Finset ι) (i : ι) (b : ℝ) (hb : 0< b)
    (hbetter : ∀ j,j≠i → r j< b)
    (hS : Finite.Optimal c (Function.update r i b) S) : i∈S := by
  apply Finite.included_of_few_competitors c _ S hS i (by simpa using hb)
  have he : Finset.univ.filter
      (fun j => j≠i ∧ Function.update r i b i≤ Function.update r i b j)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hne,hineq⟩ := (Finset.mem_filter.mp hj).2
    simp only [Function.update_self,Function.update_of_ne hne] at hineq
    exact (not_lt.mpr hineq) (hbetter j hne)
  rw [he]
  simp only [Finset.card_empty]
  exact hc

end Finite

theorem private_gain_lower {v b b' q q' A d : ℝ}
    (_hA : 0≤ A) (hv : A≤ v-b') (_hd : 0≤ d)
    (hb : b≤ b') (hstep : b'-b≤ d)
    (hq : q∈Icc (0:ℝ) 1) (_hq' : q'∈Icc (0:ℝ) 1) (hmono : q≤ q') :
    A*(q'-q)-d ≤ (v-b')*q'-(v-b)*q := by
  have hm := mul_le_mul_of_nonneg_right hv (sub_nonneg.mpr hmono)
  have hc := mul_le_mul_of_nonneg_left hq.2 (sub_nonneg.mpr hb)
  have hn := mul_nonneg (sub_nonneg.mpr hb) hq.1
  nlinarith

section Carrier
variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
variable (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Z) [IsProbabilityMeasure ν]
variable (m c : ℕ)

abbrev Experiment := (Fin m → X) × Z

def experiment : Measure (Experiment (X:=X) (Z:=Z) m) :=
  (Measure.pi (fun _ : Fin m => μ)).prod ν

instance : IsProbabilityMeasure (experiment μ ν m) := by unfold experiment;infer_instance

def allEvent (E : Set X) : Set (Experiment (X:=X) (Z:=Z) m) :=
  (Set.univ.pi (fun _ : Fin m => E)) ×ˢ univ

include m in
lemma measurableSet_allEvent (E : Set X) (hE : MeasurableSet E) :
    MeasurableSet (allEvent (Z:=Z) m E) :=
  (MeasurableSet.univ_pi (fun _ => hE)).prod MeasurableSet.univ

theorem allEvent_mass (E : Set X) (_hE : MeasurableSet E) :
    (experiment μ ν m).real (allEvent (Z:=Z) m E)=(μ.real E)^m := by
  rw [measureReal_def,experiment,allEvent,Measure.prod_prod,measure_univ,mul_one,
    Measure.pi_pi]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.toReal_pow]
  rfl

include Z m c in
omit [MeasurableSpace X] [MeasurableSpace Z] in
theorem summed_gain_lower (eligible E : Set X) (hsub : E⊆eligible)
    (v b b' q q' : Experiment (X:=X) (Z:=Z) m → Fin m → ℝ)
    (A d : ℝ) (hA : 0≤ A) (hd : 0≤ d)
    (hq : ∀ ω i,q ω i∈Icc (0:ℝ) 1 ∧ q' ω i∈Icc (0:ℝ) 1)
    (hmono : ∀ ω i,ω.1 i∈eligible → q ω i≤ q' ω i)
    (hv : ∀ ω i,ω.1 i∈eligible → A≤ v ω i-b' ω i)
    (hb : ∀ ω i,ω.1 i∈eligible → b ω i≤ b' ω i ∧ b' ω i-b ω i≤ d)
    (hnew : ∀ ω,ω∈allEvent (Z:=Z) m E → ∀ i,q' ω i=1)
    (hcapacity : ∀ ω,ω∈allEvent (Z:=Z) m E → ∑ i,q ω i≤(c:ℝ))
    (ω : Experiment (X:=X) (Z:=Z) m) :
    A*((m:ℝ)-c)*(allEvent (Z:=Z) m E).indicator (fun _ => (1:ℝ)) ω-
      d*(∑ i : Fin m,if ω.1 i∈eligible then (1:ℝ) else 0) ≤
      ∑ i : Fin m,if ω.1 i∈eligible then
        (v ω i-b' ω i)*q' ω i-(v ω i-b ω i)*q ω i else 0 := by
  have hsingle (i : Fin m) :
      (if ω.1 i∈eligible then A*(q' ω i-q ω i)-d else 0) ≤
      (if ω.1 i∈eligible then
        (v ω i-b' ω i)*q' ω i-(v ω i-b ω i)*q ω i else 0) := by
    split_ifs with hi
    · exact private_gain_lower hA (hv ω i hi) hd (hb ω i hi).1 (hb ω i hi).2
        (hq ω i).1 (hq ω i).2 (hmono ω i hi)
    · exact le_rfl
  apply le_trans _ (Finset.sum_le_sum (fun i _ => hsingle i))
  by_cases he : ω∈allEvent (Z:=Z) m E
  · have hell (i : Fin m) : ω.1 i∈eligible := hsub (he.1 i (mem_univ i))
    simp only [Set.indicator_of_mem he,hell,ite_true,mul_one]
    simp_rw [hnew ω he]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    have hm := mul_le_mul_of_nonneg_left (hcapacity ω he) hA
    nlinarith
  · rw [Set.indicator_of_notMem he,mul_zero,zero_sub]
    rw [Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · have hn := mul_nonneg hA (sub_nonneg.mpr (hmono ω i hi))
      linarith
    · simp

include Z μ ν m c in
theorem finite_noisy_cluster_bound (eligible E : Set X)
    (he : MeasurableSet eligible) (hE : MeasurableSet E) (hsub : E⊆eligible)
    (v b b' q q' : Experiment (X:=X) (Z:=Z) m → Fin m → ℝ)
    (A d : ℝ) (hA : 0≤ A) (hd : 0≤ d)
    (hq : ∀ ω i,q ω i∈Icc (0:ℝ) 1 ∧ q' ω i∈Icc (0:ℝ) 1)
    (hmono : ∀ ω i,ω.1 i∈eligible → q ω i≤ q' ω i)
    (hv : ∀ ω i,ω.1 i∈eligible → A≤ v ω i-b' ω i)
    (hb : ∀ ω i,ω.1 i∈eligible → b ω i≤ b' ω i ∧ b' ω i-b ω i≤ d)
    (hnew : ∀ ω,ω∈allEvent (Z:=Z) m E → ∀ i,q' ω i=1)
    (hcapacity : ∀ ω,ω∈allEvent (Z:=Z) m E → ∑ i,q ω i≤(c:ℝ))
    (hgain : ∀ i,Integrable (fun ω => if ω.1 i∈eligible then
      (v ω i-b' ω i)*q' ω i-(v ω i-b ω i)*q ω i else 0) (experiment μ ν m))
    (hIC : ∀ i,(∫ ω,if ω.1 i∈eligible then
      (v ω i-b' ω i)*q' ω i-(v ω i-b ω i)*q ω i else 0 ∂experiment μ ν m)≤0) :
    A*((m:ℝ)-c)*(μ.real E)^m ≤ d*(m:ℝ)*μ.real eligible := by
  let e : Experiment (X:=X) (Z:=Z) m → Fin m → ℝ :=
    fun ω i => if ω.1 i∈eligible then 1 else 0
  have hei (i : Fin m) : Integrable (fun ω => e ω i) (experiment μ ν m) := by
    have hme : MeasurableSet {ω : Experiment (X:=X) (Z:=Z) m | ω.1 i∈eligible} :=
      he.preimage ((measurable_pi_apply i).comp measurable_fst)
    exact (integrable_const (1:ℝ)).indicator hme
  have hei_mass (i : Fin m) : (∫ ω,e ω i ∂experiment μ ν m)=μ.real eligible := by
    have hp : MeasurePreserving (fun ω : Experiment (X:=X) (Z:=Z) m => ω.1 i)
        (experiment μ ν m) μ :=
      (measurePreserving_eval (fun _ : Fin m => μ) i).comp
        (measurePreserving_fst (μ := Measure.pi (fun _ : Fin m => μ)) (ν := ν))
    change (∫ ω,eligible.indicator (fun _ => (1:ℝ)) (ω.1 i) ∂experiment μ ν m)=_
    calc
      _ = ∫ x,eligible.indicator (fun _ => (1:ℝ)) x
          ∂((experiment μ ν m).map (fun ω => ω.1 i)) :=
        (integral_map hp.measurable.aemeasurable
          (measurable_const.indicator he).aestronglyMeasurable).symm
      _ = μ.real eligible := by
        rw [hp.map_eq,integral_indicator_const (1:ℝ) he,smul_eq_mul,mul_one]
  have hsumint : Integrable (fun ω => ∑ i : Fin m,e ω i) (experiment μ ν m) :=
    integrable_finsetSum _ (fun i _ => hei i)
  have hfirst : Integrable (fun ω => A*((m:ℝ)-c)*
      (allEvent (Z:=Z) m E).indicator (fun _ => (1:ℝ)) ω) (experiment μ ν m) :=
    ((integrable_const (1:ℝ)).indicator (measurableSet_allEvent m E hE)).const_mul _
  have hsecond : Integrable (fun ω => d*∑ i : Fin m,e ω i) (experiment μ ν m) :=
    hsumint.const_mul d
  have hleft : Integrable (fun ω => A*((m:ℝ)-c)*
      (allEvent (Z:=Z) m E).indicator (fun _ => (1:ℝ)) ω-d*∑ i : Fin m,e ω i)
      (experiment μ ν m) := hfirst.sub hsecond
  have hright := integrable_finsetSum Finset.univ (fun i _ => hgain i)
  have hh := integral_mono hleft hright
    (summed_gain_lower m c eligible E hsub v b b' q q' A d hA hd hq hmono hv hb hnew hcapacity)
  rw [integral_sub hfirst hsecond] at hh
  simp only [integral_const_mul,integral_indicator_const (1:ℝ) (measurableSet_allEvent m E hE),
    smul_eq_mul,mul_one,allEvent_mass μ ν m E hE] at hh
  rw [integral_finsetSum _ (fun i _ => hei i),
    integral_finsetSum _ (fun i _ => hgain i)] at hh
  simp_rw [hei_mass] at hh
  have hi := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hIC i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  nlinarith

end Carrier

theorem atom_zero_of_power_bound {m : ℕ} (hm : 0< m) {p K : ℝ}
    (hp : 0≤ p) (hK : 0< K) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (h : ∀ n,K*p^m≤ r n) : p=0 := by
  have hle : K*p^m≤(0:ℝ) := ge_of_tendsto hr (Eventually.of_forall h)
  have hnonneg : 0≤K*p^m := mul_nonneg hK.le (pow_nonneg hp m)
  have heq : K*p^m=0 := le_antisymm hle hnonneg
  have hpow : p^m=0 := (mul_eq_zero.mp heq).resolve_left hK.ne'
  exact (pow_eq_zero_iff (Nat.ne_of_gt hm)).mp hpow

theorem partial_atom_zero_of_cluster_bounds (m : ℕ) (hm : 0< m)
    (H : ℕ → ProbabilityMeasure ℝ) (H0 : ProbabilityMeasure ℝ)
    (hH : Tendsto H atTop (𝓝 H0)) (b K : ℝ) (hK : 0< K)
    (r err : ℕ → ℝ) (hr : ∀ n,0< r n) (herr : Tendsto err atTop (𝓝 0))
    (hfinite : ∀ n,∀ᶠ j : ℕ in atTop,
      K*((H j : Measure ℝ).real (Ioo (b-r n) (b+r n)))^m≤ err n) :
    (H0 : Measure ℝ) {b}=0 := by
  have hbound (n : ℕ) : K*((H0 : Measure ℝ).real {b})^m≤ err n := by
    obtain ⟨φ,hφ,p,q,s,hp,hq,hs,hplo,hqhi,hshi⟩ :=
      LowBody.exists_three_cluster_mass_subsequence H H H0 hH hH
        (Ioo (b-r n) (b+r n)) ∅ ∅ isOpen_Ioo isClosed_empty isClosed_empty
    have hpbound : K*p.1^m≤ err n :=
      le_of_tendsto_of_tendsto ((hp.pow m).const_mul K) tendsto_const_nhds
        (hφ.tendsto_atTop.eventually (hfinite n))
    have hmass : (H0 : Measure ℝ).real {b}≤ p.1 :=
      (measureReal_mono (singleton_subset_iff.mpr
        (show b∈Ioo (b-r n) (b+r n) from ⟨by linarith [hr n],by linarith [hr n]⟩))).trans hplo
    have hpow : ((H0 : Measure ℝ).real {b})^m≤ p.1^m := by
      gcongr
    exact (mul_le_mul_of_nonneg_left hpow hK.le).trans hpbound
  have hz := atom_zero_of_power_bound hm
    (show 0≤(H0 : Measure ℝ).real {b} from measureReal_nonneg) hK err herr hbound
  exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top _ _)

end FCAppendix.Affine.Tail04.PartialAtomCarrier
