import FCAppendix.Affine.LowBody.PureCrossing
import FCAppendix.Affine.LowBody.CategoricalRateGuards
import FCAppendix.Game.CommonListSeeds
import FCAppendix.Proposer.LotterySupport

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Game Set
open scoped BigOperators ENNReal

def lowTie (κ b : ℝ) : Set RowRival := {x | x.1=0 ∧ (x.2=b ∨ x.2=κ*b)}

lemma measurableSet_lowTie (κ b : ℝ) : MeasurableSet (lowTie κ b) :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter
    ((measurableSet_eq_fun measurable_snd measurable_const).union
      (measurableSet_eq_fun measurable_snd measurable_const))

def rowBothUnderflow {N : ℕ} (c : ℕ) : Set (Fin N → RowRival) :=
  {ω | BothUnderflow c (fun i=>(ω i).1)}

lemma measurableSet_rowBothUnderflow {N : ℕ} (c : ℕ) :
    MeasurableSet (rowBothUnderflow (N:=N) c) := by
  have hm : Measurable (fun ω : Fin N → RowRival=>fun i=>(ω i).1) :=
    measurable_pi_lambda _ (fun i=>(measurable_pi_apply i).fst)
  exact hm (MeasurableSet.of_discrete : MeasurableSet {x : Fin N → Fin 4 | BothUnderflow c x})

lemma rowBothUnderflow_delete_low {N : ℕ} (c : ℕ) (ω : Fin (N+1) → RowRival)
    (i : Fin (N+1)) (hi : (ω i).1=0) :
    ω∈rowBothUnderflow c ↔ (fun j=>ω (i.succAbove j))∈rowBothUnderflow c := by
  have hfirst := Fin.sum_univ_succAbove (fun j=>firstHigher (ω j).1) i
  have hsecond := Fin.sum_univ_succAbove (fun j=>secondHigher (ω j).1) i
  have hfirst0 : firstHigher (ω i).1=0 := by simp [hi,firstHigher]
  have hsecond0 : secondHigher (ω i).1=0 := by simp [hi,secondHigher]
  rw [hfirst0,zero_add] at hfirst
  rw [hsecond0,zero_add] at hsecond
  simp only [rowBothUnderflow,mem_setOf_eq,BothUnderflow,hfirst,hsecond]

lemma measurableSet_harmfulCluster {N : ℕ} (c : ℕ) (κ b : ℝ) :
    MeasurableSet {ω : Fin (N+1)→RowRival |
      ω∈rowBothUnderflow c ∧ ∃i : Fin (N+1),ω i∈lowTie κ b} := by
  simp only [setOf_and,setOf_exists]
  exact (measurableSet_rowBothUnderflow c).inter
    (MeasurableSet.iUnion (fun i=>(measurable_pi_apply i) (measurableSet_lowTie κ b)))

def harmfulLossEnvelope {N : ℕ} (c : ℕ) (κ b η : ℝ) (ω : Fin (N+1)→RowRival) : ℝ := by
  classical
  exact if ω∈rowBothUnderflow c ∧ ∃i : Fin (N+1),ω i∈lowTie κ b then η*b else 0

section Law
variable (s a h : ℝ) (hs : 0  ≤  s) (ha : 0  ≤  a) (hh : 0  ≤  h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
local notation "mu"=>rivalLaw s a h G
include hs ha hh hsum

omit ha hh hsum [IsProbabilityMeasure G] in
lemma lowTie_probability (κ b : ℝ) : (mu).real (lowTie κ b) ≤ s*(G.real {b}+G.real {κ*b}) := by
  classical
  have hlow : Measurable (fun x : ℝ=>((0:Fin 4),x)) := measurable_const.prodMk measurable_id
  have he : mu (lowTie κ b)=ENNReal.ofReal s*G ({b}∪{κ*b}) := by
    simp only [rivalLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
    rw [Measure.map_apply hlow (measurableSet_lowTie κ b)]
    have hp : (fun x : ℝ=>((0:Fin 4),x)) ⁻¹' lowTie κ b={b}∪{κ*b} := by
      ext x
      simp [lowTie,or_comm]
    rw [hp]
    have h1 : ((1:Fin 4),0)∉lowTie κ b := by intro hx;have hv := congrArg Fin.val hx.1;norm_num at hv
    have h2 : ((2:Fin 4),0)∉lowTie κ b := by intro hx;have hv := congrArg Fin.val hx.1;norm_num at hv
    have h3 : ((3:Fin 4),0)∉lowTie κ b := by intro hx;have hv := congrArg Fin.val hx.1;norm_num at hv
    simp only [Measure.dirac_apply,Set.indicator_of_notMem h1,Set.indicator_of_notMem h2,
      Set.indicator_of_notMem h3,mul_zero,add_zero]
  have her : (mu).real (lowTie κ b)=s*G.real ({b}∪{κ*b}) := by
    rw [measureReal_def,he,ENNReal.toReal_mul,ENNReal.toReal_ofReal hs]
    rfl
  rw [her]
  exact mul_le_mul_of_nonneg_left (measureReal_union_le _ _) hs

lemma rowBothUnderflow_probability (N c : ℕ) :
    (Measure.pi (fun _ : Fin N=>mu)).real (rowBothUnderflow c)=
      (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) := by
  classical
  letI : IsProbabilityMeasure mu := rivalLaw_isProbability s a h hs ha hh hsum G
  have hcat := FiniteLaw.ofMeasure_pi_eq_iid mu N (fun _=>Prod.fst)
    (fun _=>measurable_fst) (categoryLaw s a h hs ha hh hsum G) (fun _=>rfl)
  rw [FiniteLaw.prob_eq_expect,←hcat,FiniteLaw.expect_ofMeasure]
  simpa only [rowBothUnderflow,Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using
    (integral_indicator_one (μ:=Measure.pi (fun _ : Fin N=>mu))
      (measurableSet_rowBothUnderflow (N:=N) c)).symm

lemma deleted_lowTie_underflow_probability {N : ℕ} (c : ℕ) (κ b : ℝ) (i : Fin (N+1)) :
    (Measure.pi (fun _ : Fin (N+1)=>mu)).real
      {ω | ω i∈lowTie κ b ∧ (fun j=>ω (i.succAbove j))∈rowBothUnderflow c}=
      (mu).real (lowTie κ b)*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) := by
  classical
  letI : IsProbabilityMeasure mu := rivalLaw_isProbability s a h hs ha hh hsum G
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (N+1)=>mu) i
  have he := congrArg (fun ν : Measure (RowRival × (Fin N → RowRival))=>
    ν (lowTie κ b ×ˢ rowBothUnderflow c)) hp.map_eq
  rw [Measure.map_apply hp.measurable
    ((measurableSet_lowTie κ b).prod (measurableSet_rowBothUnderflow c)),Measure.prod_prod] at he
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_mul] at hr
  change (Measure.pi (fun _ : Fin (N+1)=>mu)).real
      {ω | ω i∈lowTie κ b ∧ (fun j=>ω (i.succAbove j))∈rowBothUnderflow c}=
    (mu).real (lowTie κ b)*(Measure.pi (fun _ : Fin N=>mu)).real (rowBothUnderflow c) at hr
  rw [rowBothUnderflow_probability s a h hs ha hh hsum G N c] at hr
  exact hr

theorem harmful_cluster_probability {N : ℕ} (c : ℕ) (κ b : ℝ) :
    (Measure.pi (fun _ : Fin (N+1)=>mu)).real
      {ω | ∃i : Fin (N+1),ω i∈lowTie κ b ∧
        (fun j=>ω (i.succAbove j))∈rowBothUnderflow c} ≤
      (N+1:ℕ)*s*(G.real {b}+G.real {κ*b})*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) := by
  classical
  letI : IsProbabilityMeasure mu := rivalLaw_isProbability s a h hs ha hh hsum G
  have hu := measureReal_iUnion_fintype_le (μ:=Measure.pi (fun _ : Fin (N+1)=>mu))
    (fun i : Fin (N+1)=>{ω | ω i∈lowTie κ b ∧
      (fun j=>ω (i.succAbove j))∈rowBothUnderflow c})
  have he : {ω : Fin (N+1) → RowRival | ∃i : Fin (N+1),ω i∈lowTie κ b ∧
      (fun j=>ω (i.succAbove j))∈rowBothUnderflow c}=
      ⋃i : Fin (N+1),{ω | ω i∈lowTie κ b ∧
        (fun j=>ω (i.succAbove j))∈rowBothUnderflow c} := by ext ω;simp
  rw [he]
  apply hu.trans
  simp_rw [deleted_lowTie_underflow_probability s a h hs ha hh hsum G c κ b]
  have hp := (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob_nonneg (BothUnderflow c)
  have hbnd := mul_le_mul_of_nonneg_right (lowTie_probability s a h hs G κ b) hp
  calc
    _  ≤  ∑ _i : Fin (N+1),s*(G.real {b}+G.real {κ*b})*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) :=
      Finset.sum_le_sum (fun _ _=>hbnd)
    _ = _ := by simp;ring

theorem harmful_cluster_full_underflow_probability {N : ℕ} (c : ℕ) (κ b : ℝ) :
    (Measure.pi (fun _ : Fin (N+1)=>mu)).real
      {ω | ω∈rowBothUnderflow c ∧ ∃i : Fin (N+1),ω i∈lowTie κ b} ≤
      (N+1:ℕ)*s*(G.real {b}+G.real {κ*b})*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) := by
  classical
  letI : IsProbabilityMeasure mu := rivalLaw_isProbability s a h hs ha hh hsum G
  apply (measureReal_mono (μ:=Measure.pi (fun _ : Fin (N+1)=>mu)) ?_).trans
    (harmful_cluster_probability s a h hs ha hh hsum G c κ b)
  intro ω hω
  obtain ⟨i,hi⟩ := hω.2
  exact ⟨i,hi,(rowBothUnderflow_delete_low c ω i hi.1).mp hω.1⟩

theorem expected_harmful_envelope {N : ℕ} (c : ℕ) (κ b η : ℝ)
    (hb : 0 ≤ b) (hη : 0 ≤ η) :
    (∫ω : Fin (N+1)→RowRival,
      harmfulLossEnvelope c κ b η ω
      ∂Measure.pi (fun _ : Fin (N+1)=>mu)) ≤
      η*b*(N+1:ℕ)*s*(G.real {b}+G.real {κ*b})*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) := by
  classical
  letI : IsProbabilityMeasure mu := rivalLaw_isProbability s a h hs ha hh hsum G
  have he := integral_indicator_const (μ:=Measure.pi (fun _ : Fin (N+1)=>mu)) (η*b)
    (measurableSet_harmfulCluster c κ b)
  have he' : (∫ω : Fin (N+1)→RowRival,
      harmfulLossEnvelope c κ b η ω
      ∂Measure.pi (fun _ : Fin (N+1)=>mu)) =
      η*b*(Measure.pi (fun _ : Fin (N+1)=>mu)).real
        {ω | ω∈rowBothUnderflow c ∧ ∃i : Fin (N+1),ω i∈lowTie κ b} := by
    simpa only [harmfulLossEnvelope,Set.indicator,Set.mem_setOf_eq,smul_eq_mul,mul_comm] using he
  rw [he']
  have hh' := mul_le_mul_of_nonneg_left
    (harmful_cluster_full_underflow_probability s a h hs ha hh hsum G (N:=N) c κ b) (mul_nonneg hη hb)
  simpa only [mul_assoc] using hh'

end Law
end FCAppendix.Affine.LowBody
