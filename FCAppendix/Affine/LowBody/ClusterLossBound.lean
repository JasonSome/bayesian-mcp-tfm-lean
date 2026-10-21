import FCAppendix.Affine.LowBody.HarmfulJumpBound

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators ENNReal

def lowCluster (B : Set ℝ) : Set RowRival:={x | x.1=0 ∧ x.2∈B}

theorem measurableSet_lowCluster (B : Set ℝ) (hB : MeasurableSet B) :
    MeasurableSet (lowCluster B) :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter (measurable_snd hB)

def harmfulCluster {N : ℕ} (c : ℕ) (B : Set ℝ) : Set (Fin (N+1)→RowRival):=
  {ω | ω∈rowBothUnderflow c ∧ ∃i : Fin (N+1),ω i∈lowCluster B}

theorem measurableSet_harmfulCluster_set {N : ℕ} (c : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    MeasurableSet (harmfulCluster (N:=N) c B) := by
  simp only [harmfulCluster,setOf_and,setOf_exists]
  exact (measurableSet_rowBothUnderflow c).inter
    (MeasurableSet.iUnion (fun i=>(measurable_pi_apply i) (measurableSet_lowCluster B hB)))

section Law
variable (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
local notation "mu"=>rivalLaw s a h G
include hs ha hh hsum

omit ha hh hsum [IsProbabilityMeasure G] in
theorem lowCluster_probability (B : Set ℝ) (hB : MeasurableSet B) :
    (mu).real (lowCluster B)=s*G.real B := by
  have hlow : Measurable (fun x : ℝ=>((0:Fin 4),x)):=measurable_const.prodMk measurable_id
  have hpre : (fun x : ℝ=>((0:Fin 4),x)) ⁻¹' lowCluster B=B := by ext x; simp [lowCluster]
  have hn1 : ((1:Fin 4),0)∉lowCluster B := by
    intro hx; have hv:=congrArg Fin.val hx.1; norm_num at hv
  have hn2 : ((2:Fin 4),0)∉lowCluster B := by
    intro hx; have hv:=congrArg Fin.val hx.1; norm_num at hv
  have hn3 : ((3:Fin 4),0)∉lowCluster B := by
    intro hx; have hv:=congrArg Fin.val hx.1; norm_num at hv
  have he : mu (lowCluster B)=ENNReal.ofReal s*G B := by
    simp only [rivalLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
    rw [Measure.map_apply hlow (measurableSet_lowCluster B hB),hpre]
    simp only [Measure.dirac_apply,Set.indicator_of_notMem hn1,Set.indicator_of_notMem hn2,
      Set.indicator_of_notMem hn3,mul_zero,add_zero]
  rw [measureReal_def,he,ENNReal.toReal_mul,ENNReal.toReal_ofReal hs]
  rfl

theorem deleted_lowCluster_underflow_probability {N : ℕ} (c : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (i : Fin (N+1)) :
    (Measure.pi (fun _ : Fin (N+1)=>mu)).real
      {ω | ω i∈lowCluster B ∧ (fun j=>ω (i.succAbove j))∈rowBothUnderflow c}=
      s*G.real B*(CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) := by
  letI : IsProbabilityMeasure mu:=rivalLaw_isProbability s a h hs ha hh hsum G
  have hp:=measurePreserving_piFinSuccAbove (fun _ : Fin (N+1)=>mu) i
  have he:=congrArg (fun ν : Measure (RowRival×(Fin N→RowRival))=>
    ν (lowCluster B×ˢrowBothUnderflow c)) hp.map_eq
  rw [Measure.map_apply hp.measurable
    ((measurableSet_lowCluster B hB).prod (measurableSet_rowBothUnderflow c)),Measure.prod_prod] at he
  have hr:=congrArg ENNReal.toReal he
  rw [ENNReal.toReal_mul] at hr
  change (Measure.pi (fun _ : Fin (N+1)=>mu)).real
      {ω | ω i∈lowCluster B ∧ (fun j=>ω (i.succAbove j))∈rowBothUnderflow c}=
    (mu).real (lowCluster B)*(Measure.pi (fun _ : Fin N=>mu)).real (rowBothUnderflow c) at hr
  rw [lowCluster_probability s a h hs G B hB,
    rowBothUnderflow_probability s a h hs ha hh hsum G N c] at hr
  exact hr

theorem harmfulCluster_probability {N : ℕ} (c : ℕ) (B : Set ℝ) (hB : MeasurableSet B) :
    (Measure.pi (fun _ : Fin (N+1)=>mu)).real (harmfulCluster c B)≤
      (N+1:ℕ)*s*G.real B*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) := by
  letI : IsProbabilityMeasure mu:=rivalLaw_isProbability s a h hs ha hh hsum G
  let E : Fin (N+1)→Set (Fin (N+1)→RowRival):=fun i=>
    {ω | ω i∈lowCluster B ∧ (fun j=>ω (i.succAbove j))∈rowBothUnderflow c}
  have hsub : harmfulCluster c B⊆⋃i,E i := by
    intro ω hω
    obtain ⟨i,hi⟩:=hω.2
    exact mem_iUnion.mpr ⟨i,hi,(rowBothUnderflow_delete_low c ω i hi.1).mp hω.1⟩
  calc
    _≤(Measure.pi (fun _ : Fin (N+1)=>mu)).real (⋃i,E i):=measureReal_mono hsub
    _≤∑i,(Measure.pi (fun _ : Fin (N+1)=>mu)).real (E i):=measureReal_iUnion_fintype_le E
    _=_:=by
      simp only [E,deleted_lowCluster_underflow_probability s a h hs ha hh hsum G c B hB,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem expected_cluster_loss {N : ℕ} (c : ℕ) (B : Set ℝ) (hB : MeasurableSet B)
    (cost : ℝ) (hcost : 0≤cost) :
    (∫ω : Fin (N+1)→RowRival,(harmfulCluster c B).indicator (fun _=>cost) ω
      ∂Measure.pi (fun _ : Fin (N+1)=>mu))≤
      cost*(N+1:ℕ)*s*G.real B*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) := by
  letI : IsProbabilityMeasure mu:=rivalLaw_isProbability s a h hs ha hh hsum G
  rw [integral_indicator_const cost (measurableSet_harmfulCluster_set c B hB)]
  have hm:=mul_le_mul_of_nonneg_left (harmfulCluster_probability s a h hs ha hh hsum G (N:=N) c B hB) hcost
  simp only [smul_eq_mul]
  convert hm using 1 <;> first | rfl | ring

theorem expected_two_cluster_loss {N : ℕ} (c : ℕ)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (cost : ℝ) (hcost : 0≤cost) :
    (∫ω : Fin (N+1)→RowRival,(harmfulCluster c (B∪C)).indicator (fun _=>cost) ω
      ∂Measure.pi (fun _ : Fin (N+1)=>mu))≤
      cost*(N+1:ℕ)*s*(G.real B+G.real C)*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c) := by
  apply (expected_cluster_loss s a h hs ha hh hsum G c (B∪C) (hB.union hC) cost hcost).trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left (measureReal_union_le B C)
      (mul_nonneg (mul_nonneg hcost (Nat.cast_nonneg _)) hs)
  · exact (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob_nonneg (BothUnderflow c)

end Law
end FCAppendix.Affine.LowBody
