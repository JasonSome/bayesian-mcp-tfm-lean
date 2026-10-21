import FCAppendix.Affine.Tail04.NativeLowSourceIC
import FCAppendix.Affine.Tail04.CountLaws
import FCAppendix.Probability.ActiveCountBounds

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLowCountBounds
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid LowBody NativeContinuation NativeLowCoordinates NativeLowSelector
open NativeLowIntegration
open scoped BigOperators

def activeUnderflow {N : ℕ} (c : ℕ) : Set (Fin N→ RowRival) :=
  {row | classCount 1 row< c}

lemma measurable_classCount (N : ℕ) (k : Fin 4) :
    Measurable (classCount (N:=N) k) := by
  unfold classCount
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_pi_apply i).fst) measurable_const)
    measurable_const measurable_const

lemma measurableSet_activeUnderflow (N c : ℕ) :
    MeasurableSet (activeUnderflow (N:=N) c) :=
  measurableSet_lt (measurable_classCount N 1) measurable_const

section Native
variable {N c : ℕ} (D : NativeLocalPolicy.Data (N+1) c)
  (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed)
  (hpolicy : Γ.policy=D.completedPolicy)

include hpolicy in
theorem focal_count_zero_of_active_overload
    (i : Fin (N+1)) (a : JointAction 2) (hk : a.routeCount=2)
    (hb : a.bid≤ D.E.d) (ω : Sample (N+1) 2 NativeLocalPolicy.Seed)
    (hr : ∀ r : Fin N,NativeMenuReports.MenuAction D.E (ω.1.1 (i.succAbove r)).1.2)
    (hover : c≤ classCount 1 (rivalRow D.E i ω.1)) :
    focalCount Γ i a ω=0 := by
  let X := rowContextAt i a.bid (rivalRow D.E i ω.1)
  change c≤classCount 1 (rowProfile D.E i ω.1.1) at hover
  have hz (j : Fin 2) : NativeContinuation.residual c j X=0 := by
    fin_cases j <;>
      dsimp [X,rowContextAt,reindexContext,rowContext,NativeContinuation.residual,contextUpper] <;> omega
  have hempty (j : Fin 2) :
      NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c j X (ω.1.2 j).2=∅ := by
    have hf := NativeExactLow.select_feasible D.ξ D.xi_pos D.xi_lt_one c j X (ω.1.2 j).2
    have hc : (NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c j X (ω.1.2 j).2).card≤0 := by
      simpa only [hz j] using hf.1
    exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hc)
  rw [low_focal_count D Γ hpolicy i a hk hb ω hr]
  change focalCopy (pair D X ω.1.2) i=0
  simp [pair,hempty,focalCopy]

variable
  (hprofiles : ∀ᵐp ∂userProfileLaw Γ,∀l,NativeMenuReports.MenuAction D.E (p l).1.2)

include hpolicy hprofiles in
theorem load_le_active_underflow
    (i : Fin (N+1)) (ν : Measure (Fin N→ RowRival))
    (hlaw : (userProfileLaw Γ).map (rowProfile D.E i)=ν)
    (a : JointAction 2) (hk : a.routeCount=2) (hb : a.bid≤ D.E.d) :
    ((problem Γ i).outcome a).load≤2*ν.real (activeUnderflow c) := by
  let E : Set (Sample (N+1) 2 NativeLocalPolicy.Seed) :=
    {ω | rowProfile D.E i ω.1.1∈activeUnderflow c}
  have hrow := measurable_rowProfile D.E i
  have hE : MeasurableSet E :=
    (measurableSet_activeUnderflow N c).preimage (hrow.comp measurable_fst.fst)
  have hpMP : MeasurePreserving
      (fun ω : Sample (N+1) 2 NativeLocalPolicy.Seed=> ω.1.1)
      (sampleLaw Γ) (userProfileLaw Γ) :=
    (measurePreserving_fst (μ:=userProfileLaw Γ)
      (ν:=Measure.pi (fun _ : Fin 2=> Γ.seedLaw))).comp
        (measurePreserving_fst (μ:=backgroundLaw Γ) (ν:=permLaw 2))
  have hp := hpMP.quasiMeasurePreserving.ae hprofiles
  have hpoint : ∀ᵐω ∂sampleLaw Γ,
      ((focalCount Γ i a ω).val:ℝ)≤ E.indicator (fun _=>(2:ℝ)) ω := by
    filter_upwards [hp] with ω hω
    by_cases he : ω∈E
    · rw [Set.indicator_of_mem he]
      exact_mod_cast (show (focalCount Γ i a ω).val≤2 from Nat.le_of_lt_succ
        (focalCount Γ i a ω).isLt)
    · have hover : c≤ classCount 1 (rivalRow D.E i ω.1) := by
        change ¬classCount 1 (rowProfile D.E i ω.1.1)< c at he
        exact Nat.le_of_not_gt he
      rw [focal_count_zero_of_active_overload D Γ hpolicy i a hk hb ω
        (fun r=> hω (i.succAbove r)) hover,Set.indicator_of_notMem he]
      norm_num
  rw [problem_outcome,CountLaw.load,CountLaw.expect_ofMeasure]
  have hi := CountLaw.integrable_comp (sampleLaw Γ) (focalCount Γ i a)
    (measurable_focalCount Γ i a) (fun r : Fin 3=>(r.val:ℝ))
  have hbound := integral_mono_ae hi ((integrable_const (2:ℝ)).indicator hE) hpoint
  rw [integral_indicator_const (2:ℝ) hE] at hbound
  have hmap : (sampleLaw Γ).map
      (fun ω : Sample (N+1) 2 NativeLocalPolicy.Seed=> rowProfile D.E i ω.1.1)=ν := by
    change (sampleLaw Γ).map (rowProfile D.E i∘
      (fun ω : Sample (N+1) 2 NativeLocalPolicy.Seed=> ω.1.1))=ν
    rw [←Measure.map_map hrow hpMP.measurable,hpMP.map_eq,hlaw]
  have hm := Measure.map_apply (μ:=sampleLaw Γ) (hrow.comp hpMP.measurable)
    (measurableSet_activeUnderflow N c)
  change ((sampleLaw Γ).map (fun ω : Sample (N+1) 2 NativeLocalPolicy.Seed=>
    rowProfile D.E i ω.1.1)) (activeUnderflow c)=_ at hm
  rw [hmap] at hm
  have hmass : (sampleLaw Γ).real E=ν.real (activeUnderflow c) :=
    congrArg ENNReal.toReal hm.symm
  simpa only [smul_eq_mul,hmass,mul_comm] using hbound

end Native

def activeTrial : Set RowRival := {z | z.1=1}

lemma measurableSet_activeTrial : MeasurableSet activeTrial :=
  measurableSet_eq_fun measurable_fst measurable_const

lemma classCount_eq_sampleCount {N : ℕ} (row : Fin N→ RowRival) :
    classCount 1 row=Probability.sampleCount activeTrial row := by
  unfold classCount Probability.sampleCount
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [activeTrial,Set.mem_setOf_eq]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (row i).1=1 <;> simp only [hi,ite_true,ite_false]

lemma rivalLaw_active_mass (s a h : ℝ) (ha : 0≤ a)
    (G : Measure ℝ) : (rivalLaw s a h G).real activeTrial=a := by
  have hlow : (fun b : ℝ=>((0:Fin 4),b)) ⁻¹' activeTrial=∅ := by
    ext b
    simp [activeTrial]
  rw [measureReal_def]
  simp only [rivalLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
  rw [Measure.map_apply (μ:=G)
    (show Measurable (fun b : ℝ=>((0:Fin 4),b)) from measurable_const.prodMk measurable_id)
    measurableSet_activeTrial,hlow]
  simp [Measure.dirac_apply,activeTrial,ha,ENNReal.toReal_ofReal]

theorem active_underflow_le (s a h : ℝ)
    (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (N c : ℕ) (hN : 0< N) (γ : ℝ) (hγ : 0≤ γ)
    (hcap : (c:ℝ)≤(N:ℝ)*(a-γ)) :
    (Measure.pi (fun _ : Fin N=> rivalLaw s a h G)).real (activeUnderflow c)≤
      Real.exp (-2*(N:ℝ)*γ^2) := by
  letI := rivalLaw_isProbability s a h hs ha hh hsum G
  have hsset : activeUnderflow (N:=N) c⊆
      {row | (Probability.sampleCount activeTrial row:ℝ)≤
        (N:ℝ)*((rivalLaw s a h G).real activeTrial-γ)} := by
    intro row hr
    change (Probability.sampleCount activeTrial row:ℝ)≤
      (N:ℝ)*((rivalLaw s a h G).real activeTrial-γ)
    rw [rivalLaw_active_mass s a h ha G,←classCount_eq_sampleCount]
    exact (show (classCount 1 row:ℝ)≤ c from
      Nat.cast_le.mpr (show classCount 1 row≤ c from hr.le)).trans hcap
  exact (measureReal_mono hsset).trans
    (Probability.iid_indicator_lower_tail_le (rivalLaw s a h G)
      activeTrial measurableSet_activeTrial N hN hγ)

end FCAppendix.Affine.Tail04.NativeLowCountBounds
