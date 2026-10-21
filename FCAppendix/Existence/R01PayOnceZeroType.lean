import FCAppendix.Existence.R01PayOnceFloorEmbedding
import FCAppendix.PayOnce.SaturatedBounds

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open MeasureTheory ProbabilityTheory Set Topology Filter
open scoped BigOperators
open FCAppendix.Existence.Distributional
attribute [local instance] Classical.propDecidable

def zeroClass {ε W : ℝ} (z : Value W × FloorAction ε W) : Prop :=
  z.1.1=0 ∧ present z.2=true

theorem measurableSet_zeroClass {ε W : ℝ} :
    MeasurableSet {z : Value W × FloorAction ε W | zeroClass z} :=
  (measurableSet_eq_fun (measurable_subtype_coe.comp measurable_fst) measurable_const).inter
    (measurableSet_eq_fun (continuous_present.measurable.comp measurable_snd) measurable_const)

def zeroLoss {ε W : ℝ} (m n c : ℕ)
    (x : Fin m → Value W × FloorAction ε W) (i : Fin m) : ℝ :=
  if zeroClass (x i) then -profilePayoff m n c x i else 0

theorem zeroLoss_nonneg {ε W : ℝ} (m n c : ℕ) (hn : 2 ≤ n) (hε : 0<ε)
    (x : Fin m → Value W × FloorAction ε W) (i : Fin m) : 0 ≤ zeroLoss m n c x i := by
  by_cases h : zeroClass (x i)
  · have hs := (success_bounds n c hn hε (fun j=>(x j).2) i).1
    have hb := (bid_pos_of_present hε (x i).2 h.2).le
    simp only [zeroLoss,if_pos h,profilePayoff,h.1,zero_sub,neg_mul,neg_neg]
    exact mul_nonneg hb hs
  · simp [zeroLoss,h]

theorem integrable_zeroLoss {ε W : ℝ} (m n c : ℕ) (hn : 2 ≤ n) (hε : 0<ε)
    (π : ProbabilityMeasure (Value W × FloorAction ε W)) (i : Fin m) :
    Integrable (fun x=>zeroLoss m n c x i) (rowLaw m π : Measure (Fin m → Value W × FloorAction ε W)) := by
  have hi : Integrable (fun x : Fin m → Value W × FloorAction ε W =>
      -profilePayoff m n c x i) (rowLaw m π : Measure _) :=
    (ContinuousMap.equivBoundedOfCompact _ _
      ⟨_,(continuous_profilePayoff m n c hn hε i).neg⟩).integrable _
  convert hi.indicator (measurableSet_zeroClass.preimage (measurable_pi_apply i)) using 1
  all_goals rfl

theorem integral_zeroLoss_head_inner {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n) (hε : 0<ε)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ) (z : Value W × FloorAction ε W) :
    (∫ r,zeroLoss (N+1) n c (Fin.cons z r) 0
      ∂(rowLaw N π.1 : Measure (Fin N → Value W × FloorAction ε W))) =
    if zeroClass z then -floorPayoff N n c (π,z) else 0 := by
  have hf : Continuous (fun r : Fin N → Value W × FloorAction ε W =>
      success n c (insertFocal N z.2 r) 0) := (PayOnce.continuous_success n).comp
    ((continuous_apply (0 : Fin (N+1))).comp ((continuous_marginal n c hn hε).comp
      ((continuous_insertFocal N).comp (continuous_const.prodMk continuous_id))))
  have he (r : Fin N → Value W × FloorAction ε W) :
      (fun j=>((Fin.cons (α:=fun _ : Fin (N+1)=>Value W × FloorAction ε W) z r) j).2)=
      insertFocal N z.2 r := by
    funext j; refine Fin.cases ?_ (fun k=>?_) j <;> simp [insertFocal]
  by_cases h : zeroClass z
  · simp only [zeroLoss,Fin.cons_zero,if_pos h,profilePayoff]
    simp_rw [he]
    rw [integral_neg,integral_const_mul]
    rfl
  · simp [zeroLoss,h]

theorem integral_zeroLoss_head_nonpos {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n) (hε : 0<ε)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ)
    (hIC : AllActionOptimal π (fun z=>floorPayoff N n c (π,z))) :
    (∫ x,zeroLoss (N+1) n c x 0 ∂(rowLaw (N+1) π.1 : Measure (Fin (N+1) → Value W × FloorAction ε W))) ≤ 0 := by
  let f := fun x : Fin (N+1) → Value W × FloorAction ε W=>zeroLoss (N+1) n c x 0
  let cons := fun p : (Value W × FloorAction ε W) ×
      (Fin N → Value W × FloorAction ε W)=>Fin.cons (α:=fun _ : Fin (N+1)=>Value W × FloorAction ε W) p.1 p.2
  have hc : Continuous cons := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd
  have hfm : AEStronglyMeasurable f (rowLaw (N+1) π.1 : Measure (Fin (N+1) → Value W × FloorAction ε W)) :=
    (integrable_zeroLoss (N+1) n c hn hε π.1 0).aestronglyMeasurable
  have hint : Integrable (f ∘ cons)
      ((π.1 : Measure (Value W × FloorAction ε W)).prod (rowLaw N π.1 : Measure _)) :=
    (integrable_map_measure hfm hc.measurable.aemeasurable).mp
      (integrable_zeroLoss (N+1) n c hn hε π.1 0)
  have hm : (∫ x,f x ∂(rowLaw (N+1) π.1 : Measure (Fin (N+1) → Value W × FloorAction ε W))) =
      ∫ z,∫ r,f (Fin.cons z r) ∂(rowLaw N π.1 : Measure _) ∂(π.1 : Measure _) := by
    change (∫ x,f x ∂Measure.map cons ((π.1 : Measure _).prod (rowLaw N π.1 : Measure _)))=_
    calc
      _ = ∫ p,f (cons p) ∂((π.1 : Measure _).prod (rowLaw N π.1 : Measure _)) :=
        integral_map hc.measurable.aemeasurable hfm
      _ = _ := integral_prod _ hint
  rw [hm]
  apply integral_nonpos_of_ae
  filter_upwards [hIC] with z hz
  rw [show (∫ r,f (Fin.cons z r) ∂(rowLaw N π.1 : Measure _))=_ from
    integral_zeroLoss_head_inner N n c hn hε π z]
  split_ifs
  · have hh:=hz (.inl ())
    rw [floorPayoff_abstain] at hh
    change -floorPayoff N n c (π,z) ≤ 0
    exact neg_nonpos.mpr hh
  · exact le_rfl

theorem zeroLoss_relabel {ε W : ℝ} (m n c : ℕ) (hn : 2 ≤ n) (hε : 0<ε)
    (e : Equiv.Perm (Fin m)) (x : Fin m → Value W × FloorAction ε W) (i : Fin m) :
    zeroLoss m n c (x ∘ e) i=zeroLoss m n c x (e i) := by
  have hs:=success_relabel e n c hn hε (fun j=>(x j).2) i
  change success n c (fun j=>(x (e j)).2) i=_ at hs
  simp only [zeroLoss,Function.comp_apply,profilePayoff,hs]

theorem integral_zeroLoss_eq_head {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n) (hε : 0<ε)
    (π : ProbabilityMeasure (Value W × FloorAction ε W)) (i : Fin (N+1)) :
    (∫ x,zeroLoss (N+1) n c x i ∂(rowLaw (N+1) π : Measure (Fin (N+1) → Value W × FloorAction ε W)))=
      ∫ x,zeroLoss (N+1) n c x 0 ∂(rowLaw (N+1) π : Measure (Fin (N+1) → Value W × FloorAction ε W)) := by
  let e : Equiv.Perm (Fin (N+1)):=Equiv.swap 0 i
  let E:=MeasurableEquiv.piCongrLeft (fun _ : Fin (N+1)=>Value W × FloorAction ε W) e
  have hmp : MeasurePreserving E (rowLaw (N+1) π : Measure (Fin (N+1) → Value W × FloorAction ε W)) (rowLaw (N+1) π : Measure (Fin (N+1) → Value W × FloorAction ε W)) := by
    rw [rowLaw_eq_pi]
    exact measurePreserving_piCongrLeft (α:=fun _ : Fin (N+1)=>Value W × FloorAction ε W)
      (fun _ : Fin (N+1)=>(π : Measure (Value W × FloorAction ε W))) e
  have he (x : Fin (N+1) → Value W × FloorAction ε W) : E x=x ∘ e := by
    funext j; simp [E,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,e]
  have hh:=hmp.integral_comp' (fun x=>zeroLoss (N+1) n c x 0)
  convert hh using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x=>by
    dsimp only
    rw [he,zeroLoss_relabel (N+1) n c hn hε e x 0]
    simp [e])

theorem sum_zeroLoss_lower {ε W : ℝ} (m n c : ℕ) (hn : 2 ≤ n) (hc : c ≤ m)
    (hε : 0<ε) (x : Fin m → Value W × FloorAction ε W) :
    ε*c*(if ∀ i,zeroClass (x i) then 1 else 0) ≤ ∑ i,zeroLoss m n c x i := by
  by_cases hC : ∀ i,zeroClass (x i)
  · have hp:=marginal_spec n c hn hε (fun j=>(x j).2)
    have hact : activeSet (fun j=>(x j).2)=Finset.univ := by
      ext i; simp [activeSet,(hC i).2]
    have hsum : (∑ i : Fin m,marginal n c (fun j=>(x j).2) i)=(c:ℝ) := by
      simpa [hact,Nat.min_eq_left hc] using hp.2.2
    have hpoint : ∀ i : Fin m,ε*marginal n c (fun j=>(x j).2) i ≤ zeroLoss m n c x i := by
      intro i
      have hb : ε ≤ bid (x i).2 := by
        rcases ha:(x i).2 with u|bb
        · have hh := (hC i).2
          simp [ha,present] at hh
        · exact bb.2.1
      have hs : marginal n c (fun j=>(x j).2) i ≤ success n c (fun j=>(x j).2) i :=
        PayOnce.RareSuccessSlope.marginal_le_success (by omega) ⟨hp.1 i,hp.2.1 i⟩
      have hz : zeroLoss m n c x i=bid (x i).2*success n c (fun j=>(x j).2) i := by
        simp [zeroLoss,hC i,profilePayoff,(hC i).1]
      rw [hz]
      exact (mul_le_mul_of_nonneg_left hs hε.le).trans
        (mul_le_mul_of_nonneg_right hb (success_bounds n c hn hε _ i).1)
    have hh:=Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=>hpoint i)
    rw [← Finset.mul_sum,hsum] at hh
    simpa [if_pos hC] using hh
  · simp only [if_neg hC,mul_zero]
    exact Finset.sum_nonneg (fun i _=>zeroLoss_nonneg m n c hn hε x i)

theorem floor_zero_type_active_null {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n)
    (hc1 : 1 ≤ c) (hcm : c ≤ N+1) (hε : 0<ε) {μ : Measure (Value W)}
    (π : FloorLaw ε W μ) (hIC : AllActionOptimal π (fun z=>floorPayoff N n c (π,z))) :
    (π.1 : Measure (Value W × FloorAction ε W)) {z|zeroClass z}=0 := by
  let C : Set (Value W × FloorAction ε W):={z|zeroClass z}
  let ν : Measure (Fin (N+1) → Value W × FloorAction ε W):=rowLaw (N+1) π.1
  have hC : MeasurableSet C:=measurableSet_zeroClass
  have hAll : MeasurableSet {x : Fin (N+1) → Value W × FloorAction ε W|∀ i,x i∈C} := by
    convert MeasurableSet.iInter (fun i=>hC.preimage (measurable_pi_apply i)) using 1
    · ext x; simp
    · infer_instance
  have hiAll : Integrable (fun x : Fin (N+1) → Value W × FloorAction ε W=>
      if ∀ i,x i∈C then (1:ℝ) else 0) ν := by
    convert (integrable_const (1:ℝ)).indicator (μ:=ν) hAll using 1
    all_goals first | rfl | (funext x; simp only [Set.indicator,mem_setOf_eq])
  have hiSum := integrable_finsetSum Finset.univ
    (fun i _=>integrable_zeroLoss (N+1) n c hn hε π.1 i)
  have hle:=integral_mono (hiAll.const_mul (ε*c)) hiSum
    (sum_zeroLoss_lower (N+1) n c hn hcm hε)
  have heAll : (∫ x : Fin (N+1) → Value W × FloorAction ε W,
      if ∀ i,x i∈C then (1:ℝ) else 0 ∂ν)=((π.1 : Measure (Value W × FloorAction ε W)).real C)^(N+1) := by
    calc
      _=ν.real {x|∀ i,x i∈C} := by
        convert integral_indicator_one (μ:=ν) hAll using 1
        congr 1; funext x; simp only [Set.indicator,mem_setOf_eq,Pi.one_apply]
      _=_ := by
        change ((rowLaw (N+1) π.1 : Measure (Fin (N+1) → Value W × FloorAction ε W)) {x|∀ i,x i∈C}).toReal=_
        rw [rowLaw_all (N+1) π.1 C hC,ENNReal.toReal_pow]; rfl
  rw [integral_const_mul,heAll,integral_finsetSum _
    (fun i _=>integrable_zeroLoss (N+1) n c hn hε π.1 i)] at hle
  have hnonpos : (∑ i : Fin (N+1),∫ x,zeroLoss (N+1) n c x i ∂ν) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    rw [integral_zeroLoss_eq_head N n c hn hε π.1 i]
    exact integral_zeroLoss_head_nonpos N n c hn hε π hIC
  by_contra hmass
  have hq : 0<(π.1 : Measure (Value W × FloorAction ε W)).real C :=
    ENNReal.toReal_pos hmass (measure_ne_top _ _)
  have hcR : (0:ℝ)<c:=by exact_mod_cast (show 0<c by omega)
  have hpos:=mul_pos (mul_pos hε hcR) (pow_pos hq (N+1))
  linarith

theorem floorLaw_zero_value_mass {ε W : ℝ} {μ : Measure (Value W)}
    (π : FloorLaw ε W μ) :
    (π.1 : Measure (Value W × FloorAction ε W)) {z | z.1.1=0}=
      μ {w | w.1=0} := by
  have hm:=Measure.map_apply (μ:=(π.1 : Measure (Value W × FloorAction ε W)))
    (s:={w : Value W | w.1=0}) measurable_fst
    (measurableSet_eq_fun measurable_subtype_coe measurable_const)
  rw [π.2] at hm
  exact hm.symm

theorem floor_zero_type_inactive_mass {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n)
    (hc1 : 1 ≤ c) (hcm : c ≤ N+1) (hε : 0<ε) {μ : Measure (Value W)}
    (π : FloorLaw ε W μ) (hIC : AllActionOptimal π (fun z=>floorPayoff N n c (π,z))) :
    (π.1 : Measure (Value W × FloorAction ε W)) {z | z.1.1=0 ∧ present z.2=false}=
      μ {w | w.1=0} := by
  have hnull:=floor_zero_type_active_null N n c hn hc1 hcm hε π hIC
  have ha:=measure_eq_zero_iff_ae_notMem.mp hnull
  have he : {z : Value W × FloorAction ε W | z.1.1=0 ∧ present z.2=false}
      =ᵐ[(π.1 : Measure (Value W × FloorAction ε W))] {z | z.1.1=0} := by
    filter_upwards [ha] with z hz
    apply propext
    change (z.1.1=0 ∧ present z.2=false) ↔ z.1.1=0
    cases hp : present z.2
    · simp
    · have hnz : z.1.1≠0 := fun hw=>hz ⟨hw,hp⟩
      simp [hnz]
  exact (measure_congr he).trans (floorLaw_zero_value_mass π)

theorem actual_floor_limit_no_zero_type_active (W : ℝ) (N n c : ℕ)
    (hn : 2 ≤ n) (hc1 : 1 ≤ c) (hcm : c ≤ N+1)
    (μ : Measure (Value W)) (ε : ℕ→ℝ) (hε : ∀j,0<ε j)
    (π : (j:ℕ)→FloorLaw (ε j) W μ)
    (hIC : ∀j,AllActionOptimal (π j) (fun z=>floorPayoff N n c (π j,z)))
    (ν₀ : FloorLaw 0 W μ)
    (hν : Tendsto (fun j=>(embeddedFloorLaw (hε j).le (π j)).1) atTop (𝓝 ν₀.1)) :
    (ν₀.1 : Measure (Value W × FloorAction 0 W)) {z | zeroClass z}=0 := by
  let C : Set (Value W × FloorAction 0 W):={z | z.1.1=0 ∧ present z.2=false}
  let D : Set (Value W × FloorAction 0 W):={z | z.1.1=0}
  have hC : IsClosed C := (isClosed_eq (continuous_subtype_val.comp continuous_fst)
    continuous_const).inter ((isClosed_discrete {false}).preimage
      (continuous_present.comp continuous_snd))
  have hj (j:ℕ) : ((embeddedFloorLaw (hε j).le (π j)).1 :
      Measure (Value W × FloorAction 0 W)) C=μ {w | w.1=0} := by
    change Measure.map (embedFloorPair (hε j).le) ((π j).1 : Measure _) C=_
    rw [Measure.map_apply (continuous_embedFloorPair (hε j).le).measurable hC.measurableSet]
    have he : embedFloorPair (hε j).le ⁻¹' C=
        {z : Value W × FloorAction (ε j) W | z.1.1=0 ∧ present z.2=false} := by
      ext z; simp [C,embedFloorPair]
    rw [he]
    exact floor_zero_type_inactive_mass N n c hn hc1 hcm (hε j) (π j) (hIC j)
  have hport:=ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hν hC
  simp_rw [hj] at hport
  rw [limsup_const] at hport
  have hmass : (ν₀.1 : Measure (Value W × FloorAction 0 W)) C=
      (ν₀.1 : Measure (Value W × FloorAction 0 W)) D :=
    le_antisymm (measure_mono (fun _ h=>h.1))
      ((floorLaw_zero_value_mass ν₀).trans_le hport)
  have he : {z : Value W × FloorAction 0 W | zeroClass z}=D\C := by
    ext z
    change (z.1.1=0 ∧ present z.2=true) ↔ (z.1.1=0 ∧ ¬(z.1.1=0 ∧ present z.2=false))
    cases present z.2 <;> simp
  have hsub : C ⊆ D := fun _ h=>h.1
  rw [he,measure_sdiff hsub hC.measurableSet.nullMeasurableSet (measure_ne_top _ _),hmass]
  exact tsub_self _

end FCAppendix.Existence.PayOnceBounded
