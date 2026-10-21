import FCAppendix.Existence.R01PayOnceImprovement

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped BigOperators
open FCAppendix.Existence.Distributional
attribute [local instance] Classical.propDecidable

private theorem continuous_consProfile {W : ℝ} (N : ℕ) (z : Value W × FloorAction 0 W) :
    Continuous (fun r : Fin N→Value W × FloorAction 0 W=>Fin.cons
      (α:=fun _ : Fin (N+1)=>Value W × FloorAction 0 W) z r) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact continuous_const
  · exact continuous_apply j

private theorem consProfile_actions {W : ℝ} (N : ℕ) (z : Value W × FloorAction 0 W)
    (r : Fin N→Value W × FloorAction 0 W) :
    (fun j=>((Fin.cons (α:=fun _ : Fin (N+1)=>Value W × FloorAction 0 W) z r) j).2)=
      insertFocal N z.2 r := by
  funext j
  refine Fin.cases ?_ (fun k=>?_) j <;> simp [insertFocal]

private theorem positivePayoff_eq_focal_integral {W : ℝ} (N n c : ℕ)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (z : Value W × FloorAction 0 W) :
    positivePayoff N n c π z=∫r,positiveProfilePayoff (N+1) n c (Fin.cons z r) 0
      ∂(rowLaw N π : Measure (Fin N→Value W × FloorAction 0 W)) := by
  change (z.1.1-bid z.2)*(∫r,positiveSuccess n c (insertFocal N z.2 r) 0 ∂_)=_
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun r=>by
    simp only [positiveProfilePayoff,Fin.cons_zero]
    rw [consProfile_actions])

private theorem clippedPayoff_eq_focal_integral {W : ℝ} (N n c : ℕ)
    (δ : ℝ) (hδW : δ≤W) (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (z : Value W × FloorAction 0 W) :
    clippedPayoff N n c δ hδW π z=∫r,clippedProfilePayoff (N+1) n c δ hδW (Fin.cons z r) 0
      ∂(rowLaw N π : Measure (Fin N→Value W × FloorAction 0 W)) := by
  change (z.1.1-bid (clipToFloor δ hδW z.2))*
    (∫r,success n c (clippedInsertFocal N δ hδW z.2 r) 0 ∂_)=_
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun r=>by
    simp only [clippedProfilePayoff,Fin.cons_zero]
    have he:=consProfile_actions N z r
    have hh:=congrArg (fun x=>success n c (fun j=>clipToFloor δ hδW (x j)) 0) he
    exact congrArg (fun x=>(z.1.1-bid (clipToFloor δ hδW z.2))*x) hh.symm)

private theorem focal_integrable_positive {W : ℝ} (N n c : ℕ) (hn : 2≤n) (hW : 0≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (z : Value W × FloorAction 0 W) :
    Integrable (fun r=>positiveProfilePayoff (N+1) n c (Fin.cons z r) 0)
      (rowLaw N π : Measure (Fin N→Value W × FloorAction 0 W)) := by
  apply Integrable.of_bound ((measurable_positiveProfilePayoff (N+1) n c hn 0).comp
    (continuous_consProfile N z).measurable).aestronglyMeasurable W
  exact Filter.Eventually.of_forall (fun r=>by
    change ‖positiveProfilePayoff (N+1) n c (Fin.cons z r) 0‖≤W
    simpa only [Real.norm_eq_abs] using positiveProfilePayoff_abs_le (N+1) n c hn hW (Fin.cons z r) 0)

private theorem focal_integrable_clipped {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (z : Value W × FloorAction 0 W) :
    Integrable (fun r=>clippedProfilePayoff (N+1) n c δ hδW (Fin.cons z r) 0)
      (rowLaw N π : Measure (Fin N→Value W × FloorAction 0 W)) :=
  (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,
    (continuous_clippedProfilePayoff (N+1) n c hn δ hδ hδW 0).comp
      (continuous_consProfile N z)⟩).integrable _

private theorem focal_error_from_profile_bound {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (z : Value W × FloorAction 0 W)
    (a : ℝ)
    (hpoint : ∀r : Fin N→Value W × FloorAction 0 W,
      |clippedProfilePayoff (N+1) n c δ hδW (Fin.cons z r) 0-
        positiveProfilePayoff (N+1) n c (Fin.cons z r) 0|≤
      (2*W)*(a+∑j:Fin N,if r j∈smallActive δ then (1:ℝ) else 0)) :
    |clippedPayoff N n c δ hδW π z-positivePayoff N n c π z|≤
      (2*W)*(a+N*(π : Measure (Value W × FloorAction 0 W)).real (smallActive δ)) := by
  let ν : Measure (Fin N→Value W × FloorAction 0 W):=rowLaw N π
  have hiP:=focal_integrable_positive N n c hn (hδ.le.trans hδW) π z
  have hiC:=focal_integrable_clipped N n c hn δ hδ hδW π z
  have hiCount : Integrable (fun r : Fin N→Value W × FloorAction 0 W=>
      ∑j:Fin N,if r j∈smallActive δ then (1:ℝ) else 0) ν := by
    apply integrable_finsetSum
    intro j _
    convert (integrable_const (1:ℝ)).indicator (μ:=ν)
      ((isClosed_smallActive δ).measurableSet.preimage (measurable_pi_apply j)) using 1
    all_goals rfl
  rw [clippedPayoff_eq_focal_integral,positivePayoff_eq_focal_integral,
    ← integral_sub hiC hiP]
  have hab := abs_integral_le_integral_abs
    (f:=fun r=>clippedProfilePayoff (N+1) n c δ hδW (Fin.cons z r) 0-
      positiveProfilePayoff (N+1) n c (Fin.cons z r) 0) (μ:=ν)
  have hle:=integral_mono (hiC.sub hiP).abs
    (((integrable_const a).add hiCount).const_mul (2*W)) hpoint
  have hcnt : (∫r,∑j:Fin N,if r j∈smallActive δ then (1:ℝ) else 0 ∂ν)=
      (N:ℝ)*(π : Measure (Value W × FloorAction 0 W)).real (smallActive δ) :=
    integral_row_class_count N π (smallActive δ) (isClosed_smallActive δ).measurableSet
  simp only [Pi.add_apply,Pi.sub_apply] at hle
  rw [integral_const_mul,integral_add (integrable_const a) hiCount,hcnt] at hle
  simpa only [integral_const,probReal_univ,one_smul] using hab.trans hle

private theorem focal_error_bound {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (z : Value W × FloorAction 0 W) :
    |clippedPayoff N n c δ hδW π z-positivePayoff N n c π z|≤
      (2*W)*((if z∈smallActive δ then (1:ℝ) else 0)+
        N*(π : Measure (Value W × FloorAction 0 W)).real (smallActive δ)) := by
  apply focal_error_from_profile_bound N n c hn δ hδ hδW π z
  intro r
  simpa only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ] using
    profile_clipping_error_bound (N+1) n c hn δ hδ hδW (Fin.cons z r) 0

private theorem focal_error_bound_safe {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (z : Value W × FloorAction 0 W)
    (hz : present z.2=true→δ≤bid z.2) :
    |clippedPayoff N n c δ hδW π z-positivePayoff N n c π z|≤
      (2*W)*(N*(π : Measure (Value W × FloorAction 0 W)).real (smallActive δ)) := by
  have hh:=focal_error_from_profile_bound N n c hn δ hδ hδW π z 0 (by
    intro r
    by_cases hr : ∀j,r j∉smallActive δ
    · have hs : ∀j : Fin (N+1),present ((Fin.cons (α:=fun _ : Fin (N+1)=>Value W × FloorAction 0 W) z r) j).2=true→
          δ≤bid ((Fin.cons (α:=fun _ : Fin (N+1)=>Value W × FloorAction 0 W) z r) j).2 := by
        intro j
        refine Fin.cases ?_ (fun k=>?_) j
        · exact hz
        · intro hp
          exact (lt_of_not_ge (fun hb=>hr k ⟨hp,hb⟩)).le
      have he : clippedProfilePayoff (N+1) n c δ hδW (Fin.cons z r) 0=
          positiveProfilePayoff (N+1) n c (Fin.cons z r) 0 := by
        rw [clippedProfilePayoff,bid_clipToFloor_eq δ hδW _ (hs 0),
          clipped_success_eq n c δ hδ hδW _ hs]
        rfl
      rw [he,sub_self,abs_zero]
      have hW : 0≤W:=hδ.le.trans hδW
      exact mul_nonneg (by positivity) (by positivity)
    · obtain ⟨j,hj⟩ : ∃j,r j∈smallActive δ := by simpa only [not_forall,not_not] using hr
      have hcnt : (1:ℝ)≤∑k:Fin N,if r k∈smallActive δ then 1 else 0 := by
        calc
          (1:ℝ)=(if r j∈smallActive δ then 1 else 0) := by rw [if_pos hj]
          _≤_ := Finset.single_le_sum
            (f:=fun k:Fin N=>if r k∈smallActive δ then (1:ℝ) else 0)
            (fun k _=>by split_ifs <;> norm_num) (Finset.mem_univ j)
      have hab : |clippedProfilePayoff (N+1) n c δ hδW (Fin.cons z r) 0-
          positiveProfilePayoff (N+1) n c (Fin.cons z r) 0|≤2*W := by
        have ht:=abs_sub_le
          (clippedProfilePayoff (N+1) n c δ hδW (Fin.cons z r) 0) 0
          (positiveProfilePayoff (N+1) n c (Fin.cons z r) 0)
        have hc:=clippedProfilePayoff_abs_le (N+1) n c hn δ hδ hδW (Fin.cons z r) 0
        have hp:=positiveProfilePayoff_abs_le (N+1) n c hn (hδ.le.trans hδW) (Fin.cons z r) 0
        simp only [sub_zero,zero_sub,abs_neg] at ht
        linarith
      have hW : 0≤W:=hδ.le.trans hδW
      exact hab.trans (by nlinarith))
  simpa only [zero_add] using hh

private theorem clippedPayoff_abs_le {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (z : Value W × FloorAction 0 W) :
    |clippedPayoff N n c δ hδW π z|≤W := by
  rw [clippedPayoff_eq_focal_integral]
  have hi:=focal_integrable_clipped N n c hn δ hδ hδW π z
  have hh:=integral_mono hi.abs (integrable_const W)
    (fun r=>clippedProfilePayoff_abs_le (N+1) n c hn δ hδ hδW (Fin.cons z r) 0)
  exact (abs_integral_le_integral_abs (f:=fun r=>clippedProfilePayoff (N+1) n c δ hδW (Fin.cons z r) 0)).trans
    (by simpa using hh)

theorem improvementMass_clipping_error {W : ℝ} (hW : 0≤W) (N n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (b : FloorAction 0 W)
    (hb : present b=true→δ≤bid b) :
    |clippedImprovementMass N n c δ hδW π b-improvementMass N n c π b|≤
      (4*W)*(N+1)*(π : Measure (Value W × FloorAction 0 W)).real (smallActive δ) := by
  let C:=fun z : Value W × FloorAction 0 W=>max 0
    (clippedPayoff N n c δ hδW π (z.1,b)-clippedPayoff N n c δ hδW π z)
  let P:=fun z : Value W × FloorAction 0 W=>max 0
    (positivePayoff N n c π (z.1,b)-positivePayoff N n c π z)
  let q:=(π : Measure (Value W × FloorAction 0 W)).real (smallActive δ)
  have hiC : Integrable C (π : Measure _) := by
    apply Integrable.of_bound
      ((continuous_const.max (((continuous_clippedPayoff N n c hn δ hδ hδW).comp
        (continuous_const.prodMk (continuous_fst.prodMk continuous_const))).sub
        ((continuous_clippedPayoff N n c hn δ hδ hδW).comp
          (continuous_const.prodMk continuous_id)))).aestronglyMeasurable) (2*W)
    exact Filter.Eventually.of_forall (fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_left _ _)]
      apply max_le (by positivity)
      change clippedPayoff N n c δ hδW π (z.1,b)-clippedPayoff N n c δ hδW π z≤2*W
      have h1:=abs_le.mp (clippedPayoff_abs_le N n c hn δ hδ hδW π (z.1,b))
      have h2:=abs_le.mp (clippedPayoff_abs_le N n c hn δ hδ hδW π z)
      linarith [h1.2,h2.1])
  have hiP : Integrable P (π : Measure _) := by
    apply Integrable.of_bound (measurable_const.max
      (((measurable_positivePayoff N n c hn π).comp
        (measurable_fst.prodMk measurable_const)).sub (measurable_positivePayoff N n c hn π))).aestronglyMeasurable (2*W)
    exact Filter.Eventually.of_forall (fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_left _ _)]
      apply max_le (by positivity)
      change positivePayoff N n c π (z.1,b)-positivePayoff N n c π z≤2*W
      have h1:=abs_le.mp (positivePayoff_abs_le N n c hn hW π (z.1,b))
      have h2:=abs_le.mp (positivePayoff_abs_le N n c hn hW π z)
      linarith [h1.2,h2.1])
  have hpoint : ∀z : Value W × FloorAction 0 W,|C z-P z|≤
      (2*W)*((if z∈smallActive δ then (1:ℝ) else 0)+2*N*q) := by
    intro z
    have hmax:=abs_max_sub_max_le_max 0
      (clippedPayoff N n c δ hδW π (z.1,b)-clippedPayoff N n c δ hδW π z) 0
      (positivePayoff N n c π (z.1,b)-positivePayoff N n c π z)
    simp only [sub_self,abs_zero] at hmax
    have hmax' : |C z-P z|≤|(clippedPayoff N n c δ hδW π (z.1,b)-clippedPayoff N n c δ hδW π z)-
        (positivePayoff N n c π (z.1,b)-positivePayoff N n c π z)| :=
      hmax.trans (max_eq_right (abs_nonneg _)).le
    have htri : |(clippedPayoff N n c δ hδW π (z.1,b)-clippedPayoff N n c δ hδW π z)-
        (positivePayoff N n c π (z.1,b)-positivePayoff N n c π z)|≤
        |clippedPayoff N n c δ hδW π (z.1,b)-positivePayoff N n c π (z.1,b)|+
        |clippedPayoff N n c δ hδW π z-positivePayoff N n c π z| := by
      have hh:=abs_sub_le (clippedPayoff N n c δ hδW π (z.1,b)-positivePayoff N n c π (z.1,b))
        0 (clippedPayoff N n c δ hδW π z-positivePayoff N n c π z)
      simp only [sub_zero,zero_sub,abs_neg] at hh
      convert hh using 1 <;> first | rfl | (congr 1; ring)
    have hdev:=focal_error_bound_safe N n c hn δ hδ hδW π (z.1,b) hb
    have hinc:=focal_error_bound N n c hn δ hδ hδW π z
    have he:=(hmax'.trans htri).trans (add_le_add hdev hinc)
    convert he using 1 <;> first | rfl | (dsimp [q]; ring)
  have hiInd : Integrable (fun z : Value W × FloorAction 0 W=>
      if z∈smallActive δ then (1:ℝ) else 0) (π : Measure _) := by
    convert (integrable_const (1:ℝ)).indicator (μ:=(π : Measure (Value W × FloorAction 0 W)))
      (isClosed_smallActive δ).measurableSet using 1
    all_goals rfl
  have hle:=integral_mono (hiC.sub hiP).abs
    ((hiInd.add (integrable_const (2*N*q))).const_mul (2*W)) hpoint
  have hind : (∫z : Value W × FloorAction 0 W,if z∈smallActive δ then (1:ℝ) else 0
      ∂(π : Measure _))=q := by
    convert integral_indicator_one (μ:=(π : Measure (Value W × FloorAction 0 W)))
      (isClosed_smallActive δ).measurableSet using 1
    all_goals rfl
  simp only [Pi.add_apply,Pi.sub_apply] at hle
  rw [integral_const_mul,integral_add hiInd (integrable_const (2*N*q)),hind] at hle
  have hab:=abs_integral_le_integral_abs (f:=fun z=>C z-P z) (μ:=(π : Measure _))
  rw [integral_sub hiC hiP] at hab
  change |(∫z,C z ∂(π : Measure _))-(∫z,P z ∂(π : Measure _))|≤_
  have hh:=hab.trans hle
  simp only [integral_const,probReal_univ,one_smul] at hh
  have hq : 0≤q:=ENNReal.toReal_nonneg
  exact hh.trans (by nlinarith [mul_nonneg hW hq])

end FCAppendix.Existence.PayOnceBounded
