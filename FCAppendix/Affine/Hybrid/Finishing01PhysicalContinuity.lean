import FCAppendix.Affine.Hybrid.Finishing01NoisyTransport
import FCAppendix.Affine.LowBody.PatternNullSet
import FCAppendix.Affine.Hybrid.FavoredValue

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
open scoped BigOperators

theorem ae_mapped_affine_ne {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f : X → ℝ) (hnull : ∀ t, ∀ᵐ x ∂mu, f x ≠ t)
    {a : ℝ} (ha : a ≠ 0) (b t : ℝ) :
    ∀ᵐ x ∂mu, a*f x+b ≠ t := by
  filter_upwards [hnull ((t-b)/a)] with x hx h
  apply hx
  apply (eq_div_iff ha).mpr
  nlinarith

theorem ae_iid_mapped_linear_ne {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (f : X → ℝ) (hf : Measurable f)
    (hnull : ∀ t, ∀ᵐ x ∂mu, f x ≠ t)
    {N : ℕ} (a : Fin N → ℝ) (j : Fin N) (hj : a j ≠ 0) (t : ℝ) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => mu), (∑ i, a i*f (r i)) ≠ t := by
  cases N with
  | zero => exact Fin.elim0 j
  | succ N =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => X) j
    let F : (Fin (N+1) → X) → ℝ := fun r => ∑ i, a i*f (r i)
    have hF : Measurable F := by dsimp [F]; fun_prop
    have hS : MeasurableSet {p : X×(Fin N → X) | F (e.symm p) ≠ t} :=
      (measurableSet_eq_fun (hF.comp e.symm.measurable) measurable_const).compl
    have he (x : X) (r : Fin N → X) :
        F (e.symm (x,r)) = a j*f x+∑ i, a (j.succAbove i)*f (r i) := by
      dsimp only [F]
      rw [Fin.sum_univ_succAbove _ j]
      simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
    have hp : ∀ᵐ p ∂mu.prod (Measure.pi (fun _ : Fin N => mu)), F (e.symm p) ≠ t := by
      apply (Measure.ae_prod_iff_ae_ae hS).mpr
      apply (Measure.ae_ae_comm hS).mpr
      apply ae_of_all
      intro r
      filter_upwards [ae_mapped_affine_ne mu f hnull hj
        (∑ i, a (j.succAbove i)*f (r i)) t] with x hx
      rwa [he]
    have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => mu) j).quasiMeasurePreserving.ae hp
    simpa only [e,MeasurableEquiv.symm_apply_apply] using h

theorem ae_subtype_val_ne {s : Set ℝ} (mu : Measure s) [NullSingletonClass mu]
    (b : ℝ) : ∀ᵐ x : s ∂mu, (x:ℝ) ≠ b := by
  by_cases h : ∃ x : s, (x:ℝ)=b
  · obtain ⟨x,hx⟩ := h
    filter_upwards [Measure.ae_ne mu x] with y hy he
    exact hy (Subtype.ext (he.trans hx.symm))
  · exact ae_of_all _ (fun x hx => h ⟨x,hx⟩)

variable {N : ℕ}

def physicalBadSet (kappa : ℝ) (kind : Fin N → Fin 4) : Set (ActivePhysicalData N) :=
  {t | t.2.1 ≤ 0 ∨
    (∃ j : Fin N, kind j=1 ∧ t.2.2.2 j=t.2.1) ∨
    ∃ A B : Finset (Fin (N+1)) × Finset (Fin (N+1)),
      LowBody.focalCopy A 0 ≠ LowBody.focalCopy B 0 ∧
      LowBody.CompleteInformation.potential kappa (activePhysicalBids kind t) A.1 A.2 =
        LowBody.CompleteInformation.potential kappa (activePhysicalBids kind t) B.1 B.2}

theorem isClosed_physicalBadSet (kappa : ℝ) (kind : Fin N → Fin 4) :
    IsClosed (physicalBadSet kappa kind) := by
  have hb := continuous_activePhysicalBids kind
  have he : physicalBadSet kappa kind =
      {t : ActivePhysicalData N | t.2.1 ≤ 0} ∪
      (⋃ j : Fin N, {t : ActivePhysicalData N | kind j=1 ∧ t.2.2.2 j=t.2.1}) ∪
      ⋃ A : Finset (Fin (N+1)) × Finset (Fin (N+1)),
      ⋃ B : Finset (Fin (N+1)) × Finset (Fin (N+1)),
        {t : ActivePhysicalData N | LowBody.focalCopy A 0 ≠ LowBody.focalCopy B 0 ∧
          LowBody.CompleteInformation.potential kappa (activePhysicalBids kind t) A.1 A.2 =
            LowBody.CompleteInformation.potential kappa (activePhysicalBids kind t) B.1 B.2} := by
    ext t
    simp only [physicalBadSet,mem_setOf_eq,mem_union,mem_iUnion]
    exact or_assoc.symm
  rw [he]
  apply IsClosed.union
  · apply (isClosed_le (by fun_prop) continuous_const).union
    apply isClosed_iUnion_of_finite
    intro j
    by_cases hj : kind j=1
    · simpa only [hj,true_and] using
        (isClosed_eq (show Continuous (fun t : ActivePhysicalData N => t.2.2.2 j) by fun_prop)
          (show Continuous (fun t : ActivePhysicalData N => t.2.1) by fun_prop))
    · simpa only [hj,false_and,setOf_false] using isClosed_empty
  · apply isClosed_iUnion_of_finite
    intro A
    apply isClosed_iUnion_of_finite
    intro B
    by_cases h : LowBody.focalCopy A 0=LowBody.focalCopy B 0
    · simpa only [h,ne_eq,not_true_eq_false,false_and,setOf_false] using isClosed_empty
    · simpa only [h,ne_eq,not_false_eq_true,true_and,Function.comp_def] using
        isClosed_eq ((LowBody.continuous_potential kappa A).comp hb)
          ((LowBody.continuous_potential kappa B).comp hb)

theorem physical_potential_difference (kappa v b : ℝ) (kind : Fin N → Fin 4)
    (low active : Fin N → ℝ)
    (A B : Finset (Fin (N+1)) × Finset (Fin (N+1))) :
    LowBody.CompleteInformation.potential kappa (activePhysicalBids kind (v,b,low,active)) A.1 A.2 -
      LowBody.CompleteInformation.potential kappa (activePhysicalBids kind (v,b,low,active)) B.1 B.2 =
      (LowBody.copyCoefficient kappa A 0-LowBody.copyCoefficient kappa B 0)*b +
      (∑ j, (if kind j=0 then LowBody.copyCoefficient kappa A j.succ-
        LowBody.copyCoefficient kappa B j.succ else 0)*low j) +
      (∑ j, (if kind j=1 then LowBody.copyCoefficient kappa A j.succ-
        LowBody.copyCoefficient kappa B j.succ else 0)*active j) := by
  rw [LowBody.potential_eq_copyCoefficient,LowBody.potential_eq_copyCoefficient,
    Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [activePhysicalBids,Fin.cons_zero,Fin.cons_succ]
  have hs : (∑ j, LowBody.copyCoefficient kappa A j.succ *
      (if kind j=0 then low j else if kind j=1 then active j else 0)) -
    (∑ j, LowBody.copyCoefficient kappa B j.succ *
      (if kind j=0 then low j else if kind j=1 then active j else 0)) =
    (∑ j, (if kind j=0 then LowBody.copyCoefficient kappa A j.succ-
      LowBody.copyCoefficient kappa B j.succ else 0)*low j) +
    (∑ j, (if kind j=1 then LowBody.copyCoefficient kappa A j.succ-
      LowBody.copyCoefficient kappa B j.succ else 0)*active j) := by
    rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h0 : kind j=0
    · have h1 : kind j≠1 := by rw [h0]; norm_num
      simp [h0]
      ring
    · by_cases h1 : kind j=1
      · simp [h1]
        ring
      · simp only [h0,h1,if_false,mul_zero,zero_mul,sub_self,add_zero]
  linear_combination hs

theorem ae_two_rows_ties_same_copy
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (nu : Measure Y) [IsProbabilityMeasure nu]
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfnull : ∀ t, ∀ᵐ x ∂mu, f x ≠ t) (hgnull : ∀ t, ∀ᵐ y ∂nu, g y ≠ t)
    {kappa b : ℝ} (hkappa : 0 < kappa) (hb : b ≠ 0)
    (v : ℝ) (kind : Fin N → Fin 4) :
    ∀ᵐ r ∂(Measure.pi (fun _ : Fin N => mu)).prod (Measure.pi (fun _ : Fin N => nu)),
      ∀ A B : Finset (Fin (N+1)) × Finset (Fin (N+1)),
        LowBody.CompleteInformation.potential kappa
            (activePhysicalBids kind (v,b,(fun j => f (r.1 j)),fun j => g (r.2 j))) A.1 A.2 =
          LowBody.CompleteInformation.potential kappa
            (activePhysicalBids kind (v,b,(fun j => f (r.1 j)),fun j => g (r.2 j))) B.1 B.2 →
          LowBody.focalCopy A 0=LowBody.focalCopy B 0 := by
  apply ae_all_iff.mpr
  intro A
  apply ae_all_iff.mpr
  intro B
  by_cases hcopy : LowBody.focalCopy A 0=LowBody.focalCopy B 0
  · exact ae_of_all _ (fun _ _ => hcopy)
  let a0 : Fin N → ℝ := fun j => if kind j=0 then
    LowBody.copyCoefficient kappa A j.succ-LowBody.copyCoefficient kappa B j.succ else 0
  let a1 : Fin N → ℝ := fun j => if kind j=1 then
    LowBody.copyCoefficient kappa A j.succ-LowBody.copyCoefficient kappa B j.succ else 0
  let a : ℝ := LowBody.copyCoefficient kappa A 0-LowBody.copyCoefficient kappa B 0
  have ha : a ≠ 0 := sub_ne_zero.mpr
    (LowBody.copyCoefficient_ne_of_focalCopy_ne hkappa A B 0 hcopy)
  have hms : MeasurableSet {r : (Fin N → X)×(Fin N → Y) |
      a*b+(∑ j, a0 j*f (r.1 j))+(∑ j, a1 j*g (r.2 j)) ≠ 0} := by
    apply MeasurableSet.compl
    apply measurableSet_eq_fun _ measurable_const
    fun_prop
  have hneq : ∀ᵐ r ∂(Measure.pi (fun _ : Fin N => mu)).prod (Measure.pi (fun _ : Fin N => nu)),
      a*b+(∑ j, a0 j*f (r.1 j))+(∑ j, a1 j*g (r.2 j)) ≠ 0 := by
    by_cases h0 : ∃ j, a0 j ≠ 0
    · obtain ⟨j,hj⟩ := h0
      apply (Measure.ae_prod_iff_ae_ae hms).mpr
      apply (Measure.ae_ae_comm hms).mpr
      apply ae_of_all
      intro r1
      filter_upwards [ae_iid_mapped_linear_ne mu f hf hfnull a0 j hj
        (-a*b-(∑ i, a1 i*g (r1 i)))] with r0 hr h
      exact hr (by linarith)
    · have h00 : ∀ j, a0 j=0 := by simpa only [not_exists,not_not] using h0
      by_cases h1 : ∃ j, a1 j ≠ 0
      · obtain ⟨j,hj⟩ := h1
        apply (Measure.ae_prod_iff_ae_ae hms).mpr
        apply ae_of_all
        intro r0
        filter_upwards [ae_iid_mapped_linear_ne nu g hg hgnull a1 j hj
          (-a*b-(∑ i, a0 i*f (r0 i)))] with r1 hr h
        exact hr (by linarith)
      · have h11 : ∀ j, a1 j=0 := by simpa only [not_exists,not_not] using h1
        exact ae_of_all _ (fun r => by
          simp only [h00,h11,zero_mul,Finset.sum_const_zero,add_zero]
          exact mul_ne_zero ha hb)
  filter_upwards [hneq] with r hr he
  exfalso
  apply hr
  have h := physical_potential_difference kappa v b kind
    (fun j => f (r.1 j)) (fun j => g (r.2 j)) A B
  rw [he,sub_self] at h
  exact h.symm

theorem ae_two_rows_not_bad
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (nu : Measure Y) [IsProbabilityMeasure nu]
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfnull : ∀ t, ∀ᵐ x ∂mu, f x ≠ t) (hgnull : ∀ t, ∀ᵐ y ∂nu, g y ≠ t)
    {kappa b : ℝ} (hkappa : 0 < kappa) (hb : 0 < b)
    (v : ℝ) (kind : Fin N → Fin 4) :
    ∀ᵐ r ∂(Measure.pi (fun _ : Fin N => mu)).prod (Measure.pi (fun _ : Fin N => nu)),
      (v,b,(fun j => f (r.1 j)),fun j => g (r.2 j)) ∉ physicalBadSet kappa kind := by
  have ht : ∀ᵐ r ∂Measure.pi (fun _ : Fin N => nu), ∀ j : Fin N, g (r j) ≠ b :=
    ae_all_iff.mpr (fun j =>
      (measurePreserving_eval (fun _ : Fin N => nu) j).quasiMeasurePreserving.ae (hgnull b))
  have htr : ∀ᵐ r ∂(Measure.pi (fun _ : Fin N => mu)).prod (Measure.pi (fun _ : Fin N => nu)),
      ∀ j : Fin N, g (r.2 j) ≠ b :=
    (measurePreserving_snd (μ:=Measure.pi (fun _ : Fin N => mu))
      (ν:=Measure.pi (fun _ : Fin N => nu))).quasiMeasurePreserving.ae ht
  filter_upwards [htr,ae_two_rows_ties_same_copy mu nu f g hf hg hfnull hgnull hkappa hb.ne' v kind]
    with r hr hcopy
  rintro (h0 | ⟨j,hj,he⟩ | ⟨A,B,hne,he⟩)
  · exact not_le_of_gt hb h0
  · exact hr j he
  · exact hne (hcopy A B he)

theorem continuousAt_physical_of_not_bad {xi : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (z L W : ℝ) (c : ℕ)
    (kind : Fin N → Fin 4) (t : ActivePhysicalData N)
    (hbid : ∀ i, 0 ≤ activePhysicalBids kind t i)
    (hactive : ∀ i, 0 < activePhysicalActiveBids kind t i)
    (ht : t ∉ physicalBadSet (1-xi) kind) :
    ContinuousAt (activePhysicalPatternPayoff xi z L W c kind) t := by
  have hown : 0 < t.2.1 := lt_of_not_ge (fun h => ht (Or.inl h))
  let T := activePatternTemplate c kind
  let b := activePhysicalBids kind
  have hb := continuous_activePhysicalBids kind
  by_cases hguard : activePatternGuarded xi L W c z kind
  · have he : activePhysicalPatternPayoff xi z L W c kind =
        (fun s : ActivePhysicalData N => sourceOwnerPayoff xi (1-2*xi) s.1
          (activePhysicalActiveBids kind s) (activePatternResidual c z kind)
          (activePatternOwner c z kind 0) (activePatternOwner c z kind 1) (activePatternFocal kind)) := by
      funext s
      exact if_pos hguard
    rw [he]
    apply (continuousAt_joint_sourceOwnerPayoff xi (1-2*xi) _ _ _ _ hguard.1
      hguard.2.2.1 hguard.2.2.2.1 (t.1,activePhysicalActiveBids kind t) hactive ?_).comp
        (f := fun s : ActivePhysicalData N => (s.1, activePhysicalActiveBids kind s))
        (continuous_fst.prodMk (continuous_activePhysicalActiveBids kind)).continuousAt
    intro i hi heq
    have hi0 : i.val ≠ 0 := fun h => hi (Subtype.ext h)
    obtain ⟨j,hj⟩ := Fin.eq_succ_of_ne_zero hi0
    have hj1 : kind j=1 := by
      simpa only [activePatternPred,hj,Fin.cases_succ] using i.property
    apply ht
    apply Or.inr
    apply Or.inl
    refine ⟨j,hj1,?_⟩
    simpa only [activePhysicalActiveBids,activePatternFocal,hj,Fin.cases_succ,Fin.cases_zero] using heq
  · by_cases hequal : T.residual₀=T.residual₁
    · have he : activePhysicalPatternPayoff xi z L W c kind =
          (fun s : ActivePhysicalData N => LowBody.equalPayoff xi T.residual₀ 0 s.1 (b s)) := by
        funext s
        change (if activePatternGuarded xi L W c z kind then _ else if T.residual₀ = T.residual₁ then _ else _) = _
        rw [if_neg hguard, if_pos hequal]
      rw [he]
      have hp := (EqualCapacity.continuousAt_positiveMarginal_focal hxi hxi1 T.residual₀
        (b t) hbid (0:Fin (N+1)) hown).comp (f:=b) hb.continuousAt
      have hbi : ContinuousAt (fun s => b s 0) t := ((continuous_apply 0).comp hb).continuousAt
      unfold LowBody.equalPayoff
      exact (continuous_fst.continuousAt.mul ((continuousAt_const.mul hp).sub (hp.pow 2))).sub
        (hbi.mul ((continuousAt_const.mul hp).sub (continuousAt_const.mul (hp.pow 2))))
    · have he : activePhysicalPatternPayoff xi z L W c kind =
          (fun s : ActivePhysicalData N => LowBody.purePayoff (1-xi) s.1 (b s)
            (T.selection (1-xi) (b s)) 0) := by
        funext s
        change (if activePatternGuarded xi L W c z kind then _ else if T.residual₀ = T.residual₁ then _ else _) = _
        rw [if_neg hguard, if_neg hequal]
      rw [he]
      apply LowBody.continuousAt_selected_payoff
        (fun s (A : T.Candidate) => LowBody.CompleteInformation.potential (1-xi) (b s) A.val.1 A.val.2)
        (fun A => (LowBody.continuous_potential (1-xi) A.val).comp hb)
        (fun A : T.Candidate => LowBody.focalCopy A.val 0)
        (fun s (A : T.Candidate) => LowBody.purePayoff (1-xi) s.1 (b s) A.val 0)
        (fun A => by unfold LowBody.purePayoff; split_ifs <;> fun_prop)
        (fun s A B h => LowBody.purePayoff_eq_of_focalCopy_eq (1-xi) s.1 (b s) A.val B.val 0 h) t
      intro A B he
      by_contra hne
      exact ht (Or.inr (Or.inr ⟨A.val,B.val,hne,he⟩))

end FCAppendix.Affine.Hybrid.Finish01
