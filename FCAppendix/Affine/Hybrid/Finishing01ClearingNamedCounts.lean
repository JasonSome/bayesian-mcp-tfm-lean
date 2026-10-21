import FCAppendix.Affine.Hybrid.Finishing01ClearingRelabel
import FCAppendix.Affine.Hybrid.Finishing01ClearingCountLimits
import FCAppendix.Affine.Hybrid.Finishing01PhysicalContinuity

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
open scoped BigOperators

section IidNames
variable {N : ℕ}

def namedRivalEquiv (e : Equiv.Perm (Fin (N+1))) :
    Fin N ≃ {i : Fin (N+1) // i ≠ e 0} :=
  Equiv.ofBijective (fun j => ⟨e j.succ,by
    intro h
    exact Fin.succ_ne_zero j (e.injective h)⟩) (by
      constructor
      · intro i j h
        exact Fin.succ_injective _ (e.injective (congrArg Subtype.val h))
      · intro i
        have hn : e.symm i.val ≠ 0 := by
          intro h
          apply i.property
          rw [←e.apply_symm_apply i.val,h]
        obtain ⟨j,hj⟩ := Fin.eq_succ_of_ne_zero hn
        refine ⟨j,?_⟩
        apply Subtype.ext
        change e j.succ = i.val
        rw [←hj,e.apply_symm_apply])

lemma namedRivalEquiv_apply (e : Equiv.Perm (Fin (N+1))) (j : Fin N) :
    (namedRivalEquiv e j).val = e j.succ := rfl

def reindexRivals {X : Type*} (e : Equiv.Perm (Fin (N+1)))
    (r : Fin N → X) : {i : Fin (N+1) // i ≠ e 0} → X :=
  fun i => r ((namedRivalEquiv e).symm i)

lemma reindexRivals_apply {X : Type*} (e : Equiv.Perm (Fin (N+1)))
    (r : Fin N → X) (j : Fin N) :
    reindexRivals e r (namedRivalEquiv e j) = r j := by
  simp only [reindexRivals,Equiv.symm_apply_apply]

lemma measurable_reindexRivals {X : Type*} [MeasurableSpace X]
    (e : Equiv.Perm (Fin (N+1))) : Measurable (reindexRivals (X:=X) e) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply ((namedRivalEquiv e).symm i))

theorem reindexRivals_law {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (e : Equiv.Perm (Fin (N+1))) :
    (Measure.pi (fun _ : Fin N => mu)).map (reindexRivals e) =
      Measure.pi (fun _ : {i : Fin (N+1) // i ≠ e 0} => mu) := by
  have h := (measurePreserving_piCongrLeft
    (fun _ : {i : Fin (N+1) // i ≠ e 0} => mu) (namedRivalEquiv e)).map_eq
  convert! h using 1
  congr 1
  funext r i
  obtain ⟨j, rfl⟩ := (namedRivalEquiv e).surjective i
  simp only [reindexRivals, Equiv.symm_apply_apply, MeasurableEquiv.piCongrLeft_apply_apply]

theorem retained_original_rows_relabel
    {R X Y Z : Type*} [MeasurableSpace R] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z]
    (rho : Measure R) [IsProbabilityMeasure rho]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (nu : Measure Y) [IsProbabilityMeasure nu]
    (tau : Measure Z) [IsProbabilityMeasure tau]
    (e : Equiv.Perm (Fin (N+1))) :
    (rho.prod ((Measure.pi (fun _ : Fin N => mu)).prod
      ((Measure.pi (fun _ : Fin N => nu)).prod (Measure.pi (fun _ : Fin N => tau))))).map
      (fun p => (p.1,reindexRivals e p.2.1,
        reindexRivals e p.2.2.1,reindexRivals e p.2.2.2)) =
      rho.prod ((Measure.pi (fun _ : {i : Fin (N+1) // i ≠ e 0} => mu)).prod
        ((Measure.pi (fun _ : {i : Fin (N+1) // i ≠ e 0} => nu)).prod
          (Measure.pi (fun _ : {i : Fin (N+1) // i ≠ e 0} => tau)))) := by
  let fX := reindexRivals (X:=X) e
  let fY := reindexRivals (X:=Y) e
  let fZ := reindexRivals (X:=Z) e
  have hX : Measurable fX := measurable_reindexRivals e
  have hY : Measurable fY := measurable_reindexRivals e
  have hZ : Measurable fZ := measurable_reindexRivals e
  change (rho.prod ((Measure.pi (fun _ : Fin N => mu)).prod
      ((Measure.pi (fun _ : Fin N => nu)).prod (Measure.pi (fun _ : Fin N => tau))))).map
      (Prod.map id (Prod.map fX (Prod.map fY fZ))) = _
  rw [←Measure.map_prod_map _ _ measurable_id (hX.prodMap (hY.prodMap hZ)),
    Measure.map_id,←Measure.map_prod_map _ _ hX (hY.prodMap hZ),
    ←Measure.map_prod_map _ _ hY hZ]
  simp only [fX,fY,fZ,reindexRivals_law]

lemma named_physical_bid_focal (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) (bid : ℝ) (rows : ActiveCountRows N) :
    (activePhysicalBids kind (0,bid,rows) ∘ e.symm) (e 0) = bid := by
  simp [activePhysicalBids]

lemma named_physical_bid_rival (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) (bid : ℝ) (rows : ActiveCountRows N) (j : Fin N) :
    (activePhysicalBids kind (0,bid,rows) ∘ e.symm) (namedRivalEquiv e j) =
      if kind j=0 then rows.1 j else if kind j=1 then rows.2 j else 0 := by
  simp [namedRivalEquiv_apply,activePhysicalBids]

end IidNames

namespace Primitives
variable (P : Primitives)

theorem actual_original_noisy_rows_relabel (N : ℕ)
    (low : ProbabilityMeasure P.Low) (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) (e : Equiv.Perm (Fin (N+1))) :
    ((((pi.1 : Measure (P.Value×P.Bid)).prod (volume : Measure unitInterval)).prod
        (Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)))).prod
      ((Measure.pi (fun _ : Fin N => FiniteLaw.probabilityMeasure P.categories)).prod
        ((Measure.pi (fun _ : Fin N => (low : Measure P.Low))).prod
          (Measure.pi (fun _ : Fin N =>
            (pi.1 : Measure (P.Value×P.Bid)).prod (volume : Measure unitInterval)))))).map
      (fun p => (p.1,reindexRivals e p.2.1,
        reindexRivals e p.2.2.1,reindexRivals e p.2.2.2)) =
      (((pi.1 : Measure (P.Value×P.Bid)).prod (volume : Measure unitInterval)).prod
        (Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)))).prod
      ((Measure.pi (fun _ : {i : Fin (N+1) // i ≠ e 0} =>
        FiniteLaw.probabilityMeasure P.categories)).prod
        ((Measure.pi (fun _ : {i : Fin (N+1) // i ≠ e 0} => (low : Measure P.Low))).prod
          (Measure.pi (fun _ : {i : Fin (N+1) // i ≠ e 0} =>
            (pi.1 : Measure (P.Value×P.Bid)).prod (volume : Measure unitInterval))))) :=
  retained_original_rows_relabel _ _ _ _ e

def namedPatternCountInterim {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) (F G : Measure ℝ) (b : P.Bid) (j : Fin 3) : ℝ :=
  ∫ rows : ActiveCountRows N,
    pairCountMass (namedPhysicalAllocationLaw P.xi P.z P.L P.U c kind e b rows) (e 0) j
      ∂(Measure.pi (fun _ : Fin N => F)).prod (Measure.pi (fun _ : Fin N => G))

lemma ae_namedPhysicalAllocationLaw_count {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) (F G : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hF : ∀ t,∀ᵐ x ∂F,x ≠ t) (hG : ∀ t,∀ᵐ x ∂G,x ≠ t)
    (hbox : ∀ᵐ x ∂G,x ∈ Icc P.L P.U) (b : P.Bid) (j : Fin 3) :
    ∀ᵐ rows : ActiveCountRows N ∂
      (Measure.pi (fun _ : Fin N => F)).prod (Measure.pi (fun _ : Fin N => G)),
      pairCountMass (namedPhysicalAllocationLaw P.xi P.z P.L P.U c kind e b rows) (e 0) j =
        activePhysicalPatternCountMass P.xi P.z P.L P.U c kind b rows j := by
  have hrows : ∀ᵐ r : ActiveCountRows N ∂
      (Measure.pi (fun _ : Fin N => F)).prod (Measure.pi (fun _ : Fin N => G)),
      ∀ k,r.2 k ∈ Icc P.L P.U :=
    (measurePreserving_snd (μ:=Measure.pi (fun _ : Fin N => F))
      (ν:=Measure.pi (fun _ : Fin N => G))).quasiMeasurePreserving.ae
        (Finishing01Menus.ae_iid_box G hbox)
  have hcopy := ae_two_rows_ties_same_copy F G id id measurable_id measurable_id
    hF hG P.kappa_pos (P.bid_pos b).ne' 0 kind
  filter_upwards [hrows,hcopy] with rows hrows hcopy
  exact namedPhysicalAllocationLaw_count P.xi_pos P.xi_lt_one P.L_pos P.z c kind e
    b rows b.property hrows hcopy j

lemma namedPatternCountInterim_eq {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) (F G : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hF : ∀ t,∀ᵐ x ∂F,x ≠ t) (hG : ∀ t,∀ᵐ x ∂G,x ≠ t)
    (hbox : ∀ᵐ x ∂G,x ∈ Icc P.L P.U) (b : P.Bid) (j : Fin 3) :
    P.namedPatternCountInterim c kind e F G b j = P.patternCountInterim c kind F G b j := by
  exact integral_congr_ae (P.ae_namedPhysicalAllocationLaw_count c kind e F G hF hG hbox b j)

lemma integrable_named_physical_count {N : ℕ} (c : ℕ) (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) (F G : Measure ℝ)
    [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hF : ∀ t,∀ᵐ x ∂F,x ≠ t) (hG : ∀ t,∀ᵐ x ∂G,x ≠ t)
    (hbox : ∀ᵐ x ∂G,x ∈ Icc P.L P.U) (b : P.Bid) (j : Fin 3) :
    Integrable (fun rows : ActiveCountRows N =>
      pairCountMass (namedPhysicalAllocationLaw P.xi P.z P.L P.U c kind e b rows) (e 0) j)
      ((Measure.pi (fun _ : Fin N => F)).prod (Measure.pi (fun _ : Fin N => G))) :=
  (P.integrable_physical_count c kind F G hbox b j).congr
    (Filter.EventuallyEq.symm (P.ae_namedPhysicalAllocationLaw_count c kind e F G hF hG hbox b j))

def namedOriginalCountInterim (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    (i : Fin (N+1)) (b : P.Bid) (j : Fin 3) : ℝ :=
  (CommonList.iid P.categories N).expect (fun kind =>
    P.namedPatternCountInterim c kind (Equiv.swap 0 i)
      (Finishing01Menus.lowReal P low) (P.realBaseLaw mu pi) b j)

lemma real_low_no_atoms (low : ProbabilityMeasure P.Low)
    [NullSingletonClass (low : Measure P.Low)] (t : ℝ) :
    ∀ᵐ x ∂Finishing01Menus.lowReal P low,x ≠ t := by
  unfold Finishing01Menus.lowReal
  apply (ae_map_iff measurable_subtype_coe.aemeasurable (measurableSet_singleton t).compl).mpr
  exact ae_subtype_val_ne (low : Measure P.Low) t

lemma real_base_no_atoms (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu)
    [NullSingletonClass (pi.1.map measurable_snd.aemeasurable : Measure P.Bid)] (t : ℝ) :
    ∀ᵐ x ∂P.realBaseLaw mu pi,x ≠ t := by
  unfold realBaseLaw
  apply (ae_map_iff measurable_subtype_coe.aemeasurable (measurableSet_singleton t).compl).mpr
  exact ae_subtype_val_ne (pi.1.map measurable_snd.aemeasurable : Measure P.Bid) t

lemma namedOriginalCountInterim_eq (N c : ℕ) (low : ProbabilityMeasure P.Low)
    [NullSingletonClass (low : Measure P.Low)]
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    [NullSingletonClass (pi.1.map measurable_snd.aemeasurable : Measure P.Bid)]
    (i : Fin (N+1)) (b : P.Bid) (j : Fin 3) :
    P.namedOriginalCountInterim N c low mu pi i b j =
      P.originalCountInterim (N+1) c low mu pi b j := by
  unfold namedOriginalCountInterim originalCountInterim actualCountInterim
  apply FiniteLaw.expect_congr
  intro kind
  exact P.namedPatternCountInterim_eq c kind (Equiv.swap 0 i)
    (Finishing01Menus.lowReal P low) (P.realBaseLaw mu pi)
    (P.real_low_no_atoms low) (P.real_base_no_atoms mu pi) (P.realBaseLaw_box mu pi) b j

def namedConditionalCountMass (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    (sigma : Kernel P.Value P.Bid) (i : Fin (N+1)) (v : P.Value) (j : Fin 3) : ℝ :=
  ∫ b : P.Bid,P.namedOriginalCountInterim N c low mu pi i b j ∂sigma v

lemma namedConditionalCountMass_eq (N c : ℕ) (low : ProbabilityMeasure P.Low)
    [NullSingletonClass (low : Measure P.Low)]
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu)
    [NullSingletonClass (pi.1.map measurable_snd.aemeasurable : Measure P.Bid)]
    (sigma : Kernel P.Value P.Bid) (i : Fin (N+1)) (v : P.Value) (j : Fin 3) :
    P.namedConditionalCountMass N c low mu pi sigma i v j =
      P.conditionalCountMass (N+1) c low mu pi sigma v j := by
  unfold namedConditionalCountMass conditionalCountMass
  simp only [P.namedOriginalCountInterim_eq N c low mu pi i]

def AllNamedConditionalCountLimit (c : ℕ → ℕ) (low : ℕ → ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : ℕ → Law (A:=P.Bid) mu)
    (lam : ℝ) : Prop :=
  ∀ sigma : ℕ → Kernel P.Value P.Bid,
    (∀ M,IsMarkovKernel (sigma M)) →
    (∀ M,mu ⊗ₘ sigma M = ((pi M).1 : Measure (P.Value×P.Bid))) →
    ∀ᵐ v ∂mu,∀ i : (N : ℕ) → Fin (N+1),∀ j : Fin 3,
      Tendsto (fun N => P.namedConditionalCountMass N (c (N+1)) (low (N+1))
        mu (pi (N+1)) (sigma (N+1)) (i N) v j) atTop
        (𝓝 (limitingCountMass P.z (P.qResponse v lam) j))

theorem all_named_original_conditional_counts (c : ℕ → ℕ)
    (hc : Tendsto (fun M => (c M : ℝ)/(M : ℝ)) atTop (𝓝 P.rho))
    (low : ℕ → ProbabilityMeasure P.Low) (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : ℕ → Law (A:=P.Bid) mu) (hIC : P.EventualActualIC c low mu pi)
    (hLow : ∀ᶠ M in atTop,NullSingletonClass (low M : Measure P.Low))
    (hBid : ∀ᶠ M in atTop,
      NullSingletonClass ((pi M).1.map measurable_snd.aemeasurable : Measure P.Bid))
    (lam : P.Price) (hprice : Tendsto (fun M => P.price mu (pi M)) atTop (𝓝 (lam:ℝ))) :
    P.AllNamedConditionalCountLimit c low mu pi lam := by
  intro sigma hmark hdis
  have h := P.original_conditional_counts c hc low mu pi hIC lam hprice sigma hmark hdis
  filter_upwards [h] with v hv i j
  have hshift := (hv j).comp (tendsto_add_atTop_nat 1)
  apply hshift.congr'
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hLow,
    (tendsto_add_atTop_nat 1).eventually hBid] with N hlow hbid
  letI : NullSingletonClass (low (N+1) : Measure P.Low) := hlow
  letI : NullSingletonClass ((pi (N+1)).1.map measurable_snd.aemeasurable : Measure P.Bid) := hbid
  exact (P.namedConditionalCountMass_eq N (c (N+1)) (low (N+1)) mu (pi (N+1))
    (sigma (N+1)) (i N) v j).symm

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
