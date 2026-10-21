import FCAppendix.Affine.Tail04.PartialNativePublicWeight
import FCAppendix.Affine.Tail04.OriginalNoiseProduct

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialNativeGuardIntegration
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid NativeLocalPolicy NativePartialReports NativeObservationPair NativeMenuReports
open PartialNativeCoordinates PartialNativeEvents PartialNativeCategoryBounds
open PartialNativeSeed PartialNativePublicWeight OriginalFiniteFibers
open scoped BigOperators ENNReal

section FiniteMeasure
variable {X K : Type*} [MeasurableSpace X] [Fintype K]

lemma real_finite_mixture (μ : Measure X) (w : K→ℝ≥0∞) (ν : K→ Measure X)
    [∀ k,IsFiniteMeasure (ν k)] (hw : ∀ k,w k≠⊤)
    (he : μ=∑ k,w k • ν k) (B : Set X) :
    μ.real B=∑ k,(w k).toReal*(ν k).real B := by
  rw [measureReal_def,he,measure_sum_apply]
  simp only [Measure.smul_apply,smul_eq_mul]
  rw [ENNReal.toReal_sum (fun k _ => ENNReal.mul_ne_top (hw k) (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul,measureReal_def]

end FiniteMeasure

section Sections
variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  (ν : Measure Z) [IsProbabilityMeasure ν] (B : Set (X×Z)) (hB : MeasurableSet B)

def sectionMass (x : X) : ℝ := ν.real {z | (x,z)∈B}

omit [IsProbabilityMeasure ν] in
include hB in
lemma sectionMass_eq_integral (x : X) :
    sectionMass ν B x=∫ z : Z,if (x,z)∈B then (1:ℝ) else 0 ∂ν := by
  symm
  simpa only [sectionMass,Set.indicator,Pi.one_apply,mem_preimage,id_eq] using!
    integral_indicator_one (μ:=ν) (hB.preimage (measurable_const.prodMk measurable_id))

include hB in
lemma measurable_sectionMass : Measurable (sectionMass ν B) := by
  have hf : Measurable (fun z : X×Z => if z∈B then (1:ℝ) else 0) :=
    Measurable.ite hB measurable_const measurable_const
  have hi : Measurable (fun x : X => ∫ z : Z,if (x,z)∈B then (1:ℝ) else 0 ∂ν) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  simpa only [←sectionMass_eq_integral ν B hB] using hi

omit [MeasurableSpace X] in
lemma sectionMass_bounds (x : X) : sectionMass ν B x∈Icc (0:ℝ) 1 :=
  ⟨measureReal_nonneg,(measureReal_mono (subset_univ _)).trans_eq (by simp [measureReal_def])⟩

include hB in
lemma integrable_sectionMass (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable (sectionMass ν B) μ :=
  Integrable.of_bound (measurable_sectionMass ν B hB).aestronglyMeasurable 1
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sectionMass_bounds ν B x).1]
      exact (sectionMass_bounds ν B x).2)

include hB in
lemma product_real_eq_integral (μ : Measure X) [IsFiniteMeasure μ] :
    (μ.prod ν).real B=∫ x,sectionMass ν B x ∂μ := by
  have hi : Integrable (fun z : X×Z => if z∈B then (1:ℝ) else 0) (μ.prod ν) :=
    Integrable.of_bound (Measurable.ite hB measurable_const measurable_const).aestronglyMeasurable
      1 (ae_of_all _ fun z => by split_ifs <;> norm_num)
  rw [show (μ.prod ν).real B=∫ z : X×Z,if z∈B then (1:ℝ) else 0 ∂μ.prod ν by
    symm;simpa only [Set.indicator,Pi.one_apply] using integral_indicator_one (μ:=μ.prod ν) hB,
    integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => (sectionMass_eq_integral ν B hB x).symm

end Sections

section Native
variable {N c : ℕ} (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed)
  (D : Data (N+1) c) (Q : PublicScenario.Data)
  (hpublic : ∀ n z,D.publicChoice n z=
    PublicScenario.localChoice D.E Q (NativeFlag.nativeLowBidLaw Γ D.E) n z)
  (hcat : ∀ k : Fin 4,(userLaw Γ) (D.E.coarseTag ⁻¹' {k})≠0)
  (hlow : ∀ b,NativeFlag.nativeLowBidLaw Γ D.E {b}=0)
  (hmenu : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ,MenuAction D.E x.2)

def deletedTag (z : DeletedBackground N NativeLocalPolicy.Seed) : Fin N→ Fin 4 :=
  fun r => D.E.coarseTag (z.1 r)

lemma measurable_deletedTag : Measurable (deletedTag D) :=
  measurable_pi_lambda _ fun r => D.E.measurable_coarseTag.comp
    ((measurable_pi_apply r).comp measurable_fst)

lemma deletedTag_preimage (kind : Fin N→ Fin 4) :
    deletedTag D ⁻¹' {kind}=categoryFiber D.E.coarseTag kind×ˢuniv := by
  ext z
  simp only [mem_preimage,mem_singleton_iff,mem_prod,mem_univ,and_true,
    categoryFiber,mem_univ_pi]
  exact ⟨fun h r => congrFun h r,fun h => funext h⟩

lemma deleted_fiber_sum :
    deletedBackgroundLaw Γ=∑ kind : Fin N→ Fin 4,
      (deletedBackgroundLaw Γ) (deletedTag D ⁻¹' {kind}) • fiber Γ D kind := by
  calc
    deletedBackgroundLaw Γ = ∑ kind : Fin N→ Fin 4,
        (deletedBackgroundLaw Γ) (deletedTag D ⁻¹' {kind}) •
          cond (deletedBackgroundLaw Γ) (deletedTag D ⁻¹' {kind}) :=
      finite_disintegration (deletedBackgroundLaw Γ) (deletedTag D) (measurable_deletedTag D)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro kind _
      rw [deletedTag_preimage]
      rfl

lemma deleted_noLow (i : Fin (N+1)) (z : DeletedBackground N NativeLocalPolicy.Seed) :
    restoreBackground i z∈noLow D.E i ↔ ∀ r,deletedTag D z r≠0 := by
  simp only [noLow,rivalKinds,restoreBackground_rival,deletedTag,mem_setOf_eq]

lemma guard_off_noLow_deleted (i : Fin (N+1)) (side : Fin 2) :
    (backgroundLaw Γ).real (guardEvent D i side\noLow D.E i)=
      (deletedBackgroundLaw Γ).real
        (restoreBackground i ⁻¹' (guardEvent D i side\noLow D.E i)) := by
  apply native_event_deleted Γ i _
    ((measurableSet_guardEvent D i side).diff (measurableSet_noLow D.E i))
  intro ω
  have hp := present_restore_delete i ω D.E.R side
  have hn : rivalKinds D.E i (restoreBackground i (deleteBackground i ω))=rivalKinds D.E i ω := by
    funext r
    simp only [rivalKinds,restoreBackground_rival,deleteBackground,NativeFlag.deletedUsers]
  simp only [guardEvent,mem_sdiff,mem_setOf_eq,hp,noLow,hn]

include hpublic hcat hlow hmenu in
theorem native_guard_off_noLow_le
    (i : Fin (N+1)) (side : Fin 2)
    (bad : Bool→ Set ((Fin N→ UserDraw 2)×(Fin N→ unitInterval)))
    (hbad : ∀ reg,MeasurableSet (bad reg))
    (hpoint : ∀ kind r,(∀ j,D.E.coarseTag (r j)=kind j) →
      (∀ j,MenuAction D.E (r j).1.2) →
      (volume : Measure unitInterval).real {z | fiberWeight D Q i kind side (r,z)≠1}≤
        (1-Q.θ)*(Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))).real
          {z | (r,z)∈bad false}+
        Q.θ*(Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))).real
          {z | (r,z)∈bad true}) :
    (backgroundLaw Γ).real (guardEvent D i side\noLow D.E i)≤
      (1-Q.θ)*((Measure.pi (fun _ : Fin N => userLaw Γ)).prod
        (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)))).real (bad false)+
      Q.θ*((Measure.pi (fun _ : Fin N => userLaw Γ)).prod
        (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)))).real (bad true) := by
  let μ := deletedBackgroundLaw Γ
  let Z := Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))
  let w : (Fin N→ Fin 4)→ℝ≥0∞ := fun kind => μ (deletedTag D ⁻¹' {kind})
  let Ebad := restoreBackground i ⁻¹' (guardEvent D i side\noLow D.E i)
  let B : Bool→ Set (DeletedBackground N NativeLocalPolicy.Seed×(Fin N→ unitInterval)) :=
    fun reg => {z | (z.1.1,z.2)∈bad reg}
  have hB (reg : Bool) : MeasurableSet (B reg) :=
    (hbad reg).preimage (measurable_fst.fst.prodMk measurable_snd)
  haveI : IsProbabilityMeasure μ := by dsimp [μ];infer_instance
  haveI : IsProbabilityMeasure Z := by dsimp [Z];infer_instance
  haveI (kind : Fin N→ Fin 4) : IsProbabilityMeasure (fiber Γ D kind) :=
    fiber_isProbabilityMeasure Γ D hcat kind
  have hw (kind : Fin N→ Fin 4) : w kind≠⊤ := measure_ne_top _ _
  have hμ : μ=∑ kind,w kind • fiber Γ D kind := deleted_fiber_sum Γ D
  have hbound (kind : Fin N→ Fin 4) :
      (fiber Γ D kind).real Ebad≤
        (1-Q.θ)*((fiber Γ D kind).prod Z).real (B false)+
          Q.θ*((fiber Γ D kind).prod Z).real (B true) := by
    by_cases hnone : ∀ r,kind r≠0
    · have hzero : (fiber Γ D kind) Ebad=0 := by
        have ha : ∀ᵐ z ∂fiber Γ D kind,z∉Ebad := by
          filter_upwards [fiber_shape Γ D kind] with z hz
          intro hm
          exact hm.2 ((deleted_noLow D i z).mpr (fun r => by simpa only [deletedTag,hz r] using hnone r))
        simpa only [mem_setOf_eq,not_not,setOf_mem_eq] using (ae_iff.mp ha)
      rw [measureReal_def,hzero,ENNReal.toReal_zero]
      have ht0 := Q.θ_nonneg
      have ht1 := Q.θ_le_one
      positivity
    · have hpos : 0< Fintype.card {r : Fin N // kind r=0} := by
        apply Fintype.card_pos_iff.mpr
        obtain ⟨r,hr⟩ := not_forall.mp hnone
        exact ⟨⟨r,not_not.mp hr⟩⟩
      obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      let e : Fin (n+1)≃{r : Fin N // kind r=0} :=
        (Fintype.equivFinOfCardEq hn).symm
      let F : Set (DeletedBackground N NativeLocalPolicy.Seed×unitInterval) :=
        {z | fiberWeight D Q i kind side (z.1.1,z.2)≠1}
      have hF : MeasurableSet F :=
        ((measurableSet_eq_fun (measurable_fiberWeight D Q i kind side) measurable_const).compl).preimage
          (measurable_fst.fst.prodMk measurable_snd)
      have hactual := native_fiber_guard_replacement Γ D Q hpublic hcat hlow hmenu i kind n e side
      have hle : (fiber Γ D kind).real Ebad≤((fiber Γ D kind).prod volume).real F := by
        exact (measureReal_mono (preimage_mono sdiff_subset)).trans_eq hactual
      apply hle.trans
      rw [product_real_eq_integral volume F hF,
        product_real_eq_integral Z (B false) (hB false),
        product_real_eq_integral Z (B true) (hB true)]
      rw [←integral_const_mul,←integral_const_mul,←integral_add
        ((integrable_sectionMass Z (B false) (hB false) _).const_mul _)
        ((integrable_sectionMass Z (B true) (hB true) _).const_mul _)]
      apply integral_mono_ae (integrable_sectionMass volume F hF _)
        (((integrable_sectionMass Z (B false) (hB false) _).const_mul _).add
          ((integrable_sectionMass Z (B true) (hB true) _).const_mul _))
      filter_upwards [fiber_shape Γ D kind,fiber_menu Γ D hmenu kind] with z hz hmz
      exact hpoint kind z.1 hz hmz
  have hp (reg : Bool) : (μ.prod Z).real (B reg)=
      ∑ kind,(w kind).toReal*((fiber Γ D kind).prod Z).real (B reg) := by
    apply real_finite_mixture (μ.prod Z) w (fun kind => (fiber Γ D kind).prod Z) hw
    rw [hμ,prod_finsetSum]
    simp only [Measure.prod_smul_left]
  have hs := Finset.sum_le_sum (fun kind (_ : kind∈(Finset.univ : Finset (Fin N→ Fin 4))) =>
    mul_le_mul_of_nonneg_left (hbound kind) (ENNReal.toReal_nonneg (a:=w kind)))
  calc
    (backgroundLaw Γ).real (guardEvent D i side\noLow D.E i) =
        ∑ kind,(w kind).toReal*(fiber Γ D kind).real Ebad :=
      (guard_off_noLow_deleted Γ D i side).trans
        (real_finite_mixture μ w (fiber Γ D) hw hμ Ebad)
    _≤∑ kind,(w kind).toReal*((1-Q.θ)*((fiber Γ D kind).prod Z).real (B false)+
        Q.θ*((fiber Γ D kind).prod Z).real (B true)) := hs
    _=(1-Q.θ)*(μ.prod Z).real (B false)+Q.θ*(μ.prod Z).real (B true) := by
      rw [hp false,hp true,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro kind _
      ring
    _=_ := by
      have hmap : MeasurePreserving
          (fun z : DeletedBackground N NativeLocalPolicy.Seed×(Fin N→ unitInterval) => (z.1.1,z.2))
          (μ.prod Z) ((Measure.pi (fun _ : Fin N => userLaw Γ)).prod Z) :=
        measurePreserving_fst.prod (MeasurePreserving.id Z)
      have he (reg : Bool) : (μ.prod Z).real (B reg)=
          ((Measure.pi (fun _ : Fin N => userLaw Γ)).prod Z).real (bad reg) := by
        change (μ.prod Z).real (_ ⁻¹' bad reg)=_
        rw [measureReal_def,←Measure.map_apply hmap.measurable (hbad reg),hmap.map_eq]
        rfl
      rw [he false,he true]

include Q hpublic hcat hlow hmenu in
theorem badMass_refined_union_bound (i : Fin (N+1)) :
    NativePartialDeviation.badMass D Γ i≤
      (backgroundLaw Γ).real (tieEvent D i 0)+(backgroundLaw Γ).real (tieEvent D i 1)+
      (backgroundLaw Γ).real (guardEvent D i 0\noLow D.E i)+
      (backgroundLaw Γ).real (guardEvent D i 1\noLow D.E i)+
      (backgroundLaw Γ).real (noLow D.E i) := by
  have hnull := endpoint_off_noLow_null Γ D Q hpublic hcat hlow hmenu i
  have havoid : ∀ᵐ ω ∂backgroundLaw Γ,ω∉endpointEvent D i\noLow D.E i := by
    apply ae_iff.mpr
    simpa only [mem_setOf_eq,not_not,setOf_mem_eq] using hnull
  have hr := original_menu_rivals Γ D.E i hmenu
  have hsub : ({ω | ¬goodBackground D i ω} : Set (Background (N+1) 2 NativeLocalPolicy.Seed))≤ᵐ[backgroundLaw Γ]
      (((((tieEvent D i 0∪tieEvent D i 1)∪(guardEvent D i 0\noLow D.E i))∪
        (guardEvent D i 1\noLow D.E i))∪noLow D.E i) :
          Set (Background (N+1) 2 NativeLocalPolicy.Seed)) := by
    filter_upwards [hr,havoid] with ω hω hav
    intro hb
    by_cases hn : ω∈noLow D.E i
    · exact Or.inr hn
    · have hh := bad_subset_at D Q (NativeFlag.nativeLowBidLaw Γ D.E) hpublic i ω hω hb
      rcases hh with (((h|h)|h)|h)|h
      · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr ⟨h,hn⟩))
      · exact Or.inl (Or.inr ⟨h,hn⟩)
      · exact (hav ⟨h,hn⟩).elim
  have hs := real_mono_ae (backgroundLaw Γ) hsub
  apply hs.trans
  calc
    _≤(backgroundLaw Γ).real (((tieEvent D i 0∪tieEvent D i 1)∪
        (guardEvent D i 0\noLow D.E i))∪(guardEvent D i 1\noLow D.E i))+
        (backgroundLaw Γ).real (noLow D.E i) := measureReal_union_le _ _
    _≤_ := by
      have h0 := measureReal_union_le (μ:=backgroundLaw Γ) (tieEvent D i 0) (tieEvent D i 1)
      have h1 := measureReal_union_le (μ:=backgroundLaw Γ) (tieEvent D i 0∪tieEvent D i 1)
        (guardEvent D i 0\noLow D.E i)
      have h2 := measureReal_union_le (μ:=backgroundLaw Γ)
        ((tieEvent D i 0∪tieEvent D i 1)∪(guardEvent D i 0\noLow D.E i))
        (guardEvent D i 1\noLow D.E i)
      linarith

end Native
end FCAppendix.Affine.Tail04.PartialNativeGuardIntegration
