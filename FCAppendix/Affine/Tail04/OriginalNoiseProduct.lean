import FCAppendix.Affine.Tail04.CompactSourceBidLaws
import FCAppendix.Existence.R01PayOnceRowIntegration
import FCAppendix.Affine.Hybrid.FavoredNoisyPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalNoiseProduct
open MeasureTheory ProbabilityTheory Set Classical
open CompactSourceBidLaws Existence.Distributional

section Products
variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

def shuffle (p : (A×B)×(C×D)) : (A×C)×(B×D) :=
  ((p.1.1,p.2.1),(p.1.2,p.2.2))

include B C D in
lemma measurable_shuffle : Measurable (shuffle (A:=A) (B:=B) (C:=C) (D:=D)) :=
  (measurable_fst.fst.prodMk measurable_snd.fst).prodMk
    (measurable_fst.snd.prodMk measurable_snd.snd)

theorem shuffle_preserves (μA : Measure A) (μB : Measure B) (μC : Measure C) (μD : Measure D)
    [IsProbabilityMeasure μA] [IsProbabilityMeasure μB]
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μD] :
    MeasurePreserving shuffle ((μA.prod μB).prod (μC.prod μD))
      ((μA.prod μC).prod (μB.prod μD)) := by
  have inner := (measurePreserving_prodAssoc μC μB μD).comp
    (((Measure.measurePreserving_swap (μ:=μB) (ν:=μC)).prod (MeasurePreserving.id μD)).comp
      (measurePreserving_prodAssoc μB μC μD).symm)
  have all := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm.comp
    (((MeasurePreserving.id μA).prod inner).comp
      (measurePreserving_prodAssoc μA μB (μC.prod μD)))
  exact all

end Products

section Rows
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def zipRow (N : ℕ) (p : (Fin N → X)×(Fin N → Y)) : Fin N → X×Y :=
  fun j => (p.1 j,p.2 j)

include Y in
lemma measurable_zipRow (N : ℕ) : Measurable (zipRow (X:=X) (Y:=Y) N) :=
  measurable_pi_lambda _ (fun j =>
    ((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd))

theorem zipRow_preserves (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (N : ℕ) :
    MeasurePreserving (zipRow N)
      ((Measure.pi (fun _ : Fin N => μ)).prod (Measure.pi (fun _ : Fin N => ν)))
      (Measure.pi (fun _ : Fin N => μ.prod ν)) := by
  induction N with
  | zero =>
      refine ⟨measurable_zipRow 0,?_⟩
      symm
      apply Measure.pi_eq
      intro s hs
      rw [Measure.map_apply (measurable_zipRow 0) (MeasurableSet.univ_pi hs)]
      have he : zipRow 0 ⁻¹' (univ.pi s) = univ := by
        ext p
        simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, iff_true]
        intro i
        exact Fin.elim0 i
      rw [he,measure_univ]
      simp
  | succ N ih =>
      have hx := measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) 0
      have hy := measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => ν) 0
      have hz := (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ.prod ν) 0).symm
      have hp := hz.comp (((MeasurePreserving.id (μ.prod ν)).prod ih).comp
        ((shuffle_preserves μ (Measure.pi (fun _ : Fin N => μ))
          ν (Measure.pi (fun _ : Fin N => ν))).comp (hx.prod hy)))
      convert! hp using 1
      funext p j
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · simp [zipRow,shuffle,MeasurableEquiv.piFinSuccAbove,Fin.tail]

end Rows

def physicalRow {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps) (N : ℕ)
    (p : (Fin N → Icc L U)×(Fin N → unitInterval)) : Fin N → Icc L (U*(1+eps)) :=
  fun j => noisyBid hL heps (p.1 j,p.2 j)

lemma measurable_physicalRow {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps) (N : ℕ) :
    Measurable (physicalRow (U:=U) hL heps N) :=
  measurable_pi_lambda _ (fun j => (continuous_noisyBid hL heps).measurable.comp
    (((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)))

theorem physicalRow_law {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps)
    (N : ℕ) (μ : ProbabilityMeasure (Icc L U)) :
    ((Measure.pi (fun _ : Fin N => (μ : Measure (Icc L U)))).prod
      (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)))).map
      (physicalRow hL heps N)=
      Measure.pi (fun _ : Fin N => (noisyBidLaw hL heps μ : Measure (Icc L (U*(1+eps))))) := by
  let f : (Fin N → Icc L U×unitInterval) → Fin N → Icc L (U*(1+eps)) :=
    fun row j => noisyBid hL heps (row j)
  have hf : Measurable f := measurable_pi_lambda _ (fun j =>
    (continuous_noisyBid hL heps).measurable.comp (measurable_pi_apply j))
  calc
    _ = (((Measure.pi (fun _ : Fin N => (μ : Measure (Icc L U)))).prod
        (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)))).map (zipRow N)).map f :=
      (Measure.map_map hf (measurable_zipRow N)).symm
    _ = _ := by
      rw [(zipRow_preserves (μ : Measure (Icc L U)) (volume : Measure unitInterval) N).map_eq,
        Measure.pi_map_pi (fun _ => (continuous_noisyBid hL heps).measurable.aemeasurable)]
      rfl

theorem physicalRow_preserves {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps)
    (N : ℕ) (μ : ProbabilityMeasure (Icc L U)) :
    MeasurePreserving (physicalRow hL heps N)
      ((Measure.pi (fun _ : Fin N => (μ : Measure (Icc L U)))).prod
        (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))))
      (Measure.pi (fun _ : Fin N => (noisyBidLaw hL heps μ : Measure (Icc L (U*(1+eps)))))) :=
  ⟨measurable_physicalRow hL heps N,physicalRow_law hL heps N μ⟩

def splitFocalNoise {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps) (N : ℕ)
    (p : (Fin N → Icc L U)×(Fin (N+1) → unitInterval)) :
      unitInterval×(Fin N → Icc L (U*(1+eps))) :=
  (p.2 0,physicalRow hL heps N (p.1,fun j => p.2 j.succ))

theorem splitFocalNoise_preserves {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps)
    (N : ℕ) (μ : ProbabilityMeasure (Icc L U)) :
    MeasurePreserving (splitFocalNoise hL heps N)
      ((Measure.pi (fun _ : Fin N => (μ : Measure (Icc L U)))).prod
        (Measure.pi (fun _ : Fin (N+1) => (volume : Measure unitInterval))))
      ((volume : Measure unitInterval).prod
        (Measure.pi (fun _ : Fin N => (noisyBidLaw hL heps μ : Measure (Icc L (U*(1+eps))))))) := by
  let M := Measure.pi (fun _ : Fin N => (μ : Measure (Icc L U)))
  let Z := Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))
  have hs := (MeasurePreserving.id M).prod
    (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => (volume : Measure unitInterval)) 0)
  have hr := (measurePreserving_prodAssoc (volume : Measure unitInterval) M Z).comp
    (((Measure.measurePreserving_swap (μ:=M) (ν:=(volume : Measure unitInterval))).prod
      (MeasurePreserving.id Z)).comp (measurePreserving_prodAssoc M volume Z).symm)
  have hp := ((MeasurePreserving.id (volume : Measure unitInterval)).prod
    (physicalRow_preserves hL heps N μ)).comp (hr.comp hs)
  convert! hp using 1

theorem physical_cons_eq {L U eps : ℝ} (hL : 0< L) (heps : 0≤ eps) (N : ℕ)
    (b : Icc L U) (p : (Fin N → Icc L U)×(Fin (N+1) → unitInterval)) :
    physicalRow hL heps (N+1) (Fin.cons b p.1,p.2)=
      Fin.cons (noisyBid hL heps (b,(splitFocalNoise hL heps N p).1))
        (splitFocalNoise hL heps N p).2 := by
  funext j
  refine Fin.cases rfl (fun k => ?_) j
  rfl

theorem ae_noisyBidLaw_ne {L U eps : ℝ} (hL : 0< L) (heps : 0< eps)
    (μ : ProbabilityMeasure (Icc L U)) (target : ℝ) :
    ∀ᵐ (y : Icc L (U*(1+eps))) ∂(noisyBidLaw hL heps.le μ : Measure (Icc L (U*(1+eps)))), (y:ℝ)≠target := by
  change ∀ᵐ (y : Icc L (U*(1+eps))) ∂(((μ : Measure (Icc L U)).prod (volume : Measure unitInterval)).map
    (noisyBid hL heps.le)), (y:ℝ)≠target
  apply (ae_map_iff (continuous_noisyBid hL heps.le).measurable.aemeasurable
    (measurableSet_eq_fun measurable_subtype_coe measurable_const).compl).mpr
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_eq_fun measurable_subtype_coe measurable_const).compl.preimage
      (continuous_noisyBid hL heps.le).measurable)).mpr
  exact Filter.Eventually.of_forall (fun b =>
    Hybrid.ae_activeNoisyRealBid_ne eps b target heps.ne' (hL.trans_le b.2.1).ne')

theorem noisyBidLaw_singleton {L U eps : ℝ} (hL : 0< L) (heps : 0< eps)
    (μ : ProbabilityMeasure (Icc L U)) (y : Icc L (U*(1+eps))) :
    (noisyBidLaw hL heps.le μ : Measure (Icc L (U*(1+eps)))) {y}=0 := by
  have h := ae_noisyBidLaw_ne hL heps μ (y:ℝ)
  have hh : ∀ᵐ (z : Icc L (U*(1+eps))) ∂(noisyBidLaw hL heps.le μ : Measure (Icc L (U*(1+eps)))), z≠y :=
    h.mono (fun z hz hzy => hz (congrArg Subtype.val hzy))
  exact measure_eq_zero_iff_ae_notMem.mpr (hh.mono (fun z hz => by simpa using hz))

theorem noisyBidLaw_nullSingletonClass {L U eps : ℝ} (hL : 0< L) (heps : 0< eps)
    (μ : ProbabilityMeasure (Icc L U)) :
    NullSingletonClass (noisyBidLaw hL heps.le μ : Measure (Icc L (U*(1+eps)))) :=
  ⟨noisyBidLaw_singleton hL heps μ⟩

theorem ae_physicalRow_ne_fixed {L U eps : ℝ} (hL : 0< L) (heps : 0< eps)
    (N : ℕ) (μ : ProbabilityMeasure (Icc L U)) (target : ℝ) :
    ∀ᵐ (b : Fin N → Icc L (U*(1+eps))) ∂Measure.pi (fun _ : Fin N =>
      (noisyBidLaw hL heps.le μ : Measure (Icc L (U*(1+eps))))), ∀ j, (b j:ℝ)≠target :=
  ae_all_iff.mpr (fun j => (measurePreserving_eval
    (fun _ : Fin N => (noisyBidLaw hL heps.le μ : Measure (Icc L (U*(1+eps))))) j).quasiMeasurePreserving.ae
      (ae_noisyBidLaw_ne hL heps μ target))

theorem ae_physicalRow_distinct {L U eps : ℝ} (hL : 0< L) (heps : 0< eps)
    (N : ℕ) (μ : ProbabilityMeasure (Icc L U)) :
    ∀ᵐ (b : Fin N → Icc L (U*(1+eps))) ∂Measure.pi (fun _ : Fin N =>
      (noisyBidLaw hL heps.le μ : Measure (Icc L (U*(1+eps))))), ∀ i j, i≠j → (b i:ℝ)≠(b j:ℝ) := by
  let ν : Measure (Icc L (U*(1+eps))) := (noisyBidLaw hL heps.le μ : Measure (Icc L (U*(1+eps))))
  letI : IsProbabilityMeasure ν := inferInstance
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i=j
  · subst j
    exact Filter.Eventually.of_forall (fun _ h => (h rfl).elim)
  · have hdiag : ∀ᵐ (p : Icc L (U*(1+eps)) × Icc L (U*(1+eps))) ∂ν.prod ν, (p.1:ℝ)≠(p.2:ℝ) := by
      apply (Measure.ae_prod_iff_ae_ae
        (measurableSet_eq_fun measurable_fst.subtype_val measurable_snd.subtype_val).compl).mpr
      exact Filter.Eventually.of_forall (fun x =>
        (ae_noisyBidLaw_ne hL heps μ (x:ℝ)).mono (fun y hy => hy.symm))
    have hind := (iIndepFun_pi (μ:=fun _ : Fin N => ν)
      (X:=fun _ => id) (fun _ => measurable_id.aemeasurable)).indepFun hij
    have hmap := hind.map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    rw [(measurePreserving_eval (fun _ : Fin N => ν) i).map_eq,
      (measurePreserving_eval (fun _ : Fin N => ν) j).map_eq] at hmap
    have hp : MeasurePreserving (fun b : Fin N → Icc L (U*(1+eps)) => (b i,b j))
        (Measure.pi (fun _ : Fin N => ν)) (ν.prod ν) :=
      ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),hmap⟩
    exact (hp.quasiMeasurePreserving.ae hdiag).mono (fun b hb _ => hb)

theorem ae_cons_physicalRow_distinct {L U eps : ℝ} (hL : 0< L) (heps : 0< eps)
    (N : ℕ) (μ : ProbabilityMeasure (Icc L U)) (target : ℝ) :
    ∀ᵐ (b : Fin N → Icc L (U*(1+eps))) ∂Measure.pi (fun _ : Fin N =>
      (noisyBidLaw hL heps.le μ : Measure (Icc L (U*(1+eps))))),
      ∀ i j : Fin (N+1), i≠j →
        (Fin.cons target (fun k => (b k:ℝ)) : Fin (N+1) → ℝ) i ≠
          (Fin.cons target (fun k => (b k:ℝ)) : Fin (N+1) → ℝ) j := by
  filter_upwards [ae_physicalRow_ne_fixed hL heps N μ target,
    ae_physicalRow_distinct hL heps N μ] with b hb hd
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hij
      exact (hij rfl).elim
    · intro _
      simpa only [Fin.cons_zero,Fin.cons_succ] using (hb j).symm
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro _
      simpa only [Fin.cons_zero,Fin.cons_succ] using hb i
    · intro hij
      simpa only [Fin.cons_succ] using hd i j (fun h => hij (congrArg Fin.succ h))

end FCAppendix.Affine.Tail04.OriginalNoiseProduct
