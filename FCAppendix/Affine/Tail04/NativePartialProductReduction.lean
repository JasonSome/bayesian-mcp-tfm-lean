import FCAppendix.Affine.Tail04.NativePartialFiberLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePartialProductReduction
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeHighSeedProduct NativeHighExperiment NativePartialExperiment
open EqualPrivateSignal EqualPrivateUpper PrivateRowSorting

section GeneralIntegration
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma integral_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X→ℝ) (C : ℝ) (hC : ∀ x,‖f x‖≤ C) : ‖∫ x,f x ∂μ‖≤ C := by
  simpa only [probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=μ) (ae_of_all _ hC)

lemma measurable_integral (μ : Measure Y) [SFinite μ] (f : X×Y→ℝ) (hf : Measurable f) :
    Measurable (fun x => ∫ y,f (x,y) ∂μ) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_bounded (μ : Measure X) [IsFiniteMeasure μ]
    (f : X→ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ x,‖f x‖≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)

lemma integral_finite_expect {I : Type*} [Fintype I]
    (w : FiniteLaw I) (μ : Measure X) [IsFiniteMeasure μ]
    (f : I→ X→ℝ) (hf : ∀ i,Measurable (f i)) (C : ℝ) (hC : ∀ i x,‖f i x‖≤ C) :
    (∫ x,w.expect (fun i => f i x) ∂μ)=w.expect (fun i => ∫ x,f i x ∂μ) := by
  unfold FiniteLaw.expect
  rw [integral_finsetSum _ (fun i _ =>
    (integrable_bounded μ (f i) (hf i) C (hC i)).const_mul (w.mass i))]
  simp only [integral_const_mul]

lemma integral_finite_expect_two {I : Type*} [Fintype I]
    (w : FiniteLaw I) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : I→ X×Y→ℝ) (hf : ∀ i,Measurable (f i)) (C : ℝ) (hC : ∀ i x,‖f i x‖≤ C) :
    (∫ x,∫ y,w.expect (fun i => f i (x,y)) ∂ν ∂μ)=
      w.expect (fun i => ∫ x,∫ y,f i (x,y) ∂ν ∂μ) := by
  have hinner (x : X) :
      (∫ y,w.expect (fun i => f i (x,y)) ∂ν)=w.expect (fun i => ∫ y,f i (x,y) ∂ν) :=
    integral_finite_expect w ν (fun i y => f i (x,y))
      (fun i => (hf i).comp (measurable_const.prodMk measurable_id)) C
        (fun i y => hC i (x,y))
  simp_rw [hinner]
  exact integral_finite_expect w μ (fun i x => ∫ y,f i (x,y) ∂ν)
    (fun i => measurable_integral ν (f i) (hf i)) C
      (fun i x => integral_bound ν _ C (fun y => hC i (x,y)))

end GeneralIntegration

section FourFactors
variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]
  (μA : Measure A) (μB : Measure B) (μC : Measure C) (μD : Measure D)
  [IsProbabilityMeasure μA] [IsProbabilityMeasure μB]
  [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]

theorem transpose_four (f : A×(B×(C×D))→ℝ) (hf : Measurable f)
    (K : ℝ) (hK : ∀ x,‖f x‖≤ K) :
    (∫ a,∫ b,∫ c,∫ d,f (a,(b,(c,d))) ∂μD ∂μC ∂μB ∂μA)=
      ∫ b,∫ d,∫ a,∫ c,f (a,(b,(c,d))) ∂μC ∂μA ∂μD ∂μB := by
  have hs (a : A) (b : B) :
      (∫ c,∫ d,f (a,(b,(c,d))) ∂μD ∂μC)=
        ∫ d,∫ c,f (a,(b,(c,d))) ∂μC ∂μD :=
    integral_swap_bounded μC μD _
      (hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))) K
        (fun x => hK (a,(b,x)))
  simp_rw [hs]
  let q : A×(B×D)→ℝ := fun x => ∫ c,f (x.1,(x.2.1,(c,x.2.2))) ∂μC
  have hq : Measurable q := measurable_integral μC _
    (hf.comp (by fun_prop : Measurable (fun x : (A×(B×D))×C =>
      (x.1.1,(x.1.2.1,(x.2,x.1.2.2))))))
  have hqb (x) : ‖q x‖≤ K := integral_bound μC _ K (fun c => hK (x.1,(x.2.1,(c,x.2.2))))
  have hqi := integrable_bounded (μA.prod (μB.prod μD)) q hq K hqb
  have hiA (a : A) : Integrable (fun x : B×D => q (a,x)) (μB.prod μD) :=
    integrable_bounded _ _ (hq.comp (measurable_const.prodMk measurable_id)) K (fun x => hqb (a,x))
  have hiBD : Integrable (fun x : B×D => ∫ a,q (a,x) ∂μA) (μB.prod μD) :=
    integrable_bounded _ _ (measurable_integral μA _ (hq.comp measurable_swap)) K
      (fun x => integral_bound μA _ K (fun a => hqb (a,x)))
  calc
    _=∫ a,∫ x : B×D,q (a,x) ∂μB.prod μD ∂μA := by
      apply integral_congr_ae
      exact ae_of_all _ fun a => (integral_prod _ (hiA a)).symm
    _=∫ x : B×D,∫ a,q (a,x) ∂μA ∂μB.prod μD := integral_integral_swap hqi
    _=_ := integral_prod _ hiBD

end FourFactors

section Projection
variable {m c : ℕ} (K : NativeLocalPolicy.Data m c)
  (ρ : ProbabilityMeasure (Ici K.E.H ⊕ Icc K.E.R K.E.Rp))
  (H0 H1 : Fin (m+1))

def ownPayload (side : Bool) (x : RawPayload K H0 H1) :
    Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H×unitInterval := by
  cases side
  · exact (x.1.1,(x.2.1 0).1)
  · exact (x.1.2,(x.2.1 1).1)

lemma measurable_ownPayload (side : Bool) : Measurable (ownPayload K H0 H1 side) := by
  cases side
  · exact measurable_fst.fst.prodMk (((measurable_pi_apply 0).comp measurable_snd.fst).fst)
  · exact measurable_fst.snd.prodMk (((measurable_pi_apply 1).comp measurable_snd.fst).fst)

lemma ownPayload_preserves (side : Bool) : MeasurePreserving (ownPayload K H0 H1 side)
    (rawPayloadLaw K ρ H0 H1)
    ((ProbabilityMeasure.toMeasure (originalIid K.E (ownH H0 H1 side).val ρ)).prod volume) := by
  have hp := (crossPair_preserves (ProbabilityMeasure.toMeasure (originalIid K.E H0.val ρ))
    (ProbabilityMeasure.toMeasure (originalIid K.E H1.val ρ)) (volume : Measure unitInterval)
    (volume : Measure unitInterval)).comp
      ((MeasurePreserving.id ((ProbabilityMeasure.toMeasure (originalIid K.E H0.val ρ)).prod
        (ProbabilityMeasure.toMeasure (originalIid K.E H1.val ρ)))).prod highOnly_preserves)
  cases side
  · exact (measurePreserving_fst (μ:=(ProbabilityMeasure.toMeasure (originalIid K.E H0.val ρ)).prod volume)
      (ν:=(ProbabilityMeasure.toMeasure (originalIid K.E H1.val ρ)).prod volume)).comp hp
  · exact (measurePreserving_snd (μ:=(ProbabilityMeasure.toMeasure (originalIid K.E H0.val ρ)).prod volume)
      (ν:=(ProbabilityMeasure.toMeasure (originalIid K.E H1.val ρ)).prod volume)).comp hp

end Projection

section OneSide
variable {m c : ℕ} (K : NativeLocalPolicy.Data m c)
  (ρ : ProbabilityMeasure (Ici K.E.H ⊕ Icc K.E.R K.E.Rp))
  (A : ℕ) (H0 H1 G0 G1 : Fin (m+1)) (Q : PublicScenario.Data) (side low : Bool)
  (hcard : (ownH G0 G1 side).val=(ownH H0 H1 side).val+1)
  (v : ℝ) (price : Icc K.E.R K.E.Rp) (b : Fin A → Icc (1:ℝ) K.E.U) (publicSeed : unitInterval)

def insertedValue (x : RawPayload K H0 H1) : ℝ :=
  let p := ownPayload K H0 H1 side x
  value K A G0 G1 Q side low (Fin.cast hcard.symm 0) v price b
    ((Fin.cons (α:=fun _=>Ici K.E.H⊕Icc K.E.R K.E.Rp) (Sum.inr price) p.1) ∘ Fin.cast hcard) publicSeed p.2

lemma measurable_value_row_seed (j' : Fin (ownH G0 G1 side).val) : Measurable
    (fun x : Row (ownH G0 G1 side).val K.E.R K.E.Rp K.E.H×unitInterval =>
      value K A G0 G1 Q side low j' v price b x.1 publicSeed x.2) := by
  have hi := measurable_inclusion K A G0 G1 Q side low j'
  have hp : Measurable (fun x : Row (ownH G0 G1 side).val K.E.R K.E.Rp K.E.H×unitInterval =>
      (b,(x.1,(publicSeed,x.2)))) :=
    measurable_const.prodMk (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hh := hi.comp hp
  exact (measurable_const (a:=v-(price:ℝ))).mul hh

lemma measurable_insertedValue : Measurable
    (insertedValue K A H0 H1 G0 G1 Q side low hcard v price b publicSeed) := by
  have hp := measurable_ownPayload K H0 H1 side
  have hr : Measurable (fun x : RawPayload K H0 H1 =>
      (Fin.cons (α:=fun _=>Ici K.E.H⊕Icc K.E.R K.E.Rp) (Sum.inr price) (ownPayload K H0 H1 side x).1) ∘ Fin.cast hcard) := by
    apply measurable_pi_lambda
    intro k
    dsimp only [Function.comp_apply]
    generalize Fin.cast hcard k=q
    refine Fin.cases measurable_const (fun l => (measurable_pi_apply l).comp hp.fst) q
  exact (measurable_value_row_seed K A G0 G1 Q side low v price b publicSeed (Fin.cast hcard.symm 0)).comp
    (hr.prodMk hp.snd)

theorem payload_integral :
    (∫ x,insertedValue K A H0 H1 G0 G1 Q side low hcard v price b publicSeed x
      ∂rawPayloadLaw K ρ H0 H1)=
      ∫ row,∫ u : unitInterval,
        value K A G0 G1 Q side low (Fin.cast hcard.symm 0) v price b
          (Function.update row (Fin.cast hcard.symm 0) (Sum.inr price)) publicSeed u
            ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure (originalIid K.E (ownH G0 G1 side).val ρ)) := by
  let f : Row (ownH G0 G1 side).val K.E.R K.E.Rp K.E.H×unitInterval → ℝ := fun x =>
    value K A G0 G1 Q side low (Fin.cast hcard.symm 0) v price b x.1 publicSeed x.2
  have hf : Measurable f := measurable_value_row_seed K A G0 G1 Q side low v price b publicSeed (Fin.cast hcard.symm 0)
  have hb (x) : ‖f x‖≤|v|+K.E.Rp := value_bound K A G0 G1 Q side low (Fin.cast hcard.symm 0) v price b x.1 publicSeed x.2
  let ins : Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H →
      Row (ownH G0 G1 side).val K.E.R K.E.Rp K.E.H := fun row =>
    (Fin.cons (α:=fun _=>Ici K.E.H⊕Icc K.E.R K.E.Rp) (Sum.inr price) row) ∘ Fin.cast hcard
  have hins : Measurable ins := by
    apply measurable_pi_lambda
    intro k
    dsimp only [ins,Function.comp_apply]
    generalize Fin.cast hcard k=q
    refine Fin.cases measurable_const (fun l => measurable_pi_apply l) q
  let upd := fun row : Row (ownH G0 G1 side).val K.E.R K.E.Rp K.E.H =>
    Function.update row (Fin.cast hcard.symm 0) (Sum.inr price)
  have hupd : Measurable upd := measurable_update_left
  have hi := integrable_bounded ((ProbabilityMeasure.toMeasure (originalIid K.E (ownH H0 H1 side).val ρ)).prod (volume : Measure unitInterval))
    (fun x => f (ins x.1,x.2)) (hf.comp (hins.prodMap measurable_id)) (|v|+K.E.Rp)
      (fun x => hb (ins x.1,x.2))
  calc
    _=∫ x : Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H×unitInterval,
        f (ins x.1,x.2) ∂(ProbabilityMeasure.toMeasure (originalIid K.E (ownH H0 H1 side).val ρ)).prod volume :=
      (ownPayload_preserves K ρ H0 H1 side).integral_comp_ae_real hi.aestronglyMeasurable
    _=∫ row,∫ u : unitInterval,f (ins row,u) ∂(volume : Measure unitInterval) ∂(ProbabilityMeasure.toMeasure (originalIid K.E (ownH H0 H1 side).val ρ)) := integral_prod _ hi
    _=∫ u : unitInterval,∫ row,f (ins row,u) ∂(ProbabilityMeasure.toMeasure (originalIid K.E (ownH H0 H1 side).val ρ)) :=
      integral_swap_bounded (ProbabilityMeasure.toMeasure (originalIid K.E (ownH H0 H1 side).val ρ)) volume _ (hf.comp (hins.prodMap measurable_id)) _
        (fun x => hb (ins x.1,x.2))
    _=∫ u : unitInterval,∫ row,f (upd row,u) ∂(ProbabilityMeasure.toMeasure (originalIid K.E (ownH G0 G1 side).val ρ)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun u =>
        (integral_update_cast hcard (ρ : Measure _) (Sum.inr price)
          (fun row => f (row,u)) (hf.comp (measurable_id.prodMk measurable_const))
          (|v|+K.E.Rp) (fun row => hb (row,u))).symm
    _=_ := (integral_swap_bounded (ProbabilityMeasure.toMeasure (originalIid K.E (ownH G0 G1 side).val ρ)) volume _ (hf.comp (hupd.prodMap measurable_id)) _
      (fun x => hb (upd x.1,x.2))).symm

end OneSide
end FCAppendix.Affine.Tail04.NativePartialProductReduction
