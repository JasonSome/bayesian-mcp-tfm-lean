import FCAppendix.Affine.UniformFinite.OriginalHarmfulProbability
import FCAppendix.Affine.UniformFinite.ActualRaiseModulus
import FCAppendix.Affine.UniformFinite.ActualHGain

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Classical
open scoped BigOperators
namespace OriginalGain

variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X] {N : ℕ}

lemma measurePreserving_cons_iid (ρ : Measure X) [IsProbabilityMeasure ρ] :
    MeasurePreserving (fun p : X×(Fin N→ X)=> Fin.cons p.1 p.2)
      (ρ.prod (Measure.pi (fun _ : Fin N=>ρ)))
      (Measure.pi (fun _ : Fin (N+1)=>ρ)) := by
  have h:=(measurePreserving_piFinSuccAbove (fun _ : Fin (N+1)=>ρ) 0).symm
  convert! h using 1
  funext p j
  refine Fin.cases ?_ (fun k=>?_) j <;>
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]

lemma measurePreserving_carrierRow (Γ : Measure A) [IsFiniteMeasure Γ]
    (ρ : Measure X) [IsProbabilityMeasure ρ] :
    MeasurePreserving
      (fun q : (Fin N→ X)×(A×X)=>(q.2.1,(Fin.cons q.2.2 q.1 : Fin (N+1)→ X)))
      ((Measure.pi (fun _ : Fin N=>ρ)).prod (Γ.prod ρ))
      (Γ.prod (Measure.pi (fun _ : Fin (N+1)=>ρ))) := by
  let ν:=Measure.pi (fun _ : Fin N=>ρ)
  exact ((MeasurePreserving.id Γ).prod (measurePreserving_cons_iid ρ)).comp
    ((measurePreserving_prodAssoc Γ ρ ν).comp
      (Measure.measurePreserving_swap (μ:=ν) (ν:=Γ.prod ρ)))

theorem integral_carrierRow (Γ : Measure A) [IsFiniteMeasure Γ]
    (ρ : Measure X) [IsProbabilityMeasure ρ] (f : A×(Fin (N+1)→ X)→ℝ)
    (hf : Measurable f)
    (hi : Integrable f (Γ.prod (Measure.pi (fun _ : Fin (N+1)=>ρ)))) :
    (∫q : (Fin N→ X)×(A×X),f (q.2.1,Fin.cons q.2.2 q.1)
      ∂(Measure.pi (fun _ : Fin N=>ρ)).prod (Γ.prod ρ))=
      ∫t,∫ω,f (t,ω) ∂Measure.pi (fun _ : Fin (N+1)=>ρ) ∂Γ := by
  have hp:=measurePreserving_carrierRow (N:=N) Γ ρ
  rw [← integral_prod _ hi,← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable).symm

def actualPayoff (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i)
    (v : Value i) (own : Bid i) (ω : Fin N→ RivalDraw i) : ℝ :=
  rowPayoff i (restrictedLaw i (eps,pi)) (focalRow (fun j=>(ω j).1)) v
    (focalBids i (fun j=>(ω j).1) own (fun j=> drawBid i eps (ω j).2)) 0

def actualGain (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i)
    (d : Value i×unitInterval→ unitInterval) (p : LowerDraw i)
    (ω : Fin N→ RivalDraw i) : ℝ :=
  actualPayoff i N eps pi p.1.1 (drawBid i eps ((p.1.1,d p.1),p.2)) ω-
    actualPayoff i N eps pi p.1.1 (drawBid i eps p) ω

lemma measurable_actualPayoff (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i) :
    Measurable (fun p : (Value i×Bid i)×(Fin N→ RivalDraw i)=>
      actualPayoff i N eps pi p.1.1 p.1.2 p.2) := by
  let f : (Fin N→ Fin 3)×((Value i×Bid i)×(Fin N→ Bid i))→ℝ:=fun p=>
    rowPayoff i (restrictedLaw i (eps,pi)) (focalRow p.1) p.2.1.1
      (focalBids i p.1 p.2.1.2 p.2.2) 0
  have hf : Measurable f:=measurable_from_prod_countable_right (fun kind=> by
    have hb: Measurable (fun p : (Value i×Bid i)×(Fin N→ Bid i)=>
        ActualSurplus.cappedFocalBids i kind p.1.2 p.2):=
      (ActualSurplus.continuous_cappedFocalBids i kind).measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have h:=(SourceContinuity.measurable_rowPayoff i (focalRow kind) 0
      (ActualSurplus.focalRow_focal_mem kind)).comp
        ((measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).prodMk
          ((SourceContinuity.measurable_fixedLawState i (restrictedLaw i (eps,pi))).comp hb))
    have he (p : (Value i×Bid i)×(Fin N→Bid i)) : SourceContinuity.bids i
        (SourceContinuity.fixedLawState i (restrictedLaw i (eps,pi))
          (ActualSurplus.cappedFocalBids i kind p.1.2 p.2)) =
        focalBids i kind p.1.2 p.2 := ActualSurplus.cappedFocalBids_val i kind p.1.2 p.2
    change Measurable (fun p : (Value i×Bid i)×(Fin N→Bid i)=>
      rowPayoff i (restrictedLaw i (eps,pi)) (focalRow kind) p.1.1
        (SourceContinuity.bids i (SourceContinuity.fixedLawState i (restrictedLaw i (eps,pi))
          (ActualSurplus.cappedFocalBids i kind p.1.2 p.2))) 0) at h
    simpa only [f,he] using h)
  convert! hf.comp ((measurable_pi_lambda _ (fun j=> measurable_fst.comp
    ((measurable_pi_apply j).comp measurable_snd))).prodMk
      (measurable_fst.prodMk (measurable_pi_lambda _ (fun j=>
        (measurable_drawBid i eps).comp (measurable_snd.comp
          ((measurable_pi_apply j).comp measurable_snd)))))) using 1

lemma measurable_actualGain (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i)
    (d : Value i×unitInterval→ unitInterval) (hd : Measurable d) :
    Measurable (Function.uncurry (actualGain i N eps pi d)) := by
  have hp:=measurable_actualPayoff i N eps pi
  have hv:Measurable (fun p : LowerDraw i×(Fin N→ RivalDraw i)=> p.1.1.1):=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hb:Measurable (fun p : LowerDraw i×(Fin N→ RivalDraw i)=> drawBid i eps p.1):=
    (measurable_drawBid i eps).comp measurable_fst
  have hy:Measurable (fun p : LowerDraw i×(Fin N→ RivalDraw i)=>
      drawBid i eps ((p.1.1.1,d p.1.1),p.1.2)):=
    (measurable_drawBid i eps).comp
      ((hv.prodMk (hd.comp (measurable_fst.comp measurable_fst))).prodMk
        (measurable_snd.comp measurable_fst))
  convert! (hp.comp ((hv.prodMk hy).prodMk measurable_snd)).sub
    (hp.comp ((hv.prodMk hb).prodMk measurable_snd)) using 1

lemma actualGain_bound (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i)
    (d : Value i×unitInterval→ unitInterval) (p : LowerDraw i)
    (ω : Fin N→ RivalDraw i) : |actualGain i N eps pi d p ω|≤6*Uniform05.t i := by
  have hn:=noisyRowPayoff_bound i eps pi p.1.1 (d p.1) p.2
    (fun j=>(ω j).1) (fun j=> drawBid i eps (ω j).2)
  have ho:=noisyRowPayoff_bound i eps pi p.1.1 p.1.2 p.2
    (fun j=>(ω j).1) (fun j=> drawBid i eps (ω j).2)
  have hh:=abs_sub
    (actualPayoff i N eps pi p.1.1 (drawBid i eps ((p.1.1,d p.1),p.2)) ω)
    (actualPayoff i N eps pi p.1.1 (drawBid i eps p) ω)
  change |actualGain i N eps pi d p ω|≤ _ at hh
  dsimp only [actualPayoff,drawBid] at hh
  rcases p with ⟨⟨v,q⟩,z⟩
  dsimp only [drawBid] at hn ho
  linarith [v.property.2]

lemma integrable_actualGain (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i)
    (d : Value i×unitInterval→ unitInterval) (hd : Measurable d)
    (Γ : Measure (LowerDraw i)) [IsFiniteMeasure Γ] :
    Integrable (Function.uncurry (actualGain i N eps pi d))
      (Γ.prod (Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi))) :=
  Integrable.of_bound (measurable_actualGain i N eps pi d hd).aestronglyMeasurable
    (6*Uniform05.t i) (ae_of_all _ (fun p=> by
      convert! actualGain_bound i N eps pi d p.1 p.2 using 1))

def carrier (i : Row) (pi : Joint i) (E : Set (Value i×unitInterval)) : Measure (LowerDraw i) :=
  ((pi.1 : Measure (Value i×unitInterval)).restrict E).prod volume

instance carrier_finite (i : Row) (pi : Joint i) (E : Set (Value i×unitInterval)) :
    IsFiniteMeasure (carrier i pi E) := inferInstanceAs (IsFiniteMeasure
      (((pi.1 : Measure (Value i×unitInterval)).restrict E).prod (volume : Measure unitInterval)))

lemma carrier_le (i : Row) (pi : Joint i) (E : Set (Value i×unitInterval)) :
    carrier i pi E≤ lowerDrawLaw i pi :=
  Measure.prod_mono Measure.restrict_le_self le_rfl

lemma carrier_mass (i : Row) (pi : Joint i) (E : Set (Value i×unitInterval)) :
    (carrier i pi E).real univ=(pi.1 : Measure (Value i×unitInterval)).real E := by
  simp [carrier,Measure.real,Measure.prod_apply,Measure.restrict_apply,
    measure_univ]

theorem integrated_gain_nonpos (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i)
    (hIC : NoisyIC i N eps pi) (E : Set (Value i×unitInterval))
    (d : Value i×unitInterval→ unitInterval) (hd : Measurable d) :
    (∫p : LowerDraw i,∫ω : Fin N→ RivalDraw i,actualGain i N eps pi d p ω
      ∂Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi) ∂carrier i pi E)≤0 := by
  let ρ:=Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi)
  have hi:=integrable_actualGain i N eps pi d hd (carrier i pi E)
  have hI : ∀ᵐp∂(pi.1 : Measure (Value i×unitInterval)).restrict E,
      expectedUtility i N eps pi p.1 (d p)-expectedUtility i N eps pi p.1 p.2≤0 :=
    (ae_restrict_of_ae hIC).mono (fun p hp=> sub_nonpos.mpr (hp (d p)))
  have he (p : Value i×unitInterval) :
      (∫z : unitInterval,∫ω,actualGain i N eps pi d (p,z) ω ∂ρ)=
        expectedUtility i N eps pi p.1 (d p)-expectedUtility i N eps pi p.1 p.2 := by
    rw [expectedUtility_eq_original_draws,expectedUtility_eq_original_draws]
    have hpair : Integrable (fun q : unitInterval×(Fin N→ RivalDraw i)=>
        actualGain i N eps pi d (p,q.1) q.2) (volume.prod ρ) :=
      Integrable.of_bound
        ((measurable_actualGain i N eps pi d hd).comp
          (((measurable_const (a := p)).prodMk measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
        (6*Uniform05.t i) (ae_of_all _ (fun q=> by
          simpa only [Real.norm_eq_abs] using actualGain_bound i N eps pi d (p,q.1) q.2))
    have hpay (q : unitInterval) : Integrable (fun s : unitInterval×(Fin N→RivalDraw i)=>
        actualPayoff i N eps pi p.1 (drawBid i eps ((p.1,q),s.1)) s.2) (volume.prod ρ) := by
      have hb : Measurable (fun s : unitInterval×(Fin N→RivalDraw i)=>
          drawBid i eps ((p.1,q),s.1)) :=
        (measurable_drawBid i eps).comp ((measurable_const (a := (p.1,q))).prodMk measurable_fst)
      have hm := (measurable_actualPayoff i N eps pi).comp
        (((measurable_const (a := p.1)).prodMk hb).prodMk measurable_snd)
      apply Integrable.of_bound hm.aestronglyMeasurable (3*(p.1:ℝ))
      exact ae_of_all _ (fun s=>by
        simpa only [Real.norm_eq_abs,actualPayoff,drawBid,Function.comp_apply] using
          noisyRowPayoff_bound i eps pi p.1 q s.1
            (fun j=>(s.2 j).1) (fun j=>drawBid i eps (s.2 j).2))
    rw [integral_integral_swap hpair]
    calc
      _ = ∫ω, ((∫z : unitInterval,actualPayoff i N eps pi p.1
          (drawBid i eps ((p.1,d p),z)) ω)-
          (∫z : unitInterval,actualPayoff i N eps pi p.1 (drawBid i eps (p,z)) ω)) ∂ρ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun ω=> by
          have hnew : Integrable (fun z : unitInterval=> actualPayoff i N eps pi p.1
              (drawBid i eps ((p.1,d p),z)) ω) := by
            convert! ActualSurplus.integrable_noisy_own i eps pi p.1 (d p)
              (fun j=>(ω j).1) (fun j=>drawBid i eps (ω j).2) using 1
          have hold : Integrable (fun z : unitInterval=>actualPayoff i N eps pi p.1
              (drawBid i eps (p,z)) ω) := by
            convert! ActualSurplus.integrable_noisy_own i eps pi p.1 p.2
              (fun j=>(ω j).1) (fun j=>drawBid i eps (ω j).2) using 1
          convert! integral_sub hnew hold using 1)
      _ = _ := by
        rw [integral_sub (hpay (d p)).integral_prod_right (hpay p.2).integral_prod_right]
        rfl
  have hi' : Integrable (fun p : LowerDraw i=>∫ω : Fin N→RivalDraw i,
      actualGain i N eps pi d p ω ∂ρ) (carrier i pi E) := by
    convert! hi.integral_prod_left using 1
  rw [carrier] at hi'
  rw [carrier,integral_prod _ hi']
  simp_rw [he]
  exact integral_nonpos_of_ae hI

end OriginalGain
end FCAppendix.Affine.UniformFinite
