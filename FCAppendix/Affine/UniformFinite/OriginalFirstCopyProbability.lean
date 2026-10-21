import FCAppendix.Affine.UniformFinite.OriginalGainTransport

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
open scoped BigOperators
namespace OriginalGain

variable {A K : Type*} [MeasurableSpace A] [Fintype K]

lemma integral_expect_swap (C : FiniteLaw K) (μ : Measure A)
    (f : K→ A→ℝ) (hf : ∀k,Integrable (f k) μ) :
    (∫a,C.expect (fun k=> f k a) ∂μ)=C.expect (fun k=>∫a,f k a ∂μ) := by
  unfold FiniteLaw.expect
  rw [integral_finsetSum Finset.univ (fun k _=>(hf k).const_mul (C.mass k))]
  simp only [integral_const_mul]

variable {N : ℕ}

lemma measurable_boundary_test {Ω : Type*} [MeasurableSpace Ω]
    (c L : ℕ) (u : ℝ) (b : Ω→Fin N→ℝ) (hb : Measurable b)
    (kind : Ω→Fin N→Fin 3) (hk : Measurable kind) :
    MeasurableSet {ω | ActualBoundary.boundaryEvent c L (b ω) u (kind ω)} := by
  have hl := (measurable_of_countable (ActualBoundary.lowerKindCount (N:=N))).comp hk
  have hu := (measurable_of_countable (ActualBoundary.upperZeroCount (N:=N))).comp hk
  have hh : Measurable (fun ω=>ActualBoundary.higherLowerCount (b ω) u (kind ω)) := by
    unfold ActualBoundary.higherLowerCount
    exact Finset.measurable_sum _ (fun j _=>Measurable.ite
      ((measurableSet_eq_fun ((measurable_pi_apply j).comp hk) measurable_const).inter
        (measurableSet_lt measurable_const ((measurable_pi_apply j).comp hb)))
      measurable_const measurable_const)
  convert! (measurableSet_eq_fun hl measurable_const).inter
    (measurableSet_eq_fun hu ((measurable_const.sub hh).sub measurable_const)) using 1

def remainingH (i : Row) (N L : ℕ) (eps : unitInterval) (u : ℝ)
    (ω : Fin N→ RivalDraw i) : Prop :=
  ActualBoundary.boundaryEvent (Uniform07.capacity (N+2)) L
    (fun j=>(drawBid i eps (ω j).2:ℝ)) u (fun j=>(ω j).1)

lemma measurable_remainingH (i : Row) (N L : ℕ) (eps : unitInterval) (u : ℝ) :
    MeasurableSet {ω | remainingH i N L eps u ω} := by
  exact measurable_boundary_test (Uniform07.capacity (N+2)) L u
    (fun ω : Fin N→RivalDraw i=>fun j=>(drawBid i eps (ω j).2:ℝ))
    (measurable_pi_lambda _ (fun j=>measurable_subtype_coe.comp
      ((measurable_drawBid i eps).comp (measurable_snd.comp (measurable_pi_apply j)))))
    (fun ω=>fun j=>(ω j).1)
    (measurable_pi_lambda _ (fun j=>measurable_fst.comp (measurable_pi_apply j)))

theorem remainingH_probability (i : Row) (N L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (eps : unitInterval) (pi : Joint i) (u : ℝ) :
    PiBinomial.pmf N (Uniform05.t i) L *
      PiBinomial.pmf (2*Uniform07.capacity (N+2)) (1/2)
        (Uniform07.capacity (N+2)-L-1) ≤
      (Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi)).real
        {ω | remainingH i N L eps u ω} := by
  let f : ((Fin N→ Fin 3)×(Fin N→ Bid i))→ℝ:=fun p=>
    if ActualBoundary.boundaryEvent (Uniform07.capacity (N+2)) L
      (fun j=>(p.2 j:ℝ)) u p.1 then 1 else 0
  have hf : Measurable f := Measurable.ite
    (measurable_boundary_test (Uniform07.capacity (N+2)) L u
      (fun p : (Fin N→Fin 3)×(Fin N→Bid i)=>fun j=>(p.2 j:ℝ))
      (measurable_pi_lambda _ (fun j=>measurable_subtype_coe.comp
        ((measurable_pi_apply j).comp measurable_snd))) Prod.fst measurable_fst)
    measurable_const measurable_const
  have hfi (kind : Fin N→ Fin 3) : Integrable (fun b : Fin N→ Bid i=> f (kind,b))
      (rowLaw N (restrictedLaw i (eps,pi)).bidLaw : Measure (Fin N→ Bid i)) :=
    Integrable.of_bound (hf.comp ((measurable_const (a := kind)).prodMk measurable_id)).aestronglyMeasurable 1
      (ae_of_all _ (fun b=> by dsimp only [f]; split_ifs <;> norm_num))
  have htransport:=integral_drawRow i N eps pi f hf 1
    (fun p=> by dsimp only [f]; split_ifs <;> norm_num)
  have hmass : (∫ω : Fin N→ RivalDraw i,f (drawRow i N eps ω)
      ∂Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi))=
      (Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi)).real
        {ω | remainingH i N L eps u ω} := by
    simpa only [f,drawRow,remainingH,Set.indicator,mem_setOf_eq,Pi.one_apply] using
      (integral_indicator_one (μ:=Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi))
        (measurable_remainingH i N L eps u))
  rw [← hmass,htransport,← integral_expect_swap _ _ _ hfi]
  have hi := integral_mono_ae
    (μ:=(rowLaw N (restrictedLaw i (eps,pi)).bidLaw : Measure (Fin N→ Bid i)))
    (integrable_const (PiBinomial.pmf N (Uniform05.t i) L *
      PiBinomial.pmf (2*Uniform07.capacity (N+2)) (1/2)
        (Uniform07.capacity (N+2)-L-1)))
    (integrable_finsetSum _ (fun k _=>(hfi k).const_mul ((categoryRowLaw i N).mass k)))
    (ae_of_all _ (fun b=> by
      simpa only [f,FiniteLaw.prob_eq_expect,FiniteLaw.expect] using
        ActualBoundary.literal_H_probability i N (Uniform07.capacity (N+2)) L hN
          (fun j=>(b j:ℝ)) u))
  simpa [FiniteLaw.expect] using hi

def remainingTemplate (kind : Fin N→ Fin 3) :=
  Source.lowerTemplate (ActualBoundary.pairRow kind)

def remainingBids (i : Row) (eps : unitInterval) (ω : Fin N→ RivalDraw i) : Fin (N+2)→ℝ :=
  Source.lowerBids (ActualBoundary.pairRow (fun j=>(ω j).1))
    (ActualBoundary.pairFullBids (fun j=>(drawBid i eps (ω j).2:ℝ)) 0 0)

lemma measurable_remainingBids (i : Row) (N : ℕ) (eps : unitInterval) :
    Measurable (remainingBids (N:=N) i eps) := by
  apply measurable_pi_lambda
  intro a
  refine Fin.cases ?_ (fun j=>?_) a
  · simp only [remainingBids,Source.lowerBids,ActualBoundary.pairFullBids,
      Fin.cons_zero,ite_self]
    exact measurable_const
  · refine Fin.cases ?_ (fun k=>?_) j
    · simp only [remainingBids,Source.lowerBids,ActualBoundary.pairFullBids,
        Fin.cons_succ,Fin.cons_zero,ite_self]
      exact measurable_const
    · have he : (fun ω : Fin N→RivalDraw i=>remainingBids i eps ω k.succ.succ) =
          (fun ω=>if (ω k).1=0 then (drawBid i eps (ω k).2:ℝ) else 0) := by
        funext ω
        simp [remainingBids,Source.lowerBids,ActualBoundary.pairRow,Source.countRowOfKind,
          ActualBoundary.pairKind,ActualBoundary.pairFullBids]
      rw [he]
      exact Measurable.ite (measurableSet_eq_fun
        (measurable_fst.comp (measurable_pi_apply k)) measurable_const)
        (measurable_subtype_coe.comp ((measurable_drawBid i eps).comp
          (measurable_snd.comp (measurable_pi_apply k)))) measurable_const

def rejectPair (i : Row) (eps : unitInterval)
    (ω : Fin N→ RivalDraw i) (x y : ℝ) : Prop :=
  (0:Fin (N+2))∉((remainingTemplate (fun j=>(ω j).1)).selection (Uniform05.kappa i)
    (LowBody.pairBids (remainingBids i eps ω) 0 (0:Fin (N+1)).succ x y)).1

lemma measurable_rejectPair (i : Row) (N : ℕ) (eps : unitInterval) :
    MeasurableSet {p : (Fin N→ RivalDraw i)×(ℝ×ℝ) |
      rejectPair i eps p.1 p.2.1 p.2.2} := by
  have hsel:Measurable (fun p : (Fin N→ Fin 3)×(Fin (N+2)→ℝ)=>
      (remainingTemplate p.1).selection (Uniform05.kappa i) p.2):=
    measurable_from_prod_countable_right (fun k=>(remainingTemplate k).measurable_selection _)
  exact (((measurable_of_countable (fun P : Allocation (N+2)=>(0:Fin (N+2))∉P.1)).comp
    (hsel.comp ((measurable_pi_lambda _ (fun j=> measurable_fst.comp
      ((measurable_pi_apply j).comp measurable_fst))).prodMk
        (LowBody.measurable_pairBids_joint _ (measurable_remainingBids i N eps) 0
          (0:Fin (N+1)).succ)))).setOf)

theorem normalized_original_pair_rejection (i : Row) (N L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (eps : unitInterval) (pi : Joint i) (u : ℝ) (hu : 0≤ u)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hμ : ∀ᵐx∂μ,x≤ u) :
    (PiBinomial.pmf N (Uniform05.t i) L *
      PiBinomial.pmf (2*Uniform07.capacity (N+2)) (1/2)
        (Uniform07.capacity (N+2)-L-1))/2 ≤
      ∫ω in {ω | remainingH i N L eps u ω},
        (μ.prod μ).real {p : ℝ×ℝ | rejectPair i eps ω p.1 p.2}
        ∂Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi) := by
  have h:=LowBody.integrated_variable_pair_rejection_ge_half
    (remainingTemplate (N:=N)) (fun ω : Fin N→ RivalDraw i=> fun j=>(ω j).1)
    (measurable_pi_lambda _ (fun j=> measurable_fst.comp (measurable_pi_apply j)))
    (Uniform05.kappa i) (remainingBids i eps) (measurable_remainingBids i N eps)
    (0:Fin (N+2)) (0:Fin (N+1)).succ (Ne.symm (Fin.succ_ne_zero _))
    (fun ω=> ActualBoundary.pairRow_focal_mem _) (fun ω=> ActualBoundary.pairRow_rival_mem _)
    u {ω | remainingH i N L eps u ω} (measurable_remainingH i N L eps u)
    (fun ω hω=>(ActualBoundary.boundary_residuals L hN hroom
      (fun j=>(drawBid i eps (ω j).2:ℝ)) u (fun j=>(ω j).1) hω).2)
    (fun ω a ha=> Source.lowerBids_of_not_mem _ _ ha)
    (fun ω hω=> by
      have hc:=ActualBoundary.boundary_pair_count L hN hroom
        (fun j=>(drawBid i eps (ω j).2:ℝ)) u hu (fun j=>(ω j).1) hω 0 0
      change _≤(LowBody.pairRestAbove u 0 (0:Fin (N+1)).succ
        (remainingBids i eps ω)).card
      change (LowBody.pairRestAbove u 0 (0:Fin (N+1)).succ
        (remainingBids i eps ω)).card+1=_ at hc
      rw [show (remainingTemplate (fun j=>(ω j).1)).residual₀ =
        Source.residual (ActualBoundary.pairRow (fun j=>(ω j).1)) 0 from rfl]
      omega)
    (Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi)) μ hμ
  exact (div_le_div_of_nonneg_right (remainingH_probability i N L hN eps pi u)
    (by norm_num : 0≤(2:ℝ))).trans h

def realBidLaw (i : Row) (eps : unitInterval) (pi : Joint i) : ProbabilityMeasure ℝ :=
  (bidLaw i (eps,pi)).map measurable_subtype_coe.aemeasurable

lemma realBidLaw_original (i : Row) (eps : unitInterval) (pi : Joint i) :
    (realBidLaw i eps pi : Measure ℝ)=
      (lowerDrawLaw i pi).map (fun p=>(drawBid i eps p:ℝ)) := by
  rw [realBidLaw,ProbabilityMeasure.toMeasure_map,← restrictedLaw_bidLaw,
    ← lowerDraw_bid_law,Measure.map_map measurable_subtype_coe (measurable_drawBid i eps)]
  apply congrArg (fun g : LowerDraw i→ℝ=>(lowerDrawLaw i pi).map g)
  funext p
  rfl

lemma realBidLaw_atomless (i : Row) (eps : unitInterval) (heps : 0<(eps:ℝ))
    (pi : Joint i) : NullSingletonClass (realBidLaw i eps pi : Measure ℝ) := by
  letI:=physical_bid_atomless i eps heps pi
  constructor
  intro b
  rw [realBidLaw,ProbabilityMeasure.toMeasure_map,
    Measure.map_apply measurable_subtype_coe (measurableSet_singleton b)]
  exact measure_eq_zero_iff_ae_notMem.mpr
    (LowBody.ae_injective_ne (bidLaw i (eps,pi) : Measure (Bid i))
      Subtype.val Subtype.val_injective b)

theorem finite_original_pair_rejection (i : Row) (N L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (eps : unitInterval) (heps : 0<(eps:ℝ)) (pi : Joint i)
    (E : Set (Value i×unitInterval)) (u : ℝ) (hu : 0≤ u)
    (hbox : ∀ᵐp∂carrier i pi E,(drawBid i eps p:ℝ)≤ u) :
    (carrier i pi E).real univ^2*
      (PiBinomial.pmf N (Uniform05.t i) L *
        PiBinomial.pmf (2*Uniform07.capacity (N+2)) (1/2)
          (Uniform07.capacity (N+2)-L-1))/2 ≤
    ∫ω : Fin N→ RivalDraw i,∫p : LowerDraw i×LowerDraw i,
      (if remainingH i N L eps u ω ∧ rejectPair i eps ω
        (drawBid i eps p.1) (drawBid i eps p.2) then (1:ℝ) else 0)
      ∂(carrier i pi E).prod (carrier i pi E)
      ∂Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi) := by
  let Γ:=carrier i pi E
  let x : LowerDraw i→ℝ:=fun p=>(drawBid i eps p:ℝ)
  have hx : Measurable x:=measurable_subtype_coe.comp (measurable_drawBid i eps)
  let θ:=Γ.map x
  have hθle : θ≤(realBidLaw i eps pi : Measure ℝ) := by
    rw [realBidLaw_original]
    exact Measure.map_mono (carrier_le i pi E) hx
  letI:=realBidLaw_atomless i eps heps pi
  haveI : NullSingletonClass θ:=⟨fun b=> le_antisymm
    (by simpa only [measure_singleton] using Measure.le_iff'.mp hθle {b}) bot_le⟩
  have hm : θ univ=Γ univ:=by
    dsimp only [θ]
    rw [Measure.map_apply hx MeasurableSet.univ,preimage_univ]
  by_cases hΓ : Γ univ=0
  · have hz : Γ=0:=Measure.measure_univ_eq_zero.mp hΓ
    simp only [Γ] at hz
    simp [hz]
  let μ : Measure ℝ:=(Γ univ)⁻¹ • θ
  have ht:=measure_ne_top Γ univ
  haveI : IsProbabilityMeasure μ:=⟨by
    change (Γ univ)⁻¹*θ univ=1
    rw [hm]
    exact ENNReal.inv_mul_cancel hΓ ht⟩
  haveI : NullSingletonClass μ:=⟨by
    intro b
    simp only [μ,Measure.smul_apply,measure_singleton,smul_eq_mul,mul_zero]⟩
  have hθ : ∀ᵐb∂θ,b≤ u :=
    (ae_map_iff hx.aemeasurable (measurableSet_le measurable_id measurable_const)).mpr hbox
  have hnormal:=normalized_original_pair_rejection i N L hN hroom eps pi u hu μ
    (Measure.ae_smul_measure hθ _)
  have hθrec : θ=(Γ univ) • μ := by
    dsimp only [μ]
    rw [smul_smul,ENNReal.mul_inv_cancel hΓ ht,one_smul]
  have hprod : θ.prod θ=(Γ univ*Γ univ) • (μ.prod μ) := by
    calc
      _=((Γ univ) • μ).prod ((Γ univ) • μ):=congrArg₂ Measure.prod hθrec hθrec
      _=_:=by rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  have hmap : (Γ.prod Γ).map (Prod.map x x)=θ.prod θ := by
    rw [← Measure.map_prod_map Γ Γ hx hx]
  have hinner (ω : Fin N→ RivalDraw i) :
      (∫p : LowerDraw i×LowerDraw i,
        if remainingH i N L eps u ω ∧ rejectPair i eps ω (x p.1) (x p.2)
        then (1:ℝ) else 0 ∂Γ.prod Γ)=
      (Γ.real univ)^2*(if remainingH i N L eps u ω then
        (μ.prod μ).real {p : ℝ×ℝ | rejectPair i eps ω p.1 p.2} else 0) := by
    have hR : MeasurableSet {p : ℝ×ℝ | rejectPair i eps ω p.1 p.2} := by
      convert! (measurable_rejectPair i N eps).preimage
        ((measurable_const (a := ω)).prodMk measurable_id) using 1
    by_cases hH : remainingH i N L eps u ω
    · simp only [hH,true_and,if_true]
      have hi : Measurable (fun p : ℝ×ℝ=> if rejectPair i eps ω p.1 p.2 then (1:ℝ) else 0):=
        Measurable.ite hR measurable_const measurable_const
      have he : (∫p : LowerDraw i×LowerDraw i,
          if rejectPair i eps ω (x p.1) (x p.2) then (1:ℝ) else 0 ∂Γ.prod Γ) =
          ∫p : ℝ×ℝ, if rejectPair i eps ω p.1 p.2 then (1:ℝ) else 0
            ∂(Γ.prod Γ).map (Prod.map x x) := by
        convert! (integral_map
          (show AEMeasurable (Prod.map x x) (Γ.prod Γ) from (hx.prodMap hx).aemeasurable)
          hi.aestronglyMeasurable).symm using 1
      rw [he,hmap,hprod,integral_smul_measure]
      have hI:=integral_indicator_one (μ:=μ.prod μ) hR
      simp only [Set.indicator,mem_setOf_eq,Pi.one_apply] at hI
      rw [hI]
      simp only [ENNReal.toReal_mul,smul_eq_mul,measureReal_def,pow_two]
    · simp [hH]
  change _ ≤ ∫ω : Fin N→RivalDraw i,∫p : LowerDraw i×LowerDraw i,
    (if remainingH i N L eps u ω ∧ rejectPair i eps ω (x p.1) (x p.2) then (1:ℝ) else 0)
      ∂Γ.prod Γ ∂Measure.pi (fun _ : Fin N=>rivalDrawLaw i pi)
  simp_rw [hinner]
  rw [integral_const_mul]
  have hRI : (∫ω,
      if remainingH i N L eps u ω then
        (μ.prod μ).real {p : ℝ×ℝ | rejectPair i eps ω p.1 p.2} else 0
      ∂Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi))=
      ∫ω in {ω | remainingH i N L eps u ω},
        (μ.prod μ).real {p : ℝ×ℝ | rejectPair i eps ω p.1 p.2}
        ∂Measure.pi (fun _ : Fin N=> rivalDrawLaw i pi) := by
    have h := integral_indicator
      (μ := Measure.pi (fun _ : Fin N=>rivalDrawLaw i pi))
      (f := fun ω : Fin N→RivalDraw i=>(μ.prod μ).real {p : ℝ×ℝ | rejectPair i eps ω p.1 p.2})
      (measurable_remainingH i N L eps u)
    simp only [Set.indicator,mem_setOf_eq] at h
    convert! h using 1
  rw [hRI]
  have h:=mul_le_mul_of_nonneg_left hnormal (sq_nonneg (Γ.real univ))
  simpa only [Γ,mul_div_assoc] using h

end OriginalGain
end FCAppendix.Affine.UniformFinite
