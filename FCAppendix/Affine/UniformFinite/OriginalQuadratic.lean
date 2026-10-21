import FCAppendix.Affine.UniformFinite.OriginalFirstCopyProbability

noncomputable section
set_option maxHeartbeats 3000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Classical
open scoped BigOperators
namespace OriginalGain
open ActualAtoms

theorem lower_carrier_integral_le (i : Row) (pi : Joint i)
    (E : Set (Value i×unitInterval))
    (f : LowerDraw i×RivalDraw i→ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀p,|f p|≤ C)
    (hpos : ∀ᵐp∂carrier i pi E,∀r : RivalDraw i,0≤ f (p,r)) :
    Uniform05.t i*(∫p : LowerDraw i,∫q : LowerDraw i,f (p,(0,q))
      ∂carrier i pi E ∂carrier i pi E) ≤
      ∫p : LowerDraw i,∫r : RivalDraw i,f (p,r)
        ∂rivalDrawLaw i pi ∂carrier i pi E := by
  let Γ:=carrier i pi E
  let μ:=lowerDrawLaw i pi
  have hi (ν : Measure (LowerDraw i×RivalDraw i)) [IsFiniteMeasure ν] : Integrable f ν :=
    Integrable.of_bound hf.aestronglyMeasurable C
      (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using hC p))
  have hg : Integrable (fun p : LowerDraw i×LowerDraw i=> f (p.1,(0,p.2))) (Γ.prod Γ) :=
    Integrable.of_bound
      (hf.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).aestronglyMeasurable C
      (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using hC (p.1,(0,p.2))))
  rw [← integral_const_mul]
  apply integral_mono_ae (hg.integral_prod_left.const_mul _) (hi _).integral_prod_left
  filter_upwards [hpos] with p hp
  have hiq (k : Fin 3) : Integrable (fun q : LowerDraw i=> f (p,(k,q))) μ :=
    Integrable.of_bound
      (hf.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable C
      (ae_of_all _ (fun q=> by simpa only [Real.norm_eq_abs] using hC (p,(k,q))))
  have hμ : (∫q,f (p,(0,q)) ∂Γ)≤∫q,f (p,(0,q)) ∂μ :=
    integral_mono_measure (carrier_le i pi E) (ae_of_all _ (fun q=> hp (0,q))) (hiq 0)
  have hk : Uniform05.t i*(∫q,f (p,(0,q)) ∂μ)≤
      (categoryLaw i).expect (fun k=>∫q,f (p,(k,q)) ∂μ) := by
    unfold FiniteLaw.expect
    have h:=Finset.single_le_sum (f:=fun k=> (categoryLaw i).mass k*
      (∫q,f (p,(k,q)) ∂μ))
      (fun k (_ : k∈(Finset.univ : Finset (Fin 3)))=> mul_nonneg
        ((categoryLaw i).nonneg k) (integral_nonneg (fun q=> hp (k,q))))
      (Finset.mem_univ (0:Fin 3))
    simpa only [categoryLaw,ite_true] using h
  have hip : Integrable (fun r : RivalDraw i=> f (p,r)) (rivalDrawLaw i pi) :=
    Integrable.of_bound (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
      (ae_of_all _ (fun r=> by simpa only [Real.norm_eq_abs] using hC (p,r)))
  rw [rivalDrawLaw,integral_prod _ hip,LowBody.integral_probabilityMeasure]
  exact (mul_le_mul_of_nonneg_left hμ (Uniform05.t_pos i).le).trans hk

lemma pair_original_bids {N : ℕ} (i : Row) (eps : unitInterval)
    (ω : Fin N→ RivalDraw i) (x y : Bid i) :
    Source.lowerBids (focalRow (Fin.cons 0 (fun j=>(ω j).1)))
      (focalBids i (Fin.cons 0 (fun j=>(ω j).1)) x
        (Fin.cons y (fun j=> drawBid i eps (ω j).2))) =
      LowBody.pairBids (remainingBids i eps ω) 0 (0:Fin (N+1)).succ x y := by
  funext a
  refine Fin.cases ?_ (fun j=>?_) a
  · simp [Source.lowerBids,focalRow,Source.countRowOfKind,focalBids,
      LowBody.pairBids]
  · refine Fin.cases ?_ (fun k=>?_) j
    · simp [Source.lowerBids,focalRow,Source.countRowOfKind,focalBids,
        LowBody.pairBids]
    · have hk1 : k.succ.succ≠(1:Fin (N+2)) := Fin.succ_succ_ne_one k
      by_cases hk : (ω k).1=0 <;>
        simp [Source.lowerBids,focalRow,Source.countRowOfKind,focalBids,
          LowBody.pairBids,remainingBids,ActualBoundary.pairFullBids,
          ActualBoundary.pairRow,ActualBoundary.pairKind,hk,hk1]

theorem actual_gain_on_H (i : Row) (N L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (eps : unitInterval) (pi : Joint i) (d : Value i×unitInterval→ unitInterval)
    (ω : Fin N→ RivalDraw i) (p q : LowerDraw i)
    (l u S width : ℝ) (hu : 0≤ u)
    (hH : remainingH i N L eps u ω)
    (hp : l≤(drawBid i eps p:ℝ) ∧ (drawBid i eps p:ℝ)≤ u ∧
      u<(drawBid i eps ((p.1.1,d p.1),p.2):ℝ) ∧
      S≤(p.1.1:ℝ)-(drawBid i eps p:ℝ) ∧
      (drawBid i eps ((p.1.1,d p.1),p.2):ℝ)-l≤ width)
    (hq : (drawBid i eps q:ℝ)≤ u) :
    (if rejectPair i eps ω (drawBid i eps p) (drawBid i eps q) then S else 0)-width ≤
      actualGain i (N+1) eps pi d p (Fin.cons (0,q) ω) := by
  let kind:=fun j=>(ω j).1
  let b:=focalBids i (Fin.cons 0 kind) (drawBid i eps p)
    (Fin.cons (drawBid i eps q) (fun j=> drawBid i eps (ω j).2))
  let row:=focalRow (Fin.cons 0 kind)
  have hrow : row=ActualBoundary.pairRow kind:=rfl
  obtain ⟨hl,hr⟩:=ActualBoundary.boundary_residuals L hN hroom
    (fun j=>(drawBid i eps (ω j).2:ℝ)) u kind hH
  have hc:=ActualBoundary.boundary_pair_count L hN hroom
    (fun j=>(drawBid i eps (ω j).2:ℝ)) u hu kind hH 0 0
  have hrest : (LowBody.pairRestAbove u 0 (0:Fin (N+1)).succ
      (remainingBids i eps ω)).card+1=Source.residual row 0:=hc
  have hfull : (Finset.univ.filter (fun k=> k≠0 ∧ u< Source.lowerBids row b k)).card<
      Source.residual row 0 := by
    rw [pair_original_bids,ActualAtoms.pair_others_above _ 0 (0:Fin (N+1)).succ
      (Ne.symm (Fin.succ_ne_zero _)) u _ _ hq]
    omega
  have h:=row_firstCopy_crossing_gain i (restrictedLaw i (eps,pi)) row p.1.1 b 0
    (ActualSurplus.focalRow_focal_mem _) (by omega) hr l u
    (drawBid i eps ((p.1.1,d p.1),p.2)) S (by simpa only [b,focalBids_zero] using hp.1)
    hp.2.2.1 (hu.trans_lt hp.2.2.1)
    (by simpa only [b,focalBids_zero] using hp.2.2.2.1) hfull
  have hb:=pair_original_bids i eps ω (drawBid i eps p) (drawBid i eps q)
  have hnew : Function.update b 0 (drawBid i eps ((p.1.1,d p.1),p.2):ℝ)=
      focalBids i (Fin.cons 0 kind) (drawBid i eps ((p.1.1,d p.1),p.2))
        (Fin.cons (drawBid i eps q) (fun j=> drawBid i eps (ω j).2)) := by
    funext a
    refine Fin.cases ?_ (fun j=>?_) a <;> simp [b,focalBids]
  rw [hnew,hb] at h
  have hkind : (fun j=> ((Fin.cons (0,q) ω : Fin (N+1)→RivalDraw i) j).1)=Fin.cons 0 kind := by
    funext j
    refine Fin.cases ?_ (fun k=>?_) j <;> rfl
  have hdraw : (fun j=> drawBid i eps ((Fin.cons (0,q) ω : Fin (N+1)→RivalDraw i) j).2)=
      Fin.cons (drawBid i eps q) (fun j=> drawBid i eps (ω j).2) := by
    funext j
    refine Fin.cases ?_ (fun k=>?_) j <;> rfl
  have hgain : actualGain i (N+1) eps pi d p (Fin.cons (0,q) ω)=
      rowPayoff i (restrictedLaw i (eps,pi)) row p.1.1
        (focalBids i (Fin.cons 0 kind) (drawBid i eps ((p.1.1,d p.1),p.2))
          (Fin.cons (drawBid i eps q) (fun j=> drawBid i eps (ω j).2))) 0-
        rowPayoff i (restrictedLaw i (eps,pi)) row p.1.1 b 0 := by
    simp only [actualGain,actualPayoff,hkind,hdraw]
    rfl
  have h' : (if rejectPair i eps ω (drawBid i eps p) (drawBid i eps q) then S else 0)-
      ((drawBid i eps ((p.1.1,d p.1),p.2):ℝ)-l)≤
      actualGain i (N+1) eps pi d p (Fin.cons (0,q) ω) := by
    rw [hgain]
    have heq : rejectPair i eps ω (drawBid i eps p) (drawBid i eps q)=
        (0∉((Source.lowerTemplate row).selection (Uniform05.kappa i)
          (LowBody.pairBids (remainingBids i eps ω) 0 (0:Fin (N+1)).succ
            (drawBid i eps p) (drawBid i eps q))).1) := by
      unfold rejectPair remainingTemplate
      rw [hrow]
    by_cases hh : rejectPair i eps ω (drawBid i eps p) (drawBid i eps q)
    · have hh' := Eq.mp heq hh
      simpa only [if_pos hh,if_pos hh'] using h
    · have hh' : ¬(0∉((Source.lowerTemplate row).selection (Uniform05.kappa i)
          (LowBody.pairBids (remainingBids i eps ω) 0 (0:Fin (N+1)).succ
            (drawBid i eps p) (drawBid i eps q))).1) := fun hx=> hh (Eq.mpr heq hx)
      simpa only [if_neg hh,if_neg hh'] using h
  exact (sub_le_sub_left hp.2.2.2.2 _).trans h'

theorem exists_actual_cluster_quadratic (i : Row) (N L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (a err : ℝ) (ha : 0< a) (herr : 0< err) :
    ∃radius : ℝ,0< radius ∧ ∀(eps : unitInterval),0<(eps:ℝ)→
      ∀(pi : Joint i),NoisyIC i (N+1) eps pi→
      ∀(E : Set (Value i×unitInterval)),MeasurableSet E→
      ∀(d : Value i×unitInterval→ unitInterval),Measurable d→
      ∀(l u S width : ℝ),a≤ l→0≤ S→0≤ width→ width< radius→
      ∀(s : Set ℝ),MeasurableSet s→
      (∀ᵐp∂carrier i pi E,
        l≤(drawBid i eps p:ℝ) ∧ (drawBid i eps p:ℝ)≤ u ∧
        u<(drawBid i eps ((p.1.1,d p.1),p.2):ℝ) ∧
        S≤(p.1.1:ℝ)-(drawBid i eps p:ℝ) ∧
        (drawBid i eps ((p.1.1,d p.1),p.2):ℝ)-l≤ width ∧
        Icc (drawBid i eps p:ℝ) (drawBid i eps ((p.1.1,d p.1),p.2):ℝ)⊆s ∧
        Icc (Uniform05.kappa i*(drawBid i eps p:ℝ))
          (Uniform05.kappa i*(drawBid i eps ((p.1.1,d p.1),p.2):ℝ))⊆s) →
      (carrier i pi E).real univ^2*Uniform05.t i*
        (PiBinomial.pmf N (Uniform05.t i) L *
          PiBinomial.pmf (2*Uniform07.capacity (N+2)) (1/2)
            (Uniform07.capacity (N+2)-L-1))*S/2 ≤
      (carrier i pi E).real univ*
        ((1+Uniform05.eta i)*width+err+
          Uniform05.eta i*u*((N+1:ℕ):ℝ)*Uniform05.t i*
            (realBidLaw i eps pi : Measure ℝ).real s*
              AtomEvents.duplicateEvent (Uniform05.zc i) (Uniform05.zc_probability_bounds i).1
                (Uniform05.zc_probability_bounds i).2 (N+2)) := by
  obtain ⟨r,hr,hmod⟩:=exists_actual_raise_modulus (M:=N+2) i a err ha herr
  refine ⟨r,hr,?_⟩
  intro eps heps pi hIC E hE d hd l u S width hal hS hw hwr s hs hbox
  let Γ:=carrier i pi E
  let ρ:=rivalDrawLaw i pi
  let ν:=Measure.pi (fun _ : Fin N=>ρ)
  let R:=Measure.pi (fun _ : Fin (N+1)=>ρ)
  let D:=deletedHarmfulEvent i N eps s
  let price:=(1+Uniform05.eta i)*width+err
  let cost:=Uniform05.eta i*u
  let F : LowerDraw i×(Fin (N+1)→ RivalDraw i)→ℝ:=fun p=>
    actualGain i (N+1) eps pi d p.1 p.2+price+(if p.2∈D then cost else 0)
  have hD : MeasurableSet D:=measurableSet_deletedHarmfulEvent i N eps s hs
  have hprice : 0≤ price:=by dsimp [price]; nlinarith [(Uniform05.eta_range i).1]
  have hwidthprice : width≤ price:=by
    dsimp [price]
    nlinarith [mul_nonneg (Uniform05.eta_range i).1.le hw]
  by_cases hz : Γ univ=0
  · have hz' : Γ.real univ=0:=by simp only [Measure.real,hz,ENNReal.toReal_zero]
    simp only [Γ] at hz'
    simp [hz']
  have hΓpos : 0<Γ.real univ:=ENNReal.toReal_pos hz (measure_ne_top Γ univ)
  have hu : 0≤ u := by
    by_contra hneg
    have hempty : ∀ᵐp∂Γ,False:=hbox.mono (fun p hp=> by
      have h:= (ha.le.trans hal).trans (hp.1.trans hp.2.1)
      exact hneg h)
    exact hz (by simpa [ae_iff] using hempty)
  have hcost : 0≤ cost:=mul_nonneg (Uniform05.eta_range i).1.le hu
  have hFm : Measurable F:=
    ((measurable_actualGain i (N+1) eps pi d hd).add measurable_const).add
      (Measurable.ite (hD.preimage measurable_snd) measurable_const measurable_const)
  have hFb (p) : |F p|≤6*Uniform05.t i+price+cost := by
    have hgain:=actualGain_bound i (N+1) eps pi d p.1 p.2
    have h1:=abs_add_le (actualGain i (N+1) eps pi d p.1 p.2) price
    have h2:=abs_add_le (actualGain i (N+1) eps pi d p.1 p.2+price)
      (if p.2∈D then cost else 0)
    dsimp only [F]
    rw [abs_of_nonneg hprice] at h1
    split_ifs at h2 ⊢ <;> simp only [abs_of_nonneg hcost,abs_zero] at h2 <;> linarith
  have hFi (μ : Measure (LowerDraw i×(Fin (N+1)→ RivalDraw i))) [IsFiniteMeasure μ] :
      Integrable F μ:=Integrable.of_bound hFm.aestronglyMeasurable _
        (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using hFb p))
  have hpos : ∀ᵐp∂Γ,∀ω : Fin (N+1)→ RivalDraw i,0≤ F (p,ω) := by
    filter_upwards [hbox] with p hp
    intro ω
    let kind:=fun j=>(ω j).1
    let old:=drawBid i eps p
    let new:=drawBid i eps ((p.1.1,d p.1),p.2)
    let x : OwnBid.Box i (N+2):=(p.1.1,restrictedLaw i (eps,pi),
      ActualSurplus.cappedFocalBids i kind old (fun j=> drawBid i eps (ω j).2))
    have hb : SourceContinuity.bids i x.2=focalBids i kind old
        (fun j=> drawBid i eps (ω j).2):=ActualSurplus.cappedFocalBids_val _ _ _ _
    have hupdate : SourceContinuity.bids i (OwnBid.change i x 0 new).2=
        focalBids i kind new (fun j=> drawBid i eps (ω j).2) := by
      rw [OwnBid.bids_change,hb]
      funext a
      refine Fin.cases ?_ (fun j=>?_) a <;> simp [focalBids]
    have hh:=hmod (focalRow kind) 0 (ActualSurplus.focalRow_focal_mem _) x new
      (by simpa only [hb,focalBids_zero] using hal.trans hp.1)
      (by rw [hb,focalBids_zero]; change noisyRealBid i eps p.1.1 p.1.2 p.2≤(p.1.1:ℝ)
          exact (noisyRealBid_bounds i eps p.1.1 p.1.2 p.2).2.trans (min_le_left _ _))
      (by simpa only [hb,focalBids_zero] using hp.2.1.trans_lt hp.2.2.1)
      (by simpa only [hb,focalBids_zero] using
        (show (new:ℝ)-(old:ℝ)≤ width by dsimp only [old,new]; linarith [hp.1,hp.2.2.2.2.1]).trans_lt hwr)
    rw [hb,hupdate] at hh
    have hevent : pureDuplicateGain i (focalRow kind)
        (focalBids i kind old (fun j=> drawBid i eps (ω j).2)) 0 new→ω∈D := by
      intro hd'
      exact duplicate_subset_deletedHarmful i N (by omega) eps p.1.1 p.1.2 p.2 ω new
        (ha.trans_le (hal.trans hp.1)) (hp.2.1.trans_lt hp.2.2.1) new.property.2 s
        hp.2.2.2.2.2.1 hp.2.2.2.2.2.2 hd'
    have hloss : (if pureDuplicateGain i (focalRow kind)
        (focalBids i kind old (fun j=> drawBid i eps (ω j).2)) 0 new
        then Uniform05.eta i*(old:ℝ) else 0)≤(if ω∈D then cost else 0) := by
      by_cases hdup : pureDuplicateGain i (focalRow kind)
        (focalBids i kind old (fun j=> drawBid i eps (ω j).2)) 0 new
      · rw [if_pos hdup,if_pos (hevent hdup)]
        exact mul_le_mul_of_nonneg_left hp.2.1 (Uniform05.eta_range i).1.le
      · rw [if_neg hdup]
        split_ifs
        · exact hcost
        · exact le_rfl
    have hprice' : (1+Uniform05.eta i)*((new:ℝ)-(old:ℝ))+err≤ price := by
      dsimp only [price]
      have hc : (new:ℝ)-(old:ℝ)≤ width:=by dsimp only [old,new]; linarith [hp.1,hp.2.2.2.2.1]
      nlinarith [mul_le_mul_of_nonneg_left hc (by linarith [(Uniform05.eta_range i).1] : 0≤1+Uniform05.eta i)]
    dsimp only [F]
    change -(if pureDuplicateGain i (focalRow kind)
      (focalBids i kind old (fun j=> drawBid i eps (ω j).2)) 0 new then
        Uniform05.eta i*(old:ℝ) else 0)-
      (1+Uniform05.eta i)*((new:ℝ)-(old:ℝ))-err≤
        actualGain i (N+1) eps pi d p ω at hh
    linarith
  let B : (Fin N→ RivalDraw i)×(LowerDraw i×LowerDraw i)→ℝ:=fun q=>
    if remainingH i N L eps u q.1 ∧ rejectPair i eps q.1
      (drawBid i eps q.2.1) (drawBid i eps q.2.2) then 1 else 0
  have hBm : Measurable B:= by
    convert! Measurable.ite
      (((measurable_remainingH i N L eps u).preimage measurable_fst).inter
      ((measurable_rejectPair i N eps).preimage
        (measurable_fst.prodMk
          ((measurable_subtype_coe.comp ((measurable_drawBid i eps).comp
            (measurable_fst.comp measurable_snd))).prodMk
            (measurable_subtype_coe.comp ((measurable_drawBid i eps).comp
              (measurable_snd.comp measurable_snd)))))))
      (measurable_const (a:=(1:ℝ))) (measurable_const (a:=(0:ℝ))) using 1
  have hBi : Integrable B (ν.prod (Γ.prod Γ)):=Integrable.of_bound hBm.aestronglyMeasurable 1
    (ae_of_all _ (fun q=> by dsimp only [B]; split_ifs <;> norm_num))
  let Fc : (Fin N→ RivalDraw i)×(LowerDraw i×LowerDraw i)→ℝ:=fun q=>
    F (q.2.1,Fin.cons (0,q.2.2) q.1)
  have hFcm : Measurable Fc:=hFm.comp
    ((measurable_fst.comp measurable_snd).prodMk (by fun_prop))
  have hFci : Integrable Fc (ν.prod (Γ.prod Γ)):=Integrable.of_bound hFcm.aestronglyMeasurable _
    (ae_of_all _ (fun q=> by simpa only [Real.norm_eq_abs] using hFb (q.2.1,Fin.cons (0,q.2.2) q.1)))
  have hpoint : ∀ᵐq∂ν.prod (Γ.prod Γ),S*B q≤ Fc q := by
    have hp:= (Measure.quasiMeasurePreserving_snd (μ:=ν) (ν:=Γ.prod Γ)).ae
      ((Measure.quasiMeasurePreserving_fst (μ:=Γ) (ν:=Γ)).ae hbox)
    have hq:= (Measure.quasiMeasurePreserving_snd (μ:=ν) (ν:=Γ.prod Γ)).ae
      ((Measure.quasiMeasurePreserving_snd (μ:=Γ) (ν:=Γ)).ae hbox)
    have hn:= (Measure.quasiMeasurePreserving_snd (μ:=ν) (ν:=Γ.prod Γ)).ae
      ((Measure.quasiMeasurePreserving_fst (μ:=Γ) (ν:=Γ)).ae hpos)
    filter_upwards [hp,hq,hn] with q hp hq hn
    by_cases hH : remainingH i N L eps u q.1
    · have hh:=actual_gain_on_H i N L hN hroom eps pi d q.1 q.2.1 q.2.2
        l u S width hu hH ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1⟩ hq.2.1
      have he : 0≤(if Fin.cons (0,q.2.2) q.1∈D then cost else 0):=by
        split_ifs
        · exact hcost
        · exact le_rfl
      dsimp only [B,Fc,F]
      simp only [hH,true_and]
      split_ifs at hh ⊢ <;> nlinarith
    · simp only [B,hH,false_and,if_false,mul_zero]
      exact hn _
  have hbonus := integral_mono_ae (hBi.const_mul S) hFci hpoint
  rw [integral_const_mul,integral_prod _ hBi,integral_prod _ hFci] at hbonus
  have hpair:=finite_original_pair_rejection i N L hN hroom eps heps pi E u hu
    (hbox.mono (fun _ hp=> hp.2.1))
  have hpairS:=mul_le_mul_of_nonneg_left hpair hS
  have hcons : Integrable (fun q : (Fin N→ RivalDraw i)×(LowerDraw i×RivalDraw i)=>
      F (q.2.1,Fin.cons q.2.2 q.1)) (ν.prod (Γ.prod ρ)):=
    (measurePreserving_carrierRow Γ ρ).integrable_comp_of_integrable (hFi (Γ.prod R))
  have hlow : Uniform05.t i*(∫ω,∫p : LowerDraw i×LowerDraw i,F (p.1,Fin.cons (0,p.2) ω)
      ∂Γ.prod Γ ∂ν)≤
      ∫ω,∫p : LowerDraw i×RivalDraw i,F (p.1,Fin.cons p.2 ω) ∂Γ.prod ρ ∂ν := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hFci.integral_prod_left.const_mul _) hcons.integral_prod_left
    exact ae_of_all _ (fun ω=> by
      have hm:=hFm.comp (measurable_fst.prodMk (by fun_prop :
        Measurable (fun p : LowerDraw i×RivalDraw i=> Fin.cons p.2 ω)))
      have hi : Integrable (fun p : LowerDraw i×RivalDraw i=> F (p.1,Fin.cons p.2 ω))
          (Γ.prod ρ):=Integrable.of_bound hm.aestronglyMeasurable _
            (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using hFb (p.1,Fin.cons p.2 ω)))
      have hi' : Integrable (fun p : LowerDraw i×LowerDraw i=> F (p.1,Fin.cons (0,p.2) ω))
          (Γ.prod Γ):=Integrable.of_bound
            (hFcm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable _
              (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using hFb (p.1,Fin.cons (0,p.2) ω)))
      change Uniform05.t i*(∫p : LowerDraw i×LowerDraw i,F (p.1,Fin.cons (0,p.2) ω) ∂Γ.prod Γ)≤
        ∫p : LowerDraw i×RivalDraw i,F (p.1,Fin.cons p.2 ω) ∂Γ.prod ρ
      rw [integral_prod _ hi,integral_prod _ hi']
      exact lower_carrier_integral_le i pi E _ hm _
        (fun p=> hFb (p.1,Fin.cons p.2 ω)) (hpos.mono (fun p hp r=> hp _)))
  rw [← integral_prod _ hcons,integral_carrierRow Γ ρ F hFm (hFi _)] at hlow
  have hupper : (∫p : LowerDraw i,(∫ω : Fin (N+1)→RivalDraw i,F (p,ω) ∂ R) ∂ Γ)≤
      Γ.real univ*(price+cost*R.real D) := by
    have hconst : Integrable (fun p : LowerDraw i×(Fin (N+1)→ RivalDraw i)=>
        price+(if p.2∈D then cost else 0)) (Γ.prod R):=
      (integrable_const _).add ((integrable_const cost).indicator (hD.preimage measurable_snd))
    have hFassoc : F=(fun p=> actualGain i (N+1) eps pi d p.1 p.2+
        (price+(if p.2∈D then cost else 0))) := by funext p; dsimp [F]; ring
    have hig : Integrable (fun p : LowerDraw i×(Fin (N+1)→RivalDraw i)=>
        actualGain i (N+1) eps pi d p.1 p.2) (Γ.prod R) :=
      integrable_actualGain i (N+1) eps pi d hd Γ
    rw [← integral_prod _ (hFi _),hFassoc]
    have hadd : (∫p : LowerDraw i×(Fin (N+1)→RivalDraw i),
        actualGain i (N+1) eps pi d p.1 p.2+(price+(if p.2∈D then cost else 0)) ∂Γ.prod R)=
        (∫p : LowerDraw i×(Fin (N+1)→RivalDraw i),actualGain i (N+1) eps pi d p.1 p.2 ∂Γ.prod R)+
        ∫p : LowerDraw i×(Fin (N+1)→RivalDraw i),price+(if p.2∈D then cost else 0) ∂Γ.prod R := by
      convert! integral_add hig hconst using 1
    change (∫p : LowerDraw i×(Fin (N+1)→RivalDraw i),
        actualGain i (N+1) eps pi d p.1 p.2+(price+(if p.2∈D then cost else 0)) ∂Γ.prod R)≤ _
    rw [hadd,integral_prod _ hig]
    have hIC':=integrated_gain_nonpos i (N+1) eps pi hIC E d hd
    have hrest : (∫p : LowerDraw i×(Fin (N+1)→ RivalDraw i),
        price+(if p.2∈D then cost else 0) ∂Γ.prod R)=Γ.real univ*(price+cost*R.real D) := by
      rw [integral_prod _ hconst]
      have hind : (∫ω : Fin (N+1)→RivalDraw i,(if ω∈D then cost else 0) ∂ R)=R.real D*cost := by
        simpa only [Set.indicator,smul_eq_mul] using integral_indicator_const (μ:=R) cost hD
      have hinner : (∫ω : Fin (N+1)→RivalDraw i,price+(if ω∈D then cost else 0) ∂ R)=
          price+cost*R.real D := by
        have hsplit := integral_add (integrable_const price : Integrable (fun _ : Fin (N+1)→RivalDraw i=>price) R)
          ((integrable_const cost).indicator hD)
        simpa only [Set.indicator,integral_const,probReal_univ,smul_eq_mul,one_mul,hind,mul_comm] using hsplit
      change (∫_ : LowerDraw i,(∫ω : Fin (N+1)→RivalDraw i,price+(if ω∈D then cost else 0) ∂ R) ∂ Γ)=_
      rw [hinner,integral_const]
      simp only [smul_eq_mul]
    rw [hrest]
    linarith
  have hEprob:=deletedHarmfulEvent_probability i N eps pi s hs
  have hreal : ((restrictedLaw i (eps,pi)).bidLaw : Measure (Bid i)).real
      ((Subtype.val : Bid i→ℝ) ⁻¹' s)=(realBidLaw i eps pi : Measure ℝ).real s := by
    rw [realBidLaw,ProbabilityMeasure.toMeasure_map,← restrictedLaw_bidLaw]
    simp only [Measure.real,Measure.map_apply measurable_subtype_coe hs]
  rw [hreal] at hEprob
  have htail:=mul_le_mul_of_nonneg_left hEprob hcost
  have htail':=mul_le_mul_of_nonneg_left (add_le_add_right htail price) (measureReal_nonneg (μ:=Γ) (s:=univ))
  have hlift:=mul_le_mul_of_nonneg_left hbonus (Uniform05.t_pos i).le
  have hfinal:=((mul_le_mul_of_nonneg_left hpairS (Uniform05.t_pos i).le).trans hlift).trans
    (hlow.trans (hupper.trans htail'))
  dsimp only [Γ,price,cost,D,R,ν,B,Fc] at hfinal
  convert! hfinal using 1 <;> ring

end OriginalGain
end FCAppendix.Affine.UniformFinite
