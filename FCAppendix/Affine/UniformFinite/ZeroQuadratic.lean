import FCAppendix.Affine.UniformFinite.OriginalQuadratic
import FCAppendix.Affine.UniformFinite.PositiveClusters
import FCAppendix.Affine.LowBody.ZeroClusterLimit

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional
open scoped BigOperators
namespace ZeroAtoms
open OriginalGain ActualAtoms

theorem shifted_gain_quadratic (i : Row) (N L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (eps : unitInterval) (heps : 0<(eps:ℝ)) (pi : Joint i)
    (hIC : NoisyIC i (N+1) eps pi)
    (E : Set (Value i×unitInterval)) (d : Value i×unitInterval→ unitInterval)
    (hd : Measurable d) (l u S width cost : ℝ) (hu : 0≤ u) (hS : 0≤ S)
    (hwidth : 0≤ width) (hcost : width≤ cost)
    (hbox : ∀ᵐp∂carrier i pi E,
      l≤(drawBid i eps p:ℝ) ∧ (drawBid i eps p:ℝ)≤ u ∧
      u<(drawBid i eps ((p.1.1,d p.1),p.2):ℝ) ∧
      S≤(p.1.1:ℝ)-(drawBid i eps p:ℝ) ∧
      (drawBid i eps ((p.1.1,d p.1),p.2):ℝ)-l≤ width)
    (hloss : ∀ᵐp∂carrier i pi E,∀ω : Fin (N+1)→ RivalDraw i,
      -cost≤ actualGain i (N+1) eps pi d p ω) :
    (carrier i pi E).real univ^2*Uniform05.t i*
      (PiBinomial.pmf N (Uniform05.t i) L *
        PiBinomial.pmf (2*Uniform07.capacity (N+2)) (1/2)
          (Uniform07.capacity (N+2)-L-1))*S/2 ≤
        (carrier i pi E).real univ*cost := by
  let Γ:=carrier i pi E
  let ρ:=rivalDrawLaw i pi
  let ν:=Measure.pi (fun _ : Fin N=>ρ)
  let R:=Measure.pi (fun _ : Fin (N+1)=>ρ)
  let F : LowerDraw i×(Fin (N+1)→ RivalDraw i)→ℝ:=fun p=>
    actualGain i (N+1) eps pi d p.1 p.2+cost
  have hc0 : 0≤ cost:=hwidth.trans hcost
  have hFm : Measurable F:=(measurable_actualGain i (N+1) eps pi d hd).add measurable_const
  have hFb (p) : |F p|≤6*Uniform05.t i+cost := by
    exact (abs_add_le _ _).trans (by
      rw [abs_of_nonneg hc0]
      exact add_le_add_left (actualGain_bound i (N+1) eps pi d p.1 p.2) cost)
  have hFi (μ : Measure (LowerDraw i×(Fin (N+1)→ RivalDraw i))) [IsFiniteMeasure μ] :
      Integrable F μ:=Integrable.of_bound hFm.aestronglyMeasurable _
        (ae_of_all _ (fun p=> by simpa only [Real.norm_eq_abs] using hFb p))
  have hpos : ∀ᵐp∂Γ,∀ω : Fin (N+1)→ RivalDraw i,0≤ F (p,ω) :=
    hloss.mono (fun p hp ω=> by have h:=hp ω; dsimp only [F]; linarith)
  let B : (Fin N→ RivalDraw i)×(LowerDraw i×LowerDraw i)→ℝ:=fun q=>
    if remainingH i N L eps u q.1 ∧ rejectPair i eps q.1
      (drawBid i eps q.2.1) (drawBid i eps q.2.2) then 1 else 0
  have hBm : Measurable B:=by
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
        l u S width hu hH hp hq.2.1
      dsimp only [B,Fc,F]
      simp only [hH,true_and]
      split_ifs at hh ⊢ <;> linarith
    · simp only [B,hH,false_and,if_false,mul_zero]
      exact hn _
  have hbonus:=integral_mono_ae (hBi.const_mul S) hFci hpoint
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
  have hupper : (∫p : LowerDraw i,(∫ω : Fin (N+1)→RivalDraw i,F (p,ω) ∂ R) ∂ Γ)≤Γ.real univ*cost := by
    have hig : Integrable (fun p : LowerDraw i×(Fin (N+1)→RivalDraw i)=>
        actualGain i (N+1) eps pi d p.1 p.2) (Γ.prod R) :=
      integrable_actualGain i (N+1) eps pi d hd Γ
    have hadd : (∫p : LowerDraw i×(Fin (N+1)→RivalDraw i),F p ∂Γ.prod R)=
        (∫p : LowerDraw i×(Fin (N+1)→RivalDraw i),actualGain i (N+1) eps pi d p.1 p.2 ∂Γ.prod R)+
        ∫_ : LowerDraw i×(Fin (N+1)→RivalDraw i),cost ∂Γ.prod R := by
      convert! integral_add hig (integrable_const cost) using 1
    rw [← integral_prod _ (hFi _),hadd,integral_prod _ hig,integral_const]
    have hm : (Γ.prod R).real univ=Γ.real univ:=by
      rw [← univ_prod_univ,measureReal_prod_prod]
      simp
    rw [hm]
    have hh:=integrated_gain_nonpos i (N+1) eps pi hIC E d hd
    simpa only [smul_eq_mul,zero_add,add_comm] using add_le_add_right hh (Γ.real univ*cost)
  have ht:=Uniform05.t_pos i
  have h:=((mul_le_mul_of_nonneg_left hpairS ht.le).trans
    (mul_le_mul_of_nonneg_left hbonus ht.le)).trans (hlow.trans hupper)
  convert! h using 1; ring

def cluster (i : Row) (tau δ : ℝ) : Set (Value i×unitInterval) :=
  {p | tau<(p.1:ℝ) ∧ (baseBid i p:ℝ)<δ}

lemma isOpen_cluster (i : Row) (tau δ : ℝ) : IsOpen (cluster i tau δ) :=
  (isOpen_lt continuous_const continuous_fst.subtype_val).inter
    (isOpen_lt (continuous_baseBid i).subtype_val continuous_const)

def deviation (i : Row) (δ : ℝ) (p : Value i×unitInterval) : unitInterval :=
  choiceForBid i p.1 (3*δ)

lemma measurable_deviation (i : Row) (δ : ℝ) : Measurable (deviation i δ) :=
  (measurable_choiceForBid i).comp (measurable_fst.prodMk measurable_const)

theorem finite_zero_cluster_estimates (i : Row) (N L : ℕ)
    (hN : N=L+2*Uniform07.capacity (N+2))
    (hroom : L+1< Uniform07.capacity (N+2))
    (eps : ℕ→ unitInterval) (pi : ℕ→ Joint i)
    (hepspos : ∀j,0<(eps j:ℝ)) (heps0 : Tendsto eps atTop (𝓝 0))
    (hIC : ∀j,NoisyIC i (N+1) (eps j) (pi j)) :
    ∀tau : ℝ,0< tau→∀err : ℝ,0< err→∃δmax>0,
      ∀δ : ℝ,0<δ→δ<δmax→∀ᶠj in atTop,
        ((pi j).1 : Measure (Value i×unitInterval)).real (cluster i tau δ)^2*
          (Uniform05.t i*PositiveClusters.sourceH i (N+2)*tau/4) ≤
        ((pi j).1 : Measure (Value i×unitInterval)).real (cluster i tau δ)*(10*δ+err) := by
  intro tau htau err herr
  obtain ⟨r,hr,hmod⟩:=exists_actual_zero_raise_modulus (M:=N+2) i herr
  let dmax:=min (r/5) (min (tau/4) (Uniform05.cap i/4))
  have hdmax : 0< dmax:=lt_min (by positivity) (lt_min (by positivity) (by have hs:=Uniform05.cap_pos i; positivity))
  refine ⟨dmax,hdmax,?_⟩
  intro δ hδ hδmax
  have hδr : 4*δ< r:=by have h:=hδmax.trans_le (min_le_left _ _); linarith
  have hδv : 4*δ< tau:=by have h:=hδmax.trans_le ((min_le_right _ _).trans (min_le_left _ _)); linarith
  have hδcap : 4*δ< Uniform05.cap i:=by
    have h:=hδmax.trans_le ((min_le_right _ _).trans (min_le_right _ _)); linarith
  have hnoise : ∀ᶠj in atTop,(eps j:ℝ)*Uniform05.t i<δ/2 :=
    (((continuous_subtype_val.tendsto 0).comp heps0).mul_const (Uniform05.t i)).eventually_lt_const
      (by simpa using half_pos hδ)
  filter_upwards [hnoise] with j hj
  let Γ:=carrier i (pi j) (cluster i tau δ)
  have hpre:=ae_restrict_mem (μ:=((pi j).1 : Measure (Value i×unitInterval)))
    (isOpen_cluster i tau δ).measurableSet
  have hpull:=(Measure.quasiMeasurePreserving_fst
    (μ:=((pi j).1 : Measure (Value i×unitInterval)).restrict (cluster i tau δ))
    (ν:=(volume : Measure unitInterval))).ae hpre
  have hgeo : ∀ᵐp∂Γ,
      0≤(drawBid i (eps j) p:ℝ) ∧ (drawBid i (eps j) p:ℝ)≤2*δ ∧
      2*δ<(drawBid i (eps j) ((p.1.1,deviation i δ p.1),p.2):ℝ) ∧
      tau/2≤(p.1.1:ℝ)-(drawBid i (eps j) p:ℝ) ∧
      (drawBid i (eps j) ((p.1.1,deviation i δ p.1),p.2):ℝ)-0≤4*δ := by
    filter_upwards [hpull] with p hp
    have hbase:=baseBid_feasible i p.1
    have hv : 0<(p.1.1:ℝ):=htau.trans hp.1
    have htarg : 3*δ∈Icc (Uniform05.floorBid i p.1.1) (hiBid i p.1.1):=
      ⟨by linarith [hbase.1,hp.2],le_min (by linarith [hp.1]) (by linarith)⟩
    have he1:=abs_le.mp (physical_base_error i (eps j) p.1 p.2)
    have he2:=abs_le.mp (feasible_target_noise_error i (eps j) p.1.1 hv (3*δ) htarg p.2)
    have hn : (eps j:ℝ)*(p.1.1:ℝ)<δ/2:=
      (mul_le_mul_of_nonneg_left p.1.1.property.2 (eps j).property.1).trans_lt hj
    refine ⟨(drawBid i (eps j) p).property.1,?_,?_,?_,?_⟩ <;>
      dsimp only [drawBid,deviation] at * <;> linarith [hp.1,hp.2]
  have hloss : ∀ᵐp∂Γ,∀ω : Fin (N+1)→ RivalDraw i,
      -(10*δ+err)≤ actualGain i (N+1) (eps j) (pi j) (deviation i δ) p ω := by
    filter_upwards [hgeo] with p hp
    intro ω
    let kind:=fun k=>(ω k).1
    let old:=drawBid i (eps j) p
    let new:=drawBid i (eps j) ((p.1.1,deviation i δ p.1),p.2)
    let x : OwnBid.Box i (N+2):=(p.1.1,restrictedLaw i (eps j,pi j),
      ActualSurplus.cappedFocalBids i kind old (fun k=> drawBid i (eps j) (ω k).2))
    have hb : SourceContinuity.bids i x.2=focalBids i kind old
        (fun k=> drawBid i (eps j) (ω k).2):=ActualSurplus.cappedFocalBids_val _ _ _ _
    have hnew : SourceContinuity.bids i (OwnBid.change i x 0 new).2=
        focalBids i kind new (fun k=> drawBid i (eps j) (ω k).2):=by
      rw [OwnBid.bids_change,hb]
      funext a
      refine Fin.cases ?_ (fun k=>?_) a <;> simp [focalBids]
    have h:=hmod (focalRow kind) 0 (ActualSurplus.focalRow_focal_mem _) x new
      (by rw [hb,focalBids_zero]; change noisyRealBid i (eps j) p.1.1 p.1.2 p.2≤(p.1.1:ℝ)
          exact (noisyRealBid_bounds i (eps j) p.1.1 p.1.2 p.2).2.trans (min_le_left _ _))
      (by simpa only [hb,focalBids_zero] using hp.2.1.trans_lt hp.2.2.1)
      (by simpa only [hb,focalBids_zero] using
        (show (new:ℝ)-(old:ℝ)≤4*δ by dsimp [new,old]; linarith [hp.1,hp.2.2.2.2]).trans_lt hδr)
    rw [hb,hnew] at h
    change -Uniform05.eta i*(old:ℝ)-(1+Uniform05.eta i)*((new:ℝ)-(old:ℝ))-err≤
      actualGain i (N+1) (eps j) (pi j) (deviation i δ) p ω at h
    have he:=Uniform05.eta_range i
    have hx : 0≤(old:ℝ)∧(old:ℝ)≤2*δ:=⟨hp.1,hp.2.1⟩
    have hy : (new:ℝ)≤4*δ:=by simpa only [sub_zero] using hp.2.2.2.2
    have hc1:=mul_le_mul_of_nonneg_left hx.2 he.1.le
    have hc2:=mul_le_mul_of_nonneg_left (show (new:ℝ)-(old:ℝ)≤4*δ by linarith)
      (show 0≤1+Uniform05.eta i by linarith)
    nlinarith
  have h:=shifted_gain_quadratic i N L hN hroom (eps j) (hepspos j) (pi j) (hIC j)
    (cluster i tau δ) (deviation i δ) (measurable_deviation i δ) 0 (2*δ) (tau/2)
    (4*δ) (10*δ+err) (by positivity) (by positivity) (by positivity) (by linarith) hgeo hloss
  rw [carrier_mass] at h
  have hH : (PiBinomial.pmf N (Uniform05.t i) L *
      PiBinomial.pmf (2*Uniform07.capacity (N+2)) (1/2)
        (Uniform07.capacity (N+2)-L-1))=PositiveClusters.sourceH i (N+2) := by
    have he : AtomEvents.otherLower (N+2)=L:=by dsimp [AtomEvents.otherLower]; omega
    simp only [PositiveClusters.sourceH,AtomEvents.boundaryEvent,Nat.add_sub_cancel,he]
  rw [hH] at h
  convert! h using 1; ring

end ZeroAtoms
end FCAppendix.Affine.UniformFinite
