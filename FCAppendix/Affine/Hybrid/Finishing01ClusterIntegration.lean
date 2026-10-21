import FCAppendix.Affine.Hybrid.Finishing01NoisyTransport
import FCAppendix.Affine.Hybrid.Finishing01ClusterPointwise
import FCAppendix.Affine.Hybrid.Finishing01ClusterMeasures

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01.Primitives
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional
open scoped BigOperators
variable (P : Primitives)

def clusterOld (eps : ℝ) (x : P.AgentNoise) : ℝ :=
  activeNoisyRealBid eps x.1.2 x.2

def clusterRaised (eps : ℝ) (target : P.Bid) (x : P.AgentNoise) : ℝ :=
  activeNoisyRealBid eps target x.2

lemma measurable_clusterOld' (eps : ℝ) : Measurable (P.clusterOld eps) := by
  unfold clusterOld activeNoisyRealBid
  fun_prop

lemma measurable_clusterRaised (eps : ℝ) (target : P.Bid) :
    Measurable (P.clusterRaised eps target) := by
  unfold clusterRaised activeNoisyRealBid
  fun_prop

lemma activeImplementedBidLaw_real (eps : unitInterval)
    (mu : Measure P.Value) [IsProbabilityMeasure mu] (pi : Law (A:=P.Bid) mu) :
    (activeImplementedBidLaw P.L_pos eps.property.1 mu pi :
      Measure (ActivePhysicalBid P.L P.U eps)).map Subtype.val=
        P.realImplementedActiveLaw mu eps pi := by
  change (((activeNoisyLaw P.L_pos eps.property.1 mu pi).1 :
      Measure (P.Value×ActivePhysicalBid P.L P.U eps)).map Prod.snd).map Subtype.val=_
  rw [Measure.map_map measurable_subtype_coe measurable_snd]
  change (((pi.1 : Measure P.Latent).prod (volume : Measure unitInterval)).map
    (fun x => (x.1.1,activeNoisyBid P.L_pos eps.property.1 x))).map
      (fun x => (x.2:ℝ))=_
  unfold realImplementedActiveLaw
  convert! Measure.map_map (show Measurable (fun x : P.Value × ActivePhysicalBid P.L P.U eps => (x.2 : ℝ)) from measurable_snd.subtype_val)
    (show Measurable (fun x : P.Latent × unitInterval => (x.1.1,activeNoisyBid P.L_pos eps.property.1 x)) from
      ((measurable_fst.comp measurable_fst).prodMk (continuous_activeNoisyBid P.L_pos eps.property.1).measurable)) using 1

theorem noisyNumericRows_active_coordinate {N : ℕ} (eps : unitInterval)
    (low : ProbabilityMeasure P.Low) (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) (j : Fin N) :
    (P.noisyNumericRows N eps low mu pi : Measure (P.NumericRows N eps)).map
      (fun r => (r.2 j:ℝ))=P.realImplementedActiveLaw mu eps pi := by
  let nu := activeImplementedBidLaw P.L_pos eps.property.1 mu pi
  change ((rowLaw N low : Measure (Fin N→ P.Low)).prod
    (rowLaw N nu : Measure (Fin N→ ActivePhysicalBid P.L P.U eps))).map
      (fun r => (r.2 j:ℝ))=_
  change ((rowLaw N low : Measure (Fin N → P.Low)).prod (rowLaw N nu : Measure (Fin N → ActivePhysicalBid P.L P.U eps))).map
    ((fun r : Fin N → ActivePhysicalBid P.L P.U eps => (r j : ℝ)) ∘ Prod.snd) = _
  rw [←Measure.map_map (((measurable_pi_apply j).subtype_val)) measurable_snd,
    Measure.map_snd_prod,measure_univ,one_smul]
  change (rowLaw N nu : Measure (Fin N → ActivePhysicalBid P.L P.U eps)).map (Subtype.val ∘ (fun r : Fin N → ActivePhysicalBid P.L P.U eps => r j)) = _
  rw [←Measure.map_map measurable_subtype_coe (measurable_pi_apply j),
    LowBody.rowLaw_eq_measure_pi,(measurePreserving_eval
      (fun _ : Fin N => (nu:Measure (ActivePhysicalBid P.L P.U eps))) j).map_eq]
  exact P.activeImplementedBidLaw_real eps mu pi

lemma integrable_actual_clusterGain {N : ℕ} (eps : unitInterval) (c : ℕ)
    (kind : Fin N→ Fin 4) (target : P.Bid)
    (Gamma : Measure P.AgentNoise) [IsFiniteMeasure Gamma]
    (R : Measure (P.NumericRows N eps)) [IsProbabilityMeasure R] :
    Integrable (P.clusterGain eps c kind target) (Gamma.prod R) :=
  Integrable.of_bound (P.measurable_clusterGain eps c kind target).aestronglyMeasurable
    (2*P.payoffBound) (ae_of_all _ (fun p => by
      simpa only [Real.norm_eq_abs] using P.abs_clusterGain eps c kind target p))

lemma cluster_envelope_coordinate_mass {N : ℕ} (eps : unitInterval)
    (low : ProbabilityMeasure P.Low) (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) (Gamma : Measure P.AgentNoise) [IsFiniteMeasure Gamma]
    (j : Fin N) (l u : ℝ) :
    (Gamma.prod (P.noisyNumericRows N eps low mu pi : Measure (P.NumericRows N eps))).real
      {p : P.AgentNoise × P.NumericRows N eps | (p.2.2 j:ℝ)∈ Icc l u}=
      Gamma.real univ*(P.realImplementedActiveLaw mu eps pi).real (Icc l u) := by
  have hset : {p : P.AgentNoise×P.NumericRows N eps | (p.2.2 j:ℝ)∈ Icc l u}=
      (univ : Set P.AgentNoise)×ˢ{r : P.NumericRows N eps | (r.2 j:ℝ)∈ Icc l u} := by
    ext p
    simp
  rw [hset,measureReal_prod_prod]
  congr 1
  have hm := congrArg (fun nu : Measure ℝ => nu (Icc l u))
    (P.noisyNumericRows_active_coordinate eps low mu pi j)
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc] at hm
  exact congrArg ENNReal.toReal hm

theorem actual_cluster_lower (N c : ℕ) {err : ℝ} (herr : 0< err) :
    ∃delta : ℝ,0< delta ∧ ∀(eps : unitInterval)
      (low : ProbabilityMeasure P.Low) (mu : Measure P.Value) [IsProbabilityMeasure mu]
      (pi : Law (A:=P.Bid) mu) (E : Set P.Latent) (target : P.Bid)
      (l upperCluster u step : ℝ),0≤ step→
      (∀ kind : Fin N→ Fin 4,∀ t : ActivePhysicalData N,
        activePhysicalPatternPayoff P.xi P.z P.L (P.U*(1+(eps:ℝ))) c kind t=
          activePhysicalPatternPayoff P.xi P.z P.L P.U c kind t)→
      (∀ᵐb ∂P.realImplementedActiveLaw mu eps pi,b∈ Icc P.L P.U)→
      (∀ᵐx ∂P.activeLatentClusterCarrier mu pi E,
        P.clusterOld eps x∈ Icc P.L P.U ∧
        P.clusterRaised eps target x∈ Icc P.L P.U ∧
        P.clusterOld eps x< P.clusterRaised eps target x ∧
        P.clusterRaised eps target x-P.clusterOld eps x< delta ∧
        P.clusterRaised eps target x-P.clusterOld eps x≤ step ∧
        l≤ P.clusterOld eps x ∧ P.clusterOld eps x≤ upperCluster ∧
        upperCluster≤ P.clusterRaised eps target x ∧ P.clusterRaised eps target x≤ u)→
      let Gamma := P.activeLatentClusterCarrier mu pi E
      let p := Gamma.real univ
      let G := P.realImplementedActiveLaw mu eps pi
      let R := P.noisyNumericRows N eps low mu pi
      P.clusterRankGain/(16*((N+1:ℕ):ℝ)^3)*
          (CommonList.iid P.categories N).prob
            (activePatternGuarded P.xi P.L P.U c P.z)*p^2-
        P.eta*P.U*(N:ℝ)*(CommonList.iid P.categories N).prob
          (activePatternPure P.xi P.L P.U c P.z)*p*G.real (Icc l u)-
        p*(err+2*P.kappa*step) ≤
      ∑kind : Fin N→ Fin 4,(CommonList.iid P.categories N).mass kind*
        ∫q,P.clusterGain eps c kind target q ∂Gamma.prod (R : Measure _) := by
  obtain ⟨delta,hd,hmod⟩ := P.all_pattern_cluster_modulus N c herr
  refine ⟨delta,hd,?_⟩
  intro eps low mu _ pi E target l upperCluster u step hstep hstable hGbox hgeo
  let Gamma := P.activeLatentClusterCarrier mu pi E
  let R := P.noisyNumericRows N eps low mu pi
  let G := P.realImplementedActiveLaw mu eps pi
  let p := Gamma.real univ
  let g := P.clusterRankGain/(8*((N+1:ℕ):ℝ)^3)
  let C := CommonList.iid P.categories N
  have hp : 0≤ p := measureReal_nonneg
  have hg : 0≤ g := by
    dsimp [g]
    exact div_nonneg P.clusterRankGain_pos.le (by positivity)
  have hEta : 0≤ P.eta*P.U := mul_nonneg P.eta_pos.le P.U_pos.le
  have hKappa : 0≤ P.kappa := P.kappa_pos.le
  have hrows : ∀ᵐr ∂(R:Measure (P.NumericRows N eps)),∀ j : Fin N,(r.2 j:ℝ)∈ Icc P.L P.U := by
    apply ae_all_iff.mpr
    intro j
    have hh : ∀ᵐb ∂(R:Measure (P.NumericRows N eps)).map (fun r => (r.2 j:ℝ)),
        b∈ Icc P.L P.U := by
      rw [P.noisyNumericRows_active_coordinate eps low mu pi j]
      exact hGbox
    exact (ae_map_iff (by fun_prop) measurableSet_Icc).mp hh
  have hQ (kind : Fin N→ Fin 4) : Integrable (P.clusterGain eps c kind target) (Gamma.prod (R:Measure (P.NumericRows N eps))) :=
    P.integrable_actual_clusterGain eps c kind target Gamma (R:Measure (P.NumericRows N eps))
  have hpoint (kind : Fin N→ Fin 4) :
      (if activePatternGuarded P.xi P.L P.U c P.z kind then g*p^2/2 else 0)-
        (if activePatternPure P.xi P.L P.U c P.z kind then P.eta*P.U*(N:ℝ)*p*G.real (Icc l u) else 0)-
        p*(err+2*P.kappa*step) ≤
      ∫q,P.clusterGain eps c kind target q ∂Gamma.prod (R:Measure (P.NumericRows N eps)) := by
    by_cases hguard : activePatternGuarded P.xi P.L P.U c P.z kind
    · obtain ⟨j,hj,hgain⟩ := (hmod kind).1 hguard
      let A : Set (P.AgentNoise×P.NumericRows N eps) :=
        {q | (q.2.2 j:ℝ)∈ Icc (P.clusterOld eps q.1) (P.clusterRaised eps target q.1)}
      have hA : MeasurableSet A :=
        (measurableSet_le ((P.measurable_clusterOld' eps).comp measurable_fst) (by fun_prop)).inter
          (measurableSet_le (by fun_prop) ((P.measurable_clusterRaised eps target).comp measurable_fst))
      let f := fun q : P.AgentNoise×P.NumericRows N eps => g*(A.indicator (fun _ => (1:ℝ)) q)-err
      have hfm : Measurable f := (measurable_const.mul (measurable_const.indicator hA)).sub measurable_const
      have hfi : Integrable f (Gamma.prod (R:Measure (P.NumericRows N eps))) :=
        (((integrable_const (1:ℝ)).indicator hA).const_mul g).sub (integrable_const err)
      have hle : ∀ᵐq ∂Gamma.prod (R:Measure (P.NumericRows N eps)),f q≤ P.clusterGain eps c kind target q := by
        apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hfm (P.measurable_clusterGain eps c kind target))).mpr
        filter_upwards [hgeo] with x hx
        filter_upwards [hrows] with r hr
        let t : P.ClusterBox N := (x.1.1,⟨P.clusterOld eps x,hx.1⟩,
          r.1,fun j => ⟨(r.2 j:ℝ),hr j⟩)
        let y : P.Bid := ⟨P.clusterRaised eps target x,hx.2.1⟩
        have hh := hgain t y hx.2.2.1 hx.2.2.2.1
        have heq : P.clusterGain eps c kind target (x,r)=P.clusterBoxGain c kind t y := by
          unfold clusterGain clusterBoxGain
          rw [hstable,hstable]
          rfl
        rw [heq]
        simpa only [f,A,Set.indicator,Set.mem_setOf_eq,g,t,y] using hh
      have hInt := integral_mono_ae hfi (hQ kind) hle
      rw [integral_sub (((integrable_const (1:ℝ)).indicator hA).const_mul g) (integrable_const err),
        integral_const_mul,integral_indicator_const (1:ℝ) hA,integral_const] at hInt
      simp only [smul_eq_mul,mul_one] at hInt
      have hmassProd : (Gamma.prod (R:Measure (P.NumericRows N eps))).real univ=p := by
        rw [←univ_prod_univ,measureReal_prod_prod,probReal_univ (μ := (R : Measure (P.NumericRows N eps))),mul_one]
      rw [hmassProd] at hInt
      have hMap := prod_crossing_mass_map Gamma (R:Measure (P.NumericRows N eps)) G (P.clusterOld eps)
        (P.clusterRaised eps target) (P.measurable_clusterOld' eps) (P.measurable_clusterRaised eps target)
        (fun r : P.NumericRows N eps => (r.2 j:ℝ)) (by fun_prop)
        (P.noisyNumericRows_active_coordinate eps low mu pi j)
      have hGainMass := retained_crossing_mass_lower Gamma G (P.clusterOld eps)
        (P.clusterRaised eps target) (P.measurable_clusterOld' eps) (P.measurable_clusterRaised eps target)
        (P.activePhysicalClusterMeasure_le mu eps pi E) upperCluster
        (hgeo.mono (fun x hx => hx.2.2.2.2.2.2.1))
        (hgeo.mono (fun x hx => hx.2.2.2.2.2.2.2.1))
      change p^2/2≤ _ at hGainMass
      rw [←hMap] at hGainMass
      have hscaled := mul_le_mul_of_nonneg_left hGainMass hg
      have hnotPure : ¬activePatternPure P.xi P.L P.U c P.z kind := fun h => h.1 hguard
      simp only [if_pos hguard,if_neg hnotPure,sub_zero]
      have hpay : 0≤ p*(2*P.kappa*step) := by positivity
      change g*(Gamma.prod (R:Measure (P.NumericRows N eps))).real A- p*err≤ _ at hInt
      linarith
    · by_cases heq : (activePatternTemplate c kind).residual₀=(activePatternTemplate c kind).residual₁
      · have hle : ∀ᵐq ∂Gamma.prod (R:Measure (P.NumericRows N eps)),-err≤ P.clusterGain eps c kind target q := by
          apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_const
            (P.measurable_clusterGain eps c kind target))).mpr
          filter_upwards [hgeo] with x hx
          filter_upwards [hrows] with r hr
          let t : P.ClusterBox N := (x.1.1,⟨P.clusterOld eps x,hx.1⟩,
            r.1,fun j => ⟨(r.2 j:ℝ),hr j⟩)
          let y : P.Bid := ⟨P.clusterRaised eps target x,hx.2.1⟩
          have hh := (hmod kind).2 hguard heq t y hx.2.2.1 hx.2.2.2.1
          have hident : P.clusterGain eps c kind target (x,r)=P.clusterBoxGain c kind t y := by
            unfold clusterGain clusterBoxGain
            rw [hstable,hstable]
            rfl
          rwa [hident]
        have hInt := integral_mono_ae (integrable_const (-err)) (hQ kind) hle
        rw [integral_const,←univ_prod_univ,measureReal_prod_prod,probReal_univ (μ := (R : Measure (P.NumericRows N eps))),mul_one] at hInt
        have hnotPure : ¬activePatternPure P.xi P.L P.U c P.z kind := fun h => h.2 heq
        simp only [if_neg hguard,if_neg hnotPure,sub_zero,zero_sub]
        have hpay : 0≤ p*(2*P.kappa*step) := by positivity
        simpa only [smul_eq_mul, neg_mul] using (show -p*(err+2*P.kappa*step)≤ _ from by
          change p*(-err)≤ _ at hInt
          linarith)
      · have hpure : activePatternPure P.xi P.L P.U c P.z kind := ⟨hguard,heq⟩
        let B : Fin N→ Set (P.AgentNoise×P.NumericRows N eps) :=
          fun j => {q | (q.2.2 j:ℝ)∈ Icc l u}
        have hB (j : Fin N) : MeasurableSet (B j) :=
          measurableSet_Icc.preimage (by fun_prop)
        let s := fun q : P.AgentNoise×P.NumericRows N eps => ∑j : Fin N,(B j).indicator (fun _ => (1:ℝ)) q
        have hsM : Measurable s := Finset.measurable_sum _ (fun j _ => measurable_const.indicator (hB j))
        have hsI : Integrable s (Gamma.prod (R:Measure (P.NumericRows N eps))) :=
          integrable_finsetSum Finset.univ (fun j _ => (integrable_const (1:ℝ)).indicator (hB j))
        let f := fun q => -(P.eta*P.U)*s q-2*P.kappa*step
        have hfM : Measurable f := (measurable_const.mul hsM).sub measurable_const
        have hfI : Integrable f (Gamma.prod (R:Measure (P.NumericRows N eps))) :=
          (hsI.const_mul _).sub (integrable_const _)
        have hle : ∀ᵐq ∂Gamma.prod (R:Measure (P.NumericRows N eps)),f q≤ P.clusterGain eps c kind target q := by
          apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hfM (P.measurable_clusterGain eps c kind target))).mpr
          filter_upwards [hgeo] with x hx
          filter_upwards [hrows] with r hr
          let t : P.ClusterBox N := (x.1.1,⟨P.clusterOld eps x,hx.1⟩,
            r.1,fun j => ⟨(r.2 j:ℝ),hr j⟩)
          let y : P.Bid := ⟨P.clusterRaised eps target x,hx.2.1⟩
          have hh := P.cluster_pure_gain c kind hpure t y hx.2.2.1
          have hc : P.clusterCrossingCount kind t y≤ s (x,r) := by
            apply Finset.sum_le_sum
            intro j _
            by_cases hj : kind j=1 ∧ (t.2.2.2 j:ℝ)∈ Icc (t.2.1:ℝ) (y:ℝ)
            · have henv : (r.2 j:ℝ)∈ Icc l u :=
                ⟨hx.2.2.2.2.2.1.trans hj.2.1,hj.2.2.trans hx.2.2.2.2.2.2.2.2⟩
              have hmem : (x,r) ∈ B j := henv
              simp only [if_pos hj,Set.indicator_of_mem hmem]
              exact le_rfl
            · simp only [if_neg hj]
              by_cases hmem : (x,r)∈ B j
              · simp only [Set.indicator_of_mem hmem]; norm_num
              · simp only [Set.indicator_of_notMem hmem]; norm_num
          have hident : P.clusterGain eps c kind target (x,r)=P.clusterBoxGain c kind t y := by
            unfold clusterGain clusterBoxGain
            rw [hstable,hstable]
            rfl
          rw [hident]
          have hcross := mul_le_mul_of_nonneg_left hc hEta
          have hprice := mul_le_mul_of_nonneg_left hx.2.2.2.2.1 (show 0≤2*P.kappa by positivity)
          change -(P.eta*P.U)*s (x,r)-2*P.kappa*step≤ _
          linarith
        have hInt := integral_mono_ae hfI (hQ kind) hle
        have hsInt : (∫q,s q ∂Gamma.prod (R:Measure (P.NumericRows N eps)))=(N:ℝ)*p*G.real (Icc l u) := by
          rw [integral_finsetSum Finset.univ (fun j _ => (integrable_const (1:ℝ)).indicator (hB j))]
          simp_rw [integral_indicator_const (1:ℝ) (hB _),smul_eq_mul,mul_one]
          change (∑ j : Fin N, (Gamma.prod (P.noisyNumericRows N eps low mu pi : Measure (P.NumericRows N eps))).real {q : P.AgentNoise × P.NumericRows N eps | (q.2.2 j : ℝ) ∈ Icc l u}) = _
          simp_rw [P.cluster_envelope_coordinate_mass eps low mu pi Gamma _ l u]
          simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
          ring
        rw [integral_sub (hsI.const_mul _) (integrable_const _),integral_const_mul,hsInt,integral_const,
          ←univ_prod_univ,measureReal_prod_prod,probReal_univ (μ := (R : Measure (P.NumericRows N eps))),mul_one] at hInt
        simp only [if_neg hguard,if_pos hpure,zero_sub]
        have he : 0≤ p*err := mul_nonneg hp herr.le
        change -(P.eta*P.U)*((N:ℝ)*p*G.real (Icc l u))-p*(2*P.kappa*step)≤ _ at hInt
        linarith
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun kind _ =>
    mul_le_mul_of_nonneg_left (hpoint kind) (C.nonneg kind))
  have halg : (∑kind : Fin N→ Fin 4,C.mass kind*
      ((if activePatternGuarded P.xi P.L P.U c P.z kind then g*p^2/2 else 0)-
        (if activePatternPure P.xi P.L P.U c P.z kind then P.eta*P.U*(N:ℝ)*p*G.real (Icc l u) else 0)-
        p*(err+2*P.kappa*step)))=
      g/2*C.prob (activePatternGuarded P.xi P.L P.U c P.z)*p^2-
        P.eta*P.U*(N:ℝ)*C.prob (activePatternPure P.xi P.L P.U c P.z)*p*G.real (Icc l u)-
        p*(err+2*P.kappa*step) := by
    change C.expect (fun kind =>
      ((if activePatternGuarded P.xi P.L P.U c P.z kind then g*p^2/2 else 0)-
        (if activePatternPure P.xi P.L P.U c P.z kind then P.eta*P.U*(N:ℝ)*p*G.real (Icc l u) else 0))-
        p*(err+2*P.kappa*step))=_
    rw [C.expect_sub,C.expect_sub,C.expect_const]
    have hi (Q : (Fin N→ Fin 4)→ Prop) (a : ℝ) :
        C.expect (fun k => if Q k then a else 0)=a*C.prob Q := by
      rw [FiniteLaw.prob_eq_expect,←FiniteLaw.expect_const_mul]
      apply C.expect_congr
      intro k
      by_cases hk : Q k <;> simp [hk]
    rw [hi,hi]
    ring
  rw [halg] at hsum
  convert! hsum using 1
  dsimp [g,C,G,R,p,Gamma]
  ring

end FCAppendix.Affine.Hybrid.Finish01.Primitives
