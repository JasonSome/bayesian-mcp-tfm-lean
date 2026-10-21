import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Adapter
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Guard
import FCAppendix.Affine.UniformFinite.ProductPayoff
import FCAppendix.Affine.Uniform06.EntryEarlyFamilyAdapter

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Uniform06 Uniform06.LiteralExperiment

def readyPredicate (row : Uniform07.Row) (m : ℕ)
    (E : UniformFinite.ExactRestrictedLaw row m) : Prop :=
  |E.law.multiplier-Uniform07.entry row|< Uniform07.cutoff row/100000 ∧
    1/(m:ℝ)≤ 7*UniformFinite.Source.commonGuardMargin row

abbrev ReadyLaw (row : Uniform07.Row) (m : ℕ) :=
  {E : UniformFinite.ExactRestrictedLaw row m // readyPredicate row m E}

def G (row : Uniform07.Row) (m : ℕ) (E : ReadyLaw row m) : ProbabilityMeasure (ℝ×ℝ) :=
  ⟨Concrete05.realJoint E.1,inferInstance⟩

def g (row : Uniform07.Row) (m : ℕ) (E : ReadyLaw row m) : GuardData :=
  Received06.received06GuardData row m E.1.law.multiplier E.1.law.rejectionRoot

def cm (row : Uniform07.Row) (m : ℕ) (_E : ReadyLaw row m) :
    (Fin (m-1)→ Fin 4)→ℝ := Received06.received06CountMargin row m

theorem floor_eq (row : Uniform07.Row) (v : ℝ) :
    Uniform05.floorBid row v=LowChernoff.physicalFloor row v := by
  have hd : Uniform05.zc row-Uniform05.s row=Uniform07.cutoff row/400 := by
    simp only [Uniform05.zc,Uniform05.s,Uniform05.t_eq_canonical]
    ring
  unfold Uniform05.floorBid
  rw [hd]
  simp only [Uniform05.chi,Uniform05.v0,Uniform05.s,Uniform05.t_eq_canonical,
    Uniform05.lambda_eq_canonical,Uniform05.clip01,LowChernoff.physicalFloor]
  rw [max_min_distrib_left]
  norm_num

theorem cap_eq (row : Uniform07.Row) : Uniform05.cap row=ReceiptGap.cap row :=
  Received06.cap_eq row

theorem value_measure_eq (row : Uniform07.Row) :
    (sourceLowerValueLaw row:Measure ℝ)=LowChernoff.conditionalValueLaw row := by
  rw [sourceLowerValueLaw_literal]
  simp only [LowChernoff.conditionalValueLaw,one_div]

theorem realJoint_original {row : Uniform07.Row} {m : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row m) :
    Concrete05.realJoint E=(E.pi.1 : Measure (UniformFinite.Value row×unitInterval)).map
      (fun p=>((p.1:ℝ),(UniformFinite.baseBid row p:ℝ))) := by
  change Measure.map (fun p : ℝ×Uniform05.Bid row => (p.1,(p.2:ℝ)))
    (Measure.map (fun p : UniformFinite.Value row×Uniform05.Bid row => ((p.1:ℝ),p.2))
      ((UniformFinite.physicalLaw row (0,E.pi)).1 : Measure (UniformFinite.Value row×Uniform05.Bid row)))=_
  rw [UniformFinite.physicalLaw_zero]
  change Measure.map (fun p : ℝ×Uniform05.Bid row => (p.1,(p.2:ℝ)))
    (Measure.map (fun p : UniformFinite.Value row×Uniform05.Bid row => ((p.1:ℝ),p.2))
      (Measure.map (fun p : UniformFinite.Value row×unitInterval => (p.1,UniformFinite.baseBid row p))
        (E.pi.1 : Measure (UniformFinite.Value row×unitInterval))))=_
  have h0 : Measurable (fun p : UniformFinite.Value row×unitInterval =>
      (p.1,UniformFinite.baseBid row p)) :=
    measurable_fst.prodMk (UniformFinite.continuous_baseBid row).measurable
  have h1 : Measurable (fun p : UniformFinite.Value row×Uniform05.Bid row => ((p.1:ℝ),p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have h2 : Measurable (fun p : ℝ×Uniform05.Bid row => (p.1,(p.2:ℝ))) :=
    measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  rw [Measure.map_map h2 h1,Measure.map_map (h2.comp h1) h0]
  rfl

def retract (row : Uniform07.Row) (p : ℝ×ℝ) : UniformFinite.Value row×unitInterval :=
  let v:=UniformFinite.OriginalPopulation.clampValue row p.1
  (v,UniformFinite.choiceForBid row v p.2)

theorem measurable_retract (row : Uniform07.Row) : Measurable (retract row) := by
  exact ((UniformFinite.OriginalPopulation.continuous_clampValue row).measurable.comp
    measurable_fst).prodMk ((UniformFinite.measurable_choiceForBid row).comp
      (((UniformFinite.OriginalPopulation.continuous_clampValue row).measurable.comp
        measurable_fst).prodMk measurable_snd))

theorem choiceForBid_base {row : Uniform07.Row} (p : UniformFinite.Value row×unitInterval)
    (hp : 0<(p.1:ℝ)) :
    UniformFinite.choiceForBid row p.1 (UniformFinite.baseBid row p)=p.2 := by
  apply Subtype.ext
  have hw:=(UniformFinite.width_positive row p.1 hp).ne'
  simp only [UniformFinite.choiceForBid,UniformFinite.baseBid_val]
  have he : (Uniform05.floorBid row p.1+UniformFinite.width row p.1*(p.2:ℝ)-
      Uniform05.floorBid row p.1)/UniformFinite.width row p.1=(p.2:ℝ) := by
    field_simp [hw]
    ring
  rw [he,Uniform05.clip01_eq_self p.2.property]

theorem realJoint_retract {row : Uniform07.Row} {m : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row m) :
    (Concrete05.realJoint E).map (retract row)=(E.pi.1 : Measure (UniformFinite.Value row×unitInterval)) := by
  rw [realJoint_original]
  have hf : Measurable (fun p : UniformFinite.Value row×unitInterval =>
      ((p.1:ℝ),(UniformFinite.baseBid row p:ℝ))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp (UniformFinite.continuous_baseBid row).measurable)
  rw [Measure.map_map (measurable_retract row) hf]
  calc
    _=(E.pi.1 : Measure (UniformFinite.Value row×unitInterval)).map id := by
      apply Measure.map_congr
      filter_upwards [UniformFinite.original_value_positive row E.pi] with p hp
      simp only [Function.comp_apply,retract,UniformFinite.OriginalPopulation.clampValue_coe,
        choiceForBid_base p hp,id_eq,Prod.mk.eta]
    _=_:=Measure.map_id

theorem realJoint_shape {row : Uniform07.Row} {m : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row m) :
    ∀ᵐp∂Concrete05.realJoint E,
      p.1∈Ioc (0:ℝ) (Uniform07.cutoff row) ∧
      p.2∈Icc (LowChernoff.physicalFloor row p.1)
        (min p.1 (ReceiptGap.cap row)) := by
  unfold Concrete05.realJoint
  apply (ae_map_iff
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)).aemeasurable
    (by unfold LowChernoff.physicalFloor; measurability)).mpr
  filter_upwards [E.law.2.2,E.law.value_positive] with p hp hpos
  exact ⟨⟨hpos,by simpa only [Uniform05.t_eq_canonical] using hp.1.2⟩,
    ⟨by simpa only [floor_eq,Function.comp_apply] using! hp.2.1,
      le_min hp.2.2 (by simpa only [cap_eq,Function.comp_apply] using! p.2.property.2)⟩⟩

theorem realJoint_common_raw_IC {row : Uniform07.Row} {m : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row m) :
    ∀ᵐp∂Concrete05.realJoint E,
      0< p.2 ∧ ∀b∈Icc (LowChernoff.physicalFloor row p.1) (min p.1 (ReceiptGap.cap row)),
        UniformFinite.rawUtility row (m-1) E.law p.1 b≤
          UniformFinite.rawUtility row (m-1) E.law p.1 p.2 := by
  have hraw:=E.common_conull_contract
  rw [←realJoint_retract E] at hraw
  have hpull:=ae_of_ae_map (measurable_retract row).aemeasurable hraw
  filter_upwards [hpull,realJoint_shape E] with p hp hs
  let v : UniformFinite.Value row:=⟨p.1,⟨hs.1.1.le,by
    simpa only [Uniform05.t_eq_canonical] using hs.1.2⟩⟩
  have hv : UniformFinite.OriginalPopulation.clampValue row p.1=v :=
    UniformFinite.OriginalPopulation.clampValue_coe row v
  have hbid : (UniformFinite.baseBid row (retract row p):ℝ)=p.2 := by
    simp only [retract,hv]
    apply UniformFinite.choiceForBid_exact row v hs.1.1
    simpa only [UniformFinite.hiBid,floor_eq,cap_eq] using hs.2
  have hvval : ((retract row p).1:ℝ)=p.1 := by
    simp only [retract,hv]
    rfl
  refine ⟨?_,?_⟩
  · simpa only [hbid] using! hp.2.1
  · intro b hb
    have hh:=hp.2.2.2.2 b (by
      simpa only [hvval,UniformFinite.hiBid,floor_eq,cap_eq] using! hb)
    simpa only [hvval,hbid] using! hh

theorem eventually_ready (row : Uniform07.Row) :
    ∀ᶠ m in atTop,∀E : UniformFinite.ExactRestrictedLaw row m,readyPredicate row m E := by
  have ht : 0< Uniform07.cutoff row/100000:=div_pos (Uniform07.cutoff_pos row) (by norm_num)
  have he : 0<7*UniformFinite.Source.commonGuardMargin row:=by
    have hh:=UniformFinite.Source.common_guard_margin row
    positivity
  filter_upwards [UniformFinite.exact_restricted_multiplier_localization row ht,
    (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).eventually_lt_const he]
    with m hm hs E
  exact ⟨by simpa only [Uniform05.lambda_eq_canonical] using hm E,hs.le⟩

theorem eventually_exists_ready (row : Uniform07.Row) :
    ∀ᶠ m in atTop,Nonempty (ReadyLaw row m) := by
  filter_upwards [eventually_ready row,UniformFinite.eventually_exists_exact_restricted_law row]
    with m hm hE
  exact ⟨⟨Classical.choice hE,hm (Classical.choice hE)⟩⟩

theorem value (row : Uniform07.Row) (m : ℕ) (E : ReadyLaw row m) :
    (G row m E:Measure (ℝ×ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw row :=
  (Concrete05.realJoint_value E.1).trans (value_measure_eq row)

theorem permitted (row : Uniform07.Row) (m : ℕ) (E : ReadyLaw row m) :
    ∀ᵐp∂(G row m E:Measure (ℝ×ℝ)),p.2∈Icc
      (LowChernoff.physicalFloor row p.1) (min p.1 (ReceiptGap.cap row)) :=
  (realJoint_shape E.1).mono (fun _ h=>h.2)

theorem atoms (row : Uniform07.Row) (m : ℕ) (E : ReadyLaw row m) (b : ℝ) :
    ((G row m E:Measure (ℝ×ℝ)).map Prod.snd) {b}=0 := by
  change ((Concrete05.realJoint E.1).map Prod.snd) {b}=0
  rw [Concrete05.realJoint_bid]
  exact measure_singleton b

theorem roots (row : Uniform07.Row) :
    EntryEarlyFamilyAdapter.RootFields (G row) (g row) row := by
  refine {
    literal:=fun m E=>Received06.received06GuardData_fields row
      (by have hh:=E.1.cluster.market_two_le; omega) _ _
    positive:=fun m E=>source_guard_multiplier_positive row (Concrete05.multiplier_lower E.1)
    clearing:=?_
    rejection:=?_
    population:=fun _ _=>rfl
    margin:=fun m E=>(Received06.received06GuardData_margin row m _ _).le }
  · intro m E
    change (∫ p,ClippedResidual.exposure (Uniform07.xi row) E.1.law.multiplier p.2
      ∂Concrete05.realJoint E.1)=_
    have hm : Measurable (fun p : ℝ×Uniform05.Bid row => (p.1,(p.2:ℝ))) :=
      measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
    have hL : 0<E.1.law.multiplier :=
      source_guard_multiplier_positive row (Concrete05.multiplier_lower E.1)
    have hcont := ClippedResidual.continuous_exposure (Uniform07.xi_pos row) hL
    have hf : Measurable (fun p : ℝ×ℝ =>
        ClippedResidual.exposure (Uniform07.xi row) E.1.law.multiplier p.2) :=
      hcont.measurable.comp measurable_snd
    rw [Concrete05.realJoint,integral_map hm.aemeasurable hf.aestronglyMeasurable]
    change (∫ p : ℝ×Uniform05.Bid row,
      ClippedResidual.exposure (Uniform07.xi row) E.1.law.multiplier p.2 ∂(E.1.law.1 : Measure _))=_
    have hb : Measurable (fun b : Uniform05.Bid row =>
        ClippedResidual.exposure (Uniform07.xi row) E.1.law.multiplier b) :=
      hcont.measurable.comp measurable_subtype_coe
    rw [←E.1.law.integral_bidLaw hb.aestronglyMeasurable]
    simpa only [Uniform05.lawDemand,Uniform05.xi_eq_canonical,Received06.demand_eq] using
      E.1.law.multiplier_equation
  · intro m E
    change (∫ p,PrefixRoot.sourcePsi row E.1.law.rejectionRoot p.2
      ∂Concrete05.realJoint E.1)=_
    have hm : Measurable (fun p : ℝ×Uniform05.Bid row => (p.1,(p.2:ℝ))) :=
      measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
    have hf : Measurable (fun p : ℝ×ℝ =>
        PrefixRoot.sourcePsi row E.1.law.rejectionRoot p.2) := by
      unfold PrefixRoot.sourcePsi PrefixRoot.psi
      fun_prop
    rw [Concrete05.realJoint,integral_map hm.aemeasurable hf.aestronglyMeasurable]
    change (∫ p : ℝ×Uniform05.Bid row,
      PrefixRoot.sourcePsi row E.1.law.rejectionRoot p.2 ∂(E.1.law.1 : Measure _))=_
    have hb : Measurable (fun b : Uniform05.Bid row => PrefixRoot.sourcePsi row E.1.law.rejectionRoot b) := by
      unfold PrefixRoot.sourcePsi PrefixRoot.psi
      fun_prop
    rw [←E.1.law.integral_bidLaw hb.aestronglyMeasurable]
    simpa only [Uniform05.lawRejection,Uniform05.rejectionExposure,Uniform05.rejectionScale,
      Uniform05.t_eq_canonical,PrefixRoot.sourcePsi,PrefixRoot.psi,Received06.demand_eq] using
      E.1.law.rejectionRoot_equation

theorem count_contract (row : Uniform07.Row) (m : ℕ) (E : ReadyLaw row m) :
    EntryFullRestoration.CountContract row (g row m E) (cm row m E) := by
  exact Received06.received06_count_contract row
    E.1.cluster.market_two_le (by simpa only [one_div] using E.2.2) _ _

theorem comparison (row : Uniform07.Row) (m : ℕ) (E : ReadyLaw row m)
    (v : ℝ) (hv : Uniform07.entry row< v) (hvt : v≤ Uniform07.cutoff row)
    (hL : 0<(g row m E).multiplier) (hLv : (g row m E).multiplier< v) :
    ActiveLocalization.bestBid (Uniform07.xi row) v (g row m E).multiplier∈
      Icc (LowChernoff.physicalFloor row v) (min v (ReceiptGap.cap row)) := by
  let L:=E.1.law.multiplier
  let K:=Uniform07.entry row+Uniform07.cutoff row/100000
  have hξ:=Uniform07.xi_pos row
  have hξ1 : Uniform07.xi row<1:=by
    cases row <;> norm_num [Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]
  have hv0 : 0< v:=hL.trans hLv
  have hLK : L≤ K:=by
    have hh:=(abs_lt.mp E.2.1).2
    dsimp [L,K]
    linarith
  have hKL : Uniform07.entry row-Uniform07.cutoff row/100000< L:=by
    have hh:=(abs_lt.mp E.2.1).1
    dsimp [L]
    linarith
  have hfloor : LowChernoff.physicalFloor row v< L := by
    have hf:=(LiteralWeakRent.source_floor_bounds row hv0.le).2
    have hfv:=mul_le_mul_of_nonneg_left hvt (by norm_num : (0:ℝ)≤ 69/100)
    have hx : (69/100:ℝ)< Uniform07.x row-1/100000:=by
      cases row <;> norm_num [Uniform07.x,Uniform07.xQ]
    have ht:=mul_lt_mul_of_pos_right hx (Uniform07.cutoff_pos row)
    unfold Uniform07.entry at hKL
    nlinarith
  have hB:=UniformFinite.activeBidAt_bounds hξ hξ1 hL hLv
  have hmonoL:=UniformFinite.activeBidAt_mono_root hξ hξ1 hL hLK hv0.le
  have hmonoV:=UniformFinite.activeBidAt_mono_value hξ hξ1 (hL.trans_le hLK) hv0.le hvt
  have htop : UniformFinite.activeBidAt (Uniform07.xi row) K (Uniform07.cutoff row)< ReceiptGap.cap row := by
    have ht:=Uniform07.cutoff_pos row
    have hd : 0<(1-Uniform07.xi row)*Uniform07.cutoff row+Uniform07.xi row*K:=
      UniformFinite.activeBidAt_den_pos hξ hξ1 (hL.trans_le hLK) ht.le
    rw [ReceiptGap.cap_scaled]
    unfold UniformFinite.activeBidAt
    apply (div_lt_iff₀ hd).mpr
    dsimp only [K,Uniform07.entry]
    have hscalar : Uniform07.x row+1/100000< ReceiptGap.capFactor row*
        ((1-Uniform07.xi row)+Uniform07.xi row*(Uniform07.x row+1/100000)) := by
      cases row <;> norm_num [ReceiptGap.capFactor,Uniform07.x,Uniform07.xQ,
        Uniform07.kappa,Uniform07.kappaQ,Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]
    have hh:=mul_lt_mul_of_pos_right hscalar (sq_pos_of_pos ht)
    nlinarith only [hh]
  exact ⟨hfloor.le.trans hB.1.le,le_min hB.2.1.le
    ((hmonoL.trans hmonoV).trans htop.le)⟩

theorem root_limit (row : Uniform07.Row) (err : ℝ) (herr : 0< err) :
    ∀ᶠ m in atTop,∀ E : ReadyLaw row m,
      |(g row m E).multiplier-Uniform07.entry row|< err := by
  filter_upwards [UniformFinite.exact_restricted_multiplier_localization row herr] with m hm E
  simpa only [g,Received06.received06GuardData,SourcePrefixConstructor.sourceGuard,
    Uniform05.lambda_eq_canonical] using hm E.1

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
