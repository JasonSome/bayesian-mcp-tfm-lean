import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05AboveCapProbability
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Rows

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine StrictNative
open scoped BigOperators
variable {M : ℕ} [Nonempty (Fin M)] [NeZero M]

theorem dropValue_kind (i : Uniform07.Row) (x : UniformFinite.Source.Observation i) :
    UniformFinite.numericKind i (UniformFinite.dropValue i x)=
      UniformFinite.Source.observationKind i x := by cases x <;> rfl

theorem dropValue_bid (i : Uniform07.Row) (x : UniformFinite.Source.Observation i) :
    UniformFinite.numericBid i (UniformFinite.dropValue i x)=
      UniformFinite.Source.observationBid i x := by cases x <;> rfl

omit [Nonempty (Fin M)] [NeZero M] in

theorem numericContext_dropValue (i : Uniform07.Row) (a : Fin M) (own : ℝ)
    (x : Fin M→ UniformFinite.Source.Observation i) :
    UniformFinite.Late.ExceptionalProfile.numericContext i a own
      (fun j=>UniformFinite.dropValue i (x j))=
      rowContext (UniformFinite.Source.observationCountRow i (zeroFocalObservation i a x))
        (Function.update
          (fun j=>UniformFinite.Source.observationBid i (zeroFocalObservation i a x j)) a own) := by
  have hrow : UniformFinite.Late.ExceptionalProfile.numericRow i a
      (fun j=>UniformFinite.dropValue i (x j))=
        UniformFinite.Source.observationCountRow i (zeroFocalObservation i a x) := by
    unfold UniformFinite.Late.ExceptionalProfile.numericRow UniformFinite.NativeProfile.numericRow
      UniformFinite.Source.observationCountRow
    congr 1
    funext j
    by_cases hj : j=a
    · subst j
      simp only [UniformFinite.NativeProfile.insert,Function.update_self,
        UniformFinite.numericKind,zeroFocalObservation,zeroObservation,
        UniformFinite.Source.observationKind]
      rfl
    · simp only [UniformFinite.NativeProfile.insert,Function.update_of_ne hj,
        zeroFocalObservation,dropValue_kind]
  have hbid : UniformFinite.Late.ExceptionalProfile.numericBids i a own
      (fun j=>UniformFinite.dropValue i (x j))=
        Function.update
          (fun j=>UniformFinite.Source.observationBid i (zeroFocalObservation i a x j)) a own := by
    funext j
    by_cases hj : j=a
    · subst j
      simp only [UniformFinite.Late.ExceptionalProfile.numericBids,Function.update_self]
    · simp only [UniformFinite.Late.ExceptionalProfile.numericBids,Function.update_of_ne hj,
        zeroFocalObservation,dropValue_bid]
  unfold UniformFinite.Late.ExceptionalProfile.numericContext
  rw [hrow,hbid]
  rfl

omit [Nonempty (Fin M)] [NeZero M] in
theorem rival_seed_dropValue (i : Uniform07.Row) (a : Fin M)
    (x : Fin M→ UniformFinite.Source.Observation i) :
    numericRivalHasSeed i a (fun j=>UniformFinite.dropValue i (x j)) ↔
      ∃j,j≠a ∧ j∈(UniformFinite.Source.observationCountRow i (zeroFocalObservation i a x)).lower ∧
        UniformFinite.Source.observationBid i (zeroFocalObservation i a x j)≤ Uniform05.t i/2 := by
  constructor
  · rintro ⟨j,hkind,hbid⟩
    refine ⟨j,j.property,?_,?_⟩
    · simpa only [UniformFinite.Source.observationCountRow,UniformFinite.Source.countRowOfKind,
        Finset.mem_filter,Finset.mem_univ,true_and,zeroFocalObservation,
        Function.update_of_ne j.property,dropValue_kind] using hkind
    · simpa only [zeroFocalObservation,Function.update_of_ne j.property,
        dropValue_bid,Uniform05.t_eq_canonical] using hbid
  · rintro ⟨j,hja,hkind,hbid⟩
    refine ⟨⟨j,hja⟩,?_,?_⟩
    · simpa only [UniformFinite.Source.observationCountRow,UniformFinite.Source.countRowOfKind,
        Finset.mem_filter,Finset.mem_univ,true_and,zeroFocalObservation,
        Function.update_of_ne hja,dropValue_kind] using hkind
    · simpa only [zeroFocalObservation,Function.update_of_ne hja,
        dropValue_bid,Uniform05.t_eq_canonical] using hbid

theorem nativeNumericCountMoment_eq_exceptional_on_menu (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (a : Fin M) (q : Fin 3→ℝ)
    (x : Fin M→ UniformFinite.Source.Observation i) {own R δ : ℝ}
    (hown : Early.bidCap i< own) (hownR : own≤ R) (hR : 0< R)
    (hRt : R< Uniform07.cutoff i)
    (hguard : Uniform07.kappa i*R< G.multiplier-Early.nativeRadius i)
    (hreceipt : Uniform05.kappa i*Uniform05.t i≤ UniformFinite.Source.rootLo i G)
    (hδ : δ≤ UniformFinite.Source.commonGuardMargin i) (hsize : 4/(M:ℝ)≤δ)
    (hc : |(Uniform07.capacity M:ℝ)/M-Uniform05.rho|≤δ)
    (hx : UniformFinite.Source.MenuGood i G δ (zeroFocalObservation i a x)) :
    nativeNumericCountMoment i G a own q (fun j=>UniformFinite.dropValue i (x j))=
      (UniformFinite.Late.Exceptional.continuationLaw i G
        (UniformFinite.Source.observationCountRow i (zeroFocalObservation i a x))
        (Function.update
          (fun j=>UniformFinite.Source.observationBid i (zeroFocalObservation i a x j)) a own) a).expect
            (fun P=>q (UniformFinite.pairCount a P)) := by
  have hownT : own≤ Uniform05.t i := by
    simpa only [Uniform05.t_eq_canonical] using hownR.trans hRt.le
  have hboth:=both_alphas_one_of_menu i G (zeroFocalObservation i a x) a
    (zeroFocalObservation_mem i a x) (zeroFocalObservation_bid i a x)
    hown hownT hreceipt hδ hsize hc hx
  have hseed:= (rival_seed_dropValue i a x).mpr hboth.2.2
  unfold nativeNumericCountMoment
  rw [numericContext_dropValue]
  exact above_cap_context_count_eq i G _ _ a (zeroFocalObservation_mem i a x)
    (UniformFinite.Source.lowerBids_observation i (zeroFocalObservation i a x))
    (zeroFocalObservation_bid i a x)
    (fun j=>observation_bid_bounds i (zeroFocalObservation i a x j))
    hown hownR hR hguard hboth.1 hboth.2.1 _ hseed q

def affineCountTest (i : Uniform07.Row) (v b : ℝ) (r : Fin 3) : ℝ :=
  userPayoff v b 0
    (Schedule.affine 2 (Uniform07.eta i) (Uniform07.eta_pos i).le (source_eta_lt_one i).le).charge
    (Schedule.once 2).charge r.val

@[simp] theorem affineCountTest_zero (i : Uniform07.Row) (v b : ℝ) :
    affineCountTest i v b 0=0 := by
  simp [affineCountTest,userPayoff,Schedule.affine,Schedule.once,successIndicator]

@[simp] theorem affineCountTest_one (i : Uniform07.Row) (v b : ℝ) :
    affineCountTest i v b 1=v-b := by
  simp [affineCountTest,userPayoff,Schedule.affine,Schedule.once,successIndicator]

@[simp] theorem affineCountTest_two (i : Uniform07.Row) (v b : ℝ) :
    affineCountTest i v b 2=v-(1+Uniform07.eta i)*b := by
  simp [affineCountTest,userPayoff,Schedule.affine,Schedule.once,successIndicator]
  ring

omit [Nonempty (Fin M)] [NeZero M] in
theorem affineCountTest_pair (i : Uniform07.Row) (v b : ℝ) (a : Fin M)
    (P : UniformFinite.Allocation M) :
    affineCountTest i v b (UniformFinite.pairCount a P)=
      UniformFinite.pairPayoff (Uniform05.eta i) v b a P := by
  by_cases h0 : a∈P.1 <;> by_cases h1 : a∈P.2 <;>
    simp [UniformFinite.pairCount,Finset.mem_inter,Finset.mem_union,h0,h1,
      UniformFinite.pairPayoff,UniformFinite.Literal.firstCopy,UniformFinite.Literal.duplicateCopy,
      WeightedSampling.indicator,Uniform05.eta_eq_canonical]
  all_goals ring

theorem affineCountTest_bound (i : Uniform07.Row) {v b : ℝ}
    (hv : v∈Icc (0:ℝ) (Uniform07.cutoff i))
    (hb : b∈Icc (0:ℝ) (Uniform07.cutoff i)) (r : Fin 3) :
    |affineCountTest i v b r|≤ 3*Uniform07.cutoff i := by
  have ht:=Uniform07.cutoff_pos i
  have hη0:=(Uniform07.eta_pos i).le
  have hη1:=(source_eta_lt_one i).le
  have hηb : 0≤ Uniform07.eta i*b ∧ Uniform07.eta i*b≤ Uniform07.cutoff i :=
    ⟨mul_nonneg hη0 hb.1,(mul_le_mul_of_nonneg_right hη1 hb.1).trans
      (by simpa only [one_mul] using hb.2)⟩
  fin_cases r
  · change |affineCountTest i v b 0|≤3*Uniform07.cutoff i
    rw [affineCountTest_zero,abs_zero]
    positivity
  · change |affineCountTest i v b 1|≤3*Uniform07.cutoff i
    rw [affineCountTest_one,abs_le]
    constructor <;> linarith [hv.1,hv.2,hb.1,hb.2]
  · change |affineCountTest i v b 2|≤3*Uniform07.cutoff i
    rw [affineCountTest_two,abs_le]
    constructor <;> nlinarith [hv.1,hv.2,hb.1,hb.2]

def nativeNumericPayoff (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (a : Fin M) (v own : ℝ) : (Fin M→ UniformFinite.NumericObservation i)→ℝ :=
  nativeNumericCountMoment i G a own (affineCountTest i v own)

omit [NeZero M] in
theorem native_numeric_payoff_bound (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (a : Fin M) {v own : ℝ} (hv : v∈Icc (0:ℝ) (Uniform07.cutoff i))
    (hb : own∈Icc (0:ℝ) (Uniform07.cutoff i)) (z : Fin M→ UniformFinite.NumericObservation i) :
    |nativeNumericPayoff i G a v own z|≤ 27*Uniform07.cutoff i := by
  have hh:=abs_nativeNumericCountMoment_le i G a own (affineCountTest i v own) z
  have hs : (∑k : Fin 3,|affineCountTest i v own k|)≤ 9*Uniform07.cutoff i := by
    calc
      _≤∑_k : Fin 3,3*Uniform07.cutoff i :=
        Finset.sum_le_sum (fun k _=>affineCountTest_bound i hv hb k)
      _=_ := by simp; ring
  change |nativeNumericPayoff i G a v own z|≤ _ at hh
  linarith

theorem native_above_cap_menu_error (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (a : Fin M) {v own R δ : ℝ}
    (hv : v∈Icc (0:ℝ) (Uniform07.cutoff i))
    (hown : Early.bidCap i< own) (hownR : own≤ R) (hR : 0< R)
    (hRt : R< Uniform07.cutoff i)
    (hguard : Uniform07.kappa i*R< G.multiplier-Early.nativeRadius i)
    (hreceipt : Uniform05.kappa i*Uniform05.t i≤ UniformFinite.Source.rootLo i G)
    (hδ0 : 0≤δ) (hδ : δ≤ UniformFinite.Source.commonGuardMargin i)
    (hsize : 4/(M:ℝ)≤δ) :
    |(∫z,nativeNumericPayoff i G a v own z
      ∂Measure.pi (fun _ : Fin M=>UniformFinite.numericObservationLaw i G))-
      UniformFinite.productPayoff (Uniform05.xi i) v G.multiplier own|≤
      UniformFinite.Late.Exceptional.errorConstant i*δ+
        540*Uniform07.cutoff i*Real.exp (-(M:ℝ)*δ^2/2) := by
  let μ:=Measure.pi (fun _ : Fin M=>UniformFinite.Source.observationLaw i G)
  let drop:=fun x : Fin M→ UniformFinite.Source.Observation i=>
    fun j=>UniformFinite.dropValue i (x j)
  let f:=fun x : Fin M→ UniformFinite.Source.Observation i=>nativeNumericPayoff i G a v own (drop x)
  let u:=UniformFinite.productPayoff (Uniform05.xi i) v G.multiplier own
  let E : Set (Fin M→ UniformFinite.Source.Observation i):=
    {x|¬UniformFinite.Source.MenuGood i G δ (zeroFocalObservation i a x)}
  let Q:=E.indicator (fun _=>(1:ℝ))
  have hM : 0< M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : (0:ℝ)< M := by exact_mod_cast hM
  have hb0 : 0< own := (native_cap_positive i).trans hown
  have hbT : own∈Icc (0:ℝ) (Uniform07.cutoff i) := ⟨hb0.le,hownR.trans hRt.le⟩
  have hv' : v∈Icc (0:ℝ) (Uniform05.t i) := by simpa only [Uniform05.t_eq_canonical] using hv
  have hb' : own∈Icc (0:ℝ) (Uniform05.t i) := by simpa only [Uniform05.t_eq_canonical] using hbT
  have hdrop : Measurable drop := measurable_pi_lambda _ (fun j=>
    (UniformFinite.measurable_dropValue i).comp (measurable_pi_apply j))
  have hf : Measurable f := (measurable_nativeNumericCountMoment i G a own
    (affineCountTest i v own)).comp hdrop
  have hE : MeasurableSet E :=
    ((UniformFinite.Source.measurableSet_menuGood i G δ).preimage
      (measurable_zeroFocalObservation i a)).compl
  have hQ : Integrable Q μ := (integrable_const (1:ℝ)).indicator hE
  have hQmean : (∫x,Q x∂μ)=μ.real E := integral_indicator_one hE
  have hinv : 1/(M:ℝ)≤δ :=
    (div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤ 4) hMr.le).trans hsize
  have hhalf : 1/(M:ℝ)≤δ/2 := by
    have hh : 2/(M:ℝ)≤δ :=
      (div_le_div_of_nonneg_right (by norm_num : (2:ℝ)≤ 4) hMr.le).trans hsize
    have he : 2/(M:ℝ)=2*(1/(M:ℝ)) := by ring
    rw [he] at hh
    linarith
  have hc : |(Uniform07.capacity M:ℝ)/M-Uniform05.rho|≤δ :=
    (UniformFinite.Source.capacity_error_le M hM).trans hinv
  have hu : |u|≤ 3*Uniform07.cutoff i := by
    simpa only [u,Uniform05.t_eq_canonical] using
      UniformFinite.Late.Exceptional.productPayoff_bound i
        ((Uniform05.demandLo_pos i).trans G.multiplier_guards.1) hv' hb'
  have hpoint : ∀x,|f x-u|≤ 30*Uniform07.cutoff i*Q x+
      UniformFinite.Late.Exceptional.errorConstant i*δ := by
    intro x
    by_cases hx : UniformFinite.Source.MenuGood i G δ (zeroFocalObservation i a x)
    · have heq:=nativeNumericCountMoment_eq_exceptional_on_menu i G a
        (affineCountTest i v own) x hown hownR hR hRt hguard hreceipt hδ hsize hc hx
      simp only [affineCountTest_pair] at heq
      have hr:=UniformFinite.Late.Exceptional.observed_menu_error i G
        (zeroFocalObservation i a x) a (zeroFocalObservation_mem i a x)
        (zeroFocalObservation_bid i a x) hv' hb' hreceipt hδ0 hδ hsize hc hx
      have hfrow : f x=UniformFinite.Late.Exceptional.rowPayoff i G
          (UniformFinite.Source.observationCountRow i (zeroFocalObservation i a x)) v
          (Function.update
            (fun j=>UniformFinite.Source.observationBid i (zeroFocalObservation i a x j)) a own) a := by
        simpa only [f,drop,nativeNumericPayoff,
          UniformFinite.Late.Exceptional.rowPayoff,Function.update_self] using heq
      rw [←hfrow] at hr
      have hn : x∉E := fun hn=>hn hx
      simpa only [Q,Set.indicator_of_notMem hn,mul_zero,zero_add,u] using hr
    · have hfull:=(abs_sub (f x) u).trans
        (add_le_add (native_numeric_payoff_bound i G a hv hbT (drop x)) hu)
      have hD : 0≤ UniformFinite.Late.Exceptional.errorConstant i*δ :=
        mul_nonneg (UniformFinite.Late.Exceptional.errorConstant_pos i).le hδ0
      have hm : x∈E := hx
      dsimp only [Q]
      rw [Set.indicator_of_mem hm]
      simp only [mul_one]
      linarith
  have hbound:=UniformFinite.Late.Exceptional.integral_menu_error μ f Q u
    (30*Uniform07.cutoff i) (UniformFinite.Late.Exceptional.errorConstant i*δ)
    hf.aestronglyMeasurable hQ (Eventually.of_forall hpoint)
  rw [hQmean] at hbound
  have hbad:=updated_menu_bad_le i G a (zeroObservation i) hM hδ0 hhalf
  have hmul:=mul_le_mul_of_nonneg_left hbad
    (mul_nonneg (by norm_num : (0:ℝ)≤30) (Uniform07.cutoff_pos i).le)
  have hmap : μ.map drop=Measure.pi (fun _ : Fin M=>UniformFinite.numericObservationLaw i G) :=
    UniformFinite.dropValueRow_law i G M
  dsimp only [nativeNumericPayoff]
  rw [←hmap,integral_map hdrop.aemeasurable
    (measurable_nativeNumericCountMoment i G a own (affineCountTest i v own)).aestronglyMeasurable]
  change |(∫x,f x∂μ)-u|≤ _
  apply hbound.trans
  change 30*Uniform07.cutoff i*μ.real E≤
    30*Uniform07.cutoff i*(18*Real.exp (-(M:ℝ)*δ^2/2)) at hmul
  calc
    _ ≤ 30*Uniform07.cutoff i*(18*Real.exp (-(M:ℝ)*δ^2/2))+
        UniformFinite.Late.Exceptional.errorConstant i*δ := add_le_add hmul le_rfl
    _ = _ := by ring

theorem native_above_cap_payoff_error {i : Uniform07.Row}
    (E : UniformFinite.ExactRestrictedLaw i M) (hc : 1≤ Uniform07.capacity M)
    {R v δ : ℝ} (hR : 0< R) (hUR : Early.bidCap i< R) (hRt : R< Uniform07.cutoff i)
    (hguard : Uniform07.kappa i*R< E.law.multiplier-Early.nativeRadius i)
    (hreceipt : Uniform05.kappa i*Uniform05.t i≤ UniformFinite.Source.rootLo i E.law)
    (a : Fin M) (A : JointAction 2) (hA : A.routeCount=2)
    (hown : Early.bidCap i< A.bid) (hownR : A.bid< R)
    (hv : v∈Icc (0:ℝ) (Uniform07.cutoff i))
    (hδ0 : 0≤δ) (hδ : δ≤ UniformFinite.Source.commonGuardMargin i) (hsize : 4/(M:ℝ)≤δ) :
    |(problem (nativeGame E hc R) a).payoff v A-
      UniformFinite.productPayoff (Uniform05.xi i) v E.law.multiplier A.bid|≤
      UniformFinite.Late.Exceptional.errorConstant i*δ+
        540*Uniform07.cutoff i*Real.exp (-(M:ℝ)*δ^2/2) := by
  have hcount:=native_broadcast_count_numeric E hc hR hUR hRt hguard a A
    ((native_cap_positive i).trans hown) hownR hA (affineCountTest i v A.bid)
  change (problem (nativeGame E hc R) a).payoff v A=_ at hcount
  rw [hcount]
  exact native_above_cap_menu_error i E.law a hv hown hownR.le hR hRt hguard
    hreceipt hδ0 hδ hsize

end FCAppendix.Affine.Uniform07Finishing.Concrete05
