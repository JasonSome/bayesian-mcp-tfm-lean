import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Rows

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open FCAppendix.Affine UniformFinite StrictNative Weighted LowBody
open scoped BigOperators
variable {row : Uniform07.Row} {m : ℕ} [Nonempty (Fin m)]

local instance : NeZero m := ⟨by
  have hi := (Classical.choice (inferInstance : Nonempty (Fin m))).isLt
  omega⟩

omit [Nonempty (Fin m)] in
theorem numeric_context_entries (row : Uniform07.Row) (i : Fin m) (own : ℝ)
    (z : Fin m→ UniformFinite.NumericObservation row) :
    (fun k=>entryBid ((UniformFinite.Late.ExceptionalProfile.numericContext row i own z).1 k))=
      UniformFinite.Late.ExceptionalProfile.numericBids row i own z :=
  UniformFinite.Late.ExceptionalProfile.raw_rowContext _ _
    (UniformFinite.Late.ExceptionalProfile.numericBids_outside row i own z)

omit [Nonempty (Fin m)] in
lemma numeric_context_decode (row : Uniform07.Row) (i : Fin m) (own : ℝ)
    (z : Fin m→ UniformFinite.NumericObservation row) :
    UniformFinite.NativeContext.decode (UniformFinite.Late.ExceptionalProfile.numericContext row i own z)=
      UniformFinite.Late.ExceptionalProfile.numericRow row i z :=
  UniformFinite.Late.ExceptionalProfile.decode_rowContext _ _

omit [Nonempty (Fin m)] in
theorem numeric_context_properties (row : Uniform07.Row) [NeZero m]
    (i : Fin m) (own : Uniform05.Bid row) (z : Fin m→ UniformFinite.NumericObservation row) :
    let X := UniformFinite.Late.ExceptionalProfile.numericContext row i own z
    UniformFinite.NativeContext.Valid X ∧ NonnegativeList X.1 ∧
      (∀k,entryBid (X.1 k)≤ Early.bidCap row) ∧ entryBid (X.1 i)=(own:ℝ) := by
  let D := UniformFinite.Late.ExceptionalProfile.numericRow row i z
  let b := UniformFinite.Late.ExceptionalProfile.numericBids row i own z
  have hg := UniformFinite.Late.ExceptionalProfile.numericBids_good row i own own.property.1 z
  refine ⟨UniformFinite.Late.ExceptionalProfile.valid_rowContext D b,
    UniformFinite.Late.ExceptionalProfile.nonnegative_rowContext D b hg.2.1,?_,?_⟩
  · intro k
    rw [congrFun (numeric_context_entries row i own z) k]
    by_cases hk : k=i
    · subst k
      simpa only [UniformFinite.Late.ExceptionalProfile.numericBids_focal,cap_eq] using own.property.2
    · change b k≤ Early.bidCap row
      by_cases hD : k∈D.lower
      · simpa only [cap_eq] using hg.2.2 k hD hk
      · dsimp only [b]
        rw [UniformFinite.Late.ExceptionalProfile.numericBids_outside row i own z k hD]
        simpa only [cap_eq] using (Uniform05.cap_pos row).le
  · rw [congrFun (numeric_context_entries row i own z) i,UniformFinite.Late.ExceptionalProfile.numericBids_focal]

omit [Nonempty (Fin m)] in
theorem numeric_context_seed_iff (row : Uniform07.Row) (i : Fin m) (own : ℝ)
    (z : Fin m→ UniformFinite.NumericObservation row) :
    (0< UniformFinite.Source.seedCount row
      (UniformFinite.NativeContext.decode (UniformFinite.Late.ExceptionalProfile.numericContext row i own z))
      (fun k=>entryBid ((UniformFinite.Late.ExceptionalProfile.numericContext row i own z).1 k))) ↔
      own≤ Uniform07.cutoff row/2 ∨ numericRivalHasSeed row i z := by
  rw [numeric_context_decode,numeric_context_entries]
  unfold UniformFinite.Source.seedCount
  rw [Finset.card_pos]
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨hL,hb⟩ := Finset.mem_filter.mp hk
    by_cases hki : k=i
    · subst k
      exact Or.inl (by simpa only [UniformFinite.Late.ExceptionalProfile.numericBids_focal,
        Uniform05.t_eq_canonical] using hb)
    · right
      refine ⟨⟨k,hki⟩,?_,?_⟩
      · simpa only [UniformFinite.Late.ExceptionalProfile.numericRow,
          UniformFinite.NativeProfile.numericRow,UniformFinite.Source.countRowOfKind,
          Finset.mem_filter,Finset.mem_univ,true_and,UniformFinite.NativeProfile.insert,
          Function.update_of_ne hki] using hL
      · simpa only [UniformFinite.Late.ExceptionalProfile.numericBids,
          Function.update_of_ne hki,Uniform05.t_eq_canonical] using hb
  · rintro (hown|⟨k,hk,hb⟩)
    · refine ⟨i,Finset.mem_filter.mpr ⟨UniformFinite.Late.ExceptionalProfile.focal_mem row i z,?_⟩⟩
      simpa only [UniformFinite.Late.ExceptionalProfile.numericBids_focal,
        Uniform05.t_eq_canonical] using hown
    · refine ⟨k,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
      · simpa only [UniformFinite.Late.ExceptionalProfile.numericRow,
          UniformFinite.NativeProfile.numericRow,UniformFinite.Source.countRowOfKind,
          Finset.mem_filter,Finset.mem_univ,true_and,UniformFinite.NativeProfile.insert,
          Function.update_of_ne k.property] using hk
      · simpa only [UniformFinite.Late.ExceptionalProfile.numericBids,
          Function.update_of_ne k.property,Uniform05.t_eq_canonical] using hb

theorem numeric_capped_count_moment (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) [NeZero m] (hm : 0< m)
    (i : Fin m) (own : Uniform05.Bid row) (z : Fin m→ UniformFinite.NumericObservation row)
    (hg : contextCopyGeneric (1-Uniform07.xi row) i
      (UniformFinite.Late.ExceptionalProfile.numericContext row i own z)) (q : Fin 3→ℝ) :
    nativeNumericCountMoment row G i own q z=
      (UniformFinite.continuationLaw row G
        (UniformFinite.Late.ExceptionalProfile.numericRow row i z)
        (UniformFinite.Late.ExceptionalProfile.numericBids row i own z)).expect
          (fun P=>q (UniformFinite.pairCount i P)) := by
  let X := UniformFinite.Late.ExceptionalProfile.numericContext row i own z
  obtain ⟨hX,h0,hU,hi⟩ := numeric_context_properties row i own z
  have h := decoded_continuation_count_moment row G hm X hX h0 hU i hg q
  dsimp only [X] at h
  rw [numeric_context_decode,numeric_context_entries] at h
  rw [h]
  change nativeContextCountMoment row G X (numericRivalHasSeed row i z) i q=
    nativeContextCountMoment row G X
      (0< UniformFinite.Source.seedCount row
        (UniformFinite.Late.ExceptionalProfile.numericRow row i z)
        (UniformFinite.Late.ExceptionalProfile.numericBids row i own z)) i q
  by_cases hs : (own:ℝ)≤ Uniform07.cutoff row/2
  · have hΛ : (54/100:ℝ)*Uniform07.cutoff row< G.multiplier := by
      simpa only [Uniform05.t_eq_canonical] using G.multiplier_guards.1
    have hR : 0< Early.bidCap row := by simpa only [cap_eq] using Uniform05.cap_pos row
    have hguard : Uniform07.kappa row*Early.bidCap row< G.multiplier-Early.nativeRadius row :=
      (le_max_left _ _).trans_lt (((Early.native_sampling_margin_guards row).2 G.multiplier hΛ).1)
    have hzG : Uniform07.cutoff row/2≤ G.rejectionRoot := by
      have hz := G.rejectionRoot_guards.1
      rw [Uniform05.t_eq_canonical] at hz
      nlinarith [Uniform07.cutoff_pos row]
    have hz (seed : Option unitInterval) := literal_sourceCountCorrection_seed_focal_zero (width:=10*UniformFinite.Source.commonGuardMargin row) row
      hΛ hR hguard hzG hm (UniformFinite.Source.common_guard_margin row)
      (Uniform07.capacity m) seed X h0 hU i (hi.trans_le hs) q
    have hz' : finitePathCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row)
        (source_xi_lt_one row) G.multiplier (Early.demandRatio row) (Early.bidCap row)
        (Uniform07.capacity m)
        (literalSourceAlpha row G.multiplier G.rejectionRoot
          (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)) X i q=0 := by
      dsimp only [literalSourceAlpha]
      rw [←integral_sourceCountCorrection]
      simp_rw [hz]
      simp
    dsimp only [literalSourceAlpha] at hz'
    unfold nativeContextCountMoment
    rw [hz']
    simp only [ite_self,add_zero]
  · have he := numeric_context_seed_iff row i own z
    rw [numeric_context_decode,numeric_context_entries] at he
    have hh : (0< UniformFinite.Source.seedCount row
        (UniformFinite.Late.ExceptionalProfile.numericRow row i z)
        (UniformFinite.Late.ExceptionalProfile.numericBids row i own z)) ↔
        numericRivalHasSeed row i z := by simpa only [hs,false_or] using he
    simp only [hh]

omit [Nonempty (Fin m)] in
theorem encoded_numeric_context (row : Uniform07.Row) (i : Fin m)
    (own : Uniform05.Bid row) (kind : Fin m→ Fin 3) (b : Fin m→ Uniform05.Bid row) :
    UniformFinite.Late.ExceptionalProfile.numericContext row i own
      (UniformFinite.encodeCategoryRow row m (kind,b))=
      UniformFinite.NativeProfile.rowContext row (UniformFinite.NativeIndexed.fixedRow i kind)
        (UniformFinite.NativeIndexed.fixedBids row i own kind b) := by
  have hD : UniformFinite.Late.ExceptionalProfile.numericRow row i
      (UniformFinite.encodeCategoryRow row m (kind,b))=UniformFinite.NativeIndexed.fixedRow i kind := by
    exact UniformFinite.NativeIndexed.encode_insert_row row i (UniformFinite.Noisy.zeroBid row) kind b
  apply Prod.ext
  · funext k
    by_cases hk : k=i
    · subst k
      simp only [UniformFinite.Late.ExceptionalProfile.numericContext,
        UniformFinite.Late.ExceptionalProfile.rowContext,hD,
        UniformFinite.NativeProfile.rowContext,UniformFinite.NativeIndexed.fixedRow_self,
        if_true,UniformFinite.Late.ExceptionalProfile.numericBids_focal,
        UniformFinite.NativeIndexed.fixedBids_self]
    · by_cases ht : kind k=0 <;>
        simp [UniformFinite.Late.ExceptionalProfile.numericContext,
          UniformFinite.Late.ExceptionalProfile.rowContext,hD,
          UniformFinite.NativeProfile.rowContext,UniformFinite.NativeIndexed.fixedRow_other _ _ _ hk,
          UniformFinite.Late.ExceptionalProfile.numericBids,
          UniformFinite.NativeIndexed.fixedBids,UniformFinite.NativeIndexed.coordinate,hk,ht,
          UniformFinite.encodeCategoryRow,UniformFinite.numericBid_encodeCategory]
  · simp only [UniformFinite.Late.ExceptionalProfile.numericContext,
      UniformFinite.Late.ExceptionalProfile.rowContext,hD,UniformFinite.NativeProfile.rowContext]

omit [Nonempty (Fin m)] in
theorem encoded_numeric_bids (row : Uniform07.Row) (i : Fin m)
    (own : Uniform05.Bid row) (kind : Fin m→ Fin 3) (b : Fin m→ Uniform05.Bid row) :
    UniformFinite.Late.ExceptionalProfile.numericBids row i own
      (UniformFinite.encodeCategoryRow row m (kind,b))=
      fun k=>(UniformFinite.NativeIndexed.fixedBids row i own kind b k:ℝ) := by
  funext k
  by_cases hk : k=i
  · subst k
    simp only [UniformFinite.Late.ExceptionalProfile.numericBids_focal,
      UniformFinite.NativeIndexed.fixedBids_self]
  · by_cases ht : kind k=0 <;> simp [UniformFinite.Late.ExceptionalProfile.numericBids,
      UniformFinite.NativeIndexed.fixedBids,UniformFinite.NativeIndexed.coordinate,hk,
      UniformFinite.encodeCategoryRow,UniformFinite.numericBid_encodeCategory,ht,UniformFinite.Noisy.zeroBid]

omit [Nonempty (Fin m)] in
theorem ae_encoded_context_generic (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) [NeZero m]
    [NullSingletonClass (G.bidLaw : Measure (Uniform05.Bid row))]
    (i : Fin m) (own : Uniform05.Bid row) (hown : 0<(own:ℝ)) (kind : Fin m→ Fin 3) :
    ∀ᵐb∂(Existence.Distributional.rowLaw m G.bidLaw : Measure (Fin m→ Uniform05.Bid row)),
      contextCopyGeneric (1-Uniform07.xi row) i
        (UniformFinite.Late.ExceptionalProfile.numericContext row i own
          (UniformFinite.encodeCategoryRow row m (kind,b))) := by
  filter_upwards [UniformFinite.NativeIndexed.ae_fixed_generic row G i own hown kind] with b hb
  let X := UniformFinite.Late.ExceptionalProfile.numericContext row i own
    (UniformFinite.encodeCategoryRow row m (kind,b))
  have h0 := (numeric_context_properties row i own (UniformFinite.encodeCategoryRow row m (kind,b))).2.1
  have he : ResidualPotential.bid X.1=
      UniformFinite.Source.lowerBids (UniformFinite.NativeIndexed.fixedRow i kind)
        (UniformFinite.SourceContinuity.bids row (SourceContinuity.fixedLawState row G (UniformFinite.NativeIndexed.fixedBids row i own kind b))) := by
    have hfixed : UniformFinite.Source.lowerBids (UniformFinite.NativeIndexed.fixedRow i kind)
        (UniformFinite.SourceContinuity.bids row (UniformFinite.SourceContinuity.fixedLawState row G
          (UniformFinite.NativeIndexed.fixedBids row i own kind b)))=
        UniformFinite.SourceContinuity.bids row (UniformFinite.SourceContinuity.fixedLawState row G
          (UniformFinite.NativeIndexed.fixedBids row i own kind b)) := by
      convert! UniformFinite.NativeIndexed.fixed_lowerBids row G i own kind b using 1
    rw [hfixed]
    calc
      ResidualPotential.bid X.1=(fun k=>entryBid (X.1 k)) := by
        rw [←decoded_potential_bids X h0,decoded_lowerBids]
      _=_ := by
        rw [numeric_context_entries,encoded_numeric_bids]
        rfl
  unfold contextCopyGeneric
  rw [he,←received_kappa_eq]
  exact hb

theorem native_capped_count_law (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hguard : Uniform07.kappa row*R< E.law.multiplier-Early.nativeRadius row)
    (i : Fin m) (own : Uniform05.Bid row) (hown : 0<(own:ℝ)) :
    (problem (nativeGame E hc R) i).outcome (Hybrid.lowBroadcast own)=
      UniformFinite.NativeProfile.indexedLaw row E.law i own := by
  letI : NeZero m := E.marketNeZero
  have hm : 0< m := lt_of_lt_of_le (by norm_num : 0<2) E.cluster.market_two_le
  have hownU : (own:ℝ)≤ Early.bidCap row := by simpa only [cap_eq] using own.property.2
  have hownR : (own:ℝ)< R := hownU.trans_lt hUR
  apply FiniteLaw.ext_expect
  intro q
  rw [native_broadcast_count_numeric E hc hR hUR hRt hguard i
    (Hybrid.lowBroadcast own) hown hownR rfl q,
    UniformFinite.NativeIndexed.indexedLaw_source row E.law i own q]
  change (∫z,nativeNumericCountMoment row E.law i own q z
    ∂Measure.pi (fun _ : Fin m=>UniformFinite.numericObservationLaw row E.law)) = _
  let f := nativeNumericCountMoment row E.law i own q
  have hf := measurable_nativeNumericCountMoment row E.law i own q
  have hi : Integrable (fun p=>f (UniformFinite.encodeCategoryRow row m p))
      ((FiniteLaw.probabilityMeasure (UniformFinite.categoryRowLaw row m)).prod
        (Existence.Distributional.rowLaw m E.law.bidLaw : Measure (Fin m→ Uniform05.Bid row))) := by
    apply Integrable.of_bound (f := fun p=>f (UniformFinite.encodeCategoryRow row m p))
      (hf.comp (UniformFinite.measurable_encodeCategoryRow row m)).aestronglyMeasurable
      (3*∑k : Fin 3,|q k|)
    filter_upwards [] with p
    simpa only [Real.norm_eq_abs, f] using
      (abs_nativeNumericCountMoment_le row E.law i own q (UniformFinite.encodeCategoryRow row m p))
  rw [←UniformFinite.encodeCategoryRow_law row E.law m,
    integral_map (UniformFinite.measurable_encodeCategoryRow row m).aemeasurable hf.aestronglyMeasurable,
    integral_prod _ hi,LowBody.integral_probabilityMeasure]
  apply FiniteLaw.expect_congr
  intro kind
  apply integral_congr_ae
  filter_upwards [ae_encoded_context_generic row E.law i own hown kind] with b hb
  dsimp only [f]
  rw [numeric_capped_count_moment row E.law hm i own _ hb q]
  have hD := UniformFinite.NativeIndexed.encode_insert_row row i (UniformFinite.Noisy.zeroBid row) kind b
  rw [show UniformFinite.Late.ExceptionalProfile.numericRow row i
      (UniformFinite.encodeCategoryRow row m (kind,b))=UniformFinite.NativeIndexed.fixedRow i kind from hD,
    encoded_numeric_bids]
  rw [UniformFinite.rowCountLaw,FiniteLaw.expect_map]
  rfl

theorem native_capped_payoff_eq_raw {N : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row (N+1))
    (hc : 1≤ Uniform07.capacity (N+1)) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hguard : Uniform07.kappa row*R< E.law.multiplier-Early.nativeRadius row)
    (i : Fin (N+1)) (v : ℝ) (own : Uniform05.Bid row) (hown : 0<(own:ℝ)) :
    (problem (nativeGame E hc R) i).payoff v (Hybrid.lowBroadcast own)=
      UniformFinite.rawUtility row N E.law v own := by
  change ((problem (nativeGame E hc R) i).outcome (Hybrid.lowBroadcast own)).utility
    v own 0 (Schedule.affine 2 (Uniform07.eta row)
      (Uniform07.eta_pos row).le (source_eta_lt_one row).le) (Schedule.once 2)=_
  rw [native_capped_count_law E hc hR hUR hRt hguard i own hown]
  convert UniformFinite.NativeIndexed.utility_positive_eq_raw row N E.law i v own hown using 1
  simp only [UniformFinite.NativeIndexed.utility,Uniform05.eta_eq_canonical]

theorem native_common_capped_positive_IC {N : ℕ} {R₀ : ℝ}
    (W : UniformFinite.NativeFiniteLowerConstruction row (N+1) R₀)
    (hc : 1≤ Uniform07.capacity (N+1)) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hguard : Uniform07.kappa row*R< W.finite.restricted.law.multiplier-Early.nativeRadius row) :
    ∀ᵐp∂(W.finite.restricted.pi.1 : Measure (UniformFinite.Value row×unitInterval)),
      ∀i : Fin (N+1),∀a : JointAction 2,
        a.routeCount=2→ 0< a.bid→ a.bid≤ Early.bidCap row→
        (problem (nativeGame W.finite.restricted hc R) i).payoff p.1 a≤
          (problem (nativeGame W.finite.restricted hc R) i).payoff p.1
            (UniformFinite.OriginalPopulation.lowerAction row p) := by
  let E := W.finite.restricted
  filter_upwards [E.common_conull_contract,original_all_broadcast_IC W] with p hp hIC
  intro i a ha2 ha0 haU
  let own : Uniform05.Bid row := ⟨a.bid,a.bid_nonneg,by simpa only [cap_eq] using haU⟩
  have ha : a=Hybrid.lowBroadcast own := UniformFinite.NativeIC.broadcast_eq a ha2 own rfl
  rw [ha,native_capped_payoff_eq_raw E hc hR hUR hRt hguard i p.1 own ha0]
  have hinc : UniformFinite.OriginalPopulation.lowerAction row p=
      Hybrid.lowBroadcast (UniformFinite.baseBid row p) := rfl
  rw [hinc,native_capped_payoff_eq_raw E hc hR hUR hRt hguard i p.1
    (UniformFinite.baseBid row p) hp.2.1]
  have haCap : a.bid≤Uniform05.cap row := by simpa only [cap_eq] using haU
  have hh := hIC a.bid a.bid_nonneg (haCap.trans_lt W.finite.upper_floor)
  rw [UniformFinite.Late.extendedRawUtility_on_path row (N+1-1) E.law p.1 a.bid own.property.2] at hh
  simpa only [Nat.add_sub_cancel] using hh

theorem native_common_incumbent_nonnegative {N : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row (N+1))
    (hc : 1≤ Uniform07.capacity (N+1)) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hguard : Uniform07.kappa row*R< E.law.multiplier-Early.nativeRadius row) :
    ∀ᵐp∂(E.pi.1 : Measure (UniformFinite.Value row×unitInterval)),∀i : Fin (N+1),
      0≤(problem (nativeGame E hc R) i).payoff p.1
        (UniformFinite.OriginalPopulation.lowerAction row p) := by
  have hIC : UniformFinite.RestrictedIC row N E.pi := by
    simpa only [Nat.add_sub_cancel] using E.restricted_IC
  filter_upwards [E.common_conull_contract,
    UniformFinite.Late.restricted_incumbent_nonnegative row N E.pi hIC] with p hp hn
  intro i
  change 0≤(problem (nativeGame E hc R) i).payoff p.1
    (Hybrid.lowBroadcast (UniformFinite.baseBid row p))
  rw [native_capped_payoff_eq_raw E hc hR hUR hRt hguard i p.1
    (UniformFinite.baseBid row p) hp.2.1]
  exact hn

end FCAppendix.Affine.Uniform07Finishing.Concrete05
