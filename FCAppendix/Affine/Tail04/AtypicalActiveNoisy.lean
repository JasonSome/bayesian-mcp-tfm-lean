import FCAppendix.Affine.Tail04.AtypicalActiveRanks
import FCAppendix.Affine.Tail04.NativeTypicalCount
import FCAppendix.Affine.Tail04.TwoCoinContinuity
import FCAppendix.Exclusive.MarkerConstruction

noncomputable section
namespace FCAppendix.Affine.Tail04.AtypicalActiveNoisy
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon AtypicalUnequal AllCountAtypical
open AtypicalActiveRanks AllNoiseFiniteSelector JoinedHighPolicy

local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤

lemma ae_noisyBids_distinct {N : ℕ} {eps : ℝ} (heps : eps≠0)
    (b : Fin N → ℝ) (hb : ∀ i, b i≠0) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ∀ i j, i≠j → noisyBids eps b z i≠noisyBids eps b z j := by
  let coefficient : Fin N → Fin N → ℝ := fun i k => if k=i then 1 else 0
  have hs (a : Fin N → ℝ) (i : Fin N) : score (fun _ => 0) coefficient a i=a i := by
    simp [score,coefficient,ite_mul]
  filter_upwards [ae_score_ties_identical (fun _ : Fin N => 0) coefficient heps b hb] with z hz
  intro i j hij heq
  have he : score (fun _ => 0) coefficient (noisyBids eps b z) i=
      score (fun _ => 0) coefficient (noisyBids eps b z) j := by simpa only [hs] using heq
  have hc := congrFun (hz i j he).2 i
  simp [coefficient,hij] at hc

lemma comparisons_eventually_eq {N : ℕ} (b : Fin N → ℝ)
    (hno : ∀ i j, i≠j → b i≠b j) :
    ∀ᶠ a in 𝓝 b, ∀ i j, (a i< a j ↔ b i< b j) := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i=j
  · subst j
    exact Eventually.of_forall fun a => by simp
  · rcases lt_or_gt_of_ne (hno i j hij) with hlt | hgt
    · have he : ∀ᶠ a : Fin N → ℝ in 𝓝 b, a i < a j :=
        (isOpen_lt (continuous_apply i) (continuous_apply j)).mem_nhds hlt
      exact he.mono (fun a ha => iff_of_true ha hlt)
    · have he : ∀ᶠ a : Fin N → ℝ in 𝓝 b, a j < a i :=
        (isOpen_lt (continuous_apply j) (continuous_apply i)).mem_nhds hgt
      exact he.mono (fun a ha => iff_of_false (not_lt.mpr ha.le) (not_lt.mpr hgt.le))

lemma ae_fittingPair_locally_constant (N H0 H1 c : ℕ) (ξ : ℝ) {eps : ℝ}
    (heps : eps≠0) (b : Fin N → ℝ) (hb : ∀ i, b i≠0) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ∀ᶠ a in 𝓝 b,
        fittingPair N H0 H1 c ξ (noisyBids eps a z)=fittingPair N H0 H1 c ξ (noisyBids eps b z) := by
  by_cases hcap : c-H0≤ N ∧ c-H1≤ N
  · let A := LowBody.CompleteInformation.Choice (ι:=Fin N) (c-H0) ×
      LowBody.CompleteInformation.Choice (ι:=Fin N) (c-H1)
    letI : Nonempty (LowBody.CompleteInformation.Choice (ι:=Fin N) (c-H0)) :=
      LowBody.CompleteInformation.choice_nonempty (c-H0) (by simpa using hcap.1)
    letI : Nonempty (LowBody.CompleteInformation.Choice (ι:=Fin N) (c-H1)) :=
      LowBody.CompleteInformation.choice_nonempty (c-H1) (by simpa using hcap.2)
    let coeff : A → Fin N → ℝ := fun p => LowBody.copyCoefficient (1-ξ) (p.1.1,p.2.1)
    have he (a : Fin N → ℝ) :
        (fun p : A => LowBody.CompleteInformation.potential (1-ξ) a p.1.1 p.2.1)=
          score (fun _ => 0) coeff a := by
      funext p
      simpa only [score,zero_add,coeff] using
        LowBody.potential_eq_copyCoefficient (1-ξ) a (p.1.1,p.2.1)
    filter_upwards [ae_noisy_selector_locally_constant (fun _ : A => 0) coeff heps b hb] with z hz
    filter_upwards [hz] with a ha
    have hh := congrArg (fun p : A => (p.1.1,p.2.1)) ha
    simp only [fittingPair,dif_pos hcap]
    unfold LowBody.CompleteInformation.selector
    rw [he,he]
    exact hh
  · exact ae_of_all _ fun z => Eventually.of_forall fun a => by simp only [fittingPair,dif_neg hcap]

lemma ae_ownerPool_locally_constant (N c : ℕ) {eps : ℝ}
    (heps0 : 0≤ eps) (heps : eps≠0) (b : Fin N → ℝ) (hb : ∀ i, 0< b i) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ∀ᶠ a in 𝓝 b, ownerPool N c (noisyBids eps a z)=ownerPool N c (noisyBids eps b z) := by
  by_cases hN : N≤2*c
  · exact ae_of_all _ fun z => Eventually.of_forall fun a => by simp [ownerPool,hN]
  · have hc : 2*c< N+1 := by omega
    filter_upwards [ae_all_topSelections_locally_constant heps0 heps b hb] with z hz
    simpa only [ownerPool,if_neg hN] using hz Finset.univ ⟨2*c,hc⟩

theorem ae_activeRule_locally_constant (N H0 H1 c : ℕ) (ξ : ℝ) {eps : ℝ}
    (heps : 0< eps) (b : Fin N → ℝ) (hb : ∀ i, 0< b i) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ∀ᶠ a in 𝓝 b, ∀ side k i,
        (activeRule N H0 H1 c ξ side (noisyBids eps a z) k i ↔
          activeRule N H0 H1 c ξ side (noisyBids eps b z) k i) := by
  filter_upwards [ae_noisyBids_distinct heps.ne' b (fun i => (hb i).ne'),
    ae_fittingPair_locally_constant N H0 H1 c ξ heps.ne' b (fun i => (hb i).ne'),
    ae_ownerPool_locally_constant N c heps.le heps.ne' b hb] with z hz hfit hpool
  have hc : ∀ᶠ a in 𝓝 b, ∀ i j,
      noisyBids eps a z i< noisyBids eps a z j ↔ noisyBids eps b z i< noisyBids eps b z j :=
    (((continuous_noisyBids eps).comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto).eventually
      (comparisons_eventually_eq (noisyBids eps b z) hz)
  filter_upwards [hfit,hpool,hc] with a ha hp hcmp
  have ho (side : Bool) : owners N H0 c (noisyBids eps a z) side=
      owners N H0 c (noisyBids eps b z) side := by simp only [owners,hp]
  have hf (side : Bool) : fittingActive N H0 H1 c ξ (noisyBids eps a z) side=
      fittingActive N H0 H1 c ξ (noisyBids eps b z) side := by simp only [fittingActive,ha]
  have hr (O : Finset (Fin N)) (i : Fin N) :
      O.filter (fun j => noisyBids eps a z i< noisyBids eps a z j)=
        O.filter (fun j => noisyBids eps b z i< noisyBids eps b z j) := by
    ext j
    simp only [Finset.mem_filter,hcmp i j]
  intro side k i
  simp only [activeRule,hf side,ho side,hr]

def acceptance (N H0 H1 c : ℕ) (ξ : ℝ) (side : Bool)
    (ν : FiniteLaw (Marks (ownCount H0 H1 side))) (b : Fin N → ℝ) (i : Fin N) : ℝ :=
  ν.prob (fun z => activeRule N H0 H1 c ξ side b (upperCount z) i)

def countLaw (N H0 H1 c : ℕ) (ξ : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (i : Fin N) : CountLaw 2 :=
  twoCoinCountLaw (acceptance N H0 H1 c ξ false ν0 b i)
    (acceptance N H0 H1 c ξ true ν1 b i)
    (ν0.prob_nonneg _) (ν0.prob_le_one _) (ν1.prob_nonneg _) (ν1.prob_le_one _)

lemma measurable_activeRule (N H0 H1 c : ℕ) (ξ : ℝ) (side : Bool) (k : ℕ) (i : Fin N) :
    MeasurableSet {b : Fin N → ℝ | activeRule N H0 H1 c ξ side b k i} := by
  unfold activeRule
  split_ifs
  · exact MeasurableSet.univ
  · have hm := Exclusive.Marker.measurable_filter Finset.univ
      (fun b : Fin N → ℝ => fun j => b i< b j)
      (fun j => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j))
    simpa only [Function.comp_def, decide_eq_true_eq] using measurableSet_eq_fun
      ((measurable_of_countable
        (fun S : Finset (Fin N) => decide (ownCount H0 H1 side+S.card< c))).comp hm)
        (show Measurable (fun _ : Fin N → ℝ => true) from measurable_const)
  · simpa only [Function.comp_def, decide_eq_true_eq] using (measurableSet_eq_fun
      ((measurable_of_countable (fun S : Finset (Fin N) => decide (i∈S))).comp
        (measurable_fittingActive N H0 H1 c ξ side)) (show Measurable (fun _ : Fin N → ℝ => true) from measurable_const))
  · have hO := measurable_owners N H0 c side
    have hK : Measurable (fun b : Fin N → ℝ =>
        (Finset.univ.filter fun j => b i< b j)) :=
      Exclusive.Marker.measurable_filter Finset.univ _
        (fun j => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j))
    have hpair : Measurable (fun b : Fin N → ℝ =>
        (owners N H0 c b side,Finset.univ.filter fun j => b i< b j)) := hO.prodMk hK
    have hh := (measurable_of_countable (fun p : Finset (Fin N) × Finset (Fin N) =>
      decide (i∈p.1 ∧ k+(p.1∩p.2).card< c))).comp hpair
    convert measurableSet_eq_fun hh
      (show Measurable (fun _ : Fin N → ℝ => true) from measurable_const) using 1
    ext b
    have he : (owners N H0 c b side ∩ Finset.univ.filter (fun j => b i < b j)) =
        (owners N H0 c b side).filter (fun j => b i < b j) := by
      ext j
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Set.mem_setOf_eq, Function.comp_def, decide_eq_true_eq, he]

lemma measurable_acceptance (N H0 H1 c : ℕ) (ξ : ℝ) (side : Bool)
    (ν : FiniteLaw (Marks (ownCount H0 H1 side))) (i : Fin N) :
    Measurable (fun b => acceptance N H0 H1 c ξ side ν b i) := by
  unfold acceptance
  simp only [FiniteLaw.prob_eq_expect,FiniteLaw.expect]
  apply Finset.measurable_sum
  intro z _
  exact measurable_const.mul (Measurable.ite
    (measurable_activeRule N H0 H1 c ξ side (upperCount z) i) measurable_const measurable_const)

lemma measurable_countLaw_mass (N H0 H1 c : ℕ) (ξ : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : Fin N) (r : Fin 3) :
    Measurable (fun b => (countLaw N H0 H1 c ξ ν0 ν1 b i).mass r) := by
  have h0 := measurable_acceptance N H0 H1 c ξ false ν0 i
  have h1 := measurable_acceptance N H0 H1 c ξ true ν1 i
  unfold countLaw
  exact measurable_twoCoinCountLaw_mass _ _ _ _ _ _ h0 h1 r

private theorem twoCoin_congr {p q p' q' : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hp0' : 0 ≤ p') (hp1' : p' ≤ 1) (hq0' : 0 ≤ q') (hq1' : q' ≤ 1)
    (hp : p = p') (hq : q = q') :
    twoCoinCountLaw p q hp0 hp1 hq0 hq1 = twoCoinCountLaw p' q' hp0' hp1' hq0' hq1' := by
  subst p'
  subst q'
  rfl

lemma countLaw_congr_rules (N H0 H1 c : ℕ) (ξ : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (a b : Fin N → ℝ) (i : Fin N)
    (h : ∀ side k, activeRule N H0 H1 c ξ side a k i ↔ activeRule N H0 H1 c ξ side b k i) :
    countLaw N H0 H1 c ξ ν0 ν1 a i=countLaw N H0 H1 c ξ ν0 ν1 b i := by
  have h0 : acceptance N H0 H1 c ξ false ν0 a i=acceptance N H0 H1 c ξ false ν0 b i := by
    exact congrArg ν0.prob (funext fun z => propext (h false (upperCount z)))
  have h1 : acceptance N H0 H1 c ξ true ν1 a i=acceptance N H0 H1 c ξ true ν1 b i := by
    exact congrArg ν1.prob (funext fun z => propext (h true (upperCount z)))
  exact twoCoin_congr _ _ _ _ _ _ _ _ h0 h1

theorem original_mean (N H0 H1 c : ℕ) {ξ B R Rp Rm : ℝ} (side : Bool)
    (b : Fin N → ℝ) (θ : Measure (Row (ownCount H0 H1 side) R Rp Rm))
    [IsProbabilityMeasure θ] (ν : FiniteLaw (Marks (ownCount H0 H1 side)))
    (hν : θ.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν)
    (hξ : ξ∈Ico (0:ℝ) 1) (hb : ∀ j, b j∈Icc (1:ℝ) B)
    (hR : 0< R) (hRRm : R≤ Rm) (hRp : Rp<1) (hgap : (1-ξ)*B< R) (hfloor : B< Rm)
    (i : Fin N) (hno : ∀ j, j≠i → b j≠b i) :
    AtypicalOriginalPosterior.mean N H0 H1 c ξ b side θ i=
      acceptance N H0 H1 c ξ side ν b i := by
  rw [acceptance,FiniteLaw.prob_eq_expect,
    ← AtypicalOriginalPosterior.markLaw_eq_of_pushforward θ ν hν,
    AtypicalOriginalPosterior.markLaw_expect]
  apply integral_congr_ae
  exact ae_of_all _ fun row => by
    dsimp only
    simp only [selected_active_iff N H0 H1 c side b row hξ hb hR hRRm hRp hgap hfloor i hno]
    rfl

theorem original_countLaw (N H0 H1 c : ℕ) {ξ B R Rp Rm : ℝ}
    (p : Parameters N H0 R Rp B)
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (hξ : ξ∈Ico (0:ℝ) 1) (hR : 0< R) (hRRm : R≤ Rm) (hRp : Rp<1)
    (hgap : (1-ξ)*B< R) (hfloor : B< Rm) (i : Fin N)
    (hno : ∀ j, j≠i → publicBids p j≠publicBids p i) :
    NativeTypicalCount.fallbackCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 i=
      countLaw N H0 H1 c ξ ν0 ν1 (publicBids p) i := by
  letI : IsProbabilityMeasure (θ0 : Measure (Row (ownCount H0 H1 false) R Rp Rm)) :=
    inferInstanceAs (IsProbabilityMeasure (θ0 : Measure (Row H0 R Rp Rm)))
  letI : IsProbabilityMeasure (θ1 : Measure (Row (ownCount H0 H1 true) R Rp Rm)) :=
    inferInstanceAs (IsProbabilityMeasure (θ1 : Measure (Row H1 R Rp Rm)))
  unfold NativeTypicalCount.fallbackCount
  rw [originalIndependentCountLaw_eq]
  have hmean0 : LocalSamplerMean.mean (NativeTypicalCount.fallback0 N H0 H1 c ξ B R Rp Rm)
      p θ0 (Sum.inl i)=acceptance N H0 H1 c ξ false ν0 (publicBids p) i := by
    have hg : Measurable (fun z : Parameters N H0 R Rp B × Row H0 R Rp Rm =>
        AllCountAtypical.select N H0 H1 c ξ (publicBids z.1) false z.2) := by
      have hh := (NativeTypicalCount.measurable_fallback0 N H0 H1 c ξ B R Rp Rm).comp
        (measurable_id.prodMk (show Measurable (fun _ : Parameters N H0 R Rp B × Row H0 R Rp Rm => (0 : unitInterval)) from measurable_const))
      simp only [Function.comp_def,Function.uncurry,NativeTypicalCount.fallback0,id_eq] at hh
      convert! hh using 1
    have hd := LocalSamplerMean.of_deterministic
      (fun z : Parameters N H0 R Rp B × Row H0 R Rp Rm =>
        AllCountAtypical.select N H0 H1 c ξ (publicBids z.1) false z.2) hg p θ0 (Sum.inl i)
    apply hd.trans
    exact @original_mean N H0 H1 c ξ B R Rp Rm false (publicBids p) θ0
      (inferInstanceAs (IsProbabilityMeasure (θ0 : Measure (Row H0 R Rp Rm))))
      ν0 hν0 hξ (fun j => (p.1.2 j).2) hR hRRm hRp hgap hfloor i hno
  have hmean1 : LocalSamplerMean.mean (NativeTypicalCount.fallback1 N H0 H1 c ξ B R Rp Rm)
      p θ1 (Sum.inl i)=acceptance N H0 H1 c ξ true ν1 (publicBids p) i := by
    have hg : Measurable (fun z : Parameters N H0 R Rp B × Row H1 R Rp Rm =>
        AllCountAtypical.select N H0 H1 c ξ (publicBids z.1) true z.2) := by
      have hh := (NativeTypicalCount.measurable_fallback1 N H0 H1 c ξ B R Rp Rm).comp
        (measurable_id.prodMk (show Measurable (fun _ : Parameters N H0 R Rp B × Row H1 R Rp Rm => (0 : unitInterval)) from measurable_const))
      simp only [Function.comp_def,Function.uncurry,NativeTypicalCount.fallback1,id_eq] at hh
      convert! hh using 1
    have hd := LocalSamplerMean.of_deterministic
      (fun z : Parameters N H0 R Rp B × Row H1 R Rp Rm =>
        AllCountAtypical.select N H0 H1 c ξ (publicBids z.1) true z.2) hg p θ1 (Sum.inl i)
    apply hd.trans
    exact @original_mean N H0 H1 c ξ B R Rp Rm true (publicBids p) θ1
      (inferInstanceAs (IsProbabilityMeasure (θ1 : Measure (Row H1 R Rp Rm))))
      ν1 hν1 hξ (fun j => (p.1.2 j).2) hR hRRm hRp hgap hfloor i hno
  unfold countLaw
  simp only [hmean0,hmean1]

def smoothedMass (N H0 H1 c : ℕ) (ξ eps : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : Fin N) (r : Fin 3)
    (b : Fin N → ℝ) : ℝ :=
  ∫ z : Fin N → unitInterval, (countLaw N H0 H1 c ξ ν0 ν1 (noisyBids eps b z) i).mass r
    ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

def smoothedPaymentMass (N H0 H1 c : ℕ) (ξ eps : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : Fin N) (r : Fin 3)
    (b : Fin N → ℝ) : ℝ :=
  ∫ z : Fin N → unitInterval, (1+eps*(z i:ℝ))*
    (countLaw N H0 H1 c ξ ν0 ν1 (noisyBids eps b z) i).mass r
      ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

lemma mass_bounds (μ : CountLaw 2) (r : Fin 3) : 0≤ μ.mass r ∧ μ.mass r≤1 :=
  ⟨μ.nonneg r,by
    have hh := Finset.single_le_sum (fun s _ => μ.nonneg s) (Finset.mem_univ r)
    simpa only [μ.total] using hh⟩

theorem continuousAt_smoothedMass (N H0 H1 c : ℕ) (ξ : ℝ) {eps : ℝ}
    (heps : 0< eps) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (i : Fin N) (r : Fin 3) (b : Fin N → ℝ) (hb : ∀ j, 0< b j) :
    ContinuousAt (smoothedMass N H0 H1 c ξ eps ν0 ν1 i r) b := by
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun a z => (countLaw N H0 H1 c ξ ν0 ν1 (noisyBids eps a z) i).mass r)
    (bound:=fun _ => (1:ℝ))
  · exact Eventually.of_forall fun a => ((measurable_countLaw_mass N H0 H1 c ξ ν0 ν1 i r).comp
      ((continuous_noisyBids eps).comp (continuous_const.prodMk continuous_id)).measurable).aestronglyMeasurable
  · exact Eventually.of_forall fun a => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mass_bounds _ r).1]
      exact (mass_bounds _ r).2
  · exact integrable_const 1
  · filter_upwards [ae_activeRule_locally_constant N H0 H1 c ξ heps b hb] with z hz
    apply (continuousAt_const : ContinuousAt (fun _ : Fin N → ℝ =>
      (countLaw N H0 H1 c ξ ν0 ν1 (noisyBids eps b z) i).mass r) b).congr
    exact hz.mono fun a ha => (congrArg (fun μ : CountLaw 2 => μ.mass r)
      (countLaw_congr_rules N H0 H1 c ξ ν0 ν1 (noisyBids eps a z) (noisyBids eps b z)
        i (fun side k => ha side k i))).symm

theorem continuousAt_smoothedPaymentMass (N H0 H1 c : ℕ) (ξ : ℝ) {eps : ℝ}
    (heps : 0< eps) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (i : Fin N) (r : Fin 3) (b : Fin N → ℝ) (hb : ∀ j, 0< b j) :
    ContinuousAt (smoothedPaymentMass N H0 H1 c ξ eps ν0 ν1 i r) b := by
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun a z => (1+eps*(z i:ℝ))*
      (countLaw N H0 H1 c ξ ν0 ν1 (noisyBids eps a z) i).mass r)
    (bound:=fun _ => 1+eps)
  · exact Eventually.of_forall fun a =>
      (by
        apply Measurable.aestronglyMeasurable
        apply Measurable.mul
        · fun_prop
        · exact (measurable_countLaw_mass N H0 H1 c ξ ν0 ν1 i r).comp
            ((continuous_noisyBids eps).comp (continuous_const.prodMk continuous_id)).measurable)
  · exact Eventually.of_forall fun a => ae_of_all _ fun z => by
      have hz0 : 0≤1+eps*(z i:ℝ) := by nlinarith [mul_nonneg heps.le (z i).2.1]
      have hz1 : 1+eps*(z i:ℝ)≤1+eps := by nlinarith [(z i).2.2]
      have hm := mass_bounds (countLaw N H0 H1 c ξ ν0 ν1 (noisyBids eps a z) i) r
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hz0 hm.1)]
      exact (mul_le_of_le_one_right hz0 hm.2).trans hz1
  · exact integrable_const _
  · filter_upwards [ae_activeRule_locally_constant N H0 H1 c ξ heps b hb] with z hz
    apply (continuousAt_const : ContinuousAt (fun _ : Fin N → ℝ =>
      (1+eps*(z i:ℝ))*(countLaw N H0 H1 c ξ ν0 ν1 (noisyBids eps b z) i).mass r) b).congr
    exact hz.mono fun a ha => by
      dsimp only
      rw [countLaw_congr_rules N H0 H1 c ξ ν0 ν1 (noisyBids eps a z) (noisyBids eps b z)
        i (fun side k => ha side k i)]

end FCAppendix.Affine.Tail04.AtypicalActiveNoisy
