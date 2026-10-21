import FCAppendix.Affine.UniformFinite.NoisyMenu

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional

def capSlack (i : Row) : ℝ := Uniform05.t i/400

theorem capSlack_pos (i : Row) : 0 < capSlack i := by
  have ht := Uniform05.t_pos i
  unfold capSlack
  positivity

theorem cap_strip_endpoint (i : Row) :
    Uniform05.cap i-capSlack i = Uniform05.activeBid i (Uniform05.t i)+Uniform05.t i/400 := by
  unfold Uniform05.cap capSlack
  ring

theorem source_bid_top_above_entry (i : Row) :
    Uniform05.lambda i < Uniform05.activeBid i (Uniform05.t i) := by
  simpa only [source_activeBid_eq] using
    (activeBidAt_bounds (Uniform05.xi_range i).1 (Uniform05.xi_range i).2
      (Uniform05.lambda_pos i) (lambda_lt_t i)).1

theorem cap_strip_above_entry (i : Row) :
    Uniform05.lambda i < Uniform05.cap i-capSlack i := by
  rw [cap_strip_endpoint]
  have ht := Uniform05.t_pos i
  linarith [source_bid_top_above_entry i]

theorem capSlack_lt_cap (i : Row) : capSlack i < Uniform05.cap i := by
  have h := cap_strip_above_entry i
  have hl := Uniform05.lambda_pos i
  linarith

theorem source_root_bounds (i : Row) :
    Uniform05.lambda i ∈ Icc ((54 : ℝ)/100*Uniform05.t i) (Uniform05.cap i) := by
  constructor
  · have ht := Uniform05.t_pos i
    cases i <;> dsimp [Uniform05.lambda,Uniform05.x] <;> linarith
  · have he := cap_strip_above_entry i
    have hs := capSlack_pos i
    linarith

def sourceProductRoot (i : Row) : ProductRoot i :=
  ⟨Uniform05.lambda i,source_root_bounds i⟩

theorem baseBid_feasible (i : Row) (p : Value i × unitInterval) :
    (baseBid i p:ℝ) ∈
      Icc (Uniform05.floorBid i p.1) (min (p.1:ℝ) (Uniform05.cap i)) :=
  noisyRealBid_bounds i 0 p.1 p.2 0

theorem uniform_source_noisy_menu (i : Row) {tol : ℝ} (htol : 0 < tol) :
    ∃ N0 : ℕ, ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ eps : unitInterval, (eps:ℝ) ≤ eps0 →
        ∀ pi : Joint i, NoisyIC i N eps pi → ∀ p : Value i × unitInterval,
          |expectedUtility i N eps pi p.1 p.2-
            productPayoff (Uniform05.xi i) p.1 (Uniform05.lambda i) (baseBid i p)| < tol := by
  have ht2 : 0 < tol/2 := by linarith
  obtain ⟨N1,e1,he1,hmenu⟩ := noisy_uniform_product_menu i ht2
  obtain ⟨radius,hr,hmod⟩ := product_uniform_modulus i ht2
  obtain ⟨N2,e2,he2,hroot⟩ := noisy_multiplier_localization i hr
  refine ⟨max N1 N2,min e1 e2,lt_min he1 he2,?_⟩
  intro N hN eps heps pi hIC p
  have hA := hmenu N ((le_max_left _ _).trans hN) eps
    (heps.trans (min_le_left _ _)) pi p
  have hL := hroot N ((le_max_right _ _).trans hN) eps
    (heps.trans (min_le_right _ _)) pi hIC
  have hP := hmod p.1 (actualProductRoot i (restrictedLaw i (eps,pi)))
    (sourceProductRoot i) (baseBid i p) (baseBid i p) hL (by simpa using hr)
  calc
    _ ≤ |expectedUtility i N eps pi p.1 p.2-
      choiceProduct i (restrictedLaw i (eps,pi)) p|+
      |choiceProduct i (restrictedLaw i (eps,pi)) p-
        productPayoff (Uniform05.xi i) p.1 (Uniform05.lambda i) (baseBid i p)| :=
        abs_sub_le _ _ _
    _ < tol/2+tol/2 := add_lt_add hA hP
    _ = tol := by ring

theorem uniform_source_raw_menu (i : Row) {tol : ℝ} (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, ∀ pi : Joint i, NoisyIC i N 0 pi →
      ∀ (v : ℝ) (b : Bid i), v ∈ Icc (0 : ℝ) (Uniform05.t i) →
        |rawUtility i N (restrictedLaw i (0,pi)) v b-
          productPayoff (Uniform05.xi i) v (Uniform05.lambda i) b| < tol := by
  have ht2 : 0 < tol/2 := by linarith
  obtain ⟨radius,hr,hmod⟩ := product_uniform_modulus i ht2
  obtain ⟨N0,eps0,he0,hroot⟩ := noisy_multiplier_localization i hr
  filter_upwards [eventually_ge_atTop N0,Source.uniform_product_menu i (tol/2) ht2]
    with N hN hmenu
  intro pi hIC v b hv
  have hL := hroot N hN 0 he0.le pi hIC
  have hP := hmod (⟨v,hv⟩ : Value i)
    (actualProductRoot i (restrictedLaw i (0,pi))) (sourceProductRoot i)
    b b hL (by simpa using hr)
  calc
    _ ≤ |rawUtility i N (restrictedLaw i (0,pi)) v b-
      productPayoff (Uniform05.xi i) v (restrictedLaw i (0,pi)).multiplier b|+
      |productPayoff (Uniform05.xi i) v (restrictedLaw i (0,pi)).multiplier b-
        productPayoff (Uniform05.xi i) v (Uniform05.lambda i) b| := abs_sub_le _ _ _
    _ < tol/2+tol/2 := add_lt_add (hmenu _ v b hv) hP
    _ = tol := by ring

def sourceActiveBid (i : Row) (v : Value i) : Bid i := by
  have hxi := Uniform05.xi_range i
  have hL := Uniform05.lambda_pos i
  have hd := activeBidAt_den_pos hxi.1 hxi.2 hL v.property.1
  have hmono := activeBidAt_mono_value hxi.1 hxi.2 hL v.property.1 v.property.2
  refine ⟨Uniform05.activeBid i v,?_,?_⟩
  · change 0 ≤ activeBidAt (Uniform05.xi i) (Uniform05.lambda i) v
    exact div_nonneg (mul_nonneg hL.le v.property.1) hd.le
  · have ht := Uniform05.t_pos i
    simp only [source_activeBid_eq] at hmono
    unfold Uniform05.cap
    linarith

theorem continuous_sourceActiveBid (i : Row) : Continuous (sourceActiveBid i) := by
  apply Continuous.subtype_mk
  change Continuous (fun v : Value i =>
    Uniform05.lambda i*(v:ℝ)/
      ((1-Uniform05.xi i)*(v:ℝ)+Uniform05.xi i*Uniform05.lambda i))
  apply (continuous_const.mul continuous_subtype_val).div
    ((continuous_const.mul continuous_subtype_val).add continuous_const)
  intro v
  exact (activeBidAt_den_pos (Uniform05.xi_range i).1 (Uniform05.xi_range i).2
    (Uniform05.lambda_pos i) v.property.1).ne'

def sourceProfit (i : Row) (v : Value i) : ℝ :=
  productPayoff (Uniform05.xi i) v (Uniform05.lambda i) (sourceActiveBid i v)

theorem continuous_sourceProfit (i : Row) : Continuous (sourceProfit i) := by
  have harg : Continuous (fun v : Value i =>
      (v,(sourceProductRoot i,sourceActiveBid i v))) :=
    continuous_id.prodMk (continuous_const.prodMk (continuous_sourceActiveBid i))
  exact (continuous_productBoxPayoff i).comp harg

def capStrip (i : Row) : Set (Value i × unitInterval) :=
  {p | Uniform05.cap i-capSlack i ≤ (baseBid i p:ℝ)}

theorem isClosed_capStrip (i : Row) : IsClosed (capStrip i) :=
  isClosed_le continuous_const ((continuous_baseBid i).subtype_val)

theorem capStrip_nonempty (i : Row) : (capStrip i).Nonempty := by
  let top : Value i := ⟨Uniform05.t i,(Uniform05.t_pos i).le,le_rfl⟩
  have hb : (baseBid i (top,1):ℝ)=Uniform05.cap i := by
    rw [baseBid_val]
    change Uniform05.floorBid i (Uniform05.t i)+
      (min (Uniform05.t i) (Uniform05.cap i)-Uniform05.floorBid i (Uniform05.t i))*1 = _
    rw [min_eq_right (Uniform05.cap_lt_t i).le]
    ring
  refine ⟨(top,1),?_⟩
  change Uniform05.cap i-capSlack i ≤ (baseBid i (top,1):ℝ)
  rw [hb]
  linarith [capSlack_pos i]

theorem capStrip_active_value (i : Row) {p : Value i × unitInterval}
    (hp : p ∈ capStrip i) : Uniform05.lambda i < (p.1:ℝ) :=
  ((cap_strip_above_entry i).trans_le hp).trans_le
    ((baseBid_feasible i p).2.trans (min_le_left _ _))

theorem source_cap_gap_pos (i : Row) {p : Value i × unitInterval}
    (hp : p ∈ capStrip i) :
    0 < sourceProfit i p.1-
      productPayoff (Uniform05.xi i) p.1 (Uniform05.lambda i) (baseBid i p) := by
  have hv := capStrip_active_value i hp
  have hxi := Uniform05.xi_range i
  have hL := Uniform05.lambda_pos i
  have hsrc : sourceProfit i p.1=((p.1:ℝ)-Uniform05.lambda i)^2/(p.1:ℝ) :=
    activeBidAt_product hxi.1 hxi.2 hL hv
  have hup := product_upper_bound hxi.1 hxi.2 hL (source_cap_receipt i).le
    (baseBid i p).property.2 hv
  have hstrict : productPayoff (Uniform05.xi i) p.1 (Uniform05.lambda i) (baseBid i p) <
      ((p.1:ℝ)-Uniform05.lambda i)^2/(p.1:ℝ) := by
    apply lt_of_le_of_ne hup
    intro he
    have heq := product_maximum_unique hxi.1 hxi.2 hL (source_cap_receipt i).le
      (baseBid i p).property.2 hv he
    have hmono := activeBidAt_mono_value hxi.1 hxi.2 hL p.1.property.1 p.1.property.2
    simp only [source_activeBid_eq] at heq hmono
    change Uniform05.cap i-capSlack i ≤ (baseBid i p:ℝ) at hp
    rw [cap_strip_endpoint,heq] at hp
    have ht := Uniform05.t_pos i
    linarith
  rw [hsrc]
  exact sub_pos.mpr hstrict

theorem source_cap_gap (i : Row) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ p : Value i × unitInterval,
      Uniform05.cap i-capSlack i ≤ (baseBid i p:ℝ) →
        gap ≤ sourceProfit i p.1-
          productPayoff (Uniform05.xi i) p.1 (Uniform05.lambda i) (baseBid i p) := by
  let f : Value i × unitInterval → ℝ := fun p => sourceProfit i p.1-
    productPayoff (Uniform05.xi i) p.1 (Uniform05.lambda i) (baseBid i p)
  have harg : Continuous (fun p : Value i × unitInterval =>
      (p.1,(sourceProductRoot i,baseBid i p))) :=
    continuous_fst.prodMk (continuous_const.prodMk (continuous_baseBid i))
  have hf : Continuous f :=
    ((continuous_sourceProfit i).comp continuous_fst).sub
      ((continuous_productBoxPayoff i).comp harg)
  obtain ⟨p,hp,hmin⟩ := (isClosed_capStrip i).isCompact.exists_isMinOn
    (capStrip_nonempty i) hf.continuousOn
  exact ⟨f p,source_cap_gap_pos i hp,fun q hq => hmin hq⟩

theorem uniform_base_cap_strip (i : Row) :
    ∃ N0 : ℕ, ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ eps : unitInterval, (eps:ℝ) ≤ eps0 →
        ∀ pi : Joint i, NoisyIC i N eps pi →
          ∀ᵐ p ∂(pi.1 : Measure (Value i × unitInterval)),
            (baseBid i p:ℝ) ≤ Uniform05.cap i-capSlack i := by
  obtain ⟨gap,hgap,hgap_lower⟩ := source_cap_gap i
  obtain ⟨N0,eps0,he0,hmenu⟩ := uniform_source_noisy_menu i
    (show 0 < gap/4 by linarith)
  refine ⟨N0,eps0,he0,?_⟩
  intro N hN eps heps pi hIC
  filter_upwards [hIC] with p hp
  by_contra hcap
  have hstrip : p ∈ capStrip i := (lt_of_not_ge hcap).le
  have hv := capStrip_active_value i hstrip
  have hv0 := (Uniform05.lambda_pos i).trans hv
  have hfeasible := source_activeBid_feasible i hv p.1.property.2
  let q' := choiceForBid i p.1 (Uniform05.activeBid i p.1)
  have hchoice : (baseBid i (p.1,q'):ℝ)=Uniform05.activeBid i p.1 :=
    choiceForBid_exact i p.1 hv0 _ hfeasible
  have hown := abs_lt.mp (hmenu N hN eps heps pi hIC p)
  have hdev := hmenu N hN eps heps pi hIC (p.1,q')
  rw [hchoice] at hdev
  have hd := abs_lt.mp hdev
  have hcomp := hp q'
  have hg := hgap_lower p hstrip
  change gap ≤ productPayoff (Uniform05.xi i) p.1 (Uniform05.lambda i)
    (Uniform05.activeBid i p.1)-
      productPayoff (Uniform05.xi i) p.1 (Uniform05.lambda i) (baseBid i p) at hg
  linarith

theorem physical_cap_margin_of_base (i : Row) (eps : unitInterval) (pi : Joint i)
    (hnoise : (eps:ℝ)*Uniform05.t i ≤ capSlack i/2)
    (hbase : ∀ᵐ p ∂(pi.1 : Measure (Value i × unitInterval)),
      (baseBid i p:ℝ) ≤ Uniform05.cap i-capSlack i) :
    (∀ᵐ p ∂(pi.1 : Measure (Value i × unitInterval)), ∀ z : unitInterval,
      (noisyBid i (eps,(p,z)):ℝ) ≤ Uniform05.cap i-capSlack i/2) ∧
    (∀ᵐ (b : Bid i) ∂(bidLaw i (eps,pi) : Measure (Bid i)),
      (b:ℝ) ≤ Uniform05.cap i-capSlack i/2) := by
  have hpoint : ∀ᵐ p ∂(pi.1 : Measure (Value i × unitInterval)), ∀ z : unitInterval,
      (noisyBid i (eps,(p,z)):ℝ) ≤ Uniform05.cap i-capSlack i/2 := by
    filter_upwards [hbase] with p hp z
    have hnoise' := (physical_base_error i eps p z).trans
      ((mul_le_mul_of_nonneg_left p.1.property.2 eps.property.1).trans hnoise)
    have hb := (abs_le.mp hnoise').2
    linarith
  refine ⟨hpoint,?_⟩
  have hs : MeasurableSet {b : Bid i | (b:ℝ) ≤ Uniform05.cap i-capSlack i/2} := by
    exact measurableSet_le measurable_subtype_coe measurable_const
  change ∀ᵐ (b : Bid i) ∂(((physicalLaw i (eps,pi)).1 : Measure (Value i × Bid i)).map Prod.snd),
    (b:ℝ) ≤ Uniform05.cap i-capSlack i/2
  apply (ae_map_iff measurable_snd.aemeasurable hs).mpr
  let psi : (Value i × unitInterval) × unitInterval → Value i × Bid i :=
    fun x => (x.1.1,noisyBid i (eps,x))
  have hm : Measurable psi := (measurable_fst.comp measurable_fst).prodMk
    (((continuous_noisyBid i).comp (continuous_const.prodMk continuous_id)).measurable)
  change ∀ᵐ p ∂(((pi.1 : Measure (Value i × unitInterval)).prod
    (volume : Measure unitInterval)).map psi),
      (p.2:ℝ) ≤ Uniform05.cap i-capSlack i/2
  apply (ae_map_iff hm.aemeasurable (hs.preimage measurable_snd)).mpr
  apply (Measure.ae_prod_iff_ae_ae ((hs.preimage measurable_snd).preimage hm)).mpr
  filter_upwards [hpoint] with p hp
  exact ae_of_all _ hp

theorem physical_cap_margin_disintegrated (i : Row) (eps : unitInterval)
    (pi : Joint i) (sigma : Kernel (Value i) unitInterval) [IsMarkovKernel sigma]
    (hdis : lowerMeasure i ⊗ₘ sigma = (pi.1 : Measure (Value i × unitInterval)))
    (hnoise : (eps:ℝ)*Uniform05.t i ≤ capSlack i/2)
    (hbase : ∀ᵐ p ∂(pi.1 : Measure (Value i × unitInterval)),
      (baseBid i p:ℝ) ≤ Uniform05.cap i-capSlack i) :
    ∀ᵐ v ∂lowerMeasure i, ∀ᵐ q ∂sigma v, ∀ z : unitInterval,
      (noisyBid i (eps,((v,q),z)):ℝ) ≤ Uniform05.cap i-capSlack i/2 := by
  have hpoint := (physical_cap_margin_of_base i eps pi hnoise hbase).1
  rw [← hdis] at hpoint
  exact Measure.ae_ae_of_ae_compProd hpoint

theorem uniform_forbidden_cap_strip (i : Row) :
    ∃ N0 : ℕ, ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ eps : unitInterval, (eps:ℝ) ≤ eps0 →
        ∀ pi : Joint i, NoisyIC i N eps pi →
          (∀ᵐ p ∂(pi.1 : Measure (Value i × unitInterval)),
            (baseBid i p:ℝ) ≤ Uniform05.cap i-capSlack i) ∧
          (∀ᵐ p ∂(pi.1 : Measure (Value i × unitInterval)), ∀ z : unitInterval,
            (noisyBid i (eps,(p,z)):ℝ) ≤ Uniform05.cap i-capSlack i/2) ∧
          (∀ᵐ (b : Bid i) ∂(bidLaw i (eps,pi) : Measure (Bid i)),
            (b:ℝ) ≤ Uniform05.cap i-capSlack i/2) := by
  obtain ⟨N0,eps0,he0,hcap⟩ := uniform_base_cap_strip i
  refine ⟨N0,min eps0 (1/800),lt_min he0 (by norm_num),?_⟩
  intro N hN eps heps pi hIC
  have hbase := hcap N hN eps (heps.trans (min_le_left _ _)) pi hIC
  have hsmall : (eps:ℝ) ≤ 1/800 := heps.trans (min_le_right _ _)
  have hnoise : (eps:ℝ)*Uniform05.t i ≤ capSlack i/2 := by
    have h := mul_le_mul_of_nonneg_right hsmall (Uniform05.t_pos i).le
    dsimp [capSlack]
    nlinarith
  exact ⟨hbase,physical_cap_margin_of_base i eps pi hnoise hbase⟩

end FCAppendix.Affine.UniformFinite
