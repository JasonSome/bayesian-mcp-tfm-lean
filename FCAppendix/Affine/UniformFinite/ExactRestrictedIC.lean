import FCAppendix.Affine.UniformFinite.RawContinuity
import FCAppendix.Affine.UniformFinite.RawCounts
import FCAppendix.Affine.UniformFinite.ActualRaiseModulus
import FCAppendix.Affine.UniformFinite.NoisyCompactLimit
import FCAppendix.Affine.LowBody.ICFromContinuousTests

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

namespace ExactIC

lemma baseBid_map (i : Row) (pi : Joint i) :
    (pi.1 : Measure (Value i×unitInterval)).map (baseBid i)=
      ((restrictedLaw i (0,pi)).bidLaw : Measure (Bid i)) := by
  rw [restrictedLaw_bidLaw]
  change _=((physicalLaw i (0,pi)).1 : Measure (Value i×Bid i)).map Prod.snd
  rw [physicalLaw_zero]
  change _=((pi.1 : Measure (Value i×unitInterval)).map
    (fun p=>(p.1,baseBid i p))).map Prod.snd
  rw [Measure.map_map measurable_snd
    (measurable_fst.prodMk (continuous_baseBid i).measurable)]
  rfl

lemma baseBid_pos_of_choice_pos (i : Row) (v : Value i) (hv : 0<(v:ℝ))
    (q : unitInterval) (hq : 0<(q:ℝ)) : 0<(baseBid i (v,q):ℝ) := by
  rw [baseBid_val]
  exact add_pos_of_nonneg_of_pos (Uniform05.floor_nonneg i v)
    (mul_pos (width_positive i v hv) hq)

lemma incumbent_good (i : Row) (pi : Joint i)
    [NullSingletonClass ((restrictedLaw i (0,pi)).bidLaw : Measure (Bid i))] :
    ExactTests.Good i pi none := by
  have hbid : ∀ᵐ(b : Bid i)∂((restrictedLaw i (0,pi)).bidLaw : Measure (Bid i)),0<(b:ℝ) := by
    filter_upwards [LowBody.ae_injective_ne
      ((restrictedLaw i (0,pi)).bidLaw : Measure (Bid i))
      (fun b : Bid i=>(b:ℝ)) Subtype.val_injective 0] with b hb
    exact lt_of_le_of_ne b.property.1 hb.symm
  have hs : MeasurableSet {b : Bid i | 0<(b:ℝ)} := by measurability
  rw [← baseBid_map i pi] at hbid
  exact (ae_map_iff (continuous_baseBid i).measurable.aemeasurable hs).mp hbid

lemma positive_choice_good (i : Row) (pi : Joint i) (q : unitInterval)
    (hq : 0<(q:ℝ)) : ExactTests.Good i pi (some q) := by
  filter_upwards [original_value_positive i pi] with p hp
  exact baseBid_pos_of_choice_pos i p.1 hp q hq

lemma continuousAt_zero_payoff (i : Row) (N : ℕ) (pi : Joint i)
    [NullSingletonClass ((restrictedLaw i (0,pi)).bidLaw : Measure (Bid i))]
    (mode : ExactTests.Mode) (p : Value i×unitInterval)
    (hp : 0<(baseBid i (p.1,ExactTests.chosen mode p):ℝ)) :
    ContinuousAt (fun x : Value i×unitInterval=>
      expectedUtility i N 0 pi x.1 (ExactTests.chosen mode x)) p := by
  simp_rw [expectedUtility_zero]
  have hmap : Continuous (fun x : Value i×unitInterval=>
      (x.1,baseBid i (x.1,ExactTests.chosen mode x))) :=
    continuous_fst.prodMk ((continuous_baseBid i).comp
      (continuous_fst.prodMk (ExactTests.continuous_chosen i mode)))
  convert! (continuousAt_rawUtility i N (restrictedLaw i (0,pi))
    (p.1,baseBid i (p.1,ExactTests.chosen mode p)) hp).comp
    (f := fun x : Value i×unitInterval=> (x.1,baseBid i (x.1,ExactTests.chosen mode x)))
    hmap.continuousAt using 1

theorem fixed_positive_IC (i : Row) (N : ℕ) (q : unitInterval) (hq : 0<(q:ℝ))
    (eps : ℕ→ unitInterval) (pi : ℕ→ Joint i) (pi0 : Joint i)
    (heps : Tendsto eps atTop (𝓝 0)) (hpi : Tendsto pi atTop (𝓝 pi0))
    (hIC : ∀n,NoisyIC i N (eps n) (pi n))
    [NullSingletonClass ((restrictedLaw i (0,pi0)).bidLaw : Measure (Bid i))] :
    ∀ᵐp∂(pi0.1 : Measure (Value i×unitInterval)),
      expectedUtility i N 0 pi0 p.1 q≤ expectedUtility i N 0 pi0 p.1 p.2 := by
  let f : Value i×unitInterval→ℝ:=fun p=>
    expectedUtility i N 0 pi0 p.1 q-expectedUtility i N 0 pi0 p.1 p.2
  let s : Set (Value i×unitInterval):=
    {p | (baseBid i (p.1,q):ℝ)≤0 ∨ (baseBid i p:ℝ)≤0}
  have hold:=incumbent_good i pi0
  have hnew:=positive_choice_good i pi0 q hq
  have hs : IsClosed s := by
    apply IsClosed.union
    · exact isClosed_le ((continuous_baseBid i).subtype_val.comp
        (continuous_fst.prodMk continuous_const)) continuous_const
    · exact isClosed_le (continuous_baseBid i).subtype_val continuous_const
  have hf : Measurable f :=
    (ExactTests.measurable_utility i N (0,pi0) (some q)).sub
      (ExactTests.measurable_utility i N (0,pi0) none)
  have hc (p : Value i×unitInterval) (hp : p∉s) : ContinuousAt f p := by
    have hn : 0<(baseBid i (p.1,q):ℝ):=lt_of_not_ge (fun h=> hp (Or.inl h))
    have ho : 0<(baseBid i p:ℝ):=lt_of_not_ge (fun h=> hp (Or.inr h))
    exact (continuousAt_zero_payoff i N pi0 (some q) p hn).sub
      (continuousAt_zero_payoff i N pi0 none p ho)
  have hb (p : Value i×unitInterval) : |f p|≤6*Uniform05.t i := by
    have h1:=expectedUtility_bound i N 0 pi0 p.1 q
    have h2:=expectedUtility_bound i N 0 pi0 p.1 p.2
    exact (abs_sub _ _).trans (by linarith [p.1.property.2])
  have ht:=LowBody.ae_nonpos_outside_closed_of_tests
    (pi0.1 : Measure (Value i×unitInterval)) f hf s hs hc
    (mul_nonneg (by norm_num) (Uniform05.t_pos i).le) hb
    (fun a ha _=> ExactTests.actual_limit_tests i N q eps pi pi0 heps hpi hIC hold hnew a ha)
  filter_upwards [ht,hold,hnew] with p hp ho hn
  exact sub_nonpos.mp (hp (by
    rintro (h|h)
    · exact not_le_of_gt hn h
    · exact not_le_of_gt ho h))

abbrev PositiveChoice := {q : unitInterval // 0<(q:ℝ)}

theorem common_positive_IC (i : Row) (N : ℕ)
    (eps : ℕ→ unitInterval) (pi : ℕ→ Joint i) (pi0 : Joint i)
    (heps : Tendsto eps atTop (𝓝 0)) (hpi : Tendsto pi atTop (𝓝 pi0))
    (hIC : ∀n,NoisyIC i N (eps n) (pi n))
    [NullSingletonClass ((restrictedLaw i (0,pi0)).bidLaw : Measure (Bid i))] :
    ∀ᵐp∂(pi0.1 : Measure (Value i×unitInterval)),∀q : unitInterval,
      0<(q:ℝ)→ expectedUtility i N 0 pi0 p.1 q≤ expectedUtility i N 0 pi0 p.1 p.2 := by
  obtain ⟨D,hDc,hDd⟩:=TopologicalSpace.exists_countable_dense PositiveChoice
  have hd : ∀ᵐp∂(pi0.1 : Measure (Value i×unitInterval)),∀q∈D,
      expectedUtility i N 0 pi0 p.1 q.val≤ expectedUtility i N 0 pi0 p.1 p.2 :=
    (ae_ball_iff hDc).mpr (fun q _=> fixed_positive_IC i N q.val q.property
      eps pi pi0 heps hpi hIC)
  filter_upwards [hd,original_value_positive i pi0] with p hp hv
  have hc : Continuous (fun q : PositiveChoice=> expectedUtility i N 0 pi0 p.1 q.val) := by
    have he : (fun q : PositiveChoice=> expectedUtility i N 0 pi0 p.1 q.val) =
        (fun q => rawUtility i N (restrictedLaw i (0,pi0)) p.1 (baseBid i (p.1,q.val))) := by
      funext q
      exact expectedUtility_zero i N pi0 p.1 q.val
    rw [he]
    apply continuous_iff_continuousAt.mpr
    intro q
    have hm : Continuous (fun z : PositiveChoice=>(p.1,baseBid i (p.1,z.val))) :=
      continuous_const.prodMk ((continuous_baseBid i).comp
        (continuous_const.prodMk continuous_subtype_val))
    convert! (continuousAt_rawUtility i N (restrictedLaw i (0,pi0))
      (p.1,baseBid i (p.1,q.val))
      (baseBid_pos_of_choice_pos i p.1 hv q.val q.property)).comp
      (f := fun z : PositiveChoice=> (p.1,baseBid i (p.1,z.val))) hm.continuousAt using 1
  have hs : IsClosed {q : PositiveChoice | expectedUtility i N 0 pi0 p.1 q.val≤
      expectedUtility i N 0 pi0 p.1 p.2} := isClosed_le hc continuous_const
  intro q hq
  have hmem : (⟨q,hq⟩ : PositiveChoice) ∈ closure D := by
    rw [hDd.closure_eq]
    exact mem_univ _
  have hsub : closure D ⊆ {z : PositiveChoice | expectedUtility i N 0 pi0 p.1 z.val≤
      expectedUtility i N 0 pi0 p.1 p.2} := closure_minimal hp hs
  convert! hsub hmem using 1

theorem raw_zero_right_bound (i : Row) (N : ℕ) {err : ℝ} (herr : 0< err) :
    ∃radius : ℝ,0< radius ∧ ∀G : Uniform05.RestrictedLaw i,∀v : Value i,∀b : Bid i,
      0<(b:ℝ)→(b:ℝ)< radius→
      rawUtility i N G v 0≤ rawUtility i N G v b+(1+Uniform05.eta i)*(b:ℝ)+err := by
  obtain ⟨r,hr,h⟩:=ActualAtoms.exists_actual_zero_raise_modulus (M:=N+1) i herr
  refine ⟨r,hr,?_⟩
  intro G v b hb hbr
  let z : Bid i:=⟨0,le_rfl,(Uniform05.cap_pos i).le⟩
  have hrow (kind : Fin N→ Fin 3) (rivals : Fin N→ Bid i) :
      rowPayoff i G (focalRow kind) v (focalBids i kind 0 rivals) 0≤
        rowPayoff i G (focalRow kind) v (focalBids i kind b rivals) 0+
          (1+Uniform05.eta i)*(b:ℝ)+err := by
    let x : OwnBid.Box i (N+1):=(v,G,ActualSurplus.cappedFocalBids i kind z rivals)
    have hf : Function.update (focalBids i kind 0 rivals) 0 (b:ℝ)=
        focalBids i kind b rivals := by
      funext a
      refine Fin.cases ?_ (fun j=>?_) a <;> simp [focalBids]
    have hh:=h (focalRow kind) 0 (ActualSurplus.focalRow_focal_mem kind) x b
      (by simpa [x,SourceContinuity.bids,ActualSurplus.cappedFocalBids,z] using v.property.1)
      (by simpa [x,SourceContinuity.bids,ActualSurplus.cappedFocalBids,z] using hb)
      (by simpa [x,SourceContinuity.bids,ActualSurplus.cappedFocalBids,z] using hbr)
    have he : SourceContinuity.bids i x.2 = focalBids i kind 0 rivals :=
      ActualSurplus.cappedFocalBids_val i kind z rivals
    rw [OwnBid.bids_change,he,hf] at hh
    simp only [focalBids_zero,mul_zero,sub_zero] at hh
    linarith
  have hin (kind : Fin N→ Fin 3) :
      (∫rivals,rowPayoff i G (focalRow kind) v (focalBids i kind 0 rivals) 0
        ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))≤
      (∫rivals,rowPayoff i G (focalRow kind) v (focalBids i kind b rivals) 0
        ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)))+
          (1+Uniform05.eta i)*(b:ℝ)+err := by
    have hnew:=integrable_raw_row i N G kind v b
    have hprice : Integrable (fun _ : Fin N→ Bid i => (1+Uniform05.eta i)*(b:ℝ))
        (rowLaw N G.bidLaw : Measure (Fin N→ Bid i)) := integrable_const _
    have herrI : Integrable (fun _ : Fin N→ Bid i => err)
        (rowLaw N G.bidLaw : Measure (Fin N→ Bid i)) := integrable_const _
    have hh:=integral_mono (integrable_raw_row i N G kind v z)
      ((hnew.add hprice).add herrI) (hrow kind)
    simp only [Pi.add_apply] at hh
    rw [integral_add
      (f := fun rivals : Fin N→Bid i=> rowPayoff i G (focalRow kind) v
        (focalBids i kind b rivals) 0+(1+Uniform05.eta i)*(b:ℝ))
      (g := fun _ : Fin N→Bid i=>err) (hnew.add hprice) herrI,
      integral_add
        (f := fun rivals : Fin N→Bid i=>rowPayoff i G (focalRow kind) v (focalBids i kind b rivals) 0)
        (g := fun _ : Fin N→Bid i=>(1+Uniform05.eta i)*(b:ℝ)) hnew hprice] at hh
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh
  have hh:=(categoryRowLaw i N).expect_mono hin
  simpa only [FiniteLaw.expect_add,FiniteLaw.expect_const,rawUtility] using hh

theorem zero_choice_IC (i : Row) (N : ℕ) (pi0 : Joint i)
    [NullSingletonClass ((restrictedLaw i (0,pi0)).bidLaw : Measure (Bid i))]
    (p : Value i×unitInterval) (hv : 0<(p.1:ℝ))
    (hpos : ∀q : unitInterval,0<(q:ℝ)→
      expectedUtility i N 0 pi0 p.1 q≤ expectedUtility i N 0 pi0 p.1 p.2) :
    expectedUtility i N 0 pi0 p.1 0≤ expectedUtility i N 0 pi0 p.1 p.2 := by
  let G:=restrictedLaw i (0,pi0)
  let q : ℕ→ unitInterval:=noiseSchedule 1
  have hqpos (n : ℕ) : 0<(q n:ℝ):=noiseSchedule_pos 1 (by norm_num) n
  have hq0 : Tendsto q atTop (𝓝 0):=noiseSchedule_tendsto_zero 1
  have hb0 : Tendsto (fun n=> baseBid i (p.1,q n)) atTop (𝓝 (baseBid i (p.1,0))):=
    (continuous_baseBid i).continuousAt.tendsto.comp (tendsto_const_nhds.prodMk_nhds hq0)
  have hpre (n : ℕ) : rawUtility i N G p.1 (baseBid i (p.1,q n))≤
      expectedUtility i N 0 pi0 p.1 p.2 := by
    simpa only [expectedUtility_zero] using hpos (q n) (hqpos n)
  by_cases hfloor : 0<(baseBid i (p.1,0):ℝ)
  · rw [expectedUtility_zero]
    have hlim : Tendsto (fun n=>rawUtility i N G p.1 (baseBid i (p.1,q n))) atTop
        (𝓝 (rawUtility i N G p.1 (baseBid i (p.1,0)))) := by
      convert! (continuousAt_rawUtility i N G (p.1,baseBid i (p.1,0)) hfloor).tendsto.comp
        (tendsto_const_nhds.prodMk_nhds hb0) using 1
    exact le_of_tendsto hlim (Eventually.of_forall hpre)
  · have hz : (baseBid i (p.1,0):ℝ)=0:=
      le_antisymm (le_of_not_gt hfloor) (baseBid i (p.1,0)).property.1
    rw [expectedUtility_zero,hz]
    apply le_of_forall_pos_le_add
    intro err herr
    obtain ⟨r,hr,hbound⟩:=raw_zero_right_bound i N herr
    have hreal : Tendsto (fun n=>(baseBid i (p.1,q n):ℝ)) atTop (𝓝 0) := by
      have hh : Tendsto (fun n=>(baseBid i (p.1,q n):ℝ)) atTop
          (𝓝 (baseBid i (p.1,0):ℝ)) := by
        convert! continuous_subtype_val.continuousAt.tendsto.comp hb0 using 1
      simpa only [hz] using hh
    have hev : ∀ᶠn in atTop,
        rawUtility i N G p.1 0≤ expectedUtility i N 0 pi0 p.1 p.2+
          (1+Uniform05.eta i)*(baseBid i (p.1,q n):ℝ)+err := by
      filter_upwards [hreal.eventually (Iio_mem_nhds hr)] with n hn
      exact (hbound G p.1 _ (baseBid_pos_of_choice_pos i p.1 hv _ (hqpos n)) hn).trans
        (by linarith [hpre n])
    have ht : Tendsto (fun n=> expectedUtility i N 0 pi0 p.1 p.2+
        (1+Uniform05.eta i)*(baseBid i (p.1,q n):ℝ)+err) atTop
        (𝓝 (expectedUtility i N 0 pi0 p.1 p.2+err)) := by
      simpa only [mul_zero,add_zero] using
        (tendsto_const_nhds.add (hreal.const_mul (1+Uniform05.eta i))).add_const err
    exact ge_of_tendsto ht hev

end ExactIC

theorem actual_common_conull_restricted_IC (i : Row) (N : ℕ)
    (eps : ℕ→ unitInterval) (pi : ℕ→ Joint i) (pi0 : Joint i)
    (heps : Tendsto eps atTop (𝓝 0)) (hpi : Tendsto pi atTop (𝓝 pi0))
    (hIC : ∀n,NoisyIC i N (eps n) (pi n))
    [NullSingletonClass ((restrictedLaw i (0,pi0)).bidLaw : Measure (Bid i))] :
    NoisyIC i N 0 pi0 := by
  filter_upwards [ExactIC.common_positive_IC i N eps pi pi0 heps hpi hIC,
    original_value_positive i pi0] with p hp hv
  intro q
  by_cases hq : 0<(q:ℝ)
  · exact hp q hq
  · have hz : q=0 := Subtype.ext (le_antisymm (le_of_not_gt hq) q.property.1)
    rw [hz]
    exact ExactIC.zero_choice_IC i N pi0 p hv hp

theorem disintegrate_exact_restricted_IC (i : Row) (N : ℕ) (pi : Joint i)
    (hIC : NoisyIC i N 0 pi) :
    ∃sigma : Kernel (Value i) unitInterval,IsMarkovKernel sigma ∧
      lowerMeasure i⊗ₘsigma=(pi.1 : Measure (Value i×unitInterval)) ∧
      DisintegratedNoisyIC i N 0 pi sigma ∧
      (∀ᵐ(v : Value i)∂lowerMeasure i,∀ᵐq∂sigma v,∀b : ℝ,
        b∈Icc (Uniform05.floorBid i v) (hiBid i v)→
          rawUtility i N (restrictedLaw i (0,pi)) v b≤
            rawUtility i N (restrictedLaw i (0,pi)) v (baseBid i (v,q))) := by
  let sigma:=(pi.1 : Measure (Value i×unitInterval)).condKernel
  have hmarg : (pi.1 : Measure (Value i×unitInterval)).fst=lowerMeasure i:=pi.property
  have hdis : lowerMeasure i⊗ₘsigma=(pi.1 : Measure (Value i×unitInterval)) := by
    calc
      _=(pi.1 : Measure (Value i×unitInterval)).fst⊗ₘsigma := by rw [hmarg]
      _=_ := Measure.disintegrate _ _
  have hcond : ∀ᵐv∂lowerMeasure i,∀ᵐq∂sigma v,∀q' : unitInterval,
      expectedUtility i N 0 pi v q'≤ expectedUtility i N 0 pi v q := by
    rw [NoisyIC,← hdis] at hIC
    exact Measure.ae_ae_of_ae_compProd hIC
  exact ⟨sigma,inferInstance,hdis,⟨inferInstance,hdis,hcond⟩,
    restricted_IC_disintegrated i N pi sigma hdis
      ((noisy_zero_iff_restricted_IC i N pi).mp hIC)⟩

end FCAppendix.Affine.UniformFinite
