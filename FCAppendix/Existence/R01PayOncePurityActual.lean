import FCAppendix.Existence.R01PayOnceSurplus
import FCAppendix.Existence.R01PayOncePurity
import Mathlib.Probability.Kernel.MeasurableIntegral

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open Purity

namespace Purity

theorem same_value_success_strict {Q : ℝ→ℝ} {w b c : ℝ} (hbc : b<c)
    (hb : Best Q w b) (hc : Best Q w c) : Q b<Q c := by
  have hwb : 0<w-b := pos_of_mul_pos_left hb.2.2.1 hb.2.1.le
  by_contra hnot
  have hQ : 0≤Q b-Q c := sub_nonneg.mpr (le_of_not_gt hnot)
  have hp := mul_nonneg hwb.le hQ
  have hg := mul_pos (sub_pos.mpr hbc) hc.2.1
  have hi := hc.2.2.2 b hb.1
  nlinarith

theorem bid_order_without_monotonicity {Q : ℝ→ℝ} {w w' b b' : ℝ}
    (hw : w<w') (hb : Best Q w b) (hb' : Best Q w' b') : b≤b' := by
  have hs := success_order hw hb hb'
  by_contra hnot
  have hbb' : b'<b := lt_of_not_ge hnot
  have hwb : 0<w-b := pos_of_mul_pos_left hb.2.2.1 hb.2.1.le
  have hp := mul_nonneg hwb.le (sub_nonneg.mpr hs)
  have hg := mul_pos (sub_pos.mpr hbb') hb'.2.1
  have hi := hb.2.2.2 b' hb'.1
  nlinarith

theorem exceptional_countable_without_monotonicity (Q : ℝ→ℝ) : (exceptional Q).Countable := by
  classical
  have hpair : ∀w : exceptional Q,∃b c : ℝ,
      Best Q w.1 b ∧ Best Q w.1 c ∧ Q b<Q c := by
    rintro ⟨w,b,c,hbc,hb,hc⟩
    exact ⟨b,c,hb,hc,same_value_success_strict hbc hb hc⟩
  choose b c hb hc hs using hpair
  have hrat : ∀w : exceptional Q,∃r : ℚ,Q (b w)<r ∧ (r:ℝ)<Q (c w) :=
    fun w=>exists_rat_btwn (hs w)
  choose r hr₁ hr₂ using hrat
  have hstrict : ∀w w' : exceptional Q,w.1<w'.1 → r w<r w' := by
    intro w w' hww'
    have he := success_order hww' (hc w) (hb w')
    exact_mod_cast (hr₂ w).trans_le he |>.trans (hr₁ w')
  have hinj : Function.Injective r := by
    intro w w' he
    apply Subtype.ext
    rcases lt_trichotomy w.1 w'.1 with h|h|h
    · have hh:=hstrict w w' h; rw [he] at hh; exact False.elim (lt_irrefl _ hh)
    · exact h
    · have hh:=hstrict w' w h; rw [he] at hh; exact False.elim (lt_irrefl _ hh)
  letI : Countable (exceptional Q) := hinj.countable
  have hc : (Subtype.val '' (univ : Set (exceptional Q))).Countable :=
    (Set.to_countable _).image Subtype.val
  simpa using hc

theorem exceptional_null_without_monotonicity (Q : ℝ→ℝ) (μ : Measure ℝ)
    (hμ : ∀w,0<w→μ {w}=0) : μ (exceptional Q)=0 := by
  letI : Countable (exceptional Q) := (exceptional_countable_without_monotonicity Q).to_subtype
  have hs : exceptional Q ⊆ ⋃w : exceptional Q,({w.1}:Set ℝ) := by
    intro w hw
    exact mem_iUnion.mpr ⟨⟨w,hw⟩,rfl⟩
  apply measure_mono_null hs
  apply measure_iUnion_null
  rintro ⟨w,b,c,hbc,hb,hc⟩
  exact hμ w (value_pos hb)

theorem unique_best_ae_without_monotonicity (Q : ℝ→ℝ) (μ : Measure ℝ)
    (hμ : ∀w,0<w→μ {w}=0) :
    ∀ᵐw ∂μ,∀b c : ℝ,Best Q w b→Best Q w c→b=c := by
  have hout := measure_eq_zero_iff_ae_notMem.mp (exceptional_null_without_monotonicity Q μ hμ)
  filter_upwards [hout] with w hw
  intro b c hb hc
  rcases lt_trichotomy b c with h|h|h
  · exact False.elim (hw ⟨b,c,h,hb,hc⟩)
  · exact h
  · exact False.elim (hw ⟨c,b,h,hc,hb⟩)

theorem pure_kernel_ae_without_monotonicity (Q : ℝ→ℝ) (μ : Measure ℝ)
    (hμ : ∀w,0<w→μ {w}=0) (σ : Kernel ℝ ℝ) [IsMarkovKernel σ]
    (hbest : ∀ᵐw ∂μ,∀ᵐb ∂σ w,Best Q w b) :
    ∀ᵐw ∂μ,∃b : ℝ,Best Q w b ∧ σ w=Measure.dirac b := by
  filter_upwards [unique_best_ae_without_monotonicity Q μ hμ,hbest] with w hu hw
  obtain ⟨b,hb⟩ := hw.exists
  refine ⟨b,hb,?_⟩
  have he : (fun _ : ℝ=>b)=ᵐ[σ w]id := by
    filter_upwards [hw] with b' hb'
    exact hu b b' hb hb'
  have hm := (Measure.map_congr he : (σ w).map (fun _ : ℝ=>b)=(σ w).map (id:ℝ→ℝ))
  simpa using hm.symm
end Purity

def boundedSuccessQ {W : ℝ} (N n c : ℕ)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (b : ℝ) : ℝ :=
  if hb : b∈Ioc 0 W then positiveQ N n c π (positiveAction ⟨b,hb⟩) else 0

@[simp] theorem boundedSuccessQ_positive {W : ℝ} (N n c : ℕ)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (b : PositiveBid W) :
    boundedSuccessQ N n c π b.1=positiveQ N n c π (positiveAction b) := by
  simp only [boundedSuccessQ,dif_pos b.2]

theorem boundedSuccessQ_best {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (w : Value W) (b : PositiveBid W)
    (hIC : ∀a : FloorAction 0 W,positivePayoff N n c π (w,a)≤
      positivePayoff N n c π (w,positiveAction b))
    (hQ : 0<positiveQ N n c π (positiveAction b)) :
    Purity.Best (boundedSuccessQ N n c π) w.1 b.1 := by
  have hs := positive_bid_bestResponse_strict_surplus N n c hn π w b hIC hQ
  refine ⟨b.2.1,?_,?_,?_⟩
  · simpa only [boundedSuccessQ_positive] using hQ
  · simpa only [boundedSuccessQ_positive,positivePayoff,positiveAction,bid] using hs.2
  · intro b' hb'
    by_cases hband : b'≤W
    · let bpos : PositiveBid W := ⟨b',hb',hband⟩
      have hh := hIC (positiveAction bpos)
      change (w.1-b')*positiveQ N n c π (positiveAction bpos)≤
        (w.1-b.1)*positiveQ N n c π (positiveAction b) at hh
      have he : boundedSuccessQ N n c π b'=positiveQ N n c π (positiveAction bpos) := by
        rw [boundedSuccessQ,dif_pos (show b'∈Ioc 0 W from ⟨hb',hband⟩)]
      rw [he,boundedSuccessQ_positive]
      exact hh
    · have hout : b'∉Ioc 0 W := fun h=>hband h.2
      rw [boundedSuccessQ,dif_neg hout,mul_zero,boundedSuccessQ_positive]
      exact hs.2.le

theorem unique_bounded_best_ae {W : ℝ} (Q : ℝ→ℝ) (μ : Measure (Value W))
    (hμ : ∀w : Value W,0<w.1→μ {w}=0) :
    ∀ᵐw ∂μ,∀b c : ℝ,Purity.Best Q w.1 b→Purity.Best Q w.1 c→b=c := by
  let S : Set (Value W) := Subtype.val ⁻¹' Purity.exceptional Q
  have hcount : S.Countable := (Purity.exceptional_countable_without_monotonicity Q).preimage Subtype.val_injective
  letI : Countable S := hcount.to_subtype
  have hnull : μ S=0 := by
    have hs : S ⊆ ⋃w : S,({w.1}:Set (Value W)) := by
      intro w hw
      exact mem_iUnion.mpr ⟨⟨w,hw⟩,rfl⟩
    apply measure_mono_null hs
    apply measure_iUnion_null
    rintro ⟨w,b,c,hbc,hb,hc⟩
    exact hμ w (Purity.value_pos hb)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with w hw
  intro b c hb hc
  rcases lt_trichotomy b c with h|h|h
  · exact False.elim (hw ⟨b,c,h,hb,hc⟩)
  · exact h
  · exact False.elim (hw ⟨c,b,h,hc,hb⟩)

theorem actual_bounded_kernel_pure_ae {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (μ : Measure (Value W)) (hμ : ∀w : Value W,0<w.1→μ {w}=0)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (σ : Kernel (Value W) (FloorAction 0 W)) [IsMarkovKernel σ]
    (hIC : ∀ᵐw ∂μ,∀ᵐa ∂σ w,∀a' : FloorAction 0 W,
      positivePayoff N n c π (w,a')≤positivePayoff N n c π (w,a))
    (hpositive : ∀ᵐw ∂μ,∀ᵐa ∂σ w,0<w.1→0<bid a)
    (hservice : ∀ᵐw ∂μ,∀ᵐa ∂σ w,0<w.1→0<positiveQ N n c π a) :
    ∀ᵐw ∂μ,0<w.1→∃b : PositiveBid W,
      σ w=Measure.dirac (positiveAction b) ∧ Purity.Best (boundedSuccessQ N n c π) w.1 b.1 := by
  filter_upwards [unique_bounded_best_ae (boundedSuccessQ N n c π) μ hμ,
    hIC,hpositive,hservice] with w hu hwIC hwpos hwservice
  intro hw
  have hbest : ∀ᵐa ∂σ w,0<bid a ∧ Purity.Best (boundedSuccessQ N n c π) w.1 (bid a) := by
    filter_upwards [hwIC,hwpos,hwservice] with a ha hpos hs
    refine ⟨hpos hw,?_⟩
    cases a with
    | inl u => have h:=hpos hw; simp [bid] at h
    | inr b =>
      exact boundedSuccessQ_best N n c hn π w ⟨b.1,hpos hw,b.2.2⟩ ha (hs hw)
  obtain ⟨a,ha⟩ := hbest.exists
  cases a with
  | inl u => simp [bid] at ha
  | inr b =>
    let bp : PositiveBid W := ⟨b.1,ha.1,b.2.2⟩
    refine ⟨bp,?_,ha.2⟩
    have he : (fun _ : FloorAction 0 W=>positiveAction bp)=ᵐ[σ w]id := by
      filter_upwards [hbest] with a' ha'
      have hb := hu b.1 (bid a') ha.2 ha'.2
      cases a' with
      | inl u => simp [bid] at ha'
      | inr b' =>
        change Sum.inr (⟨b.1,b.2⟩ : Icc 0 W)=Sum.inr b'
        exact congrArg Sum.inr (Subtype.ext hb)
    have hm := (Measure.map_congr he : (σ w).map (fun _ : FloorAction 0 W=>positiveAction bp)=
      (σ w).map (id:FloorAction 0 W→FloorAction 0 W))
    simpa using hm.symm

def meanBoundedBid {W : ℝ} (σ : Kernel (Value W) (FloorAction 0 W)) (w : Value W) : ℝ :=
  ∫a,bid a ∂σ w

theorem measurable_meanBoundedBid {W : ℝ} (σ : Kernel (Value W) (FloorAction 0 W)) :
    Measurable (meanBoundedBid σ) :=
  continuous_bid.stronglyMeasurable.integral_kernel.measurable

theorem meanBoundedBid_eq_of_dirac {W : ℝ} (σ : Kernel (Value W) (FloorAction 0 W))
    (w : Value W) (b : PositiveBid W) (hσ : σ w=Measure.dirac (positiveAction b)) :
    meanBoundedBid σ w=b.1 := by
  simp [meanBoundedBid,hσ,positiveAction,bid]

theorem actual_bounded_measurable_ordered_purity {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (μ : Measure (Value W)) (hμ : ∀w : Value W,0<w.1→μ {w}=0)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (σ : Kernel (Value W) (FloorAction 0 W)) [IsMarkovKernel σ]
    (hIC : ∀ᵐw ∂μ,∀ᵐa ∂σ w,∀a' : FloorAction 0 W,
      positivePayoff N n c π (w,a')≤positivePayoff N n c π (w,a))
    (hpositive : ∀ᵐw ∂μ,∀ᵐa ∂σ w,0<w.1→0<bid a)
    (hservice : ∀ᵐw ∂μ,∀ᵐa ∂σ w,0<w.1→0<positiveQ N n c π a) :
    ∃E : Set (Value W),μ Eᶜ=0 ∧ Measurable (meanBoundedBid σ) ∧
      MonotoneOn (meanBoundedBid σ) (E∩{w|0<w.1}) ∧
      (∀w∈E,0<w.1→∃b : PositiveBid W,meanBoundedBid σ w=b.1 ∧
        σ w=Measure.dirac (positiveAction b) ∧ Purity.Best (boundedSuccessQ N n c π) w.1 b.1) := by
  let E : Set (Value W) := {w|0<w.1→∃b : PositiveBid W,
    σ w=Measure.dirac (positiveAction b) ∧ Purity.Best (boundedSuccessQ N n c π) w.1 b.1}
  have hE : ∀ᵐw ∂μ,w∈E := actual_bounded_kernel_pure_ae N n c hn μ hμ π σ hIC hpositive hservice
  refine ⟨E,?_,measurable_meanBoundedBid σ,?_,?_⟩
  · exact (ae_iff.mp hE)
  · intro w hw w' hw' hww'
    obtain ⟨b,hb,hbest⟩ := hw.1 hw.2
    obtain ⟨b',hb',hbest'⟩ := hw'.1 hw'.2
    have he := meanBoundedBid_eq_of_dirac σ w b hb
    have he' := meanBoundedBid_eq_of_dirac σ w' b' hb'
    rcases lt_or_eq_of_le hww' with hlt|heq
    · rw [he,he']
      exact Purity.bid_order_without_monotonicity hlt hbest hbest'
    · rw [heq]
  · intro w hw hwp
    obtain ⟨b,hb,hbest⟩ := hw hwp
    exact ⟨b,meanBoundedBid_eq_of_dirac σ w b hb,hb,hbest⟩

end FCAppendix.Existence.PayOnceBounded
