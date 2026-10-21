import FCAppendix.Affine.Uniform07Finishing.Native.CommonBoundary
import FCAppendix.Affine.Uniform07Finishing.Native.OriginalLawTransport
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.Compact

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical

theorem exists_measurable_least_compact_section
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (U : ℝ) (C : Set (X × Icc (0 : ℝ) U)) (hC : IsClosed C)
    (hne : ∀ x : X, ∃ b : Icc (0 : ℝ) U, (x, b) ∈ C) :
    ∃ s : X → Icc (0 : ℝ) U, Measurable s ∧
      (∀ x, (x, s x) ∈ C) ∧
      ∀ x b, (x, b) ∈ C → s x ≤ b := by
  have hf (x : X) : IsCompact {b : Icc (0 : ℝ) U | (x, b) ∈ C} :=
    (hC.preimage (continuous_const.prodMk continuous_id)).isCompact
  have hex (x : X) : ∃ b, IsLeast {b : Icc (0 : ℝ) U | (x, b) ∈ C} b :=
    (hf x).exists_isLeast (hne x)
  choose s hs using hex
  have hval : Measurable (fun x : X => (s x : ℝ)) := by
    apply measurable_of_Iic
    intro r
    let D : Set (X × Icc (0 : ℝ) U) := C ∩ {z | (z.2 : ℝ) ≤ r}
    have hD : IsClosed D := hC.inter
      (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const)
    have he : (fun x : X => (s x : ℝ)) ⁻¹' Iic r = Prod.fst '' D := by
      ext x
      constructor
      · intro hx
        exact ⟨(x, s x), ⟨(hs x).1, hx⟩, rfl⟩
      · rintro ⟨⟨y, b⟩, ⟨hy, hbr⟩, rfl⟩
        exact (show (s y : ℝ) ≤ (b : ℝ) from (hs y).2 hy).trans hbr
    rw [he]
    exact (isClosedMap_fst_of_compactSpace D hD).measurableSet
  refine ⟨s, hval.subtype_mk, fun x => (hs x).1, ?_⟩
  exact fun x b hb => (hs x).2 hb

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def actualLowerBestGraph (Γ : FiniteGame m 2 c Seed) (U : ℝ) :
    Set (ℝ × Icc (0 : ℝ) U) :=
  {z | ∀ i : Fin m, ∀ a' : JointAction 2,
    (problem Γ i).payoff z.1 a' ≤
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)}

theorem actualLowerBestGraph_closed (Γ : FiniteGame m 2 c Seed) (U : ℝ)
    (hpay : ∀ i : Fin m, Continuous (fun z : ℝ × Icc (0 : ℝ) U =>
      (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2))) :
    IsClosed (actualLowerBestGraph Γ U) := by
  have he : actualLowerBestGraph Γ U = ⋂ i : Fin m, ⋂ a' : JointAction 2,
      {z | (problem Γ i).payoff z.1 a' ≤
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)} := by
    ext z
    simp only [actualLowerBestGraph, mem_setOf_eq, mem_iInter]
  rw [he]
  exact isClosed_iInter (fun i => isClosed_iInter (fun a' =>
    isClosed_le ((actual_payoff_continuous_value Γ i a').comp continuous_fst) (hpay i)))

def actualLowerGoodPair (Γ : FiniteGame m 2 c Seed) (U : ℝ)
    (z : ℝ × JointAction 2) : Prop :=
  z.2.bid ≤ U ∧ z.2.routeCount = 2 ∧
    ∀ i : Fin m, ∀ a' : JointAction 2,
      (problem Γ i).payoff z.1 a' ≤ (problem Γ i).payoff z.1 z.2

theorem measurableSet_actualLowerGoodPair (Γ : FiniteGame m 2 c Seed) (U : ℝ) :
    MeasurableSet {z | actualLowerGoodPair Γ U z} := by
  have hb : MeasurableSet {z : ℝ × JointAction 2 | z.2.bid ≤ U} :=
    measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_const
  have hr : MeasurableSet {z : ℝ × JointAction 2 | z.2.routeCount = 2} :=
    measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const
  have hi : MeasurableSet {z : ℝ × JointAction 2 |
      ∀ i : Fin m, (problem Γ i).BestResponse z.1 z.2} := by
    have he : {z : ℝ × JointAction 2 | ∀ i : Fin m,
        (problem Γ i).BestResponse z.1 z.2} =
        ⋂ i : Fin m, {z | (problem Γ i).BestResponse z.1 z.2} := by
      ext z
      simp only [mem_setOf_eq, mem_iInter]
    rw [he]
    exact MeasurableSet.iInter (measurableSet_bestResponse Γ)
  exact hb.inter (hr.inter hi)

theorem actual_lower_common_good_of_usersOptimal (Γ : FiniteGame m 2 c Seed)
    (U t : ℝ) (hu : UsersOptimal Γ)
    (hshape : ∀ᵐ z ∂Γ.F ⊗ₘ Γ.σ, z.1 ∈ Ioo 0 t →
      z.2.bid ≤ U ∧ z.2.routeCount = 2) :
    ∀ᵐ z ∂Γ.F ⊗ₘ Γ.σ, z.1 ∈ Ioo 0 t → actualLowerGoodPair Γ U z := by
  filter_upwards [hshape, (usersOptimal_iff_common_all_actions Γ).mp hu] with z hz hi
  intro hv
  exact ⟨(hz hv).1, (hz hv).2, hi⟩

theorem sourceLowerBroadcastAction_eq (U : ℝ) (a : JointAction 2)
    (hb : a.bid ≤ U) (hr : a.routeCount = 2) :
    sourceLowerBroadcastAction U ⟨a.bid, a.bid_nonneg, hb⟩ = a := by
  cases a with
  | mk b hb k hk =>
      dsimp at hr
      subst k
      rfl

def actualBidPayment (Γ : FiniteGame m 2 c Seed) (i : Fin m) (a : JointAction 2) : ℝ :=
  a.bid * ((problem Γ i).outcome a).charge Γ.A

theorem actualBidPayment_nonneg (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (a : JointAction 2) : 0 ≤ actualBidPayment Γ i a :=
  mul_nonneg a.bid_nonneg (((problem Γ i).outcome a).charge_nonneg Γ.A)

theorem actualBidPayment_le_two_bid (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (a : JointAction 2) : actualBidPayment Γ i a ≤ 2*a.bid := by
  have hc := (((problem Γ i).outcome a).charge_le_load Γ.A).trans
    ((problem Γ i).outcome a).load_le_n
  have hh := mul_le_mul_of_nonneg_left hc a.bid_nonneg
  simpa only [actualBidPayment, Nat.cast_ofNat, mul_comm] using hh

theorem actualBidPayment_ge_bid_success (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (a : JointAction 2) : a.bid * ((problem Γ i).outcome a).success ≤
      actualBidPayment Γ i a :=
  mul_le_mul_of_nonneg_left (((problem Γ i).outcome a).success_le_charge Γ.A) a.bid_nonneg

theorem actual_zero_base_payoff (Γ : FiniteGame m 2 c Seed) (hg : Γ.g = 0)
    (i : Fin m) (v : ℝ) (a : JointAction 2) :
    (problem Γ i).payoff v a =
      v*((problem Γ i).outcome a).success - actualBidPayment Γ i a := by
  change ((problem Γ i).outcome a).utility v a.bid Γ.g Γ.A Γ.G = _
  rw [CountLaw.utility_eq, hg, zero_mul, sub_zero]
  rfl

theorem exists_common_lower_anchor (Γ : FiniteGame m 2 c Seed) (U t : ℝ)
    (ht1 : t ≤ 1) (hF : Γ.F = Uniform07.uniformLaw)
    (hcommon : ∀ᵐ z ∂Γ.F ⊗ₘ Γ.σ,
      z.1 ∈ Ioo 0 t → actualLowerGoodPair Γ U z)
    {v : ℝ} (hv : v ∈ Ioo 0 t) :
    ∃ w : ℝ, 0 < w ∧ w < v ∧ ∃ a : JointAction 2,
      actualLowerGoodPair Γ U (w, a) := by
  have hcond := Measure.ae_ae_of_ae_compProd hcommon
  have hmass : Γ.F (Ioo 0 v) ≠ 0 := by
    rw [hF]
    change (volume.restrict (Icc (0 : ℝ) 1)) (Ioo 0 v) ≠ 0
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (show Ioo 0 v ⊆ Icc (0 : ℝ) 1 from
        fun _ hx => ⟨hx.1.le, hx.2.le.trans (hv.2.le.trans ht1)⟩), Real.volume_Ioo]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by simpa only [sub_zero] using hv.1)
  obtain ⟨w, hw, ha⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass
    (ae_restrict_of_ae hcond)
  obtain ⟨a, haa⟩ := ha.exists
  exact ⟨w, hw.1, hw.2, a, haa ⟨hw.1, hw.2.trans hv.2⟩⟩

theorem actual_best_zero_bid_limit (Γ : FiniteGame m 2 c Seed) (U : ℝ)
    (hg : Γ.g = 0) (w v : ℝ) (hw : 0 < w) (hwv : w < v)
    (a : JointAction 2) (ha : actualLowerGoodPair Γ U (w, a))
    (vn : ℕ → ℝ) (bn : ℕ → Icc (0 : ℝ) U) (b₀ : Icc (0 : ℝ) U)
    (hb₀ : (b₀ : ℝ) = 0) (hvn0 : ∀ n, 0 ≤ vn n)
    (hvn : Tendsto vn atTop (𝓝 v))
    (hbn : Tendsto (fun n => (bn n : ℝ)) atTop (𝓝 0))
    (hbest : ∀ n, ∀ i : Fin m, ∀ a' : JointAction 2,
      (problem Γ i).payoff (vn n) a' ≤
        (problem Γ i).payoff (vn n) (sourceLowerBroadcastAction U (bn n))) :
    ∀ i : Fin m, ∀ a' : JointAction 2,
      (problem Γ i).payoff v a' ≤
        (problem Γ i).payoff v (sourceLowerBroadcastAction U b₀) := by
  intro i a'
  let an : ℕ → JointAction 2 := fun n => sourceLowerBroadcastAction U (bn n)
  let Sa := ((problem Γ i).outcome a).success
  let Ca := actualBidPayment Γ i a
  have hwa : (problem Γ i).BestResponse w a := ha.2.2 i
  have hCn (n : ℕ) : actualBidPayment Γ i (an n) ≤ 2*(bn n : ℝ) :=
    actualBidPayment_le_two_bid Γ i (an n)
  have hCa0 : Ca = 0 := by
    have hle : ∀ᶠ n in atTop, Ca ≤ 2*(bn n : ℝ) := by
      filter_upwards [hvn.eventually (eventually_gt_nhds hwv)] with n hwn
      have hs := (problem Γ i).success_order w (vn n) hwn a (an n) hwa (hbest n i)
      have hi := hwa (an n)
      rw [actual_zero_base_payoff Γ hg i w (an n), actual_zero_base_payoff Γ hg i w a] at hi
      have hpos := mul_nonneg hw.le (sub_nonneg.mpr hs)
      change _ ≤ w*Sa-Ca at hi
      exact (show Ca ≤ actualBidPayment Γ i (an n) by nlinarith).trans (hCn n)
    have hz : Ca ≤ 0 := by
      have hh := ge_of_tendsto (hbn.const_mul 2) hle
      simpa only [mul_zero] using hh
    exact le_antisymm hz (actualBidPayment_nonneg Γ i a)
  have hbound : ∀ n, w*(problem Γ i).payoff (vn n) a' ≤
      vn n*(w*Sa+2*(bn n : ℝ)) := by
    intro n
    have hwaN := hwa (an n)
    rw [actual_zero_base_payoff Γ hg i w (an n), actual_zero_base_payoff Γ hg i w a] at hwaN
    change w*((problem Γ i).outcome (an n)).success-actualBidPayment Γ i (an n) ≤
      w*Sa-Ca at hwaN
    rw [hCa0, sub_zero] at hwaN
    have hs : w*((problem Γ i).outcome (an n)).success ≤ w*Sa+2*(bn n : ℝ) :=
      by linarith [hCn n]
    have hu := hbest n i a'
    rw [actual_zero_base_payoff Γ hg i (vn n) (an n)] at hu
    have hu' : (problem Γ i).payoff (vn n) a' ≤
        vn n*((problem Γ i).outcome (an n)).success :=
      hu.trans (sub_le_self _ (actualBidPayment_nonneg Γ i (an n)))
    have hl := mul_le_mul_of_nonneg_left hu' hw.le
    have hr := mul_le_mul_of_nonneg_left hs (hvn0 n)
    nlinarith
  have hleft := ((actual_payoff_continuous_value Γ i a').tendsto v).comp hvn
  have hright : Tendsto (fun n => vn n*(w*Sa+2*(bn n : ℝ))) atTop (𝓝 (v*(w*Sa))) := by
    simpa only [mul_zero, add_zero] using hvn.mul
      ((tendsto_const_nhds (x := w*Sa)).add (hbn.const_mul 2))
  have hlim := le_of_tendsto_of_tendsto (hleft.const_mul w) hright
    (Eventually.of_forall hbound)
  have hu : (problem Γ i).payoff v a' ≤ v*Sa := by nlinarith
  by_cases hab : a.bid = 0
  · have hb : (⟨a.bid, a.bid_nonneg, ha.1⟩ : Icc (0 : ℝ) U) = b₀ :=
      Subtype.ext (hab.trans hb₀.symm)
    have he : sourceLowerBroadcastAction U b₀ = a := by
      rw [← hb]
      exact sourceLowerBroadcastAction_eq U a ha.1 ha.2.1
    rw [he, actual_zero_base_payoff Γ hg i v a]
    change (problem Γ i).payoff v a' ≤ v*Sa-Ca
    rw [hCa0, sub_zero]
    exact hu
  · have hbpos : 0 < a.bid := lt_of_le_of_ne a.bid_nonneg (Ne.symm hab)
    have hs0 : Sa = 0 := by
      have hh := actualBidPayment_ge_bid_success Γ i a
      change a.bid*Sa ≤ Ca at hh
      rw [hCa0] at hh
      have hs := ((problem Γ i).outcome a).success_nonneg
      dsimp only [Sa] at *
      nlinarith
    rw [hs0, mul_zero] at hu
    apply hu.trans
    rw [actual_zero_base_payoff Γ hg i]
    change 0 ≤ v*((problem Γ i).outcome (sourceLowerBroadcastAction U b₀)).success-
      (b₀ : ℝ)*((problem Γ i).outcome (sourceLowerBroadcastAction U b₀)).charge Γ.A
    rw [hb₀, zero_mul, sub_zero]
    exact mul_nonneg (hw.trans hwv).le ((problem Γ i).outcome _).success_nonneg

def actualLowerPositiveBestGraph (Γ : FiniteGame m 2 c Seed) (U t : ℝ) :
    Set (Ioo (0 : ℝ) t × Icc (0 : ℝ) U) :=
  {z | (z.1.1, z.2) ∈ actualLowerBestGraph Γ U}

theorem actualLowerPositiveBestGraph_closed (Γ : FiniteGame m 2 c Seed) (U t : ℝ)
    (ht1 : t ≤ 1) (hF : Γ.F = Uniform07.uniformLaw) (hg : Γ.g = 0)
    (hpay : ∀ i : Fin m, ∀ z : ℝ × Icc (0 : ℝ) U, 0 < (z.2 : ℝ) →
      ContinuousAt (fun z : ℝ × Icc (0 : ℝ) U =>
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)) z)
    (hcommon : ∀ᵐ z ∂Γ.F ⊗ₘ Γ.σ,
      z.1 ∈ Ioo 0 t → actualLowerGoodPair Γ U z) :
    IsClosed (actualLowerPositiveBestGraph Γ U t) := by
  apply IsSeqClosed.isClosed
  intro z z₀ hz hlim
  have hv : Tendsto (fun n => (z n).1.1) atTop (𝓝 z₀.1.1) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto z₀).comp hlim
  have hb : Tendsto (fun n => ((z n).2 : ℝ)) atTop (𝓝 (z₀.2 : ℝ)) :=
    ((continuous_subtype_val.comp continuous_snd).tendsto z₀).comp hlim
  change ∀ i : Fin m, ∀ a' : JointAction 2, _ ≤ _
  by_cases hb₀ : (z₀.2 : ℝ) = 0
  · obtain ⟨w, hw, hwv, a, ha⟩ := exists_common_lower_anchor Γ U t ht1 hF hcommon z₀.1.2
    apply actual_best_zero_bid_limit Γ U hg w z₀.1.1 hw hwv a ha
      (fun n => (z n).1.1) (fun n => (z n).2) z₀.2 hb₀
      (fun n => (z n).1.2.1.le) hv
    · simpa only [hb₀] using hb
    · exact hz
  · have hbpos : 0 < (z₀.2 : ℝ) := lt_of_le_of_ne z₀.2.2.1 (Ne.symm hb₀)
    have hp : Tendsto (fun n => ((z n).1.1, (z n).2)) atTop (𝓝 (z₀.1.1, z₀.2)) :=
      (((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).tendsto z₀).comp hlim
    intro i a'
    exact le_of_tendsto_of_tendsto
      (((actual_payoff_continuous_value Γ i a').tendsto z₀.1.1).comp hv)
      ((hpay i (z₀.1.1, z₀.2) hbpos).tendsto.comp hp)
      (Eventually.of_forall (fun n => hz n i a'))

theorem actual_lower_best_section_nonempty (Γ : FiniteGame m 2 c Seed)
    (U t : ℝ) (_ht : 0 < t) (ht1 : t ≤ 1)
    (hF : Γ.F = Uniform07.uniformLaw) (hg : Γ.g = 0)
    (hpay : ∀ i : Fin m, ∀ z : ℝ × Icc (0 : ℝ) U, 0 < (z.2 : ℝ) →
      ContinuousAt (fun z : ℝ × Icc (0 : ℝ) U =>
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)) z)
    (hcommon : ∀ᵐ z ∂Γ.F ⊗ₘ Γ.σ,
      z.1 ∈ Ioo 0 t → actualLowerGoodPair Γ U z) :
    ∀ v ∈ Ioo 0 t, ∃ b : Icc (0 : ℝ) U,
      (v, b) ∈ actualLowerBestGraph Γ U := by
  let S : Set (Ioo (0 : ℝ) t) := Prod.fst '' actualLowerPositiveBestGraph Γ U t
  have hS : IsClosed S :=
    isClosedMap_fst_of_compactSpace _
      (actualLowerPositiveBestGraph_closed Γ U t ht1 hF hg hpay hcommon)
  have hcond : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v,
      v ∈ Ioo 0 t → actualLowerGoodPair Γ U (v, a) :=
    Measure.ae_ae_of_ae_compProd hcommon
  have hfull : ∀ᵐ v ∂Γ.F, ∀ hv : v ∈ Ioo 0 t, (⟨v, hv⟩ : Ioo (0 : ℝ) t) ∈ S := by
    filter_upwards [hcond] with v hv
    intro hvt
    obtain ⟨a, ha⟩ := hv.exists
    have hg := ha hvt
    let b : Icc (0 : ℝ) U := ⟨a.bid, a.bid_nonneg, hg.1⟩
    have hab : sourceLowerBroadcastAction U b = a :=
      sourceLowerBroadcastAction_eq U a hg.1 hg.2.1
    refine ⟨(⟨v, hvt⟩, b), ?_, rfl⟩
    change ∀ i a', _ ≤ _
    rw [hab]
    exact hg.2.2
  rw [hF] at hfull
  change ∀ᵐ v ∂volume.restrict (Icc (0 : ℝ) 1),
    ∀ hv : v ∈ Ioo 0 t, (⟨v, hv⟩ : Ioo (0 : ℝ) t) ∈ S at hfull
  have hvol : ∀ᵐ v ∂(volume : Measure ℝ),
      ∀ hv : v ∈ Ioo 0 t, (⟨v, hv⟩ : Ioo (0 : ℝ) t) ∈ S := by
    have hf := (ae_restrict_iff' measurableSet_Icc).mp hfull
    filter_upwards [hf] with v hv
    intro hvt
    exact hv ⟨hvt.1.le, hvt.2.le.trans ht1⟩ hvt
  let O : Set ℝ := (fun v : Ioo (0 : ℝ) t => (v : ℝ)) '' Sᶜ
  have hO : IsOpen O :=
    (isOpen_Ioo.isOpenMap_subtype_val) Sᶜ hS.isOpen_compl
  have hOae : ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Oᶜ := by
    filter_upwards [hvol] with v hv
    rintro ⟨w, hw, hwv⟩
    change w.1 = v at hwv
    subst v
    exact hw (hv w.2)
  have hDense : Dense Oᶜ := Measure.dense_of_ae hOae
  have hAll : Oᶜ = univ := hO.isClosed_compl.closure_eq.symm.trans hDense.closure_eq
  intro v hv
  have hvO : v ∉ O := by change v ∈ Oᶜ; rw [hAll]; trivial
  have hvS : (⟨v, hv⟩ : Ioo (0 : ℝ) t) ∈ S := by
    by_contra hn
    exact hvO ⟨⟨v, hv⟩, hn, rfl⟩
  rcases hvS with ⟨⟨w, b⟩, hb, hwb⟩
  have he : w.1 = v := congrArg Subtype.val hwb
  exact ⟨b, by simpa only [actualLowerPositiveBestGraph, mem_setOf_eq, he] using hb⟩

theorem exists_actual_measurable_lower_best_bid (Γ : FiniteGame m 2 c Seed)
    (U t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hF : Γ.F = Uniform07.uniformLaw) (hg : Γ.g = 0)
    (hpay : ∀ i : Fin m, ∀ z : ℝ × Icc (0 : ℝ) U, 0 < (z.2 : ℝ) →
      ContinuousAt (fun z : ℝ × Icc (0 : ℝ) U =>
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)) z)
    (hcommon : ∀ᵐ z ∂Γ.F ⊗ₘ Γ.σ,
      z.1 ∈ Ioo 0 t → actualLowerGoodPair Γ U z) :
    ∃ b : Ioo (0 : ℝ) t → Icc (0 : ℝ) U, Measurable b ∧
      ∀ v : Ioo (0 : ℝ) t, ∀ i : Fin m, ∀ a' : JointAction 2,
        (problem Γ i).payoff v.1 a' ≤
          (problem Γ i).payoff v.1 (sourceLowerBroadcastAction U (b v)) := by
  let C := actualLowerPositiveBestGraph Γ U t
  have hC : IsClosed C := actualLowerPositiveBestGraph_closed Γ U t ht1 hF hg hpay hcommon
  have hne : ∀ v : Ioo (0 : ℝ) t, ∃ b : Icc (0 : ℝ) U, (v, b) ∈ C :=
    fun v => actual_lower_best_section_nonempty Γ U t ht ht1 hF hg hpay hcommon v.1 v.2
  obtain ⟨b, hb, hbest, _⟩ := exists_measurable_least_compact_section U C hC hne
  exact ⟨b, hb, hbest⟩

def lowerValuePoint (t : ℝ) (ht : 0 < t) (v : ℝ) : Ioo (0 : ℝ) t :=
  ⟨if v ∈ Ioo 0 t then v else t / 2, by
    split_ifs with hv
    · exact hv
    · constructor <;> linarith⟩

theorem lowerValuePoint_measurable (t : ℝ) (ht : 0 < t) :
    Measurable (lowerValuePoint t ht) := by
  exact (measurable_id.ite measurableSet_Ioo measurable_const).subtype_mk

theorem lowerValuePoint_eq (t : ℝ) (ht : 0 < t) {v : ℝ} (hv : v ∈ Ioo 0 t) :
    lowerValuePoint t ht v = ⟨v, hv⟩ := by
  apply Subtype.ext
  simp only [lowerValuePoint, if_pos hv]

def actualGoodLowerValues (Γ : FiniteGame m 2 c Seed) (U : ℝ) : Set ℝ :=
  {v | Γ.σ v {a | ¬ actualLowerGoodPair Γ U (v, a)} = 0}

theorem measurableSet_actualGoodLowerValues (Γ : FiniteGame m 2 c Seed) (U : ℝ) :
    MeasurableSet (actualGoodLowerValues Γ U) :=
  measurableSet_eq_fun (Kernel.measurable_kernel_prodMk_left
    (measurableSet_actualLowerGoodPair Γ U).compl) measurable_const

theorem actualGoodLowerValues_iff (Γ : FiniteGame m 2 c Seed) (U v : ℝ) :
    v ∈ actualGoodLowerValues Γ U ↔ ∀ᵐ a ∂Γ.σ v, actualLowerGoodPair Γ U (v, a) := by
  exact ae_iff.symm

theorem exists_actual_lower_fixed_value_version (Γ : FiniteGame m 2 c Seed)
    (U t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hF : Γ.F = Uniform07.uniformLaw) (hg : Γ.g = 0)
    (hpay : ∀ i : Fin m, ∀ z : ℝ × Icc (0 : ℝ) U, 0 < (z.2 : ℝ) →
      ContinuousAt (fun z : ℝ × Icc (0 : ℝ) U =>
        (problem Γ i).payoff z.1 (sourceLowerBroadcastAction U z.2)) z)
    (hcommon : ∀ᵐ z ∂Γ.F ⊗ₘ Γ.σ,
      z.1 ∈ Ioo 0 t → actualLowerGoodPair Γ U z) :
    ∃ κ : Kernel ℝ (JointAction 2), ∃ hκM : IsMarkovKernel κ,
      κ =ᵐ[Γ.F] Γ.σ ∧
      (Γ.F ⊗ₘ κ = Γ.F ⊗ₘ Γ.σ) ∧
      (∀ v, v ∉ Ioo 0 t → κ v = Γ.σ v) ∧
      ∀ v : ℝ, 0 < v → v < t → ∀ᵐ a ∂κ v,
        a.bid ≤ U ∧ a.routeCount = 2 ∧
        ∀ i : Fin m, ∀ a' : JointAction 2,
          (problem (@withStrategy m 2 c Seed _ Γ κ hκM) i).payoff v a' ≤
            (problem (@withStrategy m 2 c Seed _ Γ κ hκM) i).payoff v a := by
  obtain ⟨b, hb, hbest⟩ :=
    exists_actual_measurable_lower_best_bid Γ U t ht ht1 hF hg hpay hcommon
  let a : ℝ → JointAction 2 :=
    fun v => sourceLowerBroadcastAction U (b (lowerValuePoint t ht v))
  have ha : Measurable a := (sourceLowerBroadcastAction_measurable U).comp
    (hb.comp (lowerValuePoint_measurable t ht))
  have hagood : ∀ v ∈ Ioo 0 t, actualLowerGoodPair Γ U (v, a v) := by
    intro v hv
    refine ⟨(b (lowerValuePoint t ht v)).2.2, rfl, ?_⟩
    rw [show a v = sourceLowerBroadcastAction U (b ⟨v, hv⟩) by
      dsimp [a]; rw [lowerValuePoint_eq t ht hv]]
    exact hbest ⟨v, hv⟩
  let E : Set ℝ := Ioo 0 t ∩ (actualGoodLowerValues Γ U)ᶜ
  have hE : MeasurableSet E :=
    measurableSet_Ioo.inter (measurableSet_actualGoodLowerValues Γ U).compl
  have hcond : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v,
      v ∈ Ioo 0 t → actualLowerGoodPair Γ U (v, a) :=
    Measure.ae_ae_of_ae_compProd hcommon
  have hnull : Γ.F E = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hcond] with v hv
    intro hve
    apply hve.2
    apply (actualGoodLowerValues_iff Γ U v).mpr
    filter_upwards [hv] with a ha
    exact ha hve.1
  let κ := patchStrategy Γ E hE a ha
  have hκ : κ =ᵐ[Γ.F] Γ.σ := patchStrategy_ae_eq Γ E hE hnull a ha
  refine ⟨κ, inferInstance, hκ, Measure.compProd_congr hκ, ?_, ?_⟩
  · intro v hv
    exact patchStrategy_off Γ E hE a ha (fun hve => hv hve.1)
  · intro v hv0 hvt
    have hv : v ∈ Ioo 0 t := ⟨hv0, hvt⟩
    have hpure : ∀ᵐ a' ∂κ v, actualLowerGoodPair Γ U (v, a') := by
      by_cases hve : v ∈ E
      · rw [show κ v = Measure.dirac (a v) from patchStrategy_at Γ E hE a ha hve]
        apply (ae_dirac_iff ((measurableSet_actualLowerGoodPair Γ U).preimage
          (measurable_const.prodMk measurable_id))).mpr
        exact hagood v hv
      · rw [show κ v = Γ.σ v from patchStrategy_off Γ E hE a ha hve]
        apply (actualGoodLowerValues_iff Γ U v).mp
        by_contra hn
        exact hve ⟨hv, hn⟩
    filter_upwards [hpure] with a' hg
    refine ⟨hg.1, hg.2.1, ?_⟩
    intro i a''
    simpa only [withStrategy_payoff Γ κ hκ] using hg.2.2 i a''

end FCAppendix.Affine.Uniform07Finishing
