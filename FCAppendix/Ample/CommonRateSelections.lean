import FCAppendix.Ample.CommonRateAnalytic
import FCAppendix.Ample.SlackParticipation

noncomputable section
namespace FCAppendix.Ample
open Finset Filter Topology Set Real
open scoped BigOperators

theorem commonRate_eventually_finset {α β : Type*} (l : Filter α)
    (s : Finset β) (P : α → β → Prop)
    (h : ∀ j ∈ s, ∀ᶠ t in l, P t j) : ∀ᶠ t in l, ∀ j ∈ s, P t j := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact Filter.Eventually.of_forall (by simp)
  | @insert j s _hjs ih =>
    intro h
    have hj := h j (mem_insert_self _ _)
    have hs := ih (fun k hk => h k (mem_insert_of_mem hk))
    filter_upwards [hj, hs] with t ht hts k hk
    rcases mem_insert.mp hk with rfl | hk
    · exact ht
    · exact hts k hk

theorem commonRate_coordinate_lower {n : ℕ} {lam : ℕ → ℕ → ℝ} {pi : ℕ → ℝ}
    (hconv : ∀ j ∈ Finset.Icc 1 n, Tendsto (fun t => lam t j) atTop (𝓝 (pi j)))
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ t in atTop, ∀ j ∈ Finset.Icc 1 n, pi j - d < lam t j := by
  apply commonRate_eventually_finset atTop (Finset.Icc 1 n)
  intro j hj
  exact (hconv j hj).eventually_const_lt (by linarith)

theorem commonRate_domination_width {n : ℕ} {pi : ℕ → ℝ} {h a : ℝ}
    (hh : 0 < h) (ha : a < 1) :
    ∃ d > 0, d < h ∧ ∀ j ∈ Finset.Icc 1 n, 0 < pi j → 2*d < (1-a)*pi j := by
  classical
  let s := (Finset.Icc 1 n).filter (fun j => 0 < pi j)
  obtain ⟨d, hd, hds⟩ := commonRate_common_positive s
    (fun j => (1-a)*pi j/2) (by
      intro j hj
      exact half_pos (mul_pos (sub_pos.mpr ha) (mem_filter.mp hj).2))
  refine ⟨min d (h/2), lt_min hd (half_pos hh), ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (half_lt_self hh)
  · intro j hj hp
    have ht := hds j (mem_filter.mpr ⟨hj, hp⟩)
    have hm := min_le_left d (h/2)
    linarith

end FCAppendix.Ample

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Topology Set Real
open Ample
open scoped BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem commonRate_primitive_row (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hu : UsersOptimal Γ)
    (hact : NonpositiveAbstention Γ) (hz : RejectsZeroBids Γ) :
    (∀ j, 1 ≤ j → visibleClassMass Γ 0 j = actualRouteMass Γ j) ∧
    actualRouteMass Γ 0 = 1-Γ.F.real (Ioi Γ.g) ∧
    positiveRouteMass Γ (fun _ => True) = Γ.F.real (Ioi Γ.g) := by
  refine ⟨?_, ?_, ppi_positiveParticipation_eq Γ hm hn hc hA hatom hj hu hact hz⟩
  · intro j hpos
    rw [← positiveRouteMass_class_eq Γ hpos]
    exact ppi_positiveRouteMass_eq_raw Γ hm hn hc hA hatom hj hu hact hz
      (fun k => k=j) (by intro k hk; omega)
  · have he : {x : ℝ × JointAction n | x.2.routeCount=0} =ᵐ[Γ.F ⊗ₘ Γ.σ]
        {x | Γ.g < x.1}ᶜ := by
      filter_upwards [ppi_ae_positive_draw_iff Γ hm hn hc hA hatom hj hu hact hz,
        hact] with x hx hxa
      apply propext
      change (x.2.routeCount=0) ↔ ¬ Γ.g < x.1
      constructor
      · intro hk hv
        have hr := (hx.mpr hv).2
        omega
      · intro hv
        exact hxa (le_of_not_gt hv)
    have hmeas : MeasurableSet {x : ℝ × JointAction n | Γ.g < x.1} :=
      measurableSet_lt measurable_const measurable_fst
    calc
      actualRouteMass Γ 0 = (Γ.F ⊗ₘ Γ.σ).real {x | Γ.g < x.1}ᶜ := measureReal_congr he
      _ = (Γ.F ⊗ₘ Γ.σ).real univ - (Γ.F ⊗ₘ Γ.σ).real {x | Γ.g < x.1} :=
        measureReal_compl hmeas
      _ = 1 - Γ.F.real (Ioi Γ.g) := by
        rw [probReal_univ]
        congr 1
        exact joint_value_probability Γ (Ioi Γ.g) measurableSet_Ioi

theorem commonRate_bottom_domination (Γ : FiniteGame m n c Seed)
    {pi : ℕ → ℝ} {h a d b : ℝ} (hpi : ValidLaw n pi)
    (hmass : ∑ j ∈ Finset.Icc 1 n, pi j = h)
    (ha1 : a ≤ 1)
    (hwidth : ∀ j ∈ Finset.Icc 1 n, 0 < pi j → 2*d < (1-a)*pi j)
    (htotal : positiveRouteMass Γ (fun _ => True) = h)
    (hclose : ∀ j ∈ Finset.Icc 1 n, pi j-d < visibleClassMass Γ 0 j)
    (hb : 0 ≤ b) (hbottom : h-d ≤ positiveRouteTail Γ (fun _ => True) b) :
    ∀ T : Finset (Fin n),
      a*contactWeight n pi T ≤ contactWeight n (visibleClassMass Γ b) T := by
  classical
  have hlamb := visibleClassMass_valid Γ b
  have hcoord (j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
      a*pi j ≤ visibleClassMass Γ b j := by
    have hp := hpi.nonneg j hj
    by_cases hp0 : pi j=0
    · simpa only [hp0, mul_zero] using hlamb.nonneg j hj
    · have hpp : 0 < pi j := lt_of_le_of_ne hp (Ne.symm hp0)
      have hr := removedClass_le_removedAll Γ (fun k => k=j) b hb
      rw [positiveRouteMass_class_eq Γ (Finset.mem_Icc.mp hj).1,
        positiveRouteTail_class_eq Γ b hb (Finset.mem_Icc.mp hj).1, htotal] at hr
      have he := hclose j hj
      have hw := hwidth j hj hpp
      nlinarith
  have hsum : (∑ j ∈ Finset.Icc 1 n, visibleClassMass Γ b j) ≤ h := by
    have hr := positiveRouteTail_le_mass Γ (fun _ => True) b
    have htail : (∑ j ∈ Finset.Icc 1 n, visibleClassMass Γ b j) =
        positiveRouteTail Γ (fun _ => True) b := by
      rw [← visibleLaw_prob_positiveClass Γ b hb]
      change (∑ j ∈ Finset.Icc 1 n, classMass (visibleLaw Γ b) j) =
        (visibleLaw Γ b).prob (fun T => 0<T.card ∧ True)
      rw [sum_classMass]
      simp only [FiniteLaw.prob_eq_expect]
      apply FiniteLaw.expect_congr
      intro T
      simp only [Finset.card_pos, and_true, Finset.nonempty_iff_ne_empty]
    rw [htail]
    exact hr.trans_eq htotal
  intro T
  by_cases hT : T=∅
  · subst T
    simp only [contactWeight_empty]
    have hh : h ≤ 1 := hmass ▸ hpi.total_le
    have he := mul_le_mul_of_nonneg_right ha1 (sub_nonneg.mpr hh)
    rw [one_mul] at he
    rw [hmass]
    linarith
  · rw [contactWeight_of_ne pi hT, contactWeight_of_ne (visibleClassMass Γ b) hT,
      ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hcoord T.card (card_mem_Icc_of_ne hT))
      (Nat.cast_nonneg _)

theorem commonRate_select_nonbroadcast (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hact : NonpositiveAbstention Γ) (i : Fin m)
    {h d e H : ℝ} (hd : 0 < d) (hdh : d<h) (he : 0<e)
    (htotal : positiveRouteMass Γ (fun _ => True)=h)
    (htight : Γ.F.real {v | Γ.g<v ∧ v-Γ.g ∉ Icc e H}<d/4)
    (hsmall : actualRouteMass Γ n<d/4) :
    ∃ w a, 0<w ∧ w ∈ Icc e H ∧ (problem Γ i).BestResponse (w+Γ.g) a ∧
      0<a.bid ∧ 0<a.routeCount ∧ a.routeCount<n ∧
      h-d ≤ positiveRouteTail Γ (fun _ => True) a.bid := by
  let A : Set (ℝ × JointAction n) := {x | Γ.g<x.1 ∧ x.1-Γ.g ∉ Icc e H}
  let Bad : Set (ℝ × JointAction n) := A ∪ {x | x.2.routeCount=n}
  have hA : (Γ.F ⊗ₘ Γ.σ).real A<d/4 := by
    change (Γ.F ⊗ₘ Γ.σ).real {x | x.1 ∈ {v | Γ.g<v ∧ v-Γ.g ∉ Icc e H}} < _
    have hm : MeasurableSet {v : ℝ | Γ.g < v ∧ v - Γ.g ∉ Icc e H} :=
      (measurableSet_lt measurable_const measurable_id).inter
        (((measurable_id.sub_const Γ.g) measurableSet_Icc).compl)
    rw [joint_value_probability Γ _ hm]
    exact htight
  have hBad : (Γ.F ⊗ₘ Γ.σ).real Bad < (h-d/2)-(h-d) := by
    have hu' := measureReal_union_le (μ := Γ.F ⊗ₘ Γ.σ) A {x | x.2.routeCount=n}
    change (Γ.F ⊗ₘ Γ.σ).real (A ∪ {x | x.2.routeCount=n}) < _
    dsimp [actualRouteMass] at hsmall
    linarith
  obtain ⟨x, hbr, hb, hk, _, hl, _, hx, hB⟩ := exists_supported_route_band
    Γ hatom hu hact i (fun _ => True) (by linarith : 0<h-d)
    (by linarith : h-d<h-d/2) (by rw [htotal]; linarith) Bad hBad (by
      intro x hv hnot
      by_contra hx
      exact hnot (Or.inl ⟨hv,hx⟩))
  have hkn : x.2.routeCount ≠ n := fun hkn => hB (Or.inr hkn)
  have hwl : 0 < x.1-Γ.g := he.trans_le hx.1
  refine ⟨x.1-Γ.g,x.2,hwl,hx,?_,hb,hk,?_,hl⟩
  · simpa only [sub_add_cancel] using hbr
  · have hle := x.2.routeCount_le
    omega

theorem commonRate_bottom_deficit_lower
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ)
    (hF : ∀ t, (Γ t).F=F) (hg : ∀ t, (Γ t).g=g)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A=Schedule.ppi n) (hf : ∀ t, FreeDuplicateBase (Γ t))
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hj : ∀ t j, ProposerRationalAtFeasibleLists (Γ t) j)
    (hu : ∀ t, UsersOptimal (Γ t)) (hact : ∀ t, NonpositiveAbstention (Γ t))
    {pi : ℕ → ℝ} (hpi : ValidLaw n pi) (hh : 0<F.real (Ioi g))
    (hmass : ∑ j ∈ Finset.Icc 1 n, pi j=F.real (Ioi g))
    (htotal : ∀ᶠ t in atTop, positiveRouteMass (Γ t) (fun _ => True)=F.real (Ioi g))
    (hconv : ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun t => visibleClassMass (Γ t) 0 j) atTop (𝓝 (pi j)))
    {J : ℝ}
    (hrate : HasPopulationRate M (fun t => congestProb n (M t-1) (C t) n pi) J)
    {z : ℝ} (hz : 0<z) :
    ∀ eps>0, ∀ᶠ t in atTop,
      exp (-(M t : ℝ)*(J+eps)) ≤ actualDeficit (Γ t) z := by
  intro eps heps
  let a := exp (-eps/4)
  have ha : 0<a := exp_pos _
  have ha1 : a<1 := exp_lt_one_iff.mpr (by linarith)
  have hloga : log a = -eps/4 := log_exp _
  obtain ⟨d, hd, hdh, hwidth⟩ := commonRate_domination_width (pi := pi) hh ha1
  obtain ⟨e,H,he,heH,htight⟩ := exists_compact_positive_band F g
    (show 0<d/4 by linarith)
  let K : ℝ := min 1 (z/H)*e
  have hH : 0<H := he.trans heH
  have hK : 0<K := mul_pos (lt_min zero_lt_one (div_pos hz hH)) he
  have hr := (hrate.rival_pow_mul hM ha).const_mul hM hK
  have hsmall : J-log a<J+eps := by rw [hloga]; linarith
  have hlower := hr.eventually_lower_exp hM hsmall
  have hclose := commonRate_coordinate_lower hconv hd
  filter_upwards [htotal,hclose,hlower,hrate.1,hM.eventually_gt_atTop 0]
    with t htot hcl hlow hp hm
  obtain ⟨w,act,hw,hbr,hb,_,_,hbottom,_⟩ := select_supported_route_band
    (Γ t) (hatom t) (hu t) (hact t) ⟨0,hm⟩ (fun _ => True)
    (by linarith : 0<F.real (Ioi g)-d)
    (by linarith : F.real (Ioi g)-d<F.real (Ioi g)-d/2)
    (by rw [htot]; linarith) (by
      rw [hF t,hg t]
      exact htight.trans (by linarith))
  have hw0 : 0<w := he.trans_le hw.1
  have hdom := commonRate_bottom_domination (Γ t) hpi hmass ha1.le
    hwidth htot hcl hb.le hbottom
  have hfinite := commonRate_congest_domination (N := M t-1) (c := C t)
    (k := n) hpi ha.le hdom
  have hmon := commonRate_congest_antitone (N := M t-1) (c := C t)
    (visibleClassMass_valid (Γ t) act.bid) act.routeCount_le
  have hfail : a^(M t-1)*congestProb n (M t-1) (C t) n pi ≤
      actualFailure (Γ t) act := by
    rw [actualFailure_eq_congestProb (Γ t) hm (hA t) (hatom t) (hj t) act hb]
    exact hfinite.trans hmon
  have hpay : 0≤act.bid*actualMeanLoad (Γ t) act := by
    apply mul_nonneg act.bid_nonneg
    simpa only [actualMeanLoad,dif_pos hm] using ((problem (Γ t) ⟨0,hm⟩).outcome act).load_nonneg
  have hfW := actualDeficit_eq_loss (Γ t) hm (hA t) (hf t) w act hbr
  have hbase : e*(a^(M t-1)*congestProb n (M t-1) (C t) n pi) ≤
      actualDeficit (Γ t) w := by
    have hq : 0≤a^(M t-1)*congestProb n (M t-1) (C t) n pi :=
      mul_nonneg (pow_nonneg ha.le _) hp.le
    have h1 := mul_le_mul_of_nonneg_left hfail hw0.le
    have h2 := mul_le_mul_of_nonneg_right hw.1 hq
    linarith
  have hcmp := (actualDeficit_ratio_bounds (Γ t) hm z w hz hw0).1
  have hzw : z/H≤z/w := div_le_div_of_nonneg_left hz.le hw0 hw.2
  have hmin : min 1 (z/H)≤ min 1 (z/w) := min_le_min_left 1 hzw
  have hfnonneg : 0≤actualDeficit (Γ t) w := by
    simpa only [actualDeficit,dif_pos hm] using deficit_nonneg (problem (Γ t) ⟨0,hm⟩) w hw0.le
  have h1 := mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ min 1 (z/H) from le_min zero_le_one (div_nonneg hz.le hH.le))
  have h2 := mul_le_mul_of_nonneg_right hmin hfnonneg
  have hresult : K*(a^(M t-1)*congestProb n (M t-1) (C t) n pi) ≤
      actualDeficit (Γ t) z := by
    dsimp [K]
    nlinarith
  exact hlow.trans hresult

end FCAppendix.Bayes
