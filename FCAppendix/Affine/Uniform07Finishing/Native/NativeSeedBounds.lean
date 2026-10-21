import FCAppendix.Affine.Uniform07Finishing.Native.NativeSeedLaw
import FCAppendix.Affine.Uniform07Finishing.Native.LowerVersion
import FCAppendix.Finite.NoOverbid

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine
open StrictNative

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actual_bid_lt_value_of_payoff_pos (Γ : FiniteGame m 2 c Seed)
    (hg : Γ.g = 0) (i : Fin m) (v : ℝ) (a : JointAction 2)
    (hpos : 0 < (problem Γ i).payoff v a) : a.bid < v := by
  have hpay := actualBidPayment_ge_bid_success Γ i a
  have hsuccess := ((problem Γ i).outcome a).success_nonneg
  rw [actual_zero_base_payoff Γ hg i v a] at hpos
  by_contra hnot
  have hbv : v ≤ a.bid := le_of_not_gt hnot
  have hh := mul_le_mul_of_nonneg_right hbv hsuccess
  linarith

theorem actual_best_bid_lt_value_of_positive_deviation
    (Γ : FiniteGame m 2 c Seed) (hg : Γ.g = 0)
    (i : Fin m) (v : ℝ) (a : JointAction 2)
    (hbest : (problem Γ i).BestResponse v a)
    (hpos : ∃ a' : JointAction 2, 0 < (problem Γ i).payoff v a') :
    a.bid < v := by
  obtain ⟨a', ha'⟩ := hpos
  exact actual_bid_lt_value_of_payoff_pos Γ hg i v a (ha'.trans_le (hbest a'))

theorem actual_seed_mass_lower_of_bid_le_value (Γ : FiniteGame m 2 c Seed)
    (hF : Γ.F = Uniform07.uniformLaw)
    (hbv : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ x.1)
    {zs : ℝ} (_hz0 : 0 ≤ zs) (hz1 : zs ≤ 1) :
    ENNReal.ofReal zs ≤ userLaw Γ (sourceSeedCategory zs) := by
  have hu : ∀ᵐ u ∂userLaw Γ, u.1.2.bid ≤ u.1.1 :=
    (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw 2)).quasiMeasurePreserving.ae hbv
  have hinc : ∀ᵐ u ∂userLaw Γ,
      u ∈ (fun u : UserDraw 2 => u.1.1) ⁻¹' Icc (0 : ℝ) zs →
      u ∈ sourceSeedCategory zs := by
    filter_upwards [hu] with u hu
    exact fun hv => hu.trans hv.2
  have hmass := measure_mono_ae hinc
  change userLaw Γ ((Prod.fst ∘ Prod.fst) ⁻¹' Icc (0:ℝ) zs) ≤
    userLaw Γ (sourceSeedCategory zs) at hmass
  rw [← Measure.map_apply (measurable_fst.comp measurable_fst) measurableSet_Icc] at hmass
  have hmap : (userLaw Γ).map (Prod.fst ∘ Prod.fst) = Γ.F := userLaw_value_map Γ
  rw [hmap, hF] at hmass
  change ENNReal.ofReal zs ≤ _
  simpa only [Uniform07.uniformLaw, Measure.restrict_apply measurableSet_Icc,
    inter_eq_left.mpr (show Icc (0 : ℝ) zs ⊆ Icc (0 : ℝ) 1 from
      fun _ hx => ⟨hx.1, hx.2.trans hz1⟩), Real.volume_Icc, sub_zero] using hmass

def nativeNoSeed (zs : ℝ) {N : ℕ} (d : Fin N → UserDraw 2) : Prop :=
  ∀ k : Fin N, zs < (d k).1.2.bid

theorem measurableSet_nativeNoSeed (zs : ℝ) (N : ℕ) :
    MeasurableSet {d : Fin N → UserDraw 2 | nativeNoSeed zs d} := by
  have he : {d : Fin N → UserDraw 2 | nativeNoSeed zs d} =
      univ.pi (fun _ : Fin N => (sourceSeedCategory zs)ᶜ) := by
    ext d
    simp only [nativeNoSeed, mem_setOf_eq, mem_univ_pi, mem_compl_iff,
      sourceSeedCategory, not_le]
  rw [he]
  exact MeasurableSet.univ_pi (fun _ => (measurableSet_sourceSeedCategory zs).compl)

theorem native_no_seed_mass (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ]
    (zs : ℝ) (N : ℕ) :
    (Measure.pi (fun _ : Fin N => μ)) {d | nativeNoSeed zs d} =
      (μ (sourceSeedCategory zs)ᶜ)^N := by
  have he : {d : Fin N → UserDraw 2 | nativeNoSeed zs d} =
      univ.pi (fun _ : Fin N => (sourceSeedCategory zs)ᶜ) := by
    ext d
    simp only [nativeNoSeed, mem_setOf_eq, mem_univ_pi, mem_compl_iff,
      sourceSeedCategory, not_le]
  rw [he, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem native_no_seed_real (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ]
    (zs : ℝ) (N : ℕ) :
    (Measure.pi (fun _ : Fin N => μ)).real {d | nativeNoSeed zs d} =
      (1-μ.real (sourceSeedCategory zs))^N := by
  rw [Measure.real, native_no_seed_mass, ENNReal.toReal_pow]
  congr 1
  exact probReal_compl_eq_one_sub (measurableSet_sourceSeedCategory zs)

theorem native_no_seed_real_le_exp (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ]
    (zs s : ℝ) (hseed : s ≤ μ.real (sourceSeedCategory zs)) (N : ℕ) :
    (Measure.pi (fun _ : Fin N => μ)).real {d | nativeNoSeed zs d} ≤
      Real.exp (-(N : ℝ)*s) := by
  rw [native_no_seed_real]
  have hq : μ.real (sourceSeedCategory zs) ≤ 1 := measureReal_le_one
  have hbase : 1-μ.real (sourceSeedCategory zs) ≤ Real.exp (-s) := by
    linarith [Real.add_one_le_exp (-s)]
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr hq) hbase N
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

theorem native_fixed_no_seed_real_le_exp
    (μ : Measure (UserDraw 2)) [IsProbabilityMeasure μ]
    (zs p : ℝ) (hseed : p ≤ μ.real (sourceSeedCategory zs))
    (s N : ℕ) (fixed : Fin s → UserDraw 2) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {d | (∀ k : Fin s, zs < (fixed k).1.2.bid) ∧ nativeNoSeed zs d} ≤
      Real.exp (-(N : ℝ)*p) := by
  exact (measureReal_mono (fun _ hx => hx.2)).trans
    (native_no_seed_real_le_exp μ zs p hseed N)

theorem native_no_seed_background_real (Γ : FiniteGame m 2 c Seed) (zs : ℝ) :
    (backgroundLaw Γ).real {x | nativeNoSeed zs x.1} =
      (1-(userLaw Γ).real (sourceSeedCategory zs))^m := by
  have he : {x : Background m 2 Seed | nativeNoSeed zs x.1} =
      {d : UserProfile m 2 | nativeNoSeed zs d} ×ˢ univ := by ext x; simp
  rw [he, Measure.real, backgroundLaw, Measure.prod_prod, measure_univ, mul_one]
  exact native_no_seed_real (userLaw Γ) zs m

theorem seedOnList_none_iff {N : ℕ} (μ : Measure ℝ) (L : LocalList N) :
    Hybrid.seedOnList μ L = none ↔ ∀ k : Fin N, L k = none := by
  constructor
  · intro h
    have hmin : Hybrid.localMinimum L = none := by
      cases he : Hybrid.localMinimum L with
      | none => rfl
      | some b =>
          rw [Hybrid.seedOnList, he, Option.map_some] at h
          exact (Option.some_ne_none _ h).elim
    intro k
    exact (Hybrid.scanMinimum_none (List.finRange N) L).mp hmin k (by simp)
  · intro hall
    have hmin : Hybrid.localMinimum L = none :=
      (Hybrid.scanMinimum_none (List.finRange N) L).mpr (fun k _ => hall k)
    rw [Hybrid.seedOnList, hmin]
    rfl

theorem actual_observed_seed_none_imp {N : ℕ} {zs U R : ℝ}
    (hzU : zs ≤ U) (hzR : zs < R) (μ : Measure ℝ)
    (d : UserProfile N 2)
    (hshape : ∀ k,
      ((d k).1.2.bid ≤ U ∧ (d k).1.2.routeCount = 2) ∨
      (U < (d k).1.2.bid ∧ (d k).1.2.routeCount = 1))
    (j : Fin 2)
    (hnone : Weighted.sourceSeed μ zs
      (StrictNative.observedContext R j (observe (drawsRealization d) j)) = none) :
    nativeNoSeed zs d := by
  rw [sourceSeed_observed hzR] at hnone
  change Hybrid.seedOnList μ (TaggedLocal.lowList zs U (observe (drawsRealization d) j)) = none at hnone
  have hlow := TaggedLocal.lowList_observe (fun k => sourceDrawTag zs U (d k))
    (drawsRealization d) hzU (sourceDrawTag_boxes zs U d)
    (sourceDrawTag_routes hzU d hshape) j
  have hempty := (seedOnList_none_iff μ _).mp hnone
  intro k
  by_contra hn
  have hb : (d k).1.2.bid ≤ zs := le_of_not_gt hn
  have hk : sourceDrawTag zs U (d k) = 0 := by simp only [sourceDrawTag, if_pos hb]
  have hh := hempty k
  rw [hlow] at hh
  dsimp only at hh
  rw [if_pos hk] at hh
  exact Option.some_ne_none _ hh

section Source
variable [Nonempty (Fin m)]
  (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
  {R Λ : ℝ} (hR : 0 < R) (hRt : R < Uniform07.cutoff row) (hΛ : 0 < Λ)
  (PL : ProbabilityMeasure (ℝ × JointAction 2))
  (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
    (sourceLowerValueLaw row : Measure ℝ))
  (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
    x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
  (hLbidValue : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ x.1)
  (α : ClassifiedContext m → unitInterval) (hα : Measurable α)

include hm hR hRt hLvalue hLroute hLbidValue in
theorem sourceNativeGame_bid_le_value :
    let Γ := sourceNativeGame row hc R Λ hΛ PL α hα
    ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ x.1 := by
  dsimp only
  rw [sourceNativeGame_joint_law row hm hc hR hRt hΛ PL hLvalue hLroute α hα,
    sourcePopulation_literal, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure hLbidValue _
  · apply Measure.ae_smul_measure
    filter_upwards [(source_upper_joint_properties row m hm hc hR hRt).2.1] with x hx
    exact hx.2.2.2.1

include hm hR hRt hLvalue hLroute hLbidValue in
theorem sourceNativeGame_seed_mass_lower :
    ENNReal.ofReal (Uniform07.cutoff row/2) ≤
      userLaw (sourceNativeGame row hc R Λ hΛ PL α hα)
        (sourceSeedCategory (Uniform07.cutoff row/2)) := by
  apply actual_seed_mass_lower_of_bid_le_value _ rfl
    (sourceNativeGame_bid_le_value row hm hc hR hRt hΛ PL hLvalue hLroute hLbidValue α hα)
  · exact div_nonneg (Uniform07.cutoff_pos row).le (by norm_num)
  · linarith [Uniform07.cutoff_lt_one row]

include hm hR hRt hLvalue hLroute hLbidValue in
theorem sourceNativeGame_seed_real_lower :
    Uniform07.cutoff row/2 ≤
      (userLaw (sourceNativeGame row hc R Λ hΛ PL α hα)).real
        (sourceSeedCategory (Uniform07.cutoff row/2)) := by
  have hh := ENNReal.toReal_mono (measure_ne_top _ _)
    (sourceNativeGame_seed_mass_lower row hm hc hR hRt hΛ PL hLvalue hLroute hLbidValue α hα)
  rw [ENNReal.toReal_ofReal (show 0 ≤ Uniform07.cutoff row/2 from
    (half_pos (Uniform07.cutoff_pos row)).le)] at hh
  exact hh

include hm hR hRt hLvalue hLroute hLbidValue in
theorem sourceNativeGame_seed_mass_pos :
    0 < userLaw (sourceNativeGame row hc R Λ hΛ PL α hα)
      (sourceSeedCategory (Uniform07.cutoff row/2)) := by
  exact (ENNReal.ofReal_pos.mpr (half_pos (Uniform07.cutoff_pos row))).trans_le
    (sourceNativeGame_seed_mass_lower row hm hc hR hRt hΛ PL hLvalue hLroute hLbidValue α hα)

include hm hR hRt hLvalue hLroute hLbidValue in
theorem sourceNativeGame_no_seed_bound (N : ℕ) :
    (Measure.pi (fun _ : Fin N => userLaw (sourceNativeGame row hc R Λ hΛ PL α hα))).real
      {d | nativeNoSeed (Uniform07.cutoff row/2) d} ≤
      Real.exp (-(N : ℝ)*(Uniform07.cutoff row/2)) :=
  native_no_seed_real_le_exp _ _ _
    (sourceNativeGame_seed_real_lower row hm hc hR hRt hΛ PL hLvalue hLroute hLbidValue α hα) N

include hm hR hRt hLvalue hLroute hLbidValue in

theorem sourceNativeGame_fixed_no_seed_bound (s N : ℕ) (fixed : Fin s → UserDraw 2) :
    (Measure.pi (fun _ : Fin N => userLaw (sourceNativeGame row hc R Λ hΛ PL α hα))).real
      {d | (∀ k : Fin s, Uniform07.cutoff row/2 < (fixed k).1.2.bid) ∧
        nativeNoSeed (Uniform07.cutoff row/2) d} ≤
      Real.exp (-(N : ℝ)*(Uniform07.cutoff row/2)) :=
  native_fixed_no_seed_real_le_exp _ _ _
    (sourceNativeGame_seed_real_lower row hm hc hR hRt hΛ PL hLvalue hLroute hLbidValue α hα)
    s N fixed

include hm hR hRt hLvalue hLroute hLbidValue in
theorem sourceNativeGame_observed_no_seed_bound
    (hUR : Early.bidCap row < R) (j : Fin 2) :
    let Γ := sourceNativeGame row hc R Λ hΛ PL α hα
    (userProfileLaw Γ).real {d | Weighted.sourceSeed (sourceSeedMeasure row m hc R PL)
      (Uniform07.cutoff row/2)
      (StrictNative.observedContext R j (observe (drawsRealization d) j)) = none} ≤
      Real.exp (-(m : ℝ)*(Uniform07.cutoff row/2)) := by
  let Γ := sourceNativeGame row hc R Λ hΛ PL α hα
  let E : Set (UserProfile m 2) := {d | Weighted.sourceSeed (sourceSeedMeasure row m hc R PL)
    (Uniform07.cutoff row/2)
    (StrictNative.observedContext R j (observe (drawsRealization d) j)) = none}
  have hinc : ∀ᵐ d ∂userProfileLaw Γ, d ∈ E → nativeNoSeed (Uniform07.cutoff row/2) d := by
    filter_upwards [sourceNativeGame_cap_profile row hm hc hR hUR hRt hΛ PL hLvalue hLroute α hα]
      with d hd
    exact actual_observed_seed_none_imp (source_seed_cutoff_lt_bidCap row).le
      ((source_seed_cutoff_lt_bidCap row).trans hUR) _ d hd j
  have hmono := ENNReal.toReal_mono (measure_ne_top (userProfileLaw Γ) _)
    (measure_mono_ae hinc)
  exact hmono.trans
    (sourceNativeGame_no_seed_bound row hm hc hR hRt hΛ PL hLvalue hLroute hLbidValue α hα m)

end Source
end FCAppendix.Affine.Uniform07Finishing
