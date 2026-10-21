import FCAppendix.Affine.Uniform07Finishing.Native.NativeSeedLaw
import FCAppendix.Affine.Uniform07Finishing.Native.CompleteSourceGame
import FCAppendix.Affine.Uniform07Finishing.Native.LiteralSourceGame
import FCAppendix.Affine.Hybrid.NativeRealizedContext
import FCAppendix.Finite.IdentitySymmetry

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open StrictNative

variable {m : ℕ} [Nonempty (Fin m)]

omit [Nonempty (Fin m)] in
theorem raw_payoff_congr_of_outcome_tariffs {n c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G H : FiniteGame m n c Seed) (i : Fin m)
    (v : ℝ) (a : JointAction n) (hA : G.A=H.A) (hG : G.G=H.G) (hg : G.g=H.g)
    (hout : (problem G i).outcome a=(problem H i).outcome a) :
    (problem G i).payoff v a=(problem H i).payoff v a := by
  change ((problem G i).outcome a).utility v a.bid G.g G.A G.G =
    ((problem H i).outcome a).utility v a.bid H.g H.A H.G
  rw [hout,hA,hG,hg]

def replaceSourceUpperPair (row : Uniform07.Row) (m : ℕ)
    (_hc : 1 ≤ Uniform07.capacity m) (R' : ℝ) (x : ℝ × JointAction 2) :
    ℝ × JointAction 2 :=
  if Early.bidCap row < x.2.bid then
    (x.1, Hybrid.upperAction (sourceUpperBid row m R') x.1) else x

theorem measurable_replaceSourceUpperPair (row : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R' : ℝ) :
    Measurable (replaceSourceUpperPair row m hc R') :=
  Measurable.ite
    (measurableSet_lt measurable_const ((measurable_bid 2).comp measurable_snd))
    (measurable_fst.prodMk ((Hybrid.measurable_upperAction _
      (sourceUpperBid_measurable row m hc R')).comp measurable_fst)) measurable_id

omit [Nonempty (Fin m)] in
theorem sourceUpperJoint_map_replace (row : Uniform07.Row) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {R R' : ℝ}
    (hR : 0 < R) (hUR : Early.bidCap row < R) (hRt : R < Uniform07.cutoff row) :
    (sourceUpperJoint row m hc R : Measure (ℝ × JointAction 2)).map
      (replaceSourceUpperPair row m hc R') =
        (sourceUpperJoint row m hc R' : Measure (ℝ × JointAction 2)) := by
  change ((sourceUpperValueLaw row : Measure ℝ).map
    (fun v => (v, Hybrid.upperAction (sourceUpperBid row m R) v))).map _ =
      (sourceUpperValueLaw row : Measure ℝ).map
        (fun v => (v, Hybrid.upperAction (sourceUpperBid row m R') v))
  rw [Measure.map_map (f:=fun v : ℝ => (v, Hybrid.upperAction (sourceUpperBid row m R) v))
    (measurable_replaceSourceUpperPair row m hc R')
    (show Measurable (fun v : ℝ => (v, Hybrid.upperAction (sourceUpperBid row m R) v)) from
      measurable_id.prodMk (Hybrid.measurable_upperAction _ (sourceUpperBid_measurable row m hc R)))]
  apply Measure.map_congr
  filter_upwards [sourceUpperValueLaw_support row] with v hv
  have hb := ((source_upper_envelope row m hm hc hR hRt).bid_bounds v hv.1).1
  have hb0 : 0 ≤ sourceUpperBid row m R v := hR.le.trans hb
  simp only [Function.comp_apply, replaceSourceUpperPair, Hybrid.upperAction,
    max_eq_left hb0, if_pos (hUR.trans_le hb)]

omit [Nonempty (Fin m)] in
theorem sourcePopulation_map_replace (row : Uniform07.Row) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {R R' : ℝ}
    (hR : 0 < R) (hUR : Early.bidCap row < R) (hRt : R < Uniform07.cutoff row)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2) :
    (sourcePopulation row m hc R PL : Measure (ℝ × JointAction 2)).map
      (replaceSourceUpperPair row m hc R') =
        (sourcePopulation row m hc R' PL : Measure (ℝ × JointAction 2)) := by
  have hlow : (PL : Measure (ℝ × JointAction 2)).map
      (replaceSourceUpperPair row m hc R') = (PL : Measure (ℝ × JointAction 2)) := by
    calc
      _ = (PL : Measure (ℝ × JointAction 2)).map id := by
        apply Measure.map_congr
        filter_upwards [hLroute] with x hx
        simp only [replaceSourceUpperPair, not_lt.mpr hx.1, if_false, id_eq]
      _ = _ := Measure.map_id
  rw [sourcePopulation_literal, sourcePopulation_literal,
    Measure.map_add _ _ (measurable_replaceSourceUpperPair row m hc R'),
    Measure.map_smul, Measure.map_smul, hlow,
    sourceUpperJoint_map_replace row hm hc hR hUR hRt]

def replaceSourceUpperDraw (row : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R' : ℝ) : UserDraw 2 → UserDraw 2 :=
  Prod.map (replaceSourceUpperPair row m hc R') id

theorem measurable_replaceSourceUpperDraw (row : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R' : ℝ) :
    Measurable (replaceSourceUpperDraw row m hc R') :=
  (measurable_replaceSourceUpperPair row m hc R').prodMap measurable_id

omit [Nonempty (Fin m)] in

theorem source_seed_restriction_literal (row : Uniform07.Row) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {R : ℝ}
    (hR : 0 < R) (hUR : Early.bidCap row < R) (hRt : R < Uniform07.cutoff row)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) :
    (((sourcePopulation row m hc R PL : Measure (ℝ × JointAction 2)).prod
      (permLaw 2)).restrict (sourceSeedCategory (Uniform07.cutoff row/2))) =
      ENNReal.ofReal (Uniform07.cutoff row) •
        (((PL : Measure (ℝ × JointAction 2)).prod (permLaw 2)).restrict
          (sourceSeedCategory (Uniform07.cutoff row/2))) := by
  have hzR : Uniform07.cutoff row/2 < R :=
    (source_seed_cutoff_lt_bidCap row).trans hUR
  have hu : (((sourceUpperJoint row m hc R : Measure (ℝ × JointAction 2)).prod
      (permLaw 2)).restrict (sourceSeedCategory (Uniform07.cutoff row/2))) = 0 := by
    apply Measure.restrict_eq_zero.mpr
    apply measure_eq_zero_iff_ae_notMem.mpr
    have hp := (measurePreserving_fst
      (μ := (sourceUpperJoint row m hc R : Measure (ℝ × JointAction 2)))
      (ν := permLaw 2)).quasiMeasurePreserving.ae
        (source_upper_joint_properties row m hm hc hR hRt).2.1
    filter_upwards [hp] with u hu
    exact not_le.mpr (hzR.trans_le hu.2.2.1)
  rw [sourcePopulation_literal, Measure.add_prod,
    Measure.prod_smul_left, Measure.prod_smul_left, Measure.restrict_add,
    Measure.restrict_smul, Measure.restrict_smul, hu, smul_zero, add_zero]

omit [Nonempty (Fin m)] in
theorem sourceSeedMeasure_floor_invariant (row : Uniform07.Row) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {R R' : ℝ}
    (hR : 0 < R) (hUR : Early.bidCap row < R) (hRt : R < Uniform07.cutoff row)
    (hR' : 0 < R') (hUR' : Early.bidCap row < R') (hR't : R' < Uniform07.cutoff row)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) :
    sourceSeedMeasure row m hc R PL = sourceSeedMeasure row m hc R' PL := by
  have hr : (((sourcePopulation row m hc R PL : Measure (ℝ × JointAction 2)).prod
      (permLaw 2)).restrict (sourceSeedCategory (Uniform07.cutoff row/2))) =
      (((sourcePopulation row m hc R' PL : Measure (ℝ × JointAction 2)).prod
        (permLaw 2)).restrict (sourceSeedCategory (Uniform07.cutoff row/2))) := by
    rw [source_seed_restriction_literal row hm hc hR hUR hRt PL,
      source_seed_restriction_literal row hm hc hR' hUR' hR't PL]
  have hmasses := congrArg (fun μ : Measure (UserDraw 2) => μ univ) hr
  simp only [Measure.restrict_apply_univ] at hmasses
  unfold sourceSeedMeasure ProbabilityTheory.cond
  rw [hr, hmasses]

def FloorAlignedDraw (R R' : ℝ) (x y : UserDraw 2) : Prop :=
  x.1.2.routeCount = y.1.2.routeCount ∧ x.2 = y.2 ∧
    ((x.1.2.bid = y.1.2.bid ∧ x.1.2.bid < R ∧ y.1.2.bid < R') ∨
      (R ≤ x.1.2.bid ∧ R' ≤ y.1.2.bid))

omit [Nonempty (Fin m)] in
theorem observedContext_floor_aligned {R R' : ℝ}
    (d d' : UserProfile m 2) (halign : ∀ k, FloorAlignedDraw R R' (d k) (d' k))
    (j : Fin 2) :
    observedContext R j (observe (drawsRealization d) j) =
      observedContext R' j (observe (drawsRealization d') j) := by
  let L := observe (drawsRealization d) j
  let L' := observe (drawsRealization d') j
  have hdata (k : Fin m) :
      StrictTags.tag R R (L k) = StrictTags.tag R' R' (L' k) ∧
      broadcastPart R L k = broadcastPart R' L' k := by
    have h := halign k
    have hrec : (drawsRealization d).recipients k = (drawsRealization d').recipients k := by
      change firstK (d k).2 (d k).1.2.routeCount = firstK (d' k).2 (d' k).1.2.routeCount
      rw [h.1, h.2.1]
    by_cases hj : j ∈ (drawsRealization d').recipients k
    · have hLk : L k = some (d k).1.2.bid := by
        change (if j ∈ (drawsRealization d).recipients k then some (d k).1.2.bid else none) = _
        rw [hrec, if_pos hj]
      have hLk' : L' k = some (d' k).1.2.bid := by
        change (if j ∈ (drawsRealization d').recipients k then some (d' k).1.2.bid else none) = _
        rw [if_pos hj]
      rcases h.2.2 with hl | hh
      · constructor
        · simp only [hLk,hLk',StrictTags.tag,if_pos hl.2.1,if_pos hl.2.2]
        · rw [broadcastPart_some L k hLk hl.2.1, broadcastPart_some L' k hLk' hl.2.2]
          exact congrArg some hl.1
      · constructor
        · simp only [hLk,hLk',StrictTags.tag,if_neg (not_lt.mpr hh.1),if_neg (not_lt.mpr hh.2)]
        · simp [broadcastPart,StrictTags.lowList,hLk,hLk',StrictTags.tag,
            not_lt.mpr hh.1,not_lt.mpr hh.2]
    · have hLk : L k = none := by
        change (if j ∈ (drawsRealization d).recipients k then some (d k).1.2.bid else none) = _
        rw [hrec,if_neg hj]
      have hLk' : L' k = none := by
        change (if j ∈ (drawsRealization d').recipients k then some (d' k).1.2.bid else none) = _
        rw [if_neg hj]
      constructor
      · simp only [hLk,hLk',StrictTags.tag]
      · simp [broadcastPart,StrictTags.lowList,hLk,hLk',StrictTags.tag]
  have htag (k : Fin m) := (hdata k).1
  have hlow : broadcastPart R L = broadcastPart R' L' := funext (fun k => (hdata k).2)
  have hcounts (q : Fin 4) : StrictTags.localCount R R L q = StrictTags.localCount R' R' L' q := by
    unfold StrictTags.localCount
    simp only [htag]
  change observedContext R j L = observedContext R' j L'
  unfold observedContext
  rw [hlow, hcounts 0, hcounts 2]

def replaceSourceUpperSample (row : Uniform07.Row)
    (hc : 1 ≤ Uniform07.capacity m) (R' : ℝ) :
    Sample m 2 unitInterval → Sample m 2 unitInterval :=
  fun x => ((replaceSourceUpperDraw row m hc R' ∘ x.1.1, x.1.2), x.2)

section Actual
variable (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
  {R R' Λ : ℝ}
  (hR : 0 < R) (hUR : Early.bidCap row < R) (hRt : R < Uniform07.cutoff row)
  (hR' : 0 < R') (hUR' : Early.bidCap row < R') (hR't : R' < Uniform07.cutoff row)
  (hΛ : 0 < Λ) (PL : ProbabilityMeasure (ℝ × JointAction 2))
  (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
    (sourceLowerValueLaw row : Measure ℝ))
  (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
    x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
  (α : ClassifiedContext m → unitInterval) (hα : Measurable α)

local notation "Γ" => sourceNativeGame row hc R Λ hΛ PL α hα
local notation "Γ'" => sourceNativeGame row hc R' Λ hΛ PL α hα
local notation "f" => replaceSourceUpperDraw row m hc R'

include hm hR hUR hRt hR' hR't hLvalue hLroute in
theorem sourceNativeGame_replace_user_measurePreserving :
    MeasurePreserving f (userLaw Γ) (userLaw Γ') := by
  refine ⟨measurable_replaceSourceUpperDraw row m hc R', ?_⟩
  rw [sourceNativeGame_user_law row hm hc hR hRt hΛ PL hLvalue hLroute α hα,
    sourceNativeGame_user_law row hm hc hR' hR't hΛ PL hLvalue hLroute α hα]
  change (((sourcePopulation row m hc R PL : Measure (ℝ × JointAction 2)).prod
    (permLaw 2)).map (Prod.map (replaceSourceUpperPair row m hc R') id)) = _
  rw [← Measure.map_prod_map _ _ (measurable_replaceSourceUpperPair row m hc R')
    measurable_id, Measure.map_id,
    sourcePopulation_map_replace row hm hc hR hUR hRt PL hLroute]

include hm hR hUR hRt hR' hR't hLvalue hLroute in
theorem sourceNativeGame_replace_profile_measurePreserving :
    MeasurePreserving (fun d : UserProfile m 2 => f ∘ d)
      (userProfileLaw Γ) (userProfileLaw Γ') := by
  exact measurePreserving_pi (fun _ : Fin m => userLaw Γ)
    (fun _ : Fin m => userLaw Γ')
    (fun _ => sourceNativeGame_replace_user_measurePreserving
      row hm hc hR hUR hRt hR' hR't hΛ PL hLvalue hLroute α hα)

include hm hR hUR hRt hR' hR't hLvalue hLroute in
theorem sourceNativeGame_replace_sample_measurePreserving :
    MeasurePreserving (replaceSourceUpperSample row hc R') (sampleLaw Γ) (sampleLaw Γ') :=
  ((sourceNativeGame_replace_profile_measurePreserving
    row hm hc hR hUR hRt hR' hR't hΛ PL hLvalue hLroute α hα).prod
      (MeasurePreserving.id (Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))))).prod
        (MeasurePreserving.id (permLaw 2))

include hm hR hUR hRt hR' hUR' hR't hLvalue hLroute in
theorem sourceNativeGame_replace_aligned :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ k, FloorAlignedDraw R R' (d k) (f (d k)) := by
  have hj : ∀ᵐ x ∂(Γ).F ⊗ₘ (Γ).σ,
      (x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2) ∨
      (x.1 ∈ Icc (Uniform07.cutoff row) 1 ∧ R ≤ x.2.bid ∧ x.2.routeCount = 1) := by
    rw [sourceNativeGame_joint_law row hm hc hR hRt hΛ PL hLvalue hLroute α hα]
    filter_upwards [source_population_support row m hm hc hR hRt PL hLvalue hLroute] with x hx
    rcases hx with hl | hh
    · exact Or.inl ⟨hl.2.2.1, hl.2.2.2⟩
    · exact Or.inr ⟨⟨hh.1.le, hh.2.1⟩, hh.2.2.2.1, hh.2.2.2.2.2⟩
  have hu := (measurePreserving_fst (μ := (Γ).F ⊗ₘ (Γ).σ) (ν := permLaw 2)).quasiMeasurePreserving.ae hj
  have halign : ∀ᵐ u ∂userLaw Γ, FloorAlignedDraw R R' u (f u) := by
    filter_upwards [hu] with u hu
    rcases hu with hl | hh
    · have hf : f u = u := by
        rcases u with ⟨x,τ⟩
        simp only [replaceSourceUpperDraw, Prod.map_apply, replaceSourceUpperPair,
          if_neg (not_lt.mpr hl.1), id_eq]
      rw [hf]
      exact ⟨rfl, rfl, Or.inl ⟨rfl, hl.1.trans_lt hUR, hl.1.trans_lt hUR'⟩⟩
    · have hb := ((source_upper_envelope row m hm hc hR' hR't).bid_bounds u.1.1 hh.1.1).1
      have hb0 : 0 ≤ sourceUpperBid row m R' u.1.1 := hR'.le.trans hb
      have hf : f u = ((u.1.1, Hybrid.upperAction (sourceUpperBid row m R') u.1.1), u.2) := by
        change (replaceSourceUpperPair row m hc R' u.1,u.2) = _
        rw [replaceSourceUpperPair,if_pos (hUR.trans_le hh.2.1)]
      rw [hf]
      refine ⟨?_, rfl, Or.inr ⟨hh.2.1, ?_⟩⟩
      · simpa only [Hybrid.upperAction] using hh.2.2
      · simpa only [Hybrid.upperAction, max_eq_left hb0] using hb
  exact ae_all_iff.mpr (fun k =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) k).quasiMeasurePreserving.ae halign)

include hm hR hUR hRt hR' hUR' hR't in
theorem sourceWeightedContext_floor_invariant :
    sourceWeightedContext row hc R Λ hΛ PL α hα =
      sourceWeightedContext row hc R' Λ hΛ PL α hα := by
  unfold sourceWeightedContext
  rw [sourceSeedMeasure_floor_invariant row hm hc hR hUR hRt hR' hUR' hR't PL]

include hm hR hUR hRt hR' hUR' hR't in

theorem sourceNativeGame_raw_lower_count_floor_invariant
    (u : Fin m) (a : JointAction 2)
    (haR : a.bid < R) (haR' : a.bid < R')
    (d : UserProfile m 2)
    (hd : ∀ k, FloorAlignedDraw R R' (d k) (f (d k)))
    (s : Fin 2 → unitInterval) (τ : Equiv.Perm (Fin 2)) :
    focalCount Γ u a ((d,s),τ) =
      focalCount Γ' u a (replaceSourceUpperSample row hc R' ((d,s),τ)) := by
  let C := sourceWeightedContext row hc R Λ hΛ PL α hα
  let d₀ := Function.update d u ((0,a),τ)
  let d₁ := Function.update (f ∘ d) u ((0,a),τ)
  have hdu : ∀ k, FloorAlignedDraw R R' (d₀ k) (d₁ k) := by
    intro k
    by_cases hk : k = u
    · subst k
      simp only [d₀, d₁, Function.update_self]
      exact ⟨rfl, rfl, Or.inl ⟨rfl, haR, haR'⟩⟩
    · simpa only [d₀, d₁, Function.update_of_ne hk, Function.comp_apply] using hd k
  have hctx (j : Fin 2) : observedContext R j (observe (deviated u a ((d,s),τ)) j) =
      observedContext R' j
        (observe (deviated u a (replaceSourceUpperSample row hc R' ((d,s),τ))) j) := by
    have h0 : observe (drawsRealization d₀) j =
        observe (deviated u a ((d,s),τ)) j :=
      observe_insertDraw u (((0,a),τ),(d,s)) j
    have h1 : observe (drawsRealization d₁) j =
        observe (deviated u a (replaceSourceUpperSample row hc R' ((d,s),τ))) j :=
      observe_insertDraw u (((0,a),τ),(f ∘ d,s)) j
    have hh := observedContext_floor_aligned d₀ d₁ hdu j
    change observedContext R j (observe (drawsRealization d₀) j) =
      observedContext R' j (observe (drawsRealization d₁) j) at hh
    rwa [h0, h1] at hh
  have hC := sourceWeightedContext_floor_invariant row hm hc hR hUR hRt
    hR' hUR' hR't hΛ PL α hα
  have hinc (j : Fin 2) :
      u ∈ allocation (deviated u a ((d,s),τ)) (Γ).policy s j ↔
        u ∈ allocation
          (deviated u a (replaceSourceUpperSample row hc R' ((d,s),τ))) (Γ').policy s j := by
    let L := observe (deviated u a ((d,s),τ)) j
    let L' := observe (deviated u a (replaceSourceUpperSample row hc R' ((d,s),τ))) j
    by_cases hj : j ∈ firstK τ a.routeCount
    · have hl : L u = some a.bid := by
        simp only [L, observe, deviated_recipients_self, hj,
          if_true, deviated_bid_self]
      have hl' : L' u = some a.bid := by
        simp only [L', observe, deviated_recipients_self, replaceSourceUpperSample,
          hj, if_true, deviated_bid_self]
      have h0 := C.factors R j L (s j) u (by
        rw [broadcastPart_some L u hl haR]
        exact Option.some_ne_none _)
      have h1 := (sourceWeightedContext row hc R' Λ hΛ PL α hα).factors
        R' j L' (s j) u (by
          rw [broadcastPart_some L' u hl' haR']
          exact Option.some_ne_none _)
      change (u ∈ C.selection R j L (s j)) ↔
        u ∈ (sourceWeightedContext row hc R' Λ hΛ PL α hα).selection R' j L' (s j)
      rw [h0, h1]
      change (u ∈ (sourceWeightedContext row hc R Λ hΛ PL α hα).select j
        (observedContext R j L) (s j)) ↔ _
      rw [hC, hctx j]
    · have hl : L u = none := by
        simp only [L, observe, deviated_recipients_self, if_neg hj]
      have hl' : L' u = none := by
        simp only [L', observe, deviated_recipients_self, replaceSourceUpperSample, if_neg hj]
      have hn : u ∉ allocation (deviated u a ((d,s),τ)) (Γ).policy s j := by
        intro hi
        exact ((Γ).policy j L (s j)).property.2 u hi hl
      have hn' : u ∉ allocation
          (deviated u a (replaceSourceUpperSample row hc R' ((d,s),τ))) (Γ').policy s j := by
        intro hi
        exact ((Γ').policy j L' (s j)).property.2 u hi hl'
      exact iff_of_false hn hn'
  apply Fin.ext
  change inclusionCount _ _ _ _ = inclusionCount _ _ _ _
  simp only [inclusionCount_eq_sum, hinc]
  rfl

include hm hR hUR hRt hR' hUR' hR't hLvalue hLroute in
theorem sourceNativeGame_raw_lower_outcome_floor_invariant
    (u : Fin m) (a : JointAction 2)
    (haR : a.bid < R) (haR' : a.bid < R') :
    (problem Γ u).outcome a = (problem Γ' u).outcome a := by
  have hp := sourceNativeGame_replace_sample_measurePreserving row hm hc hR hUR hRt
    hR' hR't hΛ PL hLvalue hLroute α hα
  have hd : ∀ᵐ ω ∂sampleLaw Γ,
      ∀ k, FloorAlignedDraw R R' (ω.1.1 k) (f (ω.1.1 k)) :=
    ((measurePreserving_fst (μ := userProfileLaw Γ)
      (ν := Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)))).comp
        (measurePreserving_fst (μ := backgroundLaw Γ) (ν := permLaw 2))).quasiMeasurePreserving.ae
          (sourceNativeGame_replace_aligned row hm hc hR hUR hRt hR' hUR' hR't
            hΛ PL hLvalue hLroute α hα)
  apply FiniteLaw.ext_expect
  intro q
  simp only [problem_outcome, CountLaw.expect_ofMeasure]
  calc
    _ = ∫ ω, q (focalCount Γ' u a (replaceSourceUpperSample row hc R' ω)) ∂sampleLaw Γ := by
      apply integral_congr_ae
      filter_upwards [hd] with ω hω
      rw [sourceNativeGame_raw_lower_count_floor_invariant row hm hc hR hUR hRt
        hR' hUR' hR't hΛ PL α hα u a haR haR' ω.1.1 hω ω.1.2 ω.2]
    _ = _ := by
      rw [← hp.map_eq]
      exact (integral_map_of_stronglyMeasurable hp.measurable
        (((measurable_of_countable q).comp (measurable_focalCount Γ' u a)).stronglyMeasurable)).symm

include hm hR hUR hRt hR' hUR' hR't hLvalue hLroute in
theorem sourceNativeGame_raw_lower_payoff_floor_invariant
    (u : Fin m) (v : ℝ) (a : JointAction 2)
    (haR : a.bid < R) (haR' : a.bid < R') :
    (problem Γ u).payoff v a = (problem Γ' u).payoff v a := by
  exact raw_payoff_congr_of_outcome_tariffs Γ Γ' u v a rfl rfl rfl
    (sourceNativeGame_raw_lower_outcome_floor_invariant row hm hc hR hUR hRt
      hR' hUR' hR't hΛ PL hLvalue hLroute α hα u a haR haR')

include hm hR hUR hRt hR' hUR' hR't hLvalue hLroute in

theorem sourceNativeGame_lower_outcome_floor_invariant
    (u : Fin m) (a : JointAction 2) (_ha2 : a.routeCount = 2)
    (haR : a.bid < R) (haR' : a.bid < R') :
    (problem Γ u).outcome a = (problem Γ' u).outcome a :=
  sourceNativeGame_raw_lower_outcome_floor_invariant row hm hc hR hUR hRt
    hR' hUR' hR't hΛ PL hLvalue hLroute α hα u a haR haR'

include hm hR hUR hRt hR' hUR' hR't hLvalue hLroute in
theorem sourceNativeGame_lower_payoff_floor_invariant
    (u : Fin m) (v : ℝ) (a : JointAction 2) (_ha2 : a.routeCount = 2)
    (haR : a.bid < R) (haR' : a.bid < R') :
    (problem Γ u).payoff v a = (problem Γ' u).payoff v a :=
  sourceNativeGame_raw_lower_payoff_floor_invariant row hm hc hR hUR hRt
    hR' hUR' hR't hΛ PL hLvalue hLroute α hα u v a haR haR'

include hm hR hUR hRt hR' hUR' hR't hLvalue hLroute in
theorem completeSourceNativeGame_raw_lower_outcome_floor_invariant
    (u : Fin m) (a : JointAction 2) (haR : a.bid < R) (haR' : a.bid < R') :
    (problem (completeSourceNativeGame row hc R Λ hΛ PL α hα) u).outcome a =
      (problem (completeSourceNativeGame row hc R' Λ hΛ PL α hα) u).outcome a := by
  rw [completeSourceNativeGame_outcome, completeSourceNativeGame_outcome]
  exact sourceNativeGame_raw_lower_outcome_floor_invariant row hm hc hR hUR hRt
    hR' hUR' hR't hΛ PL hLvalue hLroute α hα u a haR haR'

include hm hR hUR hRt hR' hUR' hR't hLvalue hLroute in
theorem completeSourceNativeGame_raw_lower_payoff_floor_invariant
    (u : Fin m) (v : ℝ) (a : JointAction 2) (haR : a.bid < R) (haR' : a.bid < R') :
    (problem (completeSourceNativeGame row hc R Λ hΛ PL α hα) u).payoff v a =
      (problem (completeSourceNativeGame row hc R' Λ hΛ PL α hα) u).payoff v a := by
  rw [completeSourceNativeGame_payoff, completeSourceNativeGame_payoff]
  exact sourceNativeGame_raw_lower_payoff_floor_invariant row hm hc hR hUR hRt
    hR' hUR' hR't hΛ PL hLvalue hLroute α hα u v a haR haR'

include hm hR hUR hRt hR' hUR' hR't hLvalue hLroute in
theorem completeSourceNativeGame_lower_outcome_floor_invariant
    (u : Fin m) (a : JointAction 2) (ha2 : a.routeCount = 2)
    (haR : a.bid < R) (haR' : a.bid < R') :
    (problem (completeSourceNativeGame row hc R Λ hΛ PL α hα) u).outcome a =
      (problem (completeSourceNativeGame row hc R' Λ hΛ PL α hα) u).outcome a := by
  rw [completeSourceNativeGame_outcome, completeSourceNativeGame_outcome]
  exact sourceNativeGame_lower_outcome_floor_invariant row hm hc hR hUR hRt
    hR' hUR' hR't hΛ PL hLvalue hLroute α hα u a ha2 haR haR'

include hm hR hUR hRt hR' hUR' hR't hLvalue hLroute in
theorem completeSourceNativeGame_lower_payoff_floor_invariant
    (u : Fin m) (v : ℝ) (a : JointAction 2) (ha2 : a.routeCount = 2)
    (haR : a.bid < R) (haR' : a.bid < R') :
    (problem (completeSourceNativeGame row hc R Λ hΛ PL α hα) u).payoff v a =
      (problem (completeSourceNativeGame row hc R' Λ hΛ PL α hα) u).payoff v a := by
  rw [completeSourceNativeGame_payoff, completeSourceNativeGame_payoff]
  exact sourceNativeGame_lower_payoff_floor_invariant row hm hc hR hUR hRt
    hR' hUR' hR't hΛ PL hLvalue hLroute α hα u v a ha2 haR haR'

end Actual

theorem literalSourceNativeGame_lower_outcome_floor_invariant
    (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R R' Λ : ℝ}
    (hR : 0 < R) (hUR : Early.bidCap row < R) (hRt : R < Uniform07.cutoff row)
    (hR' : 0 < R') (hUR' : Early.bidCap row < R') (hR't : R' < Uniform07.cutoff row)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (z width ε : ℝ) (u : Fin m) (a : JointAction 2)
    (ha2 : a.routeCount = 2) (haR : a.bid < R) (haR' : a.bid < R') :
    (problem (literalSourceNativeGame row hc R Λ z width ε hΛ PL) u).outcome a =
      (problem (literalSourceNativeGame row hc R' Λ z width ε hΛ PL) u).outcome a :=
  completeSourceNativeGame_lower_outcome_floor_invariant row hm hc hR hUR hRt
    hR' hUR' hR't (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute
    (literalSourceAlpha row Λ z width ε) (measurable_literalSourceAlpha row hΛ z width ε)
    u a ha2 haR haR'

theorem literalSourceNativeGame_lower_payoff_floor_invariant
    (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R R' Λ : ℝ}
    (hR : 0 < R) (hUR : Early.bidCap row < R) (hRt : R < Uniform07.cutoff row)
    (hR' : 0 < R') (hUR' : Early.bidCap row < R') (hR't : R' < Uniform07.cutoff row)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (z width ε : ℝ) (u : Fin m) (v : ℝ) (a : JointAction 2)
    (ha2 : a.routeCount = 2) (haR : a.bid < R) (haR' : a.bid < R') :
    (problem (literalSourceNativeGame row hc R Λ z width ε hΛ PL) u).payoff v a =
      (problem (literalSourceNativeGame row hc R' Λ z width ε hΛ PL) u).payoff v a :=
  completeSourceNativeGame_lower_payoff_floor_invariant row hm hc hR hUR hRt
    hR' hUR' hR't (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute
    (literalSourceAlpha row Λ z width ε) (measurable_literalSourceAlpha row hΛ z width ε)
    u v a ha2 haR haR'

theorem literalSourceNativeGame_raw_lower_outcome_floor_invariant
    (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R R' Λ : ℝ}
    (hR : 0 < R) (hUR : Early.bidCap row < R) (hRt : R < Uniform07.cutoff row)
    (hR' : 0 < R') (hUR' : Early.bidCap row < R') (hR't : R' < Uniform07.cutoff row)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (z width ε : ℝ) (u : Fin m) (a : JointAction 2)
    (haR : a.bid < R) (haR' : a.bid < R') :
    (problem (literalSourceNativeGame row hc R Λ z width ε hΛ PL) u).outcome a =
      (problem (literalSourceNativeGame row hc R' Λ z width ε hΛ PL) u).outcome a :=
  completeSourceNativeGame_raw_lower_outcome_floor_invariant row hm hc hR hUR hRt
    hR' hUR' hR't (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute
    (literalSourceAlpha row Λ z width ε) (measurable_literalSourceAlpha row hΛ z width ε)
    u a haR haR'

theorem literalSourceNativeGame_raw_lower_payoff_floor_invariant
    (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R R' Λ : ℝ}
    (hR : 0 < R) (hUR : Early.bidCap row < R) (hRt : R < Uniform07.cutoff row)
    (hR' : 0 < R') (hUR' : Early.bidCap row < R') (hR't : R' < Uniform07.cutoff row)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (z width ε : ℝ) (u : Fin m) (v : ℝ) (a : JointAction 2)
    (haR : a.bid < R) (haR' : a.bid < R') :
    (problem (literalSourceNativeGame row hc R Λ z width ε hΛ PL) u).payoff v a =
      (problem (literalSourceNativeGame row hc R' Λ z width ε hΛ PL) u).payoff v a :=
  completeSourceNativeGame_raw_lower_payoff_floor_invariant row hm hc hR hUR hRt
    hR' hUR' hR't (source_guard_multiplier_positive row hΛ) PL hLvalue hLroute
    (literalSourceAlpha row Λ z width ε) (measurable_literalSourceAlpha row hΛ z width ε)
    u v a haR haR'

end FCAppendix.Affine.Uniform07Finishing
