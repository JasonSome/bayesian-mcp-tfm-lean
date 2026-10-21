import FCAppendix.Affine.Uniform07Finishing.Native.SourceDeficitMoment
import FCAppendix.Probability.EmpiricalMean

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open StrictNative ConditionalSuccess
open scoped BigOperators ProbabilityTheory
variable {m : ℕ} [Nonempty (Fin m)]

def localUpperScore (R : ℝ) (e : Option ℝ) : ℝ :=
  if StrictTags.tag R R e=2 then 1 else if StrictTags.tag R R e=0 then 0 else -1

lemma measurable_localUpperScore (R : ℝ) : Measurable (localUpperScore R) :=
  Measurable.ite (measurableSet_eq_fun (StrictTags.measurable_tag R R) measurable_const)
    measurable_const
    (Measurable.ite (measurableSet_eq_fun (StrictTags.measurable_tag R R) measurable_const)
      measurable_const measurable_const)

lemma localUpperScore_abs_le (R : ℝ) (e : Option ℝ) : |localUpperScore R e| ≤ 1 := by
  unfold localUpperScore
  split_ifs <;> norm_num

lemma localUpperScore_linear (R : ℝ) (e : Option ℝ) :
    localUpperScore R e = 2*(if StrictTags.tag R R e=2 then (1 : ℝ) else 0)+
      (if StrictTags.tag R R e=0 then (1 : ℝ) else 0)-1 := by
  by_cases h₂ : StrictTags.tag R R e=2
  · norm_num [localUpperScore,h₂,Fin.ext_iff]
  · by_cases h₀ : StrictTags.tag R R e=0 <;> simp [localUpperScore,h₂,h₀]

omit [Nonempty (Fin m)] in

lemma observedContext_gap_sq_eq (R : ℝ) (j : Fin 2) (L : LocalList m) :
    ((observedContext R j L).2.1-(observedContext R j L).2.2 : ℝ)^2 =
      (∑ u, localUpperScore R (L u))^2 := by
  let B := StrictTags.localCount R R L 0
  let H := StrictTags.localCount R R L 2
  have hBH : B+H ≤ m := by
    dsimp only [B,H,StrictTags.localCount]
    rw [←Finset.sum_add_distrib]
    calc
      _ ≤ ∑ _ : Fin m, 1 := by
        apply Finset.sum_le_sum
        intro u _
        by_cases h₀ : StrictTags.tag R R (L u)=0
        · norm_num [h₀,Fin.ext_iff]
        · by_cases h₂ : StrictTags.tag R R (L u)=2 <;> simp [h₀,h₂]
      _ = m := by simp
  have hB : B ≤ m := by omega
  have hH : H ≤ m-B := by omega
  have hsum : (∑ u, localUpperScore R (L u)) = 2*(H : ℝ)+(B : ℝ)-(m : ℝ) := by
    simp_rw [localUpperScore_linear]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    dsimp only [B,H,StrictTags.localCount]
    push_cast
    rfl
  rw [hsum]
  have hthere : ((m-B-H : ℕ) : ℝ) = (m : ℝ)-(B : ℝ)-(H : ℝ) := by
    rw [Nat.cast_sub hH,Nat.cast_sub hB]
  by_cases hj : j=0
  · change ((if j=0 then (H,m-B-H) else (m-B-H,H)).1-
      (if j=0 then (H,m-B-H) else (m-B-H,H)).2 : ℝ)^2 = _
    rw [if_pos hj,hthere]
    ring
  · change ((if j=0 then (H,m-B-H) else (m-B-H,H)).1-
      (if j=0 then (H,m-B-H) else (m-B-H,H)).2 : ℝ)^2 = _
    rw [if_neg hj,hthere]
    ring

def upperRouteScore (R : ℝ) (j : Fin 2) (u : UserDraw 2) : ℝ :=
  if u.1.2.bid< R then 0 else if j∈firstK u.2 u.1.2.routeCount then 1 else -1

lemma measurable_upperRouteScore (R : ℝ) (j : Fin 2) : Measurable (upperRouteScore R j) :=
  Measurable.ite (measurableSet_lt measurable_draw_bid measurable_const) measurable_const
    (Measurable.ite (measurableSet_contactsProposer j) measurable_const measurable_const)

lemma upperRouteScore_abs_le (R : ℝ) (j : Fin 2) (u : UserDraw 2) :
    |upperRouteScore R j u| ≤ 1 := by
  unfold upperRouteScore
  split_ifs <;> norm_num

theorem upperRouteScore_integral_zero
    (ν : Measure (ℝ × JointAction 2)) [IsProbabilityMeasure ν]
    (R : ℝ) (j : Fin 2)
    (hu : ∀ᵐ x ∂ν, R≤ x.2.bid → x.2.routeCount=1) :
    (∫ u, upperRouteScore R j u ∂ν.prod (permLaw 2)) = 0 := by
  have hi : Integrable (upperRouteScore R j) (ν.prod (permLaw 2)) := by
    apply Integrable.of_bound (measurable_upperRouteScore R j).aestronglyMeasurable 1
    filter_upwards [] with u
    simpa only [Real.norm_eq_abs] using upperRouteScore_abs_le R j u
  rw [integral_prod _ hi]
  calc
    _ = ∫ _x, (0 : ℝ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      by_cases hb : x.2.bid< R
      · simp only [upperRouteScore,if_pos hb,integral_zero]
      · have hk : x.2.routeCount=1 := hx (le_of_not_gt hb)
        let E : Set (Equiv.Perm (Fin 2)) := {τ | j∈firstK τ 1}
        have hE : MeasurableSet E := MeasurableSet.of_discrete
        have hfun : (fun τ => upperRouteScore R j (x,τ)) =
            fun τ => 2*E.indicator (fun _ => (1 : ℝ)) τ-1 := by
          funext τ
          by_cases he : j∈firstK τ 1 <;>
            norm_num [upperRouteScore,hb,hk,E,Set.indicator,he]
        have hEint : (∫ τ, E.indicator (fun _ => (1 : ℝ)) τ ∂permLaw 2) =
            (permLaw 2).real E := by
          convert! integral_indicator_one (μ := permLaw 2) hE using 1
        rw [hfun,integral_sub (((integrable_const (1 : ℝ)).indicator hE).const_mul 2)
          (integrable_const _),integral_const_mul,hEint]
        have hprob : (permLaw 2).real E = (1 : ℝ)/2 := by
          simpa only [Nat.cast_one,Nat.cast_ofNat] using
            permLaw_mem_firstK 2 1 (by norm_num) (by norm_num) j
        rw [hprob]
        simp
    _ = 0 := by simp

omit [Nonempty (Fin m)] in

theorem upperRouteScore_sum_second_le
    (ν : Measure (ℝ × JointAction 2)) [IsProbabilityMeasure ν]
    (R : ℝ) (j : Fin 2)
    (hu : ∀ᵐ x ∂ν, R≤ x.2.bid → x.2.routeCount=1) :
    (∫ d : UserProfile m 2, (∑ u, upperRouteScore R j (d u))^2
      ∂Measure.pi (fun _ : Fin m => ν.prod (permLaw 2))) ≤ m := by
  let μ := ν.prod (permLaw 2)
  let P := Measure.pi (fun _ : Fin m => μ)
  let f := upperRouteScore R j
  let S := fun d : UserProfile m 2 => ∑ u, f (d u)
  have hL : MemLp f 2 μ := MemLp.of_bound (measurable_upperRouteScore R j).aestronglyMeasurable
    1 (Eventually.of_forall (fun u => by simpa only [Real.norm_eq_abs] using upperRouteScore_abs_le R j u))
  have hLi (u : Fin m) : MemLp (fun d : UserProfile m 2 => f (d u)) 2 P :=
    hL.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => μ) u)
  have hS : MemLp S 2 P := memLp_finsetSum _ (fun u _ => hLi u)
  have hmean : (∫ d, S d ∂P) = 0 := by
    rw [show (fun d => S d) = (fun d => ∑ u, f (d u)) from rfl,
      integral_finsetSum _ (fun u _ => (hLi u).integrable (by norm_num))]
    have he (u : Fin m) : (∫ d : UserProfile m 2, f (d u) ∂P) = ∫ x, f x ∂μ :=
      integral_comp_eval (μ := fun _ : Fin m => μ) hL.aestronglyMeasurable
    have hfzero : (∫ x, f x ∂μ) = 0 := upperRouteScore_integral_zero ν R j hu
    simp only [he,hfzero,Finset.sum_const_zero]
  have hvar : variance S P = (m : ℝ)*variance f μ := by
    have hh := variance_sum_pi (μ := fun _ : Fin m => μ) (X := fun _ => f) (fun _ => hL)
    have heq : (∑ u : Fin m, fun d : UserProfile m 2 => f (d u)) = S := by
      ext d
      simp [S]
    rw [heq] at hh
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hv : variance f μ ≤ 1 := by
    apply (variance_le_expectation_sq hL.aestronglyMeasurable).trans
    calc
      (∫ x, f x^2 ∂μ) ≤ ∫ _x, (1 : ℝ) ∂μ := by
        apply integral_mono hL.integrable_sq (integrable_const _)
        intro x
        have hb := upperRouteScore_abs_le R j x
        nlinarith [sq_abs (f x),abs_nonneg (f x)]
      _ = 1 := by simp
  rw [variance_eq_sub hS] at hvar
  simp only [Pi.pow_apply,hmean,zero_pow (by norm_num : (2 : ℕ)≠0),sub_zero] at hvar
  change (∫ d, S d^2 ∂P) ≤ (m : ℝ)
  exact hvar.le.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (α := ℝ) m))

lemma localUpperScore_observe (R : ℝ) (j : Fin 2) (u : UserDraw 2)
    (hlow : u.1.2.bid< R → u.1.2.routeCount=2) :
    localUpperScore R (if j∈firstK u.2 u.1.2.routeCount then some u.1.2.bid else none) =
      upperRouteScore R j u := by
  by_cases hb : u.1.2.bid< R
  · simp [localUpperScore,upperRouteScore,StrictTags.tag,hb,hlow hb,firstK_full_two]
  · by_cases hj : j∈firstK u.2 u.1.2.routeCount <;>
      simp [localUpperScore,upperRouteScore,StrictTags.tag,hb,hj]

omit [Nonempty (Fin m)] in

lemma deviation_localUpperScore_difference_le (R : ℝ) (i : Fin m)
    (A : JointAction 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (d : UserProfile m 2)
    (hshape : ∀ u, (d u).1.2.bid< R → (d u).1.2.routeCount=2) :
    |(∑ u, localUpperScore R (deviationList i A d τ j u))-
      ∑ u, upperRouteScore R j (d u)| ≤ 2 := by
  have he (u : Fin m) (hui : u≠i) :
      localUpperScore R (deviationList i A d τ j u) = upperRouteScore R j (d u) := by
    rw [show deviationList i A d τ j u =
      (if j∈firstK (d u).2 (d u).1.2.routeCount then some (d u).1.2.bid else none) by
        simp [deviationList,observe,deviate,drawsRealization,hui]]
    exact localUpperScore_observe R j (d u) (hshape u)
  have hsum : (∑ u, localUpperScore R (deviationList i A d τ j u))-
      (∑ u, upperRouteScore R j (d u)) =
      localUpperScore R (deviationList i A d τ j i)-upperRouteScore R j (d i) := by
    rw [←Finset.sum_sub_distrib]
    exact Finset.sum_eq_single i (fun u _ hui => by rw [he u hui,sub_self]) (by simp)
  rw [hsum]
  have ha := localUpperScore_abs_le R (deviationList i A d τ j i)
  have hb := upperRouteScore_abs_le R j (d i)
  linarith [abs_sub (localUpperScore R (deviationList i A d τ j i)) (upperRouteScore R j (d i))]

omit [Nonempty (Fin m)] in

theorem classified_deviation_upper_second_le {c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (hm : 0 < m) (R : ℝ)
    (hclass : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ,
      (x.2.bid< R ∧ x.2.routeCount=2) ∨ (R≤ x.2.bid ∧ x.2.routeCount=1))
    (i : Fin m) (A : JointAction 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    (∫ d, ((observedContext R j (deviationList i A d τ j)).2.1-
      (observedContext R j (deviationList i A d τ j)).2.2 : ℝ)^2
      ∂userProfileLaw Γ) ≤ 10*(m : ℝ) := by
  let S := fun d : UserProfile m 2 => ∑ u, upperRouteScore R j (d u)
  let T := fun d : UserProfile m 2 => ∑ u, localUpperScore R (deviationList i A d τ j u)
  have hupper : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ, R≤ x.2.bid → x.2.routeCount=1 := by
    filter_upwards [hclass] with x hx
    intro hb
    rcases hx with hl | hh
    · exact ((not_lt_of_ge hb) hl.1).elim
    · exact hh.2
  have hdraw : ∀ᵐ u ∂userLaw Γ, u.1.2.bid< R → u.1.2.routeCount=2 := by
    have hh := (measurePreserving_fst (μ := Γ.F⊗ₘΓ.σ) (ν := permLaw 2)).quasiMeasurePreserving.ae hclass
    filter_upwards [hh] with u hu
    intro hb
    rcases hu with hl | hh
    · exact hl.2
    · exact ((not_lt_of_ge hh.1) hb).elim
  have hshape : ∀ᵐ d ∂userProfileLaw Γ, ∀ u,
      (d u).1.2.bid< R → (d u).1.2.routeCount=2 :=
    ae_all_iff.mpr (fun u =>
      (measurePreserving_eval (fun _ : Fin m => userLaw Γ) u).quasiMeasurePreserving.ae hdraw)
  have hS : Measurable S := Finset.measurable_sum _ (fun u _ =>
    (measurable_upperRouteScore R j).comp (measurable_pi_apply u))
  have hT : Measurable T := Finset.measurable_sum _ (fun u _ =>
    (measurable_localUpperScore R).comp
      ((measurable_pi_apply u).comp (measurable_deviationList_profile i A τ j)))
  have hSb (d : UserProfile m 2) : |S d| ≤ (m : ℝ) := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc
        (∑ u : Fin m, |upperRouteScore R j (d u)|) ≤ ∑ _ : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum (fun u _ => upperRouteScore_abs_le R j (d u))
        _ = m := by simp)
  have hTb (d : UserProfile m 2) : |T d| ≤ (m : ℝ) := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      calc
        (∑ u : Fin m, |localUpperScore R (deviationList i A d τ j u)|) ≤ ∑ _ : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum (fun u _ => localUpperScore_abs_le R _)
        _ = m := by simp)
  have hSi : Integrable (fun d => S d^2) (userProfileLaw Γ) := by
    apply Integrable.of_bound (hS.pow_const 2).aestronglyMeasurable ((m : ℝ)^2)
    filter_upwards [] with d
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (S d)),sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (S d)) (hSb d) 2
  have hTi : Integrable (fun d => T d^2) (userProfileLaw Γ) := by
    apply Integrable.of_bound (hT.pow_const 2).aestronglyMeasurable ((m : ℝ)^2)
    filter_upwards [] with d
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (T d)),sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (T d)) (hTb d) 2
  have hsecond : (∫ d, S d^2 ∂userProfileLaw Γ) ≤ m :=
    upperRouteScore_sum_second_le (Γ.F⊗ₘΓ.σ) R j hupper
  have hpoint : ∀ᵐ d ∂userProfileLaw Γ, T d^2 ≤ 2*S d^2+8 := by
    filter_upwards [hshape] with d hd
    have he : |T d-S d| ≤ 2 := deviation_localUpperScore_difference_le R i A τ j d hd
    have he2 : (T d-S d)^2 ≤ 4 := by
      nlinarith [sq_abs (T d-S d),abs_nonneg (T d-S d)]
    nlinarith [sq_nonneg (S d-(T d-S d))]
  calc
    _ = ∫ d, T d^2 ∂userProfileLaw Γ := by
      apply integral_congr_ae
      filter_upwards [] with d
      exact observedContext_gap_sq_eq R j _
    _ ≤ ∫ d, 2*S d^2+8 ∂userProfileLaw Γ :=
      integral_mono_ae hTi ((hSi.const_mul 2).add (integrable_const _)) hpoint
    _ = 2*(∫ d, S d^2 ∂userProfileLaw Γ)+8 := by
      rw [integral_add (hSi.const_mul 2) (integrable_const _),integral_const_mul]
      simp
    _ ≤ 10*(m : ℝ) := by
      have hmn : 1 ≤ m := hm
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmn
      linarith

theorem literalSource_deviation_upper_second_le (row : Uniform07.Row)
    (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ z width ε : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hRt : R < Uniform07.cutoff row)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (i : Fin m) (A : JointAction 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    (∫ d, ((observedContext R j (deviationList i A d τ j)).2.1-
      (observedContext R j (deviationList i A d τ j)).2.2 : ℝ)^2
      ∂userProfileLaw (literalSourceNativeGame row hc R Λ z width ε hΛ PL)) ≤ 10*(m : ℝ) := by
  apply classified_deviation_upper_second_le _ (by omega) R _ i A τ j
  rw [literalSourceNativeGame_joint_law row hm hc hR hRt hΛ PL hLvalue hLroute]
  filter_upwards [source_population_support row m hm hc hR hRt PL hLvalue hLroute] with x hx
  rcases hx with hl | hh
  · exact Or.inl ⟨hl.2.2.1.trans_lt hUR,hl.2.2.2⟩
  · exact Or.inr ⟨hh.2.2.2.1,hh.2.2.2.2.2⟩

end FCAppendix.Affine.Uniform07Finishing
