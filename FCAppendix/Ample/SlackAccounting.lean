import FCAppendix.Ample.SlackSelection
import FCAppendix.Ample.PositiveBaseRoutes
import FCAppendix.Ample.Service

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped BigOperators Classical

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def cutRouteCount (b : ℝ) (x : ℝ × JointAction n) : ℕ :=
  if b < x.2.bid then x.2.routeCount else 0

lemma cutRouteCount_le (b : ℝ) (x : ℝ × JointAction n) : cutRouteCount b x ≤ n := by
  unfold cutRouteCount
  split
  · exact x.2.routeCount_le
  · exact Nat.zero_le n

lemma measurable_cutRouteCount (b : ℝ) : Measurable (cutRouteCount (n := n) b) :=
  Measurable.ite
    (measurableSet_lt measurable_const ((measurable_bid n).comp measurable_snd))
    ((measurable_routeCount n).comp measurable_snd) measurable_const

lemma integrable_cutRouteFunction (Γ : FiniteGame m n c Seed) (b : ℝ) (f : ℕ → ℝ) :
    Integrable (fun x : ℝ × JointAction n => f (cutRouteCount b x)) (Γ.F ⊗ₘ Γ.σ) := by
  apply Integrable.of_bound
    (((measurable_of_countable f).comp (measurable_cutRouteCount b)).aestronglyMeasurable)
    (∑ r ∈ Finset.range (n + 1), ‖f r‖)
  exact ae_of_all _ fun x => Finset.single_le_sum (fun r _ => norm_nonneg (f r))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (cutRouteCount_le b x)))

lemma integrable_cutRouteIndicator (Γ : FiniteGame m n c Seed) (b : ℝ)
    (P : ℕ → Prop) : Integrable (fun x : ℝ × JointAction n =>
      if 0 < cutRouteCount b x ∧ P (cutRouteCount b x) then (1 : ℝ) else 0)
      (Γ.F ⊗ₘ Γ.σ) := by
  convert integrable_cutRouteFunction Γ b
    (fun k => if 0 < k ∧ P k then (1 : ℝ) else 0) using 1

theorem visibleLaw_expect_routeFunction (Γ : FiniteGame m n c Seed) (b : ℝ) (f : ℕ → ℝ) :
    (visibleLaw Γ b).expect (fun T => f T.card) =
      ∫ x : ℝ × JointAction n, f (cutRouteCount b x) ∂(Γ.F ⊗ₘ Γ.σ) := by
  have hcard (d : UserDraw n) : (visibleContact b d).card = cutRouteCount b d.1 := by
    unfold visibleContact cutRouteCount
    split <;> simp [card_firstK _ _ d.1.2.routeCount_le]
  rw [visibleLaw, FiniteLaw.expect_ofMeasure]
  have hi : Integrable (fun d : UserDraw n => f (cutRouteCount b d.1)) (userLaw Γ) := by
    simpa only [hcard] using FiniteLaw.integrable_finite_comp (userLaw Γ)
      (visibleContact b) (measurable_visibleContact b) (fun T => f T.card)
  simp_rw [hcard]
  rw [userLaw, integral_prod _ hi]
  simp

lemma positiveRouteTail_zero (Γ : FiniteGame m n c Seed) (P : ℕ → Prop) :
    positiveRouteTail Γ P 0 = positiveRouteMass Γ P := by
  unfold positiveRouteTail positiveRouteMass
  congr 1
  ext x
  simp only [mem_setOf_eq]
  tauto

theorem visibleLaw_prob_positiveClass (Γ : FiniteGame m n c Seed)
    (b : ℝ) (hb : 0 ≤ b) (P : ℕ → Prop) :
    (visibleLaw Γ b).prob (fun T => 0 < T.card ∧ P T.card) = positiveRouteTail Γ P b := by
  classical
  rw [visibleLaw, FiniteLaw.prob_ofMeasure]
  have he : {d : UserDraw n | 0 < (visibleContact b d).card ∧ P (visibleContact b d).card} =
      {x : ℝ × JointAction n | 0 < x.2.bid ∧ 0 < x.2.routeCount ∧
        P x.2.routeCount ∧ b < x.2.bid} ×ˢ univ := by
    ext d
    by_cases h : b < d.1.2.bid
    · have hpos := lt_of_le_of_lt hb h
      simp only [visibleContact, if_true, card_firstK _ _ d.1.2.routeCount_le,
        mem_prod, mem_setOf_eq, mem_univ, and_true, hpos, true_and, h]
    · simp [visibleContact, h]
  rw [he, userLaw, measureReal_prod_prod, probReal_univ, mul_one]
  rfl

theorem positiveRouteMass_eq_visible (Γ : FiniteGame m n c Seed) (P : ℕ → Prop) :
    positiveRouteMass Γ P = (visibleLaw Γ 0).prob (fun T => 0 < T.card ∧ P T.card) := by
  rw [visibleLaw_prob_positiveClass Γ 0 le_rfl, positiveRouteTail_zero]

theorem positiveRouteTail_eq_integral (Γ : FiniteGame m n c Seed)
    (b : ℝ) (hb : 0 ≤ b) (P : ℕ → Prop) :
    positiveRouteTail Γ P b = ∫ x : ℝ × JointAction n,
      (if 0 < cutRouteCount b x ∧ P (cutRouteCount b x) then (1 : ℝ) else 0)
        ∂(Γ.F ⊗ₘ Γ.σ) := by
  classical
  rw [← visibleLaw_prob_positiveClass Γ b hb, FiniteLaw.prob_eq_expect]
  convert visibleLaw_expect_routeFunction Γ b
    (fun k => if 0 < k ∧ P k then (1 : ℝ) else 0) using 1

theorem positiveRouteMass_eq_integral (Γ : FiniteGame m n c Seed) (P : ℕ → Prop) :
    positiveRouteMass Γ P = ∫ x : ℝ × JointAction n,
      (if 0 < cutRouteCount 0 x ∧ P (cutRouteCount 0 x) then (1 : ℝ) else 0)
        ∂(Γ.F ⊗ₘ Γ.σ) := by
  rw [← positiveRouteTail_zero Γ P]
  exact positiveRouteTail_eq_integral Γ 0 le_rfl P

lemma positiveRouteMass_nonneg (Γ : FiniteGame m n c Seed) (P : ℕ → Prop) :
    0 ≤ positiveRouteMass Γ P := measureReal_nonneg

lemma positiveRouteMass_le_one (Γ : FiniteGame m n c Seed) (P : ℕ → Prop) :
    positiveRouteMass Γ P ≤ 1 := measureReal_le_one

lemma positiveRouteTail_nonneg (Γ : FiniteGame m n c Seed) (P : ℕ → Prop) (b : ℝ) :
    0 ≤ positiveRouteTail Γ P b := measureReal_nonneg

lemma positiveRouteTail_le_mass (Γ : FiniteGame m n c Seed) (P : ℕ → Prop) (b : ℝ) :
    positiveRouteTail Γ P b ≤ positiveRouteMass Γ P := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  exact ⟨hx.1, hx.2.1, hx.2.2.1⟩

lemma positiveRouteMass_mono (Γ : FiniteGame m n c Seed) {P Q : ℕ → Prop}
    (hPQ : ∀ k, 0 < k → k ≤ n → P k → Q k) :
    positiveRouteMass Γ P ≤ positiveRouteMass Γ Q := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  exact ⟨hx.1, hx.2.1, hPQ _ hx.2.1 x.2.routeCount_le hx.2.2⟩

lemma positiveRouteTail_mono_class (Γ : FiniteGame m n c Seed) {P Q : ℕ → Prop}
    (hPQ : ∀ k, 0 < k → k ≤ n → P k → Q k) (b : ℝ) :
    positiveRouteTail Γ P b ≤ positiveRouteTail Γ Q b := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  exact ⟨hx.1, hx.2.1, hPQ _ hx.2.1 x.2.routeCount_le hx.2.2.1, hx.2.2.2⟩

lemma positiveRouteTail_class_eq (Γ : FiniteGame m n c Seed) (b : ℝ) (hb : 0 ≤ b)
    {j : ℕ} (hj : 1 ≤ j) :
    positiveRouteTail Γ (fun k => k = j) b = visibleClassMass Γ b j := by
  rw [visibleClassMass_eq_compProd Γ b hj]
  unfold positiveRouteTail
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨hx.2.2.2, hx.2.2.1⟩
  · rintro ⟨hx, hk⟩
    exact ⟨lt_of_le_of_lt hb hx, by omega, hk, hx⟩

lemma positiveRouteMass_class_eq (Γ : FiniteGame m n c Seed) {j : ℕ} (hj : 1 ≤ j) :
    positiveRouteMass Γ (fun k => k = j) = visibleClassMass Γ 0 j := by
  rw [← positiveRouteTail_zero]
  exact positiveRouteTail_class_eq Γ 0 le_rfl hj

lemma positiveRouteTail_split (Γ : FiniteGame m n c Seed) (b : ℝ) (hb : 0 ≤ b) :
    positiveRouteTail Γ (fun _ => True) b =
      positiveRouteTail Γ (fun k => k = 1) b + positiveRouteTail Γ (fun k => 2 ≤ k) b := by
  classical
  simp_rw [← visibleLaw_prob_positiveClass Γ b hb, FiniteLaw.prob_eq_expect]
  rw [← FiniteLaw.expect_add]
  apply FiniteLaw.expect_congr
  intro T
  by_cases h0 : T.card = 0
  · simp [h0]
  · by_cases h1 : T.card = 1
    · simp [h1]
    · have h2 : 2 ≤ T.card := by omega
      have hk0 : 0 < T.card := by omega
      simp [h1, h2, hk0]

lemma positiveRouteMass_split (Γ : FiniteGame m n c Seed) :
    positiveRouteMass Γ (fun _ => True) =
      positiveRouteMass Γ (fun k => k = 1) + positiveRouteMass Γ (fun k => 2 ≤ k) := by
  simpa only [positiveRouteTail_zero] using positiveRouteTail_split Γ 0 le_rfl

lemma positiveRouteMass_sum_classes (Γ : FiniteGame m n c Seed) :
    positiveRouteMass Γ (fun _ => True) =
      ∑ j ∈ Finset.Icc 1 n, visibleClassMass Γ 0 j := by
  rw [positiveRouteMass_eq_visible]
  change (visibleLaw Γ 0).prob (fun T => 0 < T.card ∧ True) =
    ∑ j ∈ Finset.Icc 1 n, Ample.classMass (visibleLaw Γ 0) j
  rw [Ample.sum_classMass]
  simp only [FiniteLaw.prob_eq_expect]
  apply FiniteLaw.expect_congr
  intro T
  simp only [Finset.card_pos, and_true, Finset.nonempty_iff_ne_empty]

theorem positiveRouteMass_le_active (Γ : FiniteGame m n c Seed)
    (hact : NonpositiveAbstention Γ) (P : ℕ → Prop) :
    positiveRouteMass Γ P ≤ Γ.F.real (Ioi Γ.g) := by
  rw [← joint_value_probability Γ (Ioi Γ.g) measurableSet_Ioi]
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [hact] with x hx hxP
  by_contra hv
  have hk := hx (le_of_not_gt hv)
  have hh : 0 < x.2.routeCount := hxP.2.1
  omega

lemma arrivalMean_eq_integral (Γ : FiniteGame m n c Seed) (b : ℝ) :
    Ample.contactMarginal n (visibleClassMass Γ b) =
      (∫ x : ℝ × JointAction n, (cutRouteCount b x : ℝ) ∂(Γ.F ⊗ₘ Γ.σ)) / n := by
  have he := visibleLaw_expect_routeFunction Γ b (fun k => (k : ℝ))
  rw [visibleLaw_eq_contactLaw, Ample.contactLaw_expect_card] at he
  unfold Ample.contactMarginal
  rw [he]

lemma arrivalMean_nonneg (Γ : FiniteGame m n c Seed) (b : ℝ) :
    0 ≤ Ample.contactMarginal n (visibleClassMass Γ b) := by
  rw [arrivalMean_eq_integral]
  exact div_nonneg (integral_nonneg (fun _ => Nat.cast_nonneg _)) (Nat.cast_nonneg n)

lemma arrivalMean_le_tail (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (b : ℝ) (hb : 0 ≤ b) :
    Ample.contactMarginal n (visibleClassMass Γ b) ≤ positiveRouteTail Γ (fun _ => True) b := by
  rw [arrivalMean_eq_integral, positiveRouteTail_eq_integral Γ b hb]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
  rw [← integral_mul_const]
  apply integral_mono (integrable_cutRouteFunction Γ b (fun k => (k : ℝ)))
    ((integrable_cutRouteIndicator Γ b (fun _ => True)).mul_const n)
  intro x
  by_cases hk : 0 < cutRouteCount b x
  · simpa [hk] using (show (cutRouteCount b x : ℝ) ≤ n by exact_mod_cast cutRouteCount_le b x)
  · have hz : cutRouteCount b x = 0 := by omega
    simp [hz]

lemma arrivalMean_ge_singleton (Γ : FiniteGame m n c Seed) (_hn : 0 < n)
    (b : ℝ) (hb : 0 ≤ b) :
    positiveRouteTail Γ (fun k => k = 1) b / n ≤
      Ample.contactMarginal n (visibleClassMass Γ b) := by
  rw [arrivalMean_eq_integral, positiveRouteTail_eq_integral Γ b hb]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply integral_mono (integrable_cutRouteIndicator Γ b (fun k => k = 1))
    (integrable_cutRouteFunction Γ b (fun k => (k : ℝ)))
  intro x
  by_cases hk : cutRouteCount b x = 1
  · simp [hk]
  · simp [hk, Nat.cast_nonneg]

theorem removedClass_le_removedAll (Γ : FiniteGame m n c Seed)
    (P : ℕ → Prop) (b : ℝ) (hb : 0 ≤ b) :
    positiveRouteMass Γ P - positiveRouteTail Γ P b ≤
      positiveRouteMass Γ (fun _ => True) - positiveRouteTail Γ (fun _ => True) b := by
  classical
  rw [positiveRouteMass_eq_integral, positiveRouteTail_eq_integral Γ b hb,
    positiveRouteMass_eq_integral, positiveRouteTail_eq_integral Γ b hb,
    ← integral_sub (integrable_cutRouteIndicator Γ 0 P) (integrable_cutRouteIndicator Γ b P),
    ← integral_sub (integrable_cutRouteIndicator Γ 0 (fun _ => True))
      (integrable_cutRouteIndicator Γ b (fun _ => True))]
  apply integral_mono
    ((integrable_cutRouteIndicator Γ 0 P).sub (integrable_cutRouteIndicator Γ b P))
    ((integrable_cutRouteIndicator Γ 0 (fun _ => True)).sub
      (integrable_cutRouteIndicator Γ b (fun _ => True)))
  intro x
  dsimp only [Pi.sub_apply]
  by_cases h0 : 0 < x.2.bid
  · by_cases hb' : b < x.2.bid
    · simp [cutRouteCount, h0, hb']
    · simp only [cutRouteCount, if_pos h0, if_neg hb', Nat.lt_irrefl, false_and, if_false,
        sub_zero, and_true]
      split <;> split <;> simp_all
  · have hb' : ¬ b < x.2.bid := fun hx => h0 (lt_of_le_of_lt hb hx)
    simp [cutRouteCount, h0, hb']

theorem arrivalMean_loss_le_removedMass (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (b : ℝ) (hb : 0 ≤ b) :
    Ample.contactMarginal n (visibleClassMass Γ 0) -
        Ample.contactMarginal n (visibleClassMass Γ b) ≤
      positiveRouteMass Γ (fun _ => True) - positiveRouteTail Γ (fun _ => True) b := by
  classical
  rw [arrivalMean_eq_integral, arrivalMean_eq_integral, ← sub_div,
    positiveRouteMass_eq_integral, positiveRouteTail_eq_integral Γ b hb]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
  rw [← integral_sub (integrable_cutRouteFunction Γ 0 (fun k => (k : ℝ)))
      (integrable_cutRouteFunction Γ b (fun k => (k : ℝ))),
    ← integral_sub (integrable_cutRouteIndicator Γ 0 (fun _ => True))
      (integrable_cutRouteIndicator Γ b (fun _ => True)),
    ← integral_mul_const]
  apply integral_mono
    ((integrable_cutRouteFunction Γ 0 (fun k => (k : ℝ))).sub
      (integrable_cutRouteFunction Γ b (fun k => (k : ℝ))))
    (((integrable_cutRouteIndicator Γ 0 (fun _ => True)).sub
      (integrable_cutRouteIndicator Γ b (fun _ => True))).mul_const n)
  intro x
  dsimp only [Pi.sub_apply]
  by_cases h0 : 0 < x.2.bid
  · by_cases hb' : b < x.2.bid
    · simp [cutRouteCount, h0, hb']
    · by_cases hk : 0 < x.2.routeCount
      · simp only [cutRouteCount, if_pos h0, if_neg hb', Nat.cast_zero, sub_zero,
          hk, and_self, if_true, Nat.lt_irrefl, false_and, if_false, one_mul]
        exact_mod_cast x.2.routeCount_le
      · have hz : x.2.routeCount = 0 := by omega
        simp [cutRouteCount, h0, hb', hz]
  · have hb' : ¬ b < x.2.bid := fun hx => h0 (lt_of_le_of_lt hb hx)
    simp [cutRouteCount, h0, hb']

theorem arrivalMean_loss_ge_removedMulti (Γ : FiniteGame m n c Seed) (_hn : 0 < n)
    (b : ℝ) (hb : 0 ≤ b) :
    (2 / (n : ℝ)) * (positiveRouteMass Γ (fun k => 2 ≤ k) -
        positiveRouteTail Γ (fun k => 2 ≤ k) b) ≤
      Ample.contactMarginal n (visibleClassMass Γ 0) -
        Ample.contactMarginal n (visibleClassMass Γ b) := by
  classical
  rw [arrivalMean_eq_integral, arrivalMean_eq_integral, ← sub_div]
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [positiveRouteMass_eq_integral, positiveRouteTail_eq_integral Γ b hb,
    ← integral_sub (integrable_cutRouteFunction Γ 0 (fun k => (k : ℝ)))
      (integrable_cutRouteFunction Γ b (fun k => (k : ℝ))),
    ← integral_sub (integrable_cutRouteIndicator Γ 0 (fun k => 2 ≤ k))
      (integrable_cutRouteIndicator Γ b (fun k => 2 ≤ k)),
    ← integral_const_mul]
  apply integral_mono
    (((integrable_cutRouteIndicator Γ 0 (fun k => 2 ≤ k)).sub
      (integrable_cutRouteIndicator Γ b (fun k => 2 ≤ k))).const_mul 2)
    ((integrable_cutRouteFunction Γ 0 (fun k => (k : ℝ))).sub
      (integrable_cutRouteFunction Γ b (fun k => (k : ℝ))))
  intro x
  dsimp only [Pi.sub_apply]
  by_cases h0 : 0 < x.2.bid
  · by_cases hb' : b < x.2.bid
    · simp [cutRouteCount, h0, hb']
    · by_cases hk : 2 ≤ x.2.routeCount
      · have hk0 : 0 < x.2.routeCount := by omega
        simp only [cutRouteCount, if_pos h0, if_neg hb', Nat.cast_zero, sub_zero,
          hk0, hk, and_self, if_true, Nat.lt_irrefl, false_and, if_false, mul_one]
        exact_mod_cast hk
      · simp [cutRouteCount, h0, hb', hk, Nat.cast_nonneg]
  · have hb' : ¬ b < x.2.bid := fun hx => h0 (lt_of_le_of_lt hb hx)
    simp [cutRouteCount, h0, hb']

lemma finiteCoverage_eq_average_success (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    finiteCoverage Γ =
      (∑ i : Fin m, ∫ x : ℝ × JointAction n,
        ((problem Γ i).outcome x.2).success ∂(Γ.F ⊗ₘ Γ.σ)) / m := by
  rw [← integral_conditionalTypeCountLaw_success Γ hm]
  exact integral_conditionalTypeCountLaw_expect Γ hm _

lemma integrable_joint_success (Γ : FiniteGame m n c Seed) (i : Fin m) :
    Integrable (fun x : ℝ × JointAction n => ((problem Γ i).outcome x.2).success)
      (Γ.F ⊗ₘ Γ.σ) :=
  FiniteLaw.integrable_expect _ _ (fun r => (measurable_outcome_mass Γ i r).comp measurable_snd) _

theorem finiteCoverage_le_integral_bound (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (f : ℝ × JointAction n → ℝ) (hf : Integrable f (Γ.F ⊗ₘ Γ.σ))
    (hbound : ∀ i : Fin m, ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      ((problem Γ i).outcome x.2).success ≤ f x) :
    finiteCoverage Γ ≤ ∫ x, f x ∂(Γ.F ⊗ₘ Γ.σ) := by
  rw [finiteCoverage_eq_average_success Γ hm]
  calc
    _ ≤ (∑ _i : Fin m, ∫ x, f x ∂(Γ.F ⊗ₘ Γ.σ)) / m := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
      exact Finset.sum_le_sum fun i _ => integral_mono_ae (integrable_joint_success Γ i) hf (hbound i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hm.ne')

lemma success_zero_of_route_zero (Γ : FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) (hk : a.routeCount = 0) :
    ((problem Γ i).outcome a).success = 0 := by
  have hL := load_le_routeCount_mul_success Γ i a
  rw [hk, Nat.cast_zero, zero_mul] at hL
  exact le_antisymm (((problem Γ i).outcome a).success_le_load.trans hL)
    ((problem Γ i).outcome a).success_nonneg

theorem finiteCoverage_le_positiveParticipation (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hzero : RejectsZeroBids Γ) :
    finiteCoverage Γ ≤ positiveRouteMass Γ (fun _ => True) := by
  classical
  rw [positiveRouteMass_eq_integral]
  apply finiteCoverage_le_integral_bound Γ hm _ (integrable_cutRouteIndicator Γ 0 (fun _ => True))
  intro i
  filter_upwards [] with x
  by_cases hb : 0 < x.2.bid
  · by_cases hk : 0 < x.2.routeCount
    · simpa [cutRouteCount, hb, hk] using ((problem Γ i).outcome x.2).success_le_one
    · have hz : x.2.routeCount = 0 := by omega
      simp [cutRouteCount, hb, hz, success_zero_of_route_zero Γ i x.2 hz]
  · have hz : x.2.bid = 0 := le_antisymm (le_of_not_gt hb) x.2.bid_nonneg
    simp [cutRouteCount, hb, success_zero_of_bid_zero Γ hn hzero i x.2 hz]

lemma submittedMarginal_nonneg (Γ : FiniteGame m n c Seed) : 0 ≤ submittedMarginal Γ :=
  div_nonneg (integral_nonneg (fun _ => Nat.cast_nonneg _)) (Nat.cast_nonneg n)

lemma integrable_routeCount (Γ : FiniteGame m n c Seed) :
    Integrable (fun x : ℝ × JointAction n => (x.2.routeCount : ℝ)) (Γ.F ⊗ₘ Γ.σ) := by
  have he (x : ℝ × JointAction n) : cutRouteCount (-1) x = x.2.routeCount := by
    rw [cutRouteCount, if_pos (show (-1 : ℝ) < x.2.bid by linarith [x.2.bid_nonneg])]
  simpa only [he] using integrable_cutRouteFunction Γ (-1) (fun k => (k : ℝ))

lemma arrivalMean_le_submitted (Γ : FiniteGame m n c Seed) (b : ℝ) :
    Ample.contactMarginal n (visibleClassMass Γ b) ≤ submittedMarginal Γ := by
  rw [arrivalMean_eq_integral]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply integral_mono (integrable_cutRouteFunction Γ b _) (integrable_routeCount Γ)
  intro x
  dsimp only [cutRouteCount]
  split <;> simp [Nat.cast_nonneg]

theorem submitted_minus_positive_le_coverage_deficit (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hact : NonpositiveAbstention Γ)
    (hzero : RejectsZeroBids Γ) :
    submittedMarginal Γ - Ample.contactMarginal n (visibleClassMass Γ 0) ≤
      Γ.F.real (Ioi Γ.g) - finiteCoverage Γ := by
  classical
  have hS := finiteCoverage_le_positiveParticipation Γ hm hn hzero
  suffices h : submittedMarginal Γ - Ample.contactMarginal n (visibleClassMass Γ 0) ≤
      Γ.F.real (Ioi Γ.g) - positiveRouteMass Γ (fun _ => True) by linarith
  have hiE : Integrable
      ({x : ℝ × JointAction n | x.1 ∈ Ioi Γ.g}.indicator (1 : (ℝ × JointAction n) → ℝ))
      (Γ.F ⊗ₘ Γ.σ) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_Ioi.preimage measurable_fst)
  rw [submittedMarginal, arrivalMean_eq_integral, ← sub_div]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
  rw [positiveRouteMass_eq_integral,
    ← joint_value_probability Γ (Ioi Γ.g) measurableSet_Ioi,
    ← integral_indicator_one (s := {x : ℝ × JointAction n | x.1 ∈ Ioi Γ.g})
      (measurableSet_Ioi.preimage measurable_fst),
    ← integral_sub (integrable_routeCount Γ) (integrable_cutRouteFunction Γ 0 (fun k => (k : ℝ))),
    ← integral_sub hiE (integrable_cutRouteIndicator Γ 0 (fun _ => True)),
    ← integral_mul_const]
  apply integral_mono_ae
    ((integrable_routeCount Γ).sub (integrable_cutRouteFunction Γ 0 (fun k => (k : ℝ))))
    ((hiE.sub
        (integrable_cutRouteIndicator Γ 0 (fun _ => True))).mul_const n)
  filter_upwards [hact] with x hx
  dsimp only [Pi.sub_apply, Pi.one_apply]
  by_cases hv : Γ.g < x.1
  · by_cases hb : 0 < x.2.bid
    · by_cases hk : 0 < x.2.routeCount
      · simp [cutRouteCount, hb, hk, indicator_of_mem, hv]
      · have hz : x.2.routeCount = 0 := by omega
        simp [cutRouteCount, hb, hz, hv, Nat.cast_nonneg]
    · simp only [cutRouteCount, if_neg hb, Nat.cast_zero, sub_zero,
        Nat.lt_irrefl, false_and, if_false, Set.indicator, mem_setOf_eq, mem_Ioi, if_pos hv,
        Pi.one_apply, one_mul]
      exact_mod_cast x.2.routeCount_le
  · have hk : x.2.routeCount = 0 := hx (le_of_not_gt hv)
    simp [cutRouteCount, hk, hv]

theorem positiveRouteMass_le_raw (Γ : FiniteGame m n c Seed) (P : ℕ → Prop) :
    positiveRouteMass Γ P ≤ (Γ.F ⊗ₘ Γ.σ).real {x | 0 < x.2.routeCount ∧ P x.2.routeCount} := by
  exact measureReal_mono (fun x hx => hx.2)

end FCAppendix.Bayes
