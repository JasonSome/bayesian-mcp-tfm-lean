import FCAppendix.CommonReserve.ZeroTies
import FCAppendix.CommonReserve.FiniteEstimates

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

def localStatistic (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (w : UserDraw n r → ℝ) (d : Fin m → UserDraw n r) (i : Fin m) : ℝ :=
  ∫ s, if i ∈ (Γ.policy j (fun l => (d l).2.val j) s).val then w (d i) else 0 ∂Γ.seedLaw

def localPositive (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (w : UserDraw n r → ℝ) (d : Fin m → UserDraw n r) (i : Fin m) : ℝ :=
  localPositiveStatistic Γ.seedLaw (Γ.policy j) (fun x => x.2.val j) w d i

def localZeroShare (_Γ : FiniteGame m n c r Seed) (j : Fin n)
    (d : Fin m → UserDraw n r) (i : Fin m) : ℝ :=
  equalShare {x | x.2.val j = some 0} (slotShortfall (c := c) j 0) d i

theorem measurable_localStatistic_integrand (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (w : UserDraw n r → ℝ) (hw : Measurable w) (i : Fin m) :
    Measurable (fun p : (Fin m → UserDraw n r) × Seed =>
      if i ∈ (Γ.policy j (fun l => (p.1 l).2.val j) p.2).val then w (p.1 i) else 0) := by
  have hL : Measurable (fun p : (Fin m → UserDraw n r) × Seed =>
      fun l => (p.1 l).2.val j) :=
    measurable_pi_lambda _ fun l => (measurable_coordinate j).comp
      ((measurable_pi_apply l).comp measurable_fst)
  exact measurable_weighted_membership _
    ((Γ.policy_measurable j).comp (hL.prodMk measurable_snd)) _
    (hw.comp ((measurable_pi_apply i).comp measurable_fst)) i

theorem measurable_localStatistic (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (w : UserDraw n r → ℝ) (hw : Measurable w) (i : Fin m) :
    Measurable (fun d => localStatistic Γ j w d i) :=
  (measurable_localStatistic_integrand Γ j w hw i).stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_localStatistic (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (w : UserDraw n r → ℝ) (hw : Measurable w)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, ‖w x‖ ≤ B) (i : Fin m) :
    Integrable (fun d => localStatistic Γ j w d i)
      (Measure.pi fun _ : Fin m => Γ.userLaw) := by
  apply Integrable.of_bound (measurable_localStatistic Γ j w hw i).aestronglyMeasurable B
  apply Eventually.of_forall
  intro d
  apply (norm_integral_le_integral_norm _).trans
  have hi : Integrable (fun s => if i ∈ (Γ.policy j (fun l => (d l).2.val j) s).val
      then w (d i) else 0) Γ.seedLaw :=
    integrable_weighted_membership Γ.seedLaw _
      ((Γ.policy_measurable j).comp (measurable_const.prodMk measurable_id))
      (fun _ : Seed => w (d i)) measurable_const B hB0 (fun _ => hB _) i
  have hh := integral_mono hi.norm (integrable_const B) (fun _ => by
    split <;> simp_all)
  simpa only [integral_const, probReal_univ, one_smul] using hh

theorem integrable_localPositive (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (w : UserDraw n r → ℝ) (hw : Measurable w)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, ‖w x‖ ≤ B) (i : Fin m) :
    Integrable (fun d => localPositive Γ j w d i)
      (Measure.pi fun _ : Fin m => Γ.userLaw) :=
  integrable_localPositiveStatistic Γ.userLaw Γ.seedLaw (Γ.policy j)
    (Γ.policy_measurable j) _ (measurable_coordinate j) w hw B hB0 hB i

theorem localZeroShare_nonneg (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (d : Fin m → UserDraw n r) (i : Fin m) :
    0 ≤ localZeroShare Γ j d i :=
  equalShare_nonneg _ _ (fun _ => le_max_right _ _) d i

theorem measurable_localZeroShare (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (i : Fin m) : Measurable (fun d => localZeroShare Γ j d i) :=
  measurable_equalShare _ ((measurable_coordinate j) (measurableSet_singleton _)) _
    (measurable_slotShortfall j 0) i

theorem integrable_localZeroShare (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (i : Fin m) : Integrable (fun d => localZeroShare Γ j d i)
      (Measure.pi fun _ : Fin m => Γ.userLaw) :=
  integrable_equalShare Γ.userLaw _ ((measurable_coordinate j) (measurableSet_singleton _))
    _ (measurable_slotShortfall j 0) (fun _ => le_max_right _ _) c
    (fun _ => max_le (sub_le_self _ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) i

theorem localPositive_relabel (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r) (w : UserDraw n r → ℝ)
    (e : Equiv.Perm (Fin m)) (d : Fin m → UserDraw n r) (i : Fin m) :
    localPositive Γ j w (d ∘ e.symm) (e i) = localPositive Γ j w d i :=
  localPositiveStatistic_relabel Γ.seedLaw (Γ.policy j) (Γ.policy_measurable j)
    hT _ w e d i

theorem slotShortfall_relabel (j : Fin n) (x : ℝ)
    (e : Equiv.Perm (Fin m)) (d : Fin m → UserDraw n r) :
    slotShortfall (c := c) j x (d ∘ e.symm) = slotShortfall (c := c) j x d := by
  classical
  have he : Finset.univ.filter (fun l => (d ∘ e.symm) l ∈ aboveAt j x) =
      (Finset.univ.filter (fun l => d l ∈ aboveAt j x)).map e.toEmbedding := by
    ext l
    simp
  simp only [slotShortfall, PiBinomial.count, he, Finset.card_map]

theorem localZeroShare_relabel (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (e : Equiv.Perm (Fin m)) (d : Fin m → UserDraw n r) (i : Fin m) :
    localZeroShare Γ j (d ∘ e.symm) (e i) = localZeroShare Γ j d i :=
  equalShare_relabel _ _ (fun e d => slotShortfall_relabel j 0 e d) e d i

theorem integral_localPositive_identity_average (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (w : UserDraw n r → ℝ) (hw : Measurable w) (i : Fin m) :
    (∫ d, localPositive Γ j w d i ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) =
      (∑ l : Fin m, ∫ d, localPositive Γ j w d l
        ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) / m :=
  iid_integral_eq_identity_average Γ.userLaw _
    (fun l => measurable_localPositiveStatistic Γ.seedLaw (Γ.policy j)
      (Γ.policy_measurable j) _ (measurable_coordinate j) w hw l)
    (localPositive_relabel Γ j hT w) i

theorem integral_localZeroShare_identity_average (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (i : Fin m) :
    (∫ d, localZeroShare Γ j d i ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) =
      (∑ l : Fin m, ∫ d, localZeroShare Γ j d l
        ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) / m :=
  iid_integral_eq_identity_average Γ.userLaw _ (measurable_localZeroShare Γ j)
    (localZeroShare_relabel Γ j) i

theorem zeroSlots_actual_eq (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (d : Fin m → UserDraw n r) :
    zeroSlots (fun l => (d l).2.val j) r c = slotShortfall (c := c) j 0 d := by
  rw [zeroSlots, positiveEligible_actual_eq Γ j d]
  rfl

theorem localStatistic_le_positive_add_zero (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (w : UserDraw n r → ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hw0 : ∀ x, 0 ≤ w x) (hwB : ∀ x, w x ≤ B)
    (d : Fin m → UserDraw n r) (i : Fin m) :
    localStatistic Γ j w d i ≤ localPositive Γ j w d i + B * localZeroShare Γ j d i := by
  classical
  let L : LocalList m := fun l => (d l).2.val j
  by_cases hpos : 0 < Bayes.entryBid (L i)
  · have he : localStatistic Γ j w d i = localPositive Γ j w d i := by
      change 0 < Bayes.entryBid ((d i).2.val j) at hpos
      unfold localStatistic localPositive localPositiveStatistic positiveSelection
      simp only [Finset.mem_filter, hpos, and_true]
    rw [he]
    exact le_add_of_nonneg_right (mul_nonneg hB0 (localZeroShare_nonneg Γ j d i))
  · cases hi : L i with
    | none =>
      have hno (s : Seed) : i ∉ (Γ.policy j L s).val :=
        fun h => (Γ.policy j L s).property.2 i h hi
      have he : localStatistic Γ j w d i = 0 := by simp [localStatistic, L, hno]
      have hp : 0 ≤ localPositive Γ j w d i := integral_nonneg fun _ => by
        split <;> simp_all
      rw [he]
      exact add_nonneg hp (mul_nonneg hB0 (localZeroShare_nonneg Γ j d i))
    | some b =>
      have hb0 : 0 ≤ b := Γ.reserve_nonneg.trans ((d i).2.property j b hi)
      have hb : b = 0 := le_antisymm (by simpa [hi, Bayes.entryBid] using le_of_not_gt hpos) hb0
      subst b
      have he' : (∫ s, if i ∈ (Γ.policy j L s).val then (1 : ℝ) else 0 ∂Γ.seedLaw) =
          Γ.seedLaw.real {s | i ∈ (Γ.policy j L s).val} :=
        integral_policy_membership Γ.seedLaw (Γ.policy j) (Γ.policy_measurable j) L i
      have he : localStatistic Γ j w d i =
          w (d i) * Γ.seedLaw.real {s | i ∈ (Γ.policy j L s).val} := by
        unfold localStatistic
        rw [← he', ← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun s => by simp only [mul_ite, mul_one, mul_zero]; rfl
      have hz : localZeroShare Γ j d i = zeroSlots L r c / (zeroEligible L).card := by
        have hi' : (d i).2.val j = some 0 := hi
        unfold localZeroShare equalShare
        simp only [Set.mem_setOf_eq]
        rw [if_pos hi', ← zeroSlots_actual_eq Γ j d]
        rfl
      have hp : localPositive Γ j w d i = 0 := by
        simp [localPositive, localPositiveStatistic, positiveSelection, L, hi, Bayes.entryBid]
      rw [he, hp, zero_add, hz]
      exact (mul_le_mul_of_nonneg_left
        (zero_marginal_le_shortfall Γ.seedLaw (Γ.policy j) (Γ.policy_measurable j) hT L i hi)
        (hw0 _)).trans (mul_le_mul_of_nonneg_right (hwB _)
          (div_nonneg (zeroSlots_nonneg L) (Nat.cast_nonneg _)))

theorem localPositive_le_statistic (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (w : UserDraw n r → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (d : Fin m → UserDraw n r) (i : Fin m) :
    localPositive Γ j w d i ≤ localStatistic Γ j w d i := by
  classical
  have hm (L : LocalList m) : Measurable (fun s => (Γ.policy j L s).val) :=
    (Γ.policy_measurable j).comp (measurable_const.prodMk measurable_id)
  have hp : Integrable (fun s => if i ∈ positiveSelection (fun l => (d l).2.val j)
      (Γ.policy j (fun l => (d l).2.val j) s).val then w (d i) else 0) Γ.seedLaw :=
    integrable_weighted_membership Γ.seedLaw _
      ((measurable_positiveSelection_policy (Γ.policy j) (Γ.policy_measurable j)).comp
        (measurable_const.prodMk measurable_id)) (fun _ => w (d i)) measurable_const
      |w (d i)| (abs_nonneg _) (fun _ => by rw [Real.norm_eq_abs]) i
  have hf : Integrable (fun s => if i ∈ (Γ.policy j (fun l => (d l).2.val j) s).val
      then w (d i) else 0) Γ.seedLaw :=
    integrable_weighted_membership Γ.seedLaw _ (hm _)
      (fun _ => w (d i)) measurable_const |w (d i)| (abs_nonneg _)
      (fun _ => by rw [Real.norm_eq_abs]) i
  apply integral_mono hp hf
  intro s
  by_cases hi : i ∈ (Γ.policy j (fun l => (d l).2.val j) s).val
  · simp only [positiveSelection, Finset.mem_filter, hi, true_and, if_true]
    split <;> simp_all
  · simp [positiveSelection, hi]

theorem integral_statistic_eq_actual (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (w : UserDraw n r → ℝ) (hw : Measurable w)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, ‖w x‖ ≤ B) (i : Fin m) :
    (∫ d, localStatistic Γ j w d i ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) =
      ∫ ω, if i ∈ playedAllocation Γ j ω then w (ω.1 i) else 0 ∂Γ.sampleLaw := by
  symm
  exact integral_coordinate_seed (Measure.pi fun _ : Fin m => Γ.userLaw) Γ.seedLaw j
    _ (measurable_localStatistic_integrand Γ j w hw i) B
    (fun p => by split <;> simp_all)

theorem integral_positive_eq_actual (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (w : UserDraw n r → ℝ) (hw : Measurable w)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, ‖w x‖ ≤ B) (i : Fin m) :
    (∫ d, localPositive Γ j w d i ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) =
      ∫ ω, if i ∈ positivePlayedAllocation Γ j ω then w (ω.1 i) else 0 ∂Γ.sampleLaw := by
  classical
  have hL : Measurable (fun p : (Fin m → UserDraw n r) × Seed =>
      fun l => (p.1 l).2.val j) :=
    measurable_pi_lambda _ fun l => (measurable_coordinate j).comp
      ((measurable_pi_apply l).comp measurable_fst)
  have hm := measurable_weighted_membership _
    ((measurable_positiveSelection_policy (Γ.policy j) (Γ.policy_measurable j)).comp
      (hL.prodMk measurable_snd)) _
    (hw.comp ((measurable_pi_apply i).comp measurable_fst)) i
  symm
  exact integral_coordinate_seed (Measure.pi fun _ : Fin m => Γ.userLaw) Γ.seedLaw j
    _ hm B (fun p => by split <;> simp_all)

theorem sum_integral_positive_eq_card (Γ : FiniteGame m n c r Seed) (j : Fin n) :
    (∑ i, ∫ d, localPositive Γ j (fun _ => 1) d i
      ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) =
      ∫ ω, ((positivePlayedAllocation Γ j ω).card : ℝ) ∂Γ.sampleLaw := by
  classical
  simp_rw [integral_positive_eq_actual Γ j (fun _ => 1) measurable_const 1 (by norm_num)
    (fun _ => by norm_num)]
  rw [← integral_finsetSum _ (fun i _ =>
    integrable_weighted_membership Γ.sampleLaw _ (measurable_positivePlayedAllocation Γ j)
      (fun _ => 1) measurable_const 1 (by norm_num) (fun _ => by norm_num) i)]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => Game.sum_membership_real _

theorem sum_localPositive_one (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (d : Fin m → UserDraw n r) :
    (∑ i, localPositive Γ j (fun _ => 1) d i) =
      (min c (positiveEligible (fun l => (d l).2.val j) r).card : ℝ) := by
  classical
  let L : LocalList m := fun l => (d l).2.val j
  have hS : Measurable (fun s => positiveSelection L (Γ.policy j L s).val) :=
    (measurable_positiveSelection_policy (Γ.policy j) (Γ.policy_measurable j)).comp
      (measurable_const.prodMk measurable_id)
  unfold localPositive localPositiveStatistic
  rw [← integral_finsetSum _ (fun i _ => integrable_weighted_membership Γ.seedLaw _ hS
    (fun _ => 1) measurable_const 1 (by norm_num) (fun _ => by norm_num) i)]
  have he : (fun s => ∑ i : Fin m,
      if i ∈ positiveSelection L (Γ.policy j L s).val then (1 : ℝ) else 0) =ᵐ[Γ.seedLaw]
      fun _ => (min c (positiveEligible L r).card : ℝ) := by
    filter_upwards [hT.ae_topChoice L] with s hs
    rw [Game.sum_membership_real, hs.card_eq_min, Nat.cast_min]
  rw [integral_congr_ae he]
  simp only [integral_const, probReal_univ, one_smul]
  rfl

theorem sum_localPositive_add_zeroShare_le (Γ : FiniteGame m n c r Seed) (j : Fin n)
    (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (d : Fin m → UserDraw n r) :
    (∑ i, (localPositive Γ j (fun _ => 1) d i + localZeroShare Γ j d i)) ≤ c := by
  rw [Finset.sum_add_distrib, sum_localPositive_one Γ j hT d]
  have hz := sum_equalShare_le {x : UserDraw n r | x.2.val j = some 0}
    (slotShortfall (c := c) j 0) (fun _ => le_max_right _ _) d
  change (∑ i, localZeroShare Γ j d i) ≤ slotShortfall (c := c) j 0 d at hz
  rw [← zeroSlots_actual_eq Γ j d] at hz
  have he := positive_card_add_zeroSlots (c := c) (r := r) (fun l => (d l).2.val j)
  linarith

theorem integral_localStatistic_one_le_capacity (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r) (i : Fin m) :
    (∫ d, localStatistic Γ j (fun _ => 1) d i
      ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) ≤ (c : ℝ) / m := by
  have hp (l : Fin m) := integrable_localPositive Γ j (fun _ => 1) measurable_const
    1 (by norm_num) (fun _ => by norm_num) l
  have hz (l : Fin m) := integrable_localZeroShare Γ j l
  have hEach (l : Fin m) : Integrable
      (fun d => localPositive Γ j (fun _ => 1) d l + localZeroShare Γ j d l)
      (Measure.pi fun _ : Fin m => Γ.userLaw) := (hp l).add (hz l)
  have hsum : Integrable (fun d => ∑ l : Fin m,
      (localPositive Γ j (fun _ => 1) d l + localZeroShare Γ j d l))
      (Measure.pi fun _ : Fin m => Γ.userLaw) :=
    integrable_finsetSum Finset.univ (fun l _ => hEach l)
  have hi := integrable_localStatistic Γ j (fun _ => 1) measurable_const
    1 (by norm_num) (fun _ => by norm_num) i
  have hAdd : Integrable (fun d => localPositive Γ j (fun _ => 1) d i + localZeroShare Γ j d i)
      (Measure.pi fun _ : Fin m => Γ.userLaw) := (hp i).add (hz i)
  have hle := integral_mono hi hAdd (fun d => by
    simpa only [one_mul] using localStatistic_le_positive_add_zero Γ j hT
      (fun _ => 1) 1 (by norm_num) (fun _ => by norm_num) (fun _ => le_rfl) d i)
  rw [integral_add (hp i) (hz i)] at hle
  have he : (∫ d, localPositive Γ j (fun _ => 1) d i
      ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) +
      (∫ d, localZeroShare Γ j d i ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) =
      (∫ d, ∑ l : Fin m, (localPositive Γ j (fun _ => 1) d l + localZeroShare Γ j d l)
        ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) / m := by
    rw [integral_localPositive_identity_average Γ j hT _ measurable_const i,
      integral_localZeroShare_identity_average Γ j i,
      integral_finsetSum _ (fun l _ => hEach l)]
    simp_rw [integral_add (hp _) (hz _)]
    rw [Finset.sum_add_distrib, add_div]
  rw [he] at hle
  have hbound := integral_mono hsum (integrable_const (c : ℝ))
    (sum_localPositive_add_zeroShare_le Γ j hT)
  have hbound' : (∫ d, ∑ l : Fin m,
      (localPositive Γ j (fun _ => 1) d l + localZeroShare Γ j d l)
      ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) ≤ c := by simpa using hbound
  exact hle.trans (div_le_div_of_nonneg_right hbound' (Nat.cast_nonneg m))

theorem integral_localZeroShare_le_shortfall (Γ : FiniteGame m n c r Seed)
    (j : Fin n) (i : Fin m) :
    (∫ d, localZeroShare Γ j d i ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) ≤
      (∫ d, slotShortfall (c := c) j 0 d
        ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) / m := by
  rw [integral_localZeroShare_identity_average Γ j i,
    ← integral_finsetSum _ (fun l _ => integrable_localZeroShare Γ j l)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply integral_mono (integrable_finsetSum _ (fun l _ => integrable_localZeroShare Γ j l))
    (integrable_slotShortfall Γ j 0)
  intro d
  exact sum_equalShare_le _ _ (fun _ => le_max_right _ _) d

theorem localZeroShare_eq_zero_of_reserve_pos (Γ : FiniteGame m n c r Seed)
    (hr : 0 < r) (j : Fin n) (d : Fin m → UserDraw n r) (i : Fin m) :
    localZeroShare Γ j d i = 0 := by
  classical
  have hi : (d i).2.val j ≠ some 0 := fun h => (not_le_of_gt hr) ((d i).2.property j 0 h)
  simp [localZeroShare, equalShare, hi]

end FCAppendix.CommonReserve
