import FCAppendix.Affine.Tail04.FlagActivationMoments

noncomputable section
namespace FCAppendix.Affine.Tail04.WeightedFlagBound
open Set
open scoped BigOperators
variable {ι Ω Ξ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Ξ]

theorem expect_product_group (mu : ι → FiniteLaw Ω) (nu : ι → FiniteLaw Ξ)
    (f : (ι → Ω) → (ι → Ξ) → ℝ) :
    (BidDependentFlags.product (fun i => (mu i).prod (nu i))).expect
      (fun omega => f (fun i => (omega i).1) (fun i => (omega i).2)) =
      (BidDependentFlags.product mu).expect
        (fun x => (BidDependentFlags.product nu).expect (f x)) := by
  have he := congrArg (fun law => law.expect (fun z => f z.1 z.2))
    (BidDependentFlags.product_group mu nu)
  simpa only [FiniteLaw.expect_map, FiniteLaw.expect_prod] using he

theorem finite_expect_swap (mu : FiniteLaw Ω) (nu : FiniteLaw Ξ) (f : Ω → Ξ → ℝ) :
    mu.expect (fun x => nu.expect (f x)) =
      nu.expect (fun y => mu.expect (fun x => f x y)) := by
  unfold FiniteLaw.expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

def remainderFlags (epsilon : ℝ) (p : ι → ℝ)
    (heps : 0 < epsilon) (heps' : epsilon < 1/2)
    (hp : ∀ i, epsilon ≤ p i) (hp' : ∀ i, p i ≤ 1-epsilon) : FiniteLaw (ι → Bool) :=
  BidDependentFlags.flags (fun i => BidDependentFlags.remainderProbability epsilon (p i))
    (fun i => (BidDependentFlags.remainderProbability_mem epsilon (p i)
      heps heps' (hp i) (hp' i)).1)
    (fun i => (BidDependentFlags.remainderProbability_mem epsilon (p i)
      heps heps' (hp i) (hp' i)).2)

theorem flags_thinning_expect (epsilon : ℝ) (p : ι → ℝ)
    (heps : 0 < epsilon) (heps' : epsilon < 1/2)
    (hp : ∀ i, epsilon ≤ p i) (hp' : ∀ i, p i ≤ 1-epsilon)
    (f : (ι → Bool) → ℝ) :
    (BidDependentFlags.flags p (fun i => by linarith [hp i])
      (fun i => by linarith [hp' i])).expect f =
      (constantFlags (ι:=ι) (2*epsilon) (by positivity) (by linarith)).expect
        (fun activation => (remainderFlags epsilon p heps heps' hp hp').expect
          (fun remainder => (fairFlags ι).expect
            (fun fair => f (fun i => if activation i then fair i else remainder i)))) := by
  rw [← BidDependentFlags.fair_product_thinning epsilon p heps heps' hp hp',
    FiniteLaw.expect_map]
  let activationLaw := fun _ : ι =>
    IndependentCounts.bernoulli (2*epsilon) (by positivity) (by linarith)
  let fairLaw := fun _ : ι =>
    IndependentCounts.bernoulli (1/2) (by norm_num) (by norm_num)
  let remainderLaw := fun i : ι =>
    IndependentCounts.bernoulli (BidDependentFlags.remainderProbability epsilon (p i))
      (BidDependentFlags.remainderProbability_mem epsilon (p i) heps heps' (hp i) (hp' i)).1
      (BidDependentFlags.remainderProbability_mem epsilon (p i) heps heps' (hp i) (hp' i)).2
  change (BidDependentFlags.product (fun i =>
    (activationLaw i).prod ((fairLaw i).prod (remainderLaw i)))).expect
      (fun omega => f (fun i => if (omega i).1 then (omega i).2.1 else (omega i).2.2)) = _
  rw [expect_product_group activationLaw (fun i => (fairLaw i).prod (remainderLaw i))
    (fun activation rest => f (fun i => if activation i then (rest i).1 else (rest i).2))]
  apply FiniteLaw.expect_congr
  intro activation
  rw [expect_product_group fairLaw remainderLaw
    (fun fair remainder => f (fun i => if activation i then fair i else remainder i)), finite_expect_swap]
  rfl

def inactiveOffset (w : ι → ℝ) (activation remainder : ι → Bool) : ℝ :=
  ∑ i : {i // activation i ≠ true}, w i * bit (remainder i)

omit [DecidableEq ι] in
theorem weighted_thinning_decomposition (w : ι → ℝ)
    (activation remainder fair : ι → Bool) :
    weightedSum w (fun i => if activation i then fair i else remainder i) =
      weightedSum (fun i : {i // activation i = true} => w i) (fun i => fair i) +
        inactiveOffset w activation remainder := by
  unfold weightedSum inactiveOffset
  rw [← Fintype.sum_subtype_add_sum_subtype (p := fun i => activation i = true)
    (fun i => w i * bit (if activation i then fair i else remainder i))]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [i.property, ite_true]
  · apply Finset.sum_congr rfl
    intro i _
    have hi : activation i = false := by
      cases h : activation i
      · rfl
      · exact (i.property h).elim
    simp only [hi,Bool.false_eq_true,ite_false]

omit [DecidableEq ι] in
theorem activationCount_eq_card (activation : ι → Bool) :
    activationCount activation = (Fintype.card {i // activation i = true} : ℝ) := by
  classical
  simp only [activationCount, Fintype.card_subtype, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro i _
  cases activation i <;> simp [bit]

theorem thinned_fair_interval (w : ι → ℝ) {a : ℝ} (l : ℝ) (r : ℕ)
    (ha : 0 < a) (hw : ∀ i, a ≤ |w i|) (activation remainder : ι → Bool) :
    (fairFlags ι).prob (fun fair =>
      weightedSum w (fun i => if activation i then fair i else remainder i) ∈
        Ico l (l+(r:ℝ)*a)) ≤
      (r:ℝ)*Real.sqrt (2/(activationCount activation+1)) := by
  let active := fun i => activation i = true
  let shifted := l-inactiveOffset w activation remainder
  have hlaw : (fairFlags ι).map (fun fair (i : {i // active i}) => fair i) =
      fairFlags {i // active i} := by
    exact BidDependentFlags.product_restrict
      (fun _ : ι => IndependentCounts.bernoulli (1/2) (by norm_num) (by norm_num)) active
  have heq : (fairFlags ι).prob (fun fair =>
      weightedSum w (fun i => if activation i then fair i else remainder i) ∈
        Ico l (l+(r:ℝ)*a)) =
      (fairFlags {i // active i}).prob (fun fair =>
        weightedSum (fun i : {i // active i} => w i) fair ∈
          Ico shifted (shifted+(r:ℝ)*a)) := by
    rw [← hlaw, FiniteLaw.prob_eq_expect, FiniteLaw.prob_eq_expect, FiniteLaw.expect_map]
    apply FiniteLaw.expect_congr
    intro fair
    congr 1
    rw [weighted_thinning_decomposition]
    simp only [Set.mem_Ico, shifted]
    apply propext
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [heq, activationCount_eq_card]
  exact fair_signed_interval (fun i : {i // active i} => w i) shifted r ha (fun i => hw i)

theorem bernoulli_weighted_interval (epsilon : ℝ) (p w : ι → ℝ)
    (heps : 0 < epsilon) (heps' : epsilon < 1/2)
    (hp : ∀ i, epsilon ≤ p i) (hp' : ∀ i, p i ≤ 1-epsilon)
    (hN : 0 < Fintype.card ι) {a : ℝ} (ha : 0 < a)
    (hw : ∀ i, a ≤ |w i|) (l : ℝ) (r : ℕ) :
    (BidDependentFlags.flags p (fun i => by linarith [hp i])
      (fun i => by linarith [hp' i])).prob
        (fun flags => weightedSum w flags ∈ Ico l (l+(r:ℝ)*a)) ≤
      2/(epsilon*(Fintype.card ι : ℝ)) +
        (r:ℝ)*Real.sqrt (2/(epsilon*(Fintype.card ι : ℝ)+1)) := by
  classical
  let activationLaw := constantFlags (ι:=ι) (2*epsilon) (by positivity) (by linarith)
  let remLaw := remainderFlags epsilon p heps heps' hp hp'
  let C := (r:ℝ)*Real.sqrt (2/(epsilon*(Fintype.card ι : ℝ)+1))
  have hC : 0 ≤ C := by positivity
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hN
  have hbound (activation remainder : ι → Bool) :
      (fairFlags ι).prob (fun fair =>
        weightedSum w (fun i => if activation i then fair i else remainder i) ∈
          Ico l (l+(r:ℝ)*a)) ≤
        (if activationCount activation < epsilon*(Fintype.card ι : ℝ) then 1 else 0)+C := by
    by_cases hbad : activationCount activation < epsilon*(Fintype.card ι : ℝ)
    · have hh := (fairFlags ι).prob_le_one (fun fair =>
        weightedSum w (fun i => if activation i then fair i else remainder i) ∈
          Ico l (l+(r:ℝ)*a))
      simpa only [if_pos hbad] using hh.trans (by linarith : (1:ℝ) ≤ 1+C)
    · have hgood : epsilon*(Fintype.card ι : ℝ) ≤ activationCount activation :=
        le_of_not_gt hbad
      have hden : 0 < epsilon*(Fintype.card ι : ℝ)+1 := by positivity
      have hden' : 0 < activationCount activation+1 := by linarith
      have hratio : 2/(activationCount activation+1) ≤
          2/(epsilon*(Fintype.card ι : ℝ)+1) := by
        apply (div_le_div_iff₀ hden' hden).mpr
        nlinarith
      have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio) (Nat.cast_nonneg r)
      have hh := thinned_fair_interval w l r ha hw activation remainder
      simpa only [if_neg hbad, zero_add] using hh.trans hs
  rw [FiniteLaw.prob_eq_expect, flags_thinning_expect epsilon p heps heps' hp hp']
  change activationLaw.expect (fun activation => remLaw.expect (fun remainder =>
    (fairFlags ι).expect (fun fair => if
      weightedSum w (fun i => if activation i then fair i else remainder i) ∈
        Ico l (l+(r:ℝ)*a) then 1 else 0))) ≤ _
  calc
    _ ≤ activationLaw.expect (fun activation =>
        (if activationCount activation < epsilon*(Fintype.card ι : ℝ) then 1 else 0)+C) := by
      apply FiniteLaw.expect_mono
      intro activation
      apply FiniteLaw.expect_le_const
      intro remainder
      simpa only [FiniteLaw.prob_eq_expect] using hbound activation remainder
    _ = activationLaw.prob
        (fun activation => activationCount activation < epsilon*(Fintype.card ι : ℝ))+C := by
      rw [FiniteLaw.expect_add, FiniteLaw.expect_const]
      rfl
    _ ≤ _ := by
      have ht := activation_lower_tail heps heps' hN
      change activationLaw.prob (fun flags => activationCount flags < epsilon*(Fintype.card ι : ℝ)) ≤
        2/(epsilon*(Fintype.card ι : ℝ)) at ht
      change _ ≤ 2/(epsilon*(Fintype.card ι : ℝ))+C
      linarith

end FCAppendix.Affine.Tail04.WeightedFlagBound
