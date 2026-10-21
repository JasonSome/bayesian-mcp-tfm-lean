import FCAppendix.Affine.Uniform06.WeightedMoments
import FCAppendix.Affine.Uniform06.EntryUntilting

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryRenewal
open Set
open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.WeightedMoments
open FCAppendix.Affine.Uniform06.EntryUntilting
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def potential (k : ℕ) (s : ℝ) : ℝ := (max s 0)^(k+1)/((k : ℝ)+1)

lemma potential_nonneg (k : ℕ) (s : ℝ) : 0 ≤ potential k s := by
  unfold potential
  positivity

lemma potential_zero {s : ℝ} (hs : s ≤ 0) (k : ℕ) : potential k s=0 := by
  simp [potential,max_eq_right hs]

lemma potential_mono (k : ℕ) : Monotone (potential k) := by
  intro x y hxy
  unfold potential
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right _ hxy) (k+1)) (by positivity)

lemma deficitMoment_mono (k : ℕ) : Monotone (deficitMoment k) := by
  intro x y hxy
  by_cases hk : k=0
  · subst k
    simp only [deficitMoment_zero]
    split_ifs with hx hy <;> try norm_num
    exact (hy (hx.trans_le hxy)).elim
  · simp only [deficitMoment,if_neg hk]
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right _ hxy) k

lemma potential_increment_upper {k : ℕ} (hk : k ≤ 2) {s t : ℝ} (ht : 0 ≤ t) :
    potential k s-potential k (s-t) ≤ t*deficitMoment k s := by
  by_cases hs : s ≤ 0
  · have hst : s-t ≤ 0 := by linarith
    rw [potential_zero hs,potential_zero hst]
    simpa only [sub_self] using mul_nonneg ht (deficitMoment_nonneg k s)
  · have hs0 : 0 < s := lt_of_not_ge hs
    by_cases hst : s-t ≤ 0
    · rw [potential_zero hst,sub_zero]
      interval_cases k <;> simp only [potential,deficitMoment,if_true,if_neg (by decide : ¬1=0),
        if_neg (by decide : ¬2=0),if_pos hs0,max_eq_left hs0.le,Nat.cast_zero,Nat.cast_one,
        Nat.cast_ofNat,pow_one,pow_zero,zero_add,div_one]
      · linarith
      · nlinarith [mul_nonneg hs0.le (show 0 ≤ t-s by linarith)]
      · nlinarith [mul_nonneg (sq_nonneg s) (show 0 ≤ t-s by linarith),
          mul_nonneg (sq_nonneg s) hs0.le]
    · have hst0 : 0 < s-t := lt_of_not_ge hst
      interval_cases k <;> simp only [potential,deficitMoment,if_true,if_neg (by decide : ¬1=0),
        if_neg (by decide : ¬2=0),if_pos hs0,max_eq_left hs0.le,max_eq_left hst0.le,
        Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,pow_one,pow_zero,zero_add,div_one]
      · ring_nf
        exact le_rfl
      · nlinarith [sq_nonneg t]
      · nlinarith [mul_nonneg (sq_nonneg t) hst0.le,mul_nonneg (sq_nonneg t) ht]

lemma potential_increment_lower {k : ℕ} (hk : k ≤ 2) {s t : ℝ} (ht : 0 ≤ t) :
    t*deficitMoment k (s-t) ≤ potential k s-potential k (s-t) := by
  by_cases hst : s-t ≤ 0
  · have hm : deficitMoment k (s-t)=0 := by
      by_cases hk0 : k=0
      · simp [deficitMoment,hk0,not_lt.mpr hst]
      · simp [deficitMoment,max_eq_right hst,hk0]
    rw [hm,mul_zero,potential_zero hst,sub_zero]
    exact potential_nonneg _ _
  · have hst0 : 0 < s-t := lt_of_not_ge hst
    have hs0 : 0 < s := by linarith
    interval_cases k <;> simp only [potential,deficitMoment,if_true,if_neg (by decide : ¬1=0),
      if_neg (by decide : ¬2=0),if_pos hst0,max_eq_left hs0.le,max_eq_left hst0.le,
      Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,pow_one,pow_zero,zero_add,div_one]
    · ring_nf
      exact le_rfl
    · nlinarith [sq_nonneg t]
    · nlinarith [mul_nonneg (sq_nonneg t) hst0.le,mul_nonneg (sq_nonneg t) ht]

lemma shifted_potential_increment_lower {k : ℕ} (hk : k ≤ 2) {s t B : ℝ}
    (ht : 0 ≤ t) (htB : t ≤ B) :
    t*deficitMoment k s ≤ potential k (s+B)-potential k (s+B-t) := by
  apply (mul_le_mul_of_nonneg_left (deficitMoment_mono k (by linarith : s ≤ s+B-t)) ht).trans
  exact potential_increment_lower hk ht

def blockLaw (w : Weights ι) (S : Finset ι) : FiniteLaw (ι × ι) :=
  pairLaw (oneDraw w S) (fun i => oneDraw w (insert i S))

def blockSet (S : Finset ι) (p : ι × ι) : Finset ι := insert p.2 (insert p.1 S)
def blockSum (h : ι → ℝ) (p : ι × ι) : ℝ := h p.1+h p.2

omit [Fintype ι] [Nonempty ι] in
lemma blockSet_card_le (S : Finset ι) (p : ι × ι) :
    (blockSet S p).card ≤ S.card+2 := by
  unfold blockSet
  have h1 := Finset.card_insert_le p.1 S
  have h2 := Finset.card_insert_le p.2 (insert p.1 S)
  omega

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma blockSum_bounds (h : ι → ℝ) {a A : ℝ} (hh : ∀ i, h i ∈ Icc a A) (p : ι × ι) :
    blockSum h p ∈ Icc (2*a) (2*A) := by
  dsimp [blockSum]
  constructor <;> linarith [(hh p.1).1,(hh p.1).2,(hh p.2).1,(hh p.2).2]

lemma blockMean_drift (w : Weights ι) (h : ι → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hh : ∀ i, |h i| ≤ A) (K : ℕ) (S : Finset ι)
    (hW : 0 < totalWeight w) (hhalf : 2*(K : ℝ) ≤ totalWeight w)
    (hS : S.card+1 ≤ K) :
    |(blockLaw w S).expect (blockSum h)-2*weightedMean w h| ≤ 8*A*K/totalWeight w := by
  have he : (blockLaw w S).expect (blockSum h)=nextMean w h S+
      (oneDraw w S).expect (fun i => nextMean w h (insert i S)) := by
    rw [blockLaw,expect_pairLaw]
    simp only [blockSum,expect_add,expect_const]
    rfl
  have hfirst := nextMean_drift_bound w h hA hh K S hW hhalf (by omega)
  have hsecond : |(oneDraw w S).expect (fun i => nextMean w h (insert i S))-weightedMean w h| ≤
      4*A*K/totalWeight w := by
    rw [← expect_const (oneDraw w S) (weightedMean w h),← expect_sub]
    apply (abs_expect_le _ _).trans
    apply expect_le_const
    intro i _
    apply nextMean_drift_bound w h hA hh K (insert i S) hW hhalf
    exact (Finset.card_insert_le i S).trans hS
  rw [he]
  have htri := abs_add_le (nextMean w h S-weightedMean w h)
    ((oneDraw w S).expect (fun i => nextMean w h (insert i S))-weightedMean w h)
  have heq : nextMean w h S+(oneDraw w S).expect (fun i => nextMean w h (insert i S))-
      2*weightedMean w h=(nextMean w h S-weightedMean w h)+
        ((oneDraw w S).expect (fun i => nextMean w h (insert i S))-weightedMean w h) := by ring
  rw [heq]
  have hfac : 8*A*K/totalWeight w = 2*(4*A*K/totalWeight w) := by ring
  rw [hfac]
  linarith

def terminal (w : Weights ι) (h : ι → ℝ) (F : ℝ → ℝ) : ℕ → Finset ι → ℝ → ℝ
  | 0, _, s => F s
  | n+1, S, s => (blockLaw w S).expect (fun p => terminal w h F n (blockSet S p) (s-blockSum h p))

def occupation (w : Weights ι) (h : ι → ℝ) (k : ℕ) : ℕ → Finset ι → ℝ → ℝ
  | 0, _, _ => 0
  | n+1, S, s => deficitMoment k s+
      (blockLaw w S).expect (fun p => occupation w h k n (blockSet S p) (s-blockSum h p))

lemma terminal_nonneg (w : Weights ι) (h : ι → ℝ) {F : ℝ → ℝ} (hF : ∀ s, 0 ≤ F s)
    (n : ℕ) (S : Finset ι) (s : ℝ) : 0 ≤ terminal w h F n S s := by
  induction n generalizing S s with
  | zero => exact hF s
  | succ n ih => exact expect_nonneg _ _ fun p => ih _ _

lemma occupation_nonneg (w : Weights ι) (h : ι → ℝ) (k n : ℕ) (S : Finset ι) (s : ℝ) :
    0 ≤ occupation w h k n S s := by
  induction n generalizing S s with
  | zero => exact le_refl 0
  | succ n ih => exact add_nonneg (deficitMoment_nonneg k s) (expect_nonneg _ _ fun p => ih _ _)

lemma terminal_potential_zero (w : Weights ι) (h : ι → ℝ) {a : ℝ}
    (hh : ∀ i, a ≤ h i) (k n : ℕ) (S : Finset ι) {s : ℝ}
    (hs : s ≤ 2*a*n) : terminal w h (potential k) n S s=0 := by
  induction n generalizing S s with
  | zero => simpa [terminal] using potential_zero (k := k) (by simpa using hs)
  | succ n ih =>
    unfold terminal
    have he : (fun p : ι × ι => terminal w h (potential k) n (blockSet S p) (s-blockSum h p))=
        fun _ => 0 := by
      funext p
      apply ih
      have hstep : 2*a ≤ blockSum h p := by dsimp [blockSum]; linarith [hh p.1,hh p.2]
      push_cast at hs
      linarith
    rw [he,expect_const]

theorem potential_minus_terminal_le (w : Weights ι) (h : ι → ℝ)
    {a A δ : ℝ} (ha : 0 ≤ a) (hh : ∀ i, h i ∈ Icc a A)
    {k K : ℕ} (hk : k ≤ 2)
    (hmean : ∀ S : Finset ι, S.card+1 ≤ K →
      (blockLaw w S).expect (blockSum h) ≤ 2*(weightedMean w h+δ))
    (n : ℕ) (S : Finset ι) (hS : S.card+2*n ≤ K) (s : ℝ) :
    potential k s-terminal w h (potential k) n S s ≤
      2*(weightedMean w h+δ)*occupation w h k n S s := by
  induction n generalizing S s with
  | zero => simp [terminal,occupation]
  | succ n ih =>
    have hstep : potential k s-(blockLaw w S).expect (fun p => potential k (s-blockSum h p)) ≤
        2*(weightedMean w h+δ)*deficitMoment k s := by
      have hp := expect_le_of_support (blockLaw w S)
        (fun p => potential k s-potential k (s-blockSum h p))
        (fun p => blockSum h p*deficitMoment k s) (fun p _ =>
          potential_increment_upper hk ((mul_nonneg (by norm_num) ha).trans (blockSum_bounds h hh p).1))
      rw [expect_sub,expect_const,expect_mul_const] at hp
      exact hp.trans (mul_le_mul_of_nonneg_right (hmean S (by omega)) (deficitMoment_nonneg k s))
    have htail := expect_le_of_support (blockLaw w S)
      (fun p => potential k (s-blockSum h p)-terminal w h (potential k) n (blockSet S p) (s-blockSum h p))
      (fun p => 2*(weightedMean w h+δ)*occupation w h k n (blockSet S p) (s-blockSum h p))
      (fun p _ => ih (blockSet S p) (by have hc := blockSet_card_le S p; omega) _)
    rw [expect_sub,expect_const_mul] at htail
    simp only [terminal,occupation]
    nlinarith

theorem occupation_le_shifted_potential (w : Weights ι) (h : ι → ℝ)
    {a A δ : ℝ} (ha : 0 ≤ a) (hh : ∀ i, h i ∈ Icc a A)
    {k K : ℕ} (hk : k ≤ 2)
    (hmean : ∀ S : Finset ι, S.card+1 ≤ K →
      2*(weightedMean w h-δ) ≤ (blockLaw w S).expect (blockSum h))
    (n : ℕ) (S : Finset ι) (hS : S.card+2*n ≤ K) (s : ℝ) :
    2*(weightedMean w h-δ)*occupation w h k n S s ≤
      potential k (s+2*A)-terminal w h (fun t => potential k (t+2*A)) n S s := by
  induction n generalizing S s with
  | zero => simp [terminal,occupation]
  | succ n ih =>
    have hstep : 2*(weightedMean w h-δ)*deficitMoment k s ≤
        potential k (s+2*A)-(blockLaw w S).expect (fun p => potential k (s-blockSum h p+2*A)) := by
      have hp := expect_le_of_support (blockLaw w S)
        (fun p => blockSum h p*deficitMoment k s)
        (fun p => potential k (s+2*A)-potential k (s-blockSum h p+2*A)) (fun p _ => by
          have ht := blockSum_bounds h hh p
          simpa only [sub_add_eq_add_sub] using shifted_potential_increment_lower (s := s) hk
            ((mul_nonneg (by norm_num) ha).trans ht.1) ht.2)
      rw [expect_sub,expect_const,expect_mul_const] at hp
      exact (mul_le_mul_of_nonneg_right (hmean S (by omega)) (deficitMoment_nonneg k s)).trans hp
    have htail := expect_le_of_support (blockLaw w S)
      (fun p => 2*(weightedMean w h-δ)*occupation w h k n (blockSet S p) (s-blockSum h p))
      (fun p => potential k (s-blockSum h p+2*A)-
        terminal w h (fun t => potential k (t+2*A)) n (blockSet S p) (s-blockSum h p))
      (fun p _ => ih (blockSet S p) (by have hc := blockSet_card_le S p; omega) _)
    rw [expect_sub,expect_const_mul] at htail
    simp only [terminal,occupation]
    nlinarith

theorem actual_occupation_bounds (w : Weights ι) (h : ι → ℝ)
    {a A : ℝ} (ha : 0 < a) (hh : ∀ i, h i ∈ Icc a A)
    {k K n : ℕ} (hk : k ≤ 2) (hKn : 2*n ≤ K)
    (hW : 0 < totalWeight w) (hhalf : 2*(K : ℝ) ≤ totalWeight w)
    {s : ℝ} (hs : s ≤ 2*a*n) :
    potential k s ≤ 2*(weightedMean w h+4*A*K/totalWeight w)*occupation w h k n ∅ s ∧
    2*(weightedMean w h-4*A*K/totalWeight w)*occupation w h k n ∅ s ≤ potential k (s+2*A) := by
  have hA : 0 ≤ A := by
    let i := Classical.choice (inferInstance : Nonempty ι)
    exact (ha.le.trans (hh i).1).trans (hh i).2
  have hhabs : ∀ i, |h i| ≤ A := fun i => by
    rw [abs_of_nonneg (ha.le.trans (hh i).1)]
    exact (hh i).2
  have hmean : ∀ S : Finset ι, S.card+1 ≤ K →
      |(blockLaw w S).expect (blockSum h)-2*weightedMean w h| ≤ 2*(4*A*K/totalWeight w) := by
    intro S hS
    convert! blockMean_drift w h hA hhabs K S hW hhalf hS using 1
    ring
  constructor
  · have ht := potential_minus_terminal_le w h (δ := 4*A*K/totalWeight w) ha.le hh hk
      (fun S hS => by have hx := (abs_le.mp (hmean S hS)).2; linarith)
      n ∅ (by simpa using hKn) s
    rw [terminal_potential_zero w h (fun i => (hh i).1) k n ∅ hs,sub_zero] at ht
    exact ht
  · have ht := occupation_le_shifted_potential w h (δ := 4*A*K/totalWeight w) ha.le hh hk
      (fun S hS => by have hx := (abs_le.mp (hmean S hS)).1; linarith)
      n ∅ (by simpa using hKn) s
    exact ht.trans (sub_le_self _ (terminal_nonneg w h (fun t => potential_nonneg k (t+2*A)) n ∅ s))

theorem actual_occupation_bounds_from (w : Weights ι) (h : ι → ℝ)
    {a A : ℝ} (ha : 0 < a) (hh : ∀ i, h i ∈ Icc a A)
    {k K n : ℕ} (hk : k ≤ 2) (S : Finset ι) (hKn : S.card+2*n ≤ K)
    (hW : 0 < totalWeight w) (hhalf : 2*(K : ℝ) ≤ totalWeight w)
    {s : ℝ} (hs : s ≤ 2*a*n) :
    potential k s ≤ 2*(weightedMean w h+4*A*K/totalWeight w)*occupation w h k n S s ∧
    2*(weightedMean w h-4*A*K/totalWeight w)*occupation w h k n S s ≤ potential k (s+2*A) := by
  have hA : 0 ≤ A := by
    let i := Classical.choice (inferInstance : Nonempty ι)
    exact (ha.le.trans (hh i).1).trans (hh i).2
  have hhabs : ∀ i, |h i| ≤ A := fun i => by
    rw [abs_of_nonneg (ha.le.trans (hh i).1)]
    exact (hh i).2
  have hmean : ∀ T : Finset ι, T.card+1 ≤ K →
      |(blockLaw w T).expect (blockSum h)-2*weightedMean w h| ≤ 2*(4*A*K/totalWeight w) := by
    intro T hT
    convert! blockMean_drift w h hA hhabs K T hW hhalf hT using 1
    ring
  constructor
  · have ht := potential_minus_terminal_le w h (δ := 4*A*K/totalWeight w) ha.le hh hk
      (fun T hT => by have hx := (abs_le.mp (hmean T hT)).2; linarith)
      n S hKn s
    rw [terminal_potential_zero w h (fun i => (hh i).1) k n S hs,sub_zero] at ht
    exact ht
  · have ht := occupation_le_shifted_potential w h (δ := 4*A*K/totalWeight w) ha.le hh hk
      (fun T hT => by have hx := (abs_le.mp (hmean T hT)).1; linarith)
      n S hKn s
    exact ht.trans (sub_le_self _ (terminal_nonneg w h (fun t => potential_nonneg k (t+2*A)) n S s))

def pathMoment (w : Weights ι) (h : ι → ℝ) (k d : ℕ) (S : Finset ι) (s : ℝ) : ℝ :=
  (pathLaw w d S).expect (fun p => deficitMoment k (s-selectedSum h d p))

lemma pathMoment_nonneg (w : Weights ι) (h : ι → ℝ) (k d : ℕ) (S : Finset ι) (s : ℝ) :
    0 ≤ pathMoment w h k d S s :=
  expect_nonneg _ _ fun _ => deficitMoment_nonneg _ _

@[simp] lemma pathMoment_zero (w : Weights ι) (h : ι → ℝ) (k : ℕ) (S : Finset ι) (s : ℝ) :
    pathMoment w h k 0 S s=deficitMoment k s := by
  simp [pathMoment,pathLaw,selectedSum]

lemma pathMoment_succ (w : Weights ι) (h : ι → ℝ) (k d : ℕ) (S : Finset ι) (s : ℝ) :
    pathMoment w h k (d+1) S s=
      (oneDraw w S).expect (fun i => pathMoment w h k d (insert i S) (s-h i)) := by
  simp only [pathMoment,expect_path_succ,selectedSum]
  congr 1
  funext i
  congr 1
  funext p
  congr 1
  ring

lemma pathMoment_two_succ (w : Weights ι) (h : ι → ℝ) (k d : ℕ) (S : Finset ι) (s : ℝ) :
    pathMoment w h k (d+2) S s=
      (blockLaw w S).expect (fun p => pathMoment w h k d (blockSet S p) (s-blockSum h p)) := by
  rw [show d+2=(d+1)+1 by omega,pathMoment_succ]
  simp_rw [pathMoment_succ]
  rw [blockLaw,expect_pairLaw]
  congr 1
  funext i
  congr 1
  funext j
  change pathMoment w h k d (insert j (insert i S)) (s-h i-h j)=
    pathMoment w h k d (insert j (insert i S)) (s-(h i+h j))
  congr 1
  ring

lemma expect_finset_sum {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (J : Finset ℕ) (f : ℕ → Ω → ℝ) :
    P.expect (fun p => ∑ j ∈ J, f j p)=∑ j ∈ J, P.expect (f j) := by
  simp only [expect_def,Finset.mul_sum]
  rw [Finset.sum_comm]

lemma occupation_eq_even_sum (w : Weights ι) (h : ι → ℝ) (k n : ℕ)
    (S : Finset ι) (s : ℝ) :
    occupation w h k n S s=∑ r ∈ Finset.range n, pathMoment w h k (2*r) S s := by
  induction n generalizing S s with
  | zero => simp [occupation]
  | succ n ih =>
    rw [occupation,Finset.sum_range_succ']
    simp only [Nat.mul_zero,pathMoment_zero]
    rw [add_comm (∑ r ∈ Finset.range n, pathMoment w h k (2*(r+1)) S s)]
    congr 1
    simp_rw [ih]
    rw [expect_finset_sum]
    apply Finset.sum_congr rfl
    intro r _
    symm
    simpa only [Nat.mul_add,Nat.mul_one] using pathMoment_two_succ w h k (2*r) S s

def parityOccupation (w : Weights ι) (h : ι → ℝ) (k n e : ℕ) (s : ℝ) : ℝ :=
  ∑ r ∈ Finset.range n, pathMoment w h k (2*r+e) ∅ s

@[simp] lemma parityOccupation_even (w : Weights ι) (h : ι → ℝ) (k n : ℕ) (s : ℝ) :
    parityOccupation w h k n 0 s=occupation w h k n ∅ s := by
  simp only [parityOccupation,add_zero,occupation_eq_even_sum]

lemma parityOccupation_odd (w : Weights ι) (h : ι → ℝ) (k n : ℕ) (s : ℝ) :
    parityOccupation w h k n 1 s=
      (oneDraw w ∅).expect (fun i => occupation w h k n {i} (s-h i)) := by
  simp only [parityOccupation,occupation_eq_even_sum]
  rw [expect_finset_sum]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [Finset.insert_empty] using pathMoment_succ w h k (2*r) ∅ s

lemma parityOccupation_nonneg (w : Weights ι) (h : ι → ℝ) (k n e : ℕ) (s : ℝ) :
    0 ≤ parityOccupation w h k n e s :=
  Finset.sum_nonneg fun _ _ => pathMoment_nonneg _ _ _ _ _ _

theorem actual_parity_occupation_bounds (w : Weights ι) (h : ι → ℝ)
    {a A : ℝ} (ha : 0 < a) (hh : ∀ i, h i ∈ Icc a A)
    {k K n e : ℕ} (hk : k ≤ 2) (he : e ≤ 1) (hKn : 2*n+1 ≤ K)
    (hW : 0 < totalWeight w) (hhalf : 2*(K : ℝ) ≤ totalWeight w)
    {s : ℝ} (hs : s ≤ 2*a*n) :
    potential k (s-A) ≤ 2*(weightedMean w h+4*A*K/totalWeight w)*parityOccupation w h k n e s ∧
    2*(weightedMean w h-4*A*K/totalWeight w)*parityOccupation w h k n e s ≤ potential k (s+2*A) := by
  have hA : 0 ≤ A := by
    let i := Classical.choice (inferInstance : Nonempty ι)
    exact (ha.le.trans (hh i).1).trans (hh i).2
  rcases (show e=0 ∨ e=1 by omega) with rfl | rfl
  · rw [parityOccupation_even]
    have hh' := actual_occupation_bounds w h ha hh hk (by omega) hW hhalf hs
    exact ⟨(potential_mono k (by linarith)).trans hh'.1,hh'.2⟩
  · rw [parityOccupation_odd]
    have hfirst (i : ι) := actual_occupation_bounds_from w h ha hh hk {i}
      (by simp only [Finset.card_singleton]; omega) hW hhalf (show s-h i ≤ 2*a*n by linarith [(hh i).1])
    constructor
    · have hlow := expect_le_of_support (oneDraw w ∅)
        (fun _ => potential k (s-A))
        (fun i => 2*(weightedMean w h+4*A*K/totalWeight w)*occupation w h k n {i} (s-h i))
        (fun i _ => (potential_mono k (by linarith [(hh i).2])).trans (hfirst i).1)
      simpa only [expect_const,expect_const_mul] using hlow
    · have hup := expect_le_of_support (oneDraw w ∅)
        (fun i => 2*(weightedMean w h-4*A*K/totalWeight w)*occupation w h k n {i} (s-h i))
        (fun _ => potential k (s+2*A))
        (fun i _ => (hfirst i).2.trans (potential_mono k (by linarith [(hh i).1])))
      simpa only [expect_const,expect_const_mul] using hup

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma selectedSum_lower (h : ι → ℝ) {a : ℝ} (hh : ∀ i, a ≤ h i)
    (d : ℕ) (p : Path ι d) : a*d ≤ selectedSum h d p := by
  induction d with
  | zero => simp [selectedSum]
  | succ d ih =>
    simp only [selectedSum,Nat.cast_add_one]
    have htail := ih p.2
    nlinarith [hh p.1]

lemma pathMoment_zero_of_stopped (w : Weights ι) (h : ι → ℝ) {a : ℝ}
    (hh : ∀ i, a ≤ h i) (k d : ℕ) (S : Finset ι) {s : ℝ} (hs : s ≤ a*d) :
    pathMoment w h k d S s=0 := by
  have hzero (p : Path ι d) : deficitMoment k (s-selectedSum h d p)=0 := by
    have hx : s-selectedSum h d p ≤ 0 := by linarith [selectedSum_lower h hh d p]
    by_cases hk : k=0
    · simp [deficitMoment,hk,not_lt.mpr hx]
    · simp [deficitMoment,max_eq_right hx,hk]
  simp only [pathMoment,hzero,expect_const]

end FCAppendix.Affine.Uniform06.EntryRenewal
