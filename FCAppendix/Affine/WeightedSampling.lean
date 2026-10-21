import FCAppendix.Affine.ClippedResidualKernel

noncomputable section
namespace FCAppendix.Affine.WeightedSampling
open Set
open scoped BigOperators

universe u v w
variable {ι : Type u} {Ω : Type v} {Ξ : Type w} [Fintype ι] [DecidableEq ι]

private def ofMass [Fintype Ω] (p : Ω → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hs : ∑ a, p a = 1) : FiniteLaw Ω := ⟨p, hp, hs⟩

lemma mass_nonneg [Fintype Ω] (P : FiniteLaw Ω) (a : Ω) : 0 ≤ P.mass a := by
  rcases P with ⟨p, hp, hs⟩
  exact hp a

lemma mass_total [Fintype Ω] (P : FiniteLaw Ω) : ∑ a, P.mass a = 1 := by
  rcases P with ⟨p, hp, hs⟩
  exact hs

lemma expect_def [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ) :
    P.expect f = ∑ a, P.mass a * f a := rfl

lemma expect_const [Fintype Ω] (P : FiniteLaw Ω) (a : ℝ) :
    P.expect (fun _ => a) = a := by
  rw [expect_def, ← Finset.sum_mul, mass_total]
  ring

lemma expect_add [Fintype Ω] (P : FiniteLaw Ω) (f g : Ω → ℝ) :
    P.expect (fun a => f a+g a) = P.expect f+P.expect g := by
  simp [expect_def, mul_add, Finset.sum_add_distrib]

lemma expect_sub [Fintype Ω] (P : FiniteLaw Ω) (f g : Ω → ℝ) :
    P.expect (fun a => f a-g a) = P.expect f-P.expect g := by
  simp [expect_def, mul_sub, Finset.sum_sub_distrib]

lemma expect_mul_const [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    P.expect (fun a => f a*c) = P.expect f*c := by
  exact P.expect_mul_const f c

lemma expect_const_mul [Fintype Ω] (P : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    P.expect (fun a => c*f a) = c*P.expect f := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using expect_mul_const P f c

lemma expect_le_of_support [Fintype Ω] (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (h : ∀ a, 0 < P.mass a → f a ≤ g a) : P.expect f ≤ P.expect g := by
  rw [expect_def, expect_def]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : 0 < P.mass a
  · exact mul_le_mul_of_nonneg_left (h a ha) (mass_nonneg P a)
  · have hz : P.mass a = 0 := le_antisymm (le_of_not_gt ha) (mass_nonneg P a)
    simp [hz]

lemma expect_nonneg [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ)
    (h : ∀ a, 0 ≤ f a) : 0 ≤ P.expect f := by
  rw [expect_def]
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (mass_nonneg P a) (h a))

lemma expect_le_const [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ) (C : ℝ)
    (h : ∀ a, 0 < P.mass a → f a ≤ C) : P.expect f ≤ C := by
  simpa [expect_const] using expect_le_of_support P f (fun _ => C) h

lemma abs_expect_le [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ) :
    |P.expect f| ≤ P.expect (fun a => |f a|) := by
  rw [expect_def, expect_def]
  calc
    |∑ a, P.mass a*f a| ≤ ∑ a, |P.mass a*f a| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, P.mass a*|f a| := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg (mass_nonneg P a)]

def pairLaw [Fintype Ω] [Fintype Ξ] (P : FiniteLaw Ω)
    (Q : Ω → FiniteLaw Ξ) : FiniteLaw (Ω × Ξ) :=
  ofMass (fun a => P.mass a.1 * (Q a.1).mass a.2)
    (fun a => mul_nonneg (mass_nonneg P _) (mass_nonneg (Q _) _)) (by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, mass_total, mul_one]
      exact mass_total P)

@[simp] lemma pairLaw_mass [Fintype Ω] [Fintype Ξ] (P : FiniteLaw Ω)
    (Q : Ω → FiniteLaw Ξ) (a : Ω) (b : Ξ) :
    (pairLaw P Q).mass (a,b) = P.mass a * (Q a).mass b := rfl

lemma expect_pairLaw [Fintype Ω] [Fintype Ξ] (P : FiniteLaw Ω)
    (Q : Ω → FiniteLaw Ξ) (f : Ω × Ξ → ℝ) :
    (pairLaw P Q).expect f = P.expect (fun a => (Q a).expect (fun b => f (a,b))) := by
  simp only [expect_def, Fintype.sum_prod_type, pairLaw_mass]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

abbrev Weights (ι : Type*) := {w : ι → ℝ // ∀ i, w i ∈ Icc (0 : ℝ) 1}

def totalWeight (w : Weights ι) : ℝ := ∑ i, w.1 i

def removedWeight (w : Weights ι) (S : Finset ι) : ℝ := ∑ i ∈ S, w.1 i

def remainingWeight (w : Weights ι) (S : Finset ι) : ℝ :=
  ∑ i, if i ∈ S then 0 else w.1 i

lemma remaining_eq (w : Weights ι) (S : Finset ι) :
    remainingWeight w S = totalWeight w-removedWeight w S := by
  classical
  have h : (∑ i, if i ∈ S then w.1 i else 0) = removedWeight w S := by
    simp [removedWeight]
  have hsum : totalWeight w =
      (∑ i, if i ∈ S then w.1 i else 0)+remainingWeight w S := by
    unfold totalWeight remainingWeight
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [hi]
  rw [h] at hsum
  linarith

omit [Fintype ι] [DecidableEq ι] in
lemma removed_nonneg (w : Weights ι) (S : Finset ι) : 0 ≤ removedWeight w S :=
  Finset.sum_nonneg (fun i _ => (w.2 i).1)

omit [Fintype ι] [DecidableEq ι] in
lemma removed_le_card (w : Weights ι) (S : Finset ι) :
    removedWeight w S ≤ S.card := by
  calc
    removedWeight w S ≤ ∑ _i ∈ S, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => (w.2 i).2)
    _ = S.card := by simp

lemma denominator_lower (w : Weights ι) (S : Finset ι) :
    totalWeight w-(S.card : ℝ) ≤ remainingWeight w S := by
  rw [remaining_eq]
  linarith [removed_le_card w S]

lemma denominator_guard (w : Weights ι) (S : Finset ι)
    {d : ℕ} {ε m : ℝ} (hS : S.card ≤ d)
    (hW : (d : ℝ)+ε*m < totalWeight w) :
    ε*m < remainingWeight w S := by
  have hcard : (S.card : ℝ) ≤ d := by exact_mod_cast hS
  linarith [denominator_lower w S]

variable [Nonempty ι]

def oneDraw (w : Weights ι) (S : Finset ι) : FiniteLaw ι := by
  classical
  exact if h : 0 < remainingWeight w S then
    ofMass (fun i => (if i ∈ S then 0 else w.1 i)/remainingWeight w S)
      (fun i => div_nonneg (by
        by_cases hi : i ∈ S
        · simp [hi]
        · simpa [hi] using (w.2 i).1) h.le)
      (by
        rw [←Finset.sum_div]
        change remainingWeight w S/remainingWeight w S=1
        exact div_self h.ne')
  else FiniteLaw.dirac (Classical.choice ‹Nonempty ι›)

lemma oneDraw_mass (w : Weights ι) (S : Finset ι)
    (h : 0 < remainingWeight w S) (i : ι) :
    (oneDraw w S).mass i =
      (if i ∈ S then 0 else w.1 i)/remainingWeight w S := by
  simp [oneDraw, h, ofMass]

lemma oneDraw_support (w : Weights ι) (S : Finset ι)
    (h : 0 < remainingWeight w S) {i : ι}
    (hi : 0 < (oneDraw w S).mass i) : i ∉ S ∧ 0 < w.1 i := by
  rw [oneDraw_mass w S h] at hi
  by_cases hmem : i ∈ S
  · simp [hmem] at hi
  · simp only [hmem, if_false] at hi
    have hw : 0 < w.1 i := by
      rcases div_pos_iff.mp hi with hh | hh
      · exact hh.1
      · exact False.elim ((not_lt_of_ge h.le) hh.2)
    exact ⟨hmem, hw⟩

lemma oneDraw_expect (w : Weights ι) (S : Finset ι)
    (h : 0 < remainingWeight w S) (f : ι → ℝ) :
    (oneDraw w S).expect f =
      (∑ i, if i ∈ S then 0 else w.1 i*f i)/remainingWeight w S := by
  rw [expect_def]
  calc
    (∑ i, (oneDraw w S).mass i*f i) =
        ∑ i, (if i ∈ S then 0 else w.1 i*f i)/remainingWeight w S := by
      apply Finset.sum_congr rfl
      intro i _
      rw [oneDraw_mass w S h]
      by_cases hi : i ∈ S <;> simp [hi, div_mul_eq_mul_div]
    _ = (∑ i, if i ∈ S then 0 else w.1 i*f i)/remainingWeight w S := by
      simp only [div_eq_mul_inv, Finset.sum_mul]

lemma oneDraw_focal (w : Weights ι) (S : Finset ι)
    (h : 0 < remainingWeight w S) {i : ι} (hi : i ∉ S) :
    (oneDraw w S).mass i = w.1 i / remainingWeight w S := by
  simp [oneDraw_mass w S h, hi]

def Path (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => ι × Path ι n

instance pathFintype (n : ℕ) : Fintype (Path ι n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI : Fintype (Path ι n) := ih
    exact inferInstanceAs (Fintype (ι × Path ι n))

def pathLaw (w : Weights ι) : (n : ℕ) → Finset ι → FiniteLaw (Path ι n)
  | 0, _ => FiniteLaw.dirac PUnit.unit
  | n+1, S => pairLaw (oneDraw w S) (fun i => pathLaw w n (insert i S))

def finalSet : (n : ℕ) → Finset ι → Path ι n → Finset ι
  | 0, S, _ => S
  | n+1, S, p => finalSet n (insert p.1 S) p.2

def selectedSum (h : ι → ℝ) : (n : ℕ) → Path ι n → ℝ
  | 0, _ => 0
  | n+1, p => h p.1 + selectedSum h n p.2

lemma expect_path_succ (w : Weights ι) (n : ℕ) (S : Finset ι)
    (f : Path ι (n+1) → ℝ) :
    (pathLaw w (n+1) S).expect f =
      (oneDraw w S).expect (fun i =>
        (pathLaw w n (insert i S)).expect (fun p => f (i,p))) :=
  expect_pairLaw _ _ _

lemma path_mass_succ (w : Weights ι) (n : ℕ) (S : Finset ι)
    (p : Path ι (n+1)) :
    (pathLaw w (n+1) S).mass p =
      (oneDraw w S).mass p.1 * (pathLaw w n (insert p.1 S)).mass p.2 := rfl

lemma path_support_succ (w : Weights ι) (n : ℕ) (S : Finset ι)
    (p : Path ι (n+1)) (hp : 0 < (pathLaw w (n+1) S).mass p) :
    0 < (oneDraw w S).mass p.1 ∧
      0 < (pathLaw w n (insert p.1 S)).mass p.2 := by
  rw [path_mass_succ] at hp
  exact (mul_pos_iff.mp hp).resolve_right (by
    intro hh
    linarith [mass_nonneg (oneDraw w S) p.1, hh.1])

lemma finalSet_card (w : Weights ι) (n : ℕ) (S : Finset ι)
    (hW : (S.card : ℝ)+n < totalWeight w)
    (p : Path ι n) (hp : 0 < (pathLaw w n S).mass p) :
    (finalSet n S p).card = S.card+n := by
  classical
  induction n generalizing S with
  | zero => simp [finalSet]
  | succ n ih =>
    have hd : 0 < remainingWeight w S := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast at hW
      linarith [denominator_lower w S]
    obtain ⟨hp1,hp2⟩ := path_support_succ w n S p hp
    obtain ⟨hmem,_⟩ := oneDraw_support w S hd hp1
    have hW' : ((insert p.1 S).card : ℝ)+n < totalWeight w := by
      rw [Finset.card_insert_of_notMem hmem]
      push_cast at hW ⊢
      linarith
    have hh := ih (insert p.1 S) hW' p.2 hp2
    simpa [finalSet, Finset.card_insert_of_notMem hmem, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hh

lemma finalSet_weight_pos (w : Weights ι) (n : ℕ) (S : Finset ι)
    (hW : (S.card:ℝ)+n<totalWeight w) (hS : ∀i∈S,0<w.1 i)
    (p : Path ι n) (hp : 0<(pathLaw w n S).mass p) :
    ∀i∈finalSet n S p,0<w.1 i := by
  induction n generalizing S with
  | zero => simpa only [finalSet] using hS
  | succ n ih =>
    obtain ⟨hp₁,hp₂⟩ := path_support_succ w n S p hp
    have hR : 0<remainingWeight w S := by
      have hn : (0:ℝ)≤n := Nat.cast_nonneg n
      push_cast at hW
      linarith [denominator_lower w S]
    obtain ⟨hnew,hpos⟩ := oneDraw_support w S hR hp₁
    have hW' : ((insert p.1 S).card:ℝ)+n<totalWeight w := by
      rw [Finset.card_insert_of_notMem hnew]
      push_cast at hW ⊢
      linarith
    apply ih (insert p.1 S) hW' _ p.2 hp₂
    intro i hi
    rcases Finset.mem_insert.mp hi with hi|hi
    · exact hi ▸ hpos
    · exact hS i hi

omit [Fintype ι] [Nonempty ι] in
lemma initial_subset_final (n : ℕ) (S : Finset ι) (p : Path ι n) :
    S ⊆ finalSet n S p := by
  induction n generalizing S with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
    exact (Finset.subset_insert _ _).trans (ih (insert p.1 S) p.2)

lemma selectedSum_eq_setSum (w : Weights ι) (h : ι → ℝ)
    (n : ℕ) (S : Finset ι) (hW : (S.card : ℝ)+n < totalWeight w)
    (p : Path ι n) (hp : 0 < (pathLaw w n S).mass p) :
    selectedSum h n p = (∑ i ∈ finalSet n S p, h i)-(∑ i ∈ S, h i) := by
  classical
  induction n generalizing S with
  | zero => simp [selectedSum, finalSet]
  | succ n ih =>
    obtain ⟨hp1,hp2⟩ := path_support_succ w n S p hp
    have hd : 0 < remainingWeight w S := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast at hW
      linarith [denominator_lower w S]
    obtain ⟨hmem,_⟩ := oneDraw_support w S hd hp1
    have hW' : ((insert p.1 S).card : ℝ)+n < totalWeight w := by
      rw [Finset.card_insert_of_notMem hmem]
      push_cast at hW ⊢
      linarith
    have hh := ih (insert p.1 S) hW' p.2 hp2
    rw [selectedSum, hh, Finset.sum_insert hmem]
    simp only [finalSet]
    ring

def indicator (i : ι) (S : Finset ι) : ℝ := if i ∈ S then 1 else 0

omit [Nonempty ι] in
lemma expect_independent_indicators (P Q : FiniteLaw (Finset ι)) (i : ι) :
    (pairLaw P (fun _ => Q)).expect
      (fun z => indicator i z.1 * indicator i z.2) =
      P.expect (indicator i) * Q.expect (indicator i) := by
  rw [expect_pairLaw]
  simp_rw [expect_const_mul]
  exact expect_mul_const P (indicator i) _

omit [Nonempty ι] in
lemma exact_conditional_duplicate (P : FiniteLaw (Finset ι)) (i : ι)
    {p : ℝ} (hp : P.expect (indicator i) = p) :
    (pairLaw P (fun _ => P)).expect
      (fun z => indicator i z.1 * indicator i z.2) = p^2 := by
  rw [expect_independent_indicators, hp]
  ring

omit [Nonempty ι] in
lemma exact_conditional_success (P : FiniteLaw (Finset ι)) (i : ι)
    {p : ℝ} (hp : P.expect (indicator i) = p) :
    (pairLaw P (fun _ => P)).expect
      (fun z => indicator i z.1+indicator i z.2-indicator i z.1*indicator i z.2)
        = 2*p-p^2 := by
  have hfirst : (pairLaw P (fun _ => P)).expect
      (fun z => indicator i z.1) = p := by
    rw [expect_pairLaw]
    simp_rw [expect_const]
    exact hp
  have hsecond : (pairLaw P (fun _ => P)).expect
      (fun z => indicator i z.2) = p := by
    rw [expect_pairLaw]
    simp only [hp, expect_const]
  rw [expect_sub, expect_add, hfirst, hsecond, expect_independent_indicators, hp]
  ring

def preDeficit (c H₁ H₂ lowDemand : ℝ) : ℝ := c-(H₁+H₂)/2-lowDemand

def postDeficit (c H₁ H₂ lowDemand removedDemand : ℝ) : ℝ :=
  c-max H₁ H₂-(lowDemand-removedDemand)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma balanced_deficit_identity (c H₁ H₂ lowDemand : ℝ)
    (E : Finset ι) (p : ι → ℝ)
    (hcard : (E.card : ℝ) = |H₁-H₂|) :
    postDeficit c H₁ H₂ lowDemand (∑ i ∈ E, p i) =
      preDeficit c H₁ H₂ lowDemand-(∑ i ∈ E, (1/2-p i)) := by
  have hm : max H₁ H₂ = (H₁+H₂+|H₁-H₂|)/2 := by
    by_cases h : H₁ ≤ H₂
    · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_left (le_of_not_ge h), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [postDeficit, preDeficit, hm, hcard]
  ring

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma positive_deficit_restrictions {W D a : ℝ} (E : Finset ι) (h : ι → ℝ)
    (ha : 0 < a) (hh : ∀ i ∈ E, a ≤ h i)
    (hD : D = W-∑ i ∈ E, h i) (hpos : 0 < D) :
    0 < W ∧ (E.card : ℝ) < W/a := by
  have hs : (E.card : ℝ)*a ≤ ∑ i ∈ E, h i := by
    simpa using Finset.sum_le_sum hh
  have hc : 0 ≤ (E.card : ℝ) := Nat.cast_nonneg _
  constructor
  · nlinarith
  · apply (lt_div_iff₀ ha).2
    linarith

end FCAppendix.Affine.WeightedSampling
