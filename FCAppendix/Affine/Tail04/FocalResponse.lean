import FCAppendix.Probability.IndependentCounts
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Tail04.FocalResponse
open Set MeasureTheory
open scoped BigOperators

def denominator (ξ b W : ℝ) : ℝ := ξ*(b+1/W)

def baselinePrice (M ξ d W : ℝ) : ℝ := (M-ξ*d)/W

theorem exact_advantage (M ξ d W b p : ℝ) :
    b*(1-ξ*p)-baselinePrice M ξ (d-p) W =
      b-baselinePrice M ξ d W-denominator ξ b W*p := by
  unfold baselinePrice denominator
  ring

structure UnitPair where
  left : ℝ
  right : ℝ
  left_mem : left ∈ Icc (0:ℝ) 1
  right_mem : right ∈ Icc (0:ℝ) 1

def zeroZero : UnitPair := ⟨0,0,by norm_num,by norm_num⟩
def oneZero : UnitPair := ⟨1,0,by norm_num,by norm_num⟩
def zeroOne : UnitPair := ⟨0,1,by norm_num,by norm_num⟩
def oneOne : UnitPair := ⟨1,1,by norm_num,by norm_num⟩

def solution (a₀ a₁ : ℝ) : UnitPair :=
  if h₀ : a₀ ≤ 0 then
    if h₁ : a₁ ≤ 0 then zeroZero else oneZero
  else if h₁ : a₁ ≤ 0 then zeroOne
  else if h₀' : 1 ≤ a₀ then
    if h₁' : 1 ≤ a₁ then oneOne else zeroOne
  else if h₁' : 1 ≤ a₁ then oneZero
  else ⟨a₀,a₁,⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma measurable_solution_left :
    Measurable (fun a : ℝ × ℝ => (solution a.1 a.2).left) := by
  have he : (fun a : ℝ × ℝ => (solution a.1 a.2).left) =
      fun a => if a.1 ≤ 0 then (if a.2 ≤ 0 then 0 else 1)
        else if a.2 ≤ 0 then 0
        else if 1 ≤ a.1 then (if 1 ≤ a.2 then 1 else 0)
        else if 1 ≤ a.2 then 1 else a.1 := by
    funext a
    unfold solution
    split_ifs <;> rfl
  rw [he]
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
    (Measurable.ite (measurableSet_le measurable_snd measurable_const)
      measurable_const measurable_const)
    (Measurable.ite (measurableSet_le measurable_snd measurable_const) measurable_const
      (Measurable.ite (measurableSet_le measurable_const measurable_fst)
        (Measurable.ite (measurableSet_le measurable_const measurable_snd)
          measurable_const measurable_const)
        (Measurable.ite (measurableSet_le measurable_const measurable_snd)
          measurable_const measurable_fst)))

lemma measurable_solution_right :
    Measurable (fun a : ℝ × ℝ => (solution a.1 a.2).right) := by
  have he : (fun a : ℝ × ℝ => (solution a.1 a.2).right) =
      fun a => if a.1 ≤ 0 then 0
        else if a.2 ≤ 0 then 1
        else if 1 ≤ a.1 then 1
        else if 1 ≤ a.2 then 0 else a.2 := by
    funext a
    unfold solution
    split_ifs <;> rfl
  rw [he]
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const) measurable_const
    (Measurable.ite (measurableSet_le measurable_snd measurable_const) measurable_const
      (Measurable.ite (measurableSet_le measurable_const measurable_fst) measurable_const
        (Measurable.ite (measurableSet_le measurable_const measurable_snd)
          measurable_const measurable_snd)))

def ScalarOptimal (p a : ℝ) : Prop := ∀ r ∈ Icc (0:ℝ) 1, r*a ≤ p*a

lemma zero_optimal (a : ℝ) (ha : a ≤ 0) : ScalarOptimal 0 a := by
  intro r hr
  nlinarith [hr.1]

lemma one_optimal (a : ℝ) (ha : 0 ≤ a) : ScalarOptimal 1 a := by
  intro r hr
  nlinarith [hr.2]

lemma indifferent_optimal (p : ℝ) : ScalarOptimal p 0 := by
  intro r hr
  simp

theorem solution_optimal (a₀ a₁ D : ℝ) (hD : 0 ≤ D) :
    ScalarOptimal (solution a₀ a₁).left (D*(a₁-(solution a₀ a₁).right)) ∧
    ScalarOptimal (solution a₀ a₁).right (D*(a₀-(solution a₀ a₁).left)) := by
  unfold solution
  split_ifs with h₀ h₁ h₁ h₀' h₁' h₁'
  · exact ⟨zero_optimal _ (by simpa [zeroZero] using mul_nonpos_of_nonneg_of_nonpos hD h₁),
      zero_optimal _ (by simpa [zeroZero] using mul_nonpos_of_nonneg_of_nonpos hD h₀)⟩
  · exact ⟨one_optimal _ (by dsimp [oneZero]; nlinarith),
      zero_optimal _ (by dsimp [oneZero]; nlinarith)⟩
  · exact ⟨zero_optimal _ (by dsimp [zeroOne]; nlinarith),
      one_optimal _ (by dsimp [zeroOne]; nlinarith)⟩
  · exact ⟨one_optimal _ (by dsimp [oneOne]; nlinarith),
      one_optimal _ (by dsimp [oneOne]; nlinarith)⟩
  · exact ⟨zero_optimal _ (by dsimp [zeroOne]; nlinarith),
      one_optimal _ (by dsimp [zeroOne]; nlinarith)⟩
  · exact ⟨one_optimal _ (by dsimp [oneZero]; nlinarith),
      zero_optimal _ (by dsimp [oneZero]; nlinarith)⟩
  · simpa using And.intro (indifferent_optimal a₀) (indifferent_optimal a₁)

def focalPair (ξ b W L₀ L₁ : ℝ) : UnitPair :=
  solution ((b-L₀)/denominator ξ b W) ((b-L₁)/denominator ξ b W)

theorem focalPair_optimal (ξ b W L₀ L₁ : ℝ)
    (hD : 0 < denominator ξ b W) :
    ScalarOptimal (focalPair ξ b W L₀ L₁).left
      (b-L₁-denominator ξ b W*(focalPair ξ b W L₀ L₁).right) ∧
    ScalarOptimal (focalPair ξ b W L₀ L₁).right
      (b-L₀-denominator ξ b W*(focalPair ξ b W L₀ L₁).left) := by
  have h := solution_optimal ((b-L₀)/denominator ξ b W)
    ((b-L₁)/denominator ξ b W) (denominator ξ b W) hD.le
  have he (L p : ℝ) : denominator ξ b W*((b-L)/denominator ξ b W-p) =
      b-L-denominator ξ b W*p := by
    field_simp [hD.ne']
  simpa only [he,focalPair] using h

def coinLaw (p : UnitPair) : FiniteLaw (Bool × Bool) :=
  (IndependentCounts.bernoulli p.left p.left_mem.1 p.left_mem.2).prod
    (IndependentCounts.bernoulli p.right p.right_mem.1 p.right_mem.2)

theorem coinLaw_means (p : UnitPair) :
    (coinLaw p).expect (fun z => if z.1 then (1:ℝ) else 0) = p.left ∧
    (coinLaw p).expect (fun z => if z.2 then (1:ℝ) else 0) = p.right ∧
    (coinLaw p).expect (fun z => (if z.1 then (1:ℝ) else 0)*
      (if z.2 then (1:ℝ) else 0)) = p.left*p.right := by
  refine ⟨?_,?_,?_⟩
  all_goals simp only [coinLaw,FiniteLaw.expect_prod,IndependentCounts.expect_bernoulli,
    Bool.false_eq_true, ite_false,ite_true,mul_zero,zero_add,mul_one]
  all_goals ring

theorem focalPair_interior (ξ b W L₀ L₁ : ℝ)
    (hD : 0 < denominator ξ b W)
    (h₀ : 0 < b-L₀) (h₁ : 0 < b-L₁)
    (h₀' : b-L₀ < denominator ξ b W) (h₁' : b-L₁ < denominator ξ b W) :
    (focalPair ξ b W L₀ L₁).left = (b-L₀)/denominator ξ b W ∧
    (focalPair ξ b W L₀ L₁).right = (b-L₁)/denominator ξ b W := by
  have hp₀ := div_pos h₀ hD
  have hp₁ := div_pos h₁ hD
  have hp₀' := (div_lt_one hD).mpr h₀'
  have hp₁' := (div_lt_one hD).mpr h₁'
  simp [focalPair,solution,not_le.mpr hp₀,not_le.mpr hp₁,
    not_le.mpr hp₀',not_le.mpr hp₁']

theorem focalPair_between (ξ b W L₀ L₁ : ℝ)
    (hD : 0 < denominator ξ b W) (h₀ : L₀ < b) (h₁ : b ≤ L₁) :
    (focalPair ξ b W L₀ L₁).left = 0 ∧
    (focalPair ξ b W L₀ L₁).right = 1 := by
  have hp₀ : 0 < (b-L₀)/denominator ξ b W := div_pos (sub_pos.mpr h₀) hD
  have hp₁ : (b-L₁)/denominator ξ b W ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr h₁) hD.le
  simp [focalPair,solution,not_le.mpr hp₀,hp₁,zeroOne]

def draftClipped (ξ b L W : ℝ) : ℝ :=
  min 1 (max 0 ((b-L)/(ξ*(b+1/W))))

theorem draft_between_clipping_fails :
    ¬ ScalarOptimal (draftClipped (1/4) 1 (9/10) 4)
      (1-(11/10)-(1/4)*(1+1/4)*draftClipped (1/4) 1 (11/10) 4) := by
  intro h
  have hh := h 0 (by norm_num)
  norm_num [draftClipped] at hh

end FCAppendix.Affine.Tail04.FocalResponse
