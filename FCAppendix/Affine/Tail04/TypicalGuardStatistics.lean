import FCAppendix.Affine.Tail04.NativeTypicalCount
import FCAppendix.Affine.Tail04.TypicalCountContinuity

noncomputable section
namespace FCAppendix.Affine.Tail04.TypicalGuardStatistics
open MeasureTheory Set Classical
open EqualPrivateSignal LocalHighCommon TypicalHighPolicy NativeTypicalCount
open scoped BigOperators

def multiplier (H c ell M : ℕ) (ξ : ℝ) (reg : Bool) (W : ℝ) (z : Marks H) : ℝ :=
  ((M:ℝ)-ξ*((c-(ell+(if reg then upperCount z else H)):ℕ):ℝ))/W

def meanMultiplier (H c ell M : ℕ) (ξ : ℝ) (reg : Bool)
    (ν : FiniteLaw (Marks H)) (W : ℝ) : ℝ :=
  ν.expect (multiplier H c ell M ξ reg W)

def realizationMargin (H c ell M : ℕ) (ξ B : ℝ) (reg : Bool) (W : ℝ) : ℝ :=
  TypicalGuard.finiteMinimum (fun z : Marks H =>
    min (multiplier H c ell M ξ reg W z-(1-ξ)*B)
      (1-multiplier H c ell M ξ reg W z))

def partialMargin (H0 H1 c ell0 ell1 M : ℕ) (ξ R Rp : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (W : ℝ) : ℝ :=
  if reg then
    min (meanMultiplier H0 c ell0 M ξ reg ν0 W-Rp)
      (meanMultiplier H1 c ell1 M ξ reg ν1 W-Rp)
  else
    min (R-meanMultiplier H0 c ell0 M ξ reg ν0 W)
      (R-meanMultiplier H1 c ell1 M ξ reg ν1 W)

def margin (H0 H1 c ell0 ell1 M : ℕ) (ξ B R Rp : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (W : ℝ) : ℝ :=
  min (min (realizationMargin H0 c ell0 M ξ B reg W)
      (realizationMargin H1 c ell1 M ξ B reg W))
    (partialMargin H0 H1 c ell0 ell1 M ξ R Rp reg ν0 ν1 W)

def Structural (H0 H1 c ell0 ell1 M : ℕ) : Prop :=
  ell0+H0 ≤ c ∧ ell1+H1 ≤ c ∧ 0 < M

def weight (H0 H1 c ell0 ell1 M : ℕ) (ξ B R Rp width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (W : ℝ) : ℝ :=
  if Structural H0 H1 c ell0 ell1 M then
    probabilityClip (margin H0 H1 c ell0 ell1 M ξ B R Rp reg ν0 ν1 W/width)
  else 0

theorem weight_bounds (H0 H1 c ell0 ell1 M : ℕ) (ξ B R Rp width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (W : ℝ) :
    weight H0 H1 c ell0 ell1 M ξ B R Rp width reg ν0 ν1 W ∈ Icc (0:ℝ) 1 := by
  unfold weight
  split_ifs
  · exact probabilityClip_bounds _
  · norm_num

theorem actual_multiplier (N H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) (z : Marks H) :
    TypicalHighPolicy.multiplier N H c ξ reg O I b z =
      multiplier H c O.card I.card ξ reg (mixedReciprocalSum I b) z := by
  rw [TypicalHighPolicy.multiplier_formula]
  rfl

theorem actual_meanMultiplier (N H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) (ν : FiniteLaw (Marks H)) :
    TypicalHighPolicy.meanMultiplier N H c ξ reg O I b ν =
      meanMultiplier H c O.card I.card ξ reg ν (mixedReciprocalSum I b) := by
  apply ν.expect_congr
  exact actual_multiplier N H c ξ reg O I b

theorem actual_margin (N H0 H1 c : ℕ) (ξ B R Rp : ℝ) (reg : Bool)
    (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    TypicalGuard.margin N H0 H1 c ξ B R Rp reg I O0 O1 b ν0 ν1 =
      margin H0 H1 c O0.card O1.card I.card ξ B R Rp reg ν0 ν1
        (mixedReciprocalSum I b) := by
  unfold TypicalGuard.margin TypicalGuard.realizationMargin TypicalGuard.partialMargin
    margin realizationMargin partialMargin
  simp only [actual_multiplier,actual_meanMultiplier]

theorem actual_structural (N H0 H1 c : ℕ) (I O0 O1 : Finset (Fin N))
    (hO : Disjoint O0 O1) (hI : Disjoint I (O0 ∪ O1))
    (hcover : I ∪ (O0 ∪ O1)=Finset.univ) :
    TypicalHighPolicy.Structural N H0 H1 c I O0 O1 ↔
      Structural H0 H1 c O0.card O1.card I.card := by
  constructor
  · intro h
    exact ⟨h.2.2.2.1,h.2.2.2.2.1,Finset.card_pos.mpr h.2.2.2.2.2⟩
  · rintro ⟨h0,h1,hM⟩
    exact ⟨hO,hI,hcover,h0,h1,Finset.card_pos.mp hM⟩

theorem actual_weight (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ) (reg : Bool)
    (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hO : Disjoint O0 O1) (hI : Disjoint I (O0 ∪ O1))
    (hcover : I ∪ (O0 ∪ O1)=Finset.univ) :
    TypicalGuard.weight N H0 H1 c ξ B R Rp width reg I O0 O1 b ν0 ν1 =
      weight H0 H1 c O0.card O1.card I.card ξ B R Rp width reg ν0 ν1
        (mixedReciprocalSum I b) := by
  unfold TypicalGuard.weight weight
  rw [actual_structural N H0 H1 c I O0 O1 hO hI hcover,actual_margin]
  rfl

def phi (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (M : ℕ) (W : ℝ) : unitInterval :=
  let P := countParameters N H0 H1 c ξ reg ν0 ν1
  ⟨weight H0 H1 c (P.owner0 M) (P.owner1 M) M ξ B R Rp width reg ν0 ν1 W,
    weight_bounds H0 H1 c (P.owner0 M) (P.owner1 M) M ξ B R Rp width reg ν0 ν1 W⟩

theorem actual_weight_phi (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ) (reg : Bool)
    (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hO : Disjoint O0 O1) (hI : Disjoint I (O0 ∪ O1))
    (hcover : I ∪ (O0 ∪ O1)=Finset.univ)
    (hell0 : O0.card=(countParameters N H0 H1 c ξ reg ν0 ν1).owner0 I.card)
    (hell1 : O1.card=(countParameters N H0 H1 c ξ reg ν0 ν1).owner1 I.card) :
    TypicalGuard.weight N H0 H1 c ξ B R Rp width reg I O0 O1 b ν0 ν1 =
      (phi N H0 H1 c ξ B R Rp width reg ν0 ν1 I.card (mixedReciprocalSum I b):ℝ) := by
  rw [actual_weight N H0 H1 c ξ B R Rp width reg I O0 O1 b ν0 ν1 hO hI hcover,
    hell0,hell1]
  rfl

theorem continuousAt_listMinimum {A X : Type*} [TopologicalSpace X]
    (as : List A) (f : X → A → ℝ) (x : X)
    (hf : ∀ a ∈ as, ContinuousAt (fun y => f y a) x) :
    ContinuousAt (fun y => TypicalGuard.listMinimum as (f y)) x := by
  induction as with
  | nil => exact continuousAt_const
  | cons a as ih =>
    exact (hf a (by simp)).min (ih (fun b hb => hf b (by simp [hb])))

theorem continuousAt_finiteMinimum {A X : Type*} [Fintype A] [TopologicalSpace X]
    (f : X → A → ℝ) (x : X) (hf : ∀ a, ContinuousAt (fun y => f y a) x) :
    ContinuousAt (fun y => TypicalGuard.finiteMinimum (f y)) x :=
  continuousAt_listMinimum _ f x (fun a _ => hf a)

theorem continuousAt_multiplier (H c ell M : ℕ) (ξ : ℝ) (reg : Bool)
    (W : ℝ) (hW : W ≠ 0) (z : Marks H) :
    ContinuousAt (fun w => multiplier H c ell M ξ reg w z) W :=
  continuousAt_const.div continuousAt_id hW

theorem continuousAt_meanMultiplier (H c ell M : ℕ) (ξ : ℝ) (reg : Bool)
    (ν : FiniteLaw (Marks H)) (W : ℝ) (hW : W ≠ 0) :
    ContinuousAt (meanMultiplier H c ell M ξ reg ν) W := by
  unfold meanMultiplier FiniteLaw.expect
  apply tendsto_finsetSum
  intro z _
  exact continuousAt_const.mul (continuousAt_multiplier H c ell M ξ reg W hW z)

theorem continuousAt_realizationMargin (H c ell M : ℕ) (ξ B : ℝ) (reg : Bool)
    (W : ℝ) (hW : W ≠ 0) :
    ContinuousAt (realizationMargin H c ell M ξ B reg) W := by
  apply continuousAt_finiteMinimum
  intro z
  exact ((continuousAt_multiplier H c ell M ξ reg W hW z).sub continuousAt_const).min
    (continuousAt_const.sub (continuousAt_multiplier H c ell M ξ reg W hW z))

theorem continuousAt_partialMargin (H0 H1 c ell0 ell1 M : ℕ) (ξ R Rp : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (W : ℝ) (hW : W ≠ 0) :
    ContinuousAt (partialMargin H0 H1 c ell0 ell1 M ξ R Rp reg ν0 ν1) W := by
  cases reg
  · exact (continuousAt_const.sub (continuousAt_meanMultiplier H0 c ell0 M ξ false ν0 W hW)).min
      (continuousAt_const.sub (continuousAt_meanMultiplier H1 c ell1 M ξ false ν1 W hW))
  · exact ((continuousAt_meanMultiplier H0 c ell0 M ξ true ν0 W hW).sub continuousAt_const).min
      ((continuousAt_meanMultiplier H1 c ell1 M ξ true ν1 W hW).sub continuousAt_const)

theorem continuousAt_margin (H0 H1 c ell0 ell1 M : ℕ) (ξ B R Rp : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (W : ℝ) (hW : W ≠ 0) :
    ContinuousAt (margin H0 H1 c ell0 ell1 M ξ B R Rp reg ν0 ν1) W :=
  ((continuousAt_realizationMargin H0 c ell0 M ξ B reg W hW).min
    (continuousAt_realizationMargin H1 c ell1 M ξ B reg W hW)).min
      (continuousAt_partialMargin H0 H1 c ell0 ell1 M ξ R Rp reg ν0 ν1 W hW)

theorem continuousAt_phi (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (M : ℕ) (W : ℝ) (hW : 0 < W) :
    ContinuousAt (fun w => (phi N H0 H1 c ξ B R Rp width reg ν0 ν1 M w:ℝ)) W := by
  let P := countParameters N H0 H1 c ξ reg ν0 ν1
  by_cases hs : Structural H0 H1 c (P.owner0 M) (P.owner1 M) M
  · dsimp only [P] at hs
    simp only [phi,weight,if_pos hs]
    exact continuous_probabilityClip.continuousAt.comp
      ((continuousAt_margin H0 H1 c (P.owner0 M) (P.owner1 M) M ξ B R Rp reg
        ν0 ν1 W hW.ne').div_const width)
  · dsimp only [P] at hs
    simp only [phi,weight,if_neg hs]
    exact continuousAt_const

theorem phi_zero_mixed (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (W : ℝ) :
    (phi N H0 H1 c ξ B R Rp width reg ν0 ν1 0 W:ℝ)=0 := by
  simp [phi,weight,Structural]

theorem continuousAt_sourcePayoff {N H0 H1 c : ℕ} [Nonempty (Fin N)]
    (ξ B R Rp width e0 eta : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (i : Fin N) (fallback : CountLaw 2)
    (x : ℝ × (Fin N → ℝ)) (hb : ∀ j, 0 < x.2 j)
    (hnotie : ∀ j, j≠i → x.2 j≠x.2 i) :
    ContinuousAt (sourceTypicalJointPayoff (countParameters N H0 H1 c ξ reg ν0 ν1)
      (phi N H0 H1 c ξ B R Rp width reg ν0 ν1) e0 B eta heta0 heta1 i fallback) x :=
  continuousAt_sourceTypicalJointPayoff _ _
    (continuousAt_phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
    e0 B eta heta0 heta1 i fallback x hb hnotie

end FCAppendix.Affine.Tail04.TypicalGuardStatistics
