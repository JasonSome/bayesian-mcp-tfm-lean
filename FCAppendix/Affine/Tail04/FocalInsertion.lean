import FCAppendix.Affine.Tail04.FocalCapacity
import FCAppendix.Affine.Tail04.TypicalHighPolicy
import FCAppendix.Affine.Tail04.TypicalCountLaws

set_option maxHeartbeats 500000

noncomputable section
namespace FCAppendix.Affine.Tail04.FocalInsertion
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {N : ℕ}

abbrev Target (N H : ℕ) := Option (EqualPrivateSignal.Target N H)

def someEmbedding {α : Type*} : α ↪ Option α := ⟨some,fun _ _ h => Option.some.inj h⟩

def lift {α : Type*} (S : Finset α) : Finset (Option α) := S.map someEmbedding

@[simp] lemma mem_lift {α : Type*} [DecidableEq α] (S : Finset α) (i : α) :
    some i∈lift S ↔ i∈S := by simp [lift,someEmbedding]

@[simp] lemma none_not_mem_lift {α : Type*} [DecidableEq α] (S : Finset α) :
    (none : Option α)∉lift S := by simp [lift,someEmbedding]

@[simp] lemma lift_card {α : Type*} (S : Finset α) : (lift S).card=S.card := by simp [lift]

lemma lift_disjoint {α : Type*} [DecidableEq α] {S T : Finset α}
    (h : Disjoint S T) : Disjoint (lift S) (lift T) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  cases i with
  | none => exact (none_not_mem_lift S) hi
  | some i => exact (Finset.disjoint_left.mp h) ((mem_lift S i).mp hi) ((mem_lift T i).mp hj)

def fixed (N H : ℕ) (reg : Bool) (O : Finset (Fin N)) (z : Marks H) :
    Finset (Target N H) := lift (TypicalHighPolicy.fixed N H reg O z)

def mixed (H : ℕ) (I : Finset (Fin N)) : Finset (Target N H) := lift (activeLift H I)

def numericalBid (H : ℕ) (b : Fin N → ℝ) (y : ℝ) : Target N H → ℝ :=
  fun t => Option.elim t y (TypicalHighPolicy.commonBid H b)

@[simp] lemma fixed_card (N H : ℕ) (reg : Bool) (O : Finset (Fin N)) (z : Marks H) :
    (fixed N H reg O z).card=O.card+(if reg then upperCount z else H) := by
  rw [fixed,lift_card,TypicalHighPolicy.fixed_card]

@[simp] lemma mixed_card (H : ℕ) (I : Finset (Fin N)) : (mixed H I).card=I.card := by
  rw [mixed,lift_card,activeLift_card]

lemma reciprocal_sum (H : ℕ) (I : Finset (Fin N)) (b : Fin N → ℝ) (y : ℝ) :
    mixedReciprocalSum (mixed H I) (numericalBid H b y)=mixedReciprocalSum I b := by
  unfold mixedReciprocalSum mixed lift
  rw [Finset.sum_map,sum_activeLift]
  rfl

def multiplier (N H c : ℕ) (ξ : ℝ) (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (y p : ℝ) (z : Marks H) : ℝ :=
  FocalCapacity.multiplier ξ c (fixed N H reg O z) (mixed H I) (numericalBid H b y) p

lemma multiplier_eq (N H c : ℕ) (ξ : ℝ) (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (y p : ℝ) (z : Marks H) (hcap : O.card+H≤ c) :
    multiplier N H c ξ reg O I b y p z=
      TypicalHighPolicy.multiplier N H c ξ reg O I b z+ξ*p/mixedReciprocalSum I b := by
  have hF : (TypicalHighPolicy.fixed N H reg O z).card≤ c :=
    (TypicalHighPolicy.fixed_card_le reg O z).trans hcap
  unfold multiplier
  rw [FocalCapacity.multiplier_shift]
  congr 1
  · unfold FocalCapacity.multiplier TypicalHighPolicy.multiplier realizedMixedMultiplier realizedResidual
    rw [mixed_card,fixed,lift_card,reciprocal_sum,TypicalHighPolicy.reciprocal_sum,
      activeLift_card,Nat.cast_sub hF]
    simp only [sub_zero]
  · rw [reciprocal_sum]

def LocalGuard (N H c : ℕ) (ξ B : ℝ) (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) : Prop :=
  ∀ z : Marks H,(1-ξ)*B≤ TypicalHighPolicy.multiplier N H c ξ reg O I b z ∧
    TypicalHighPolicy.multiplier N H c ξ reg O I b z+ξ/mixedReciprocalSum I b≤1

lemma localGuard_shift (N H c : ℕ) {ξ B : ℝ} (reg : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ)
    (hξ : 0≤ ξ) (hW : 0< mixedReciprocalSum I b)
    (hcap : O.card+H≤ c) (hg : LocalGuard N H c ξ B reg O I b)
    (y p : ℝ) (hp : p∈Icc (0:ℝ) 1) (z : Marks H) :
    (1-ξ)*B≤ multiplier N H c ξ reg O I b y p z ∧
      multiplier N H c ξ reg O I b y p z≤1 := by
  rw [multiplier_eq _ _ _ _ _ _ _ _ _ _ _ hcap]
  have hs0 : 0≤ ξ*p/mixedReciprocalSum I b := div_nonneg (mul_nonneg hξ hp.1) hW.le
  have hs1 : ξ*p/mixedReciprocalSum I b≤ ξ/mixedReciprocalSum I b :=
    div_le_div_of_nonneg_right (by nlinarith [hp.2]) hW.le
  have h := hg z
  constructor <;> linarith

def law (N H c : ℕ) (ξ : ℝ) (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (y p : ℝ) (z : Marks H) : FiniteLaw (Finset (Target N H)) :=
  FocalCapacity.lottery ξ c (fixed N H reg O z) (mixed H I) (numericalBid H b y) none p

theorem implements (N H c : ℕ) {ξ B : ℝ} (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (y p : ℝ) (hξ : 0< ξ) (hξ1 : ξ≤1)
    (hb : ∀ i,b i∈Icc (1:ℝ) B) (hp : p∈Icc (0:ℝ) 1)
    (hOI : Disjoint O I) (hcap : O.card+H≤ c) (hI : I.Nonempty)
    (hg : LocalGuard N H c ξ B reg O I b) (z : Marks H) :
    ExactCapacity.Implements
      (FocalCapacity.marginal ξ c (fixed N H reg O z) (mixed H I)
        (numericalBid H b y) none p) c (law N H c ξ reg O I b y p z) := by
  have hW := mixedReciprocalSum_pos I b hI
    (fun i _ => (by norm_num : (0:ℝ)<1).trans_le (hb i).1)
  have hh := localGuard_shift N H c reg O I b hξ.le hW hcap hg y p hp z
  apply FocalCapacity.lottery_implements ξ hξ c _ _ _ none p hp
    (lift_disjoint (TypicalHighPolicy.fixed_disjoint reg O I z hOI))
    (none_not_mem_lift _) (none_not_mem_lift _)
  · change 0 < mixedReciprocalSum (mixed H I) (numericalBid H b y)
    simpa only [reciprocal_sum] using hW
  · intro i hi
    cases i with
    | none => exact ((none_not_mem_lift _) hi).elim
    | some i =>
      cases i with
      | inl i => exact (by norm_num : (0:ℝ)<1).trans_le (hb i).1
      | inr i => simp [activeLift] at hi
  · intro i hi
    cases i with
    | none => exact ((none_not_mem_lift _) hi).elim
    | some i =>
      cases i with
      | inl i =>
        exact ⟨(mul_le_mul_of_nonneg_left (hb i).2 (sub_nonneg.mpr hξ1)).trans hh.1,
          hh.2.trans (hb i).1⟩
      | inr i => simp [activeLift] at hi

def mixture (N H c : ℕ) (ξ : ℝ) (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (y p : ℝ) (ν : FiniteLaw (Marks H)) : FiniteLaw (Finset (Target N H)) :=
  FiniteLaw.finiteMix ν (law N H c ξ reg O I b y p)

def activeMean (N H c : ℕ) (ξ : ℝ) (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (y p : ℝ) (ν : FiniteLaw (Marks H)) (i : Fin N) : ℝ :=
  (mixture N H c ξ reg O I b y p ν).prob (fun S => some (Sum.inl i)∈S)

def meanPrice (N H c : ℕ) (ξ : ℝ) (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (p : ℝ) (ν : FiniteLaw (Marks H)) : ℝ :=
  TypicalHighPolicy.meanMultiplier N H c ξ reg O I b ν+ξ*p/mixedReciprocalSum I b

lemma mean_multiplier (N H c : ℕ) (ξ : ℝ) (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (y p : ℝ) (ν : FiniteLaw (Marks H)) (hcap : O.card+H≤ c) :
    ν.expect (multiplier N H c ξ reg O I b y p)=meanPrice N H c ξ reg O I b p ν := by
  have he : multiplier N H c ξ reg O I b y p = fun z =>
      TypicalHighPolicy.multiplier N H c ξ reg O I b z+ξ*p/mixedReciprocalSum I b := by
    funext z
    exact multiplier_eq N H c ξ reg O I b y p z hcap
  rw [he,FiniteLaw.expect_add,FiniteLaw.expect_const]
  rfl

lemma focal_marginal (N H c : ℕ) {ξ B : ℝ} (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (y p : ℝ) (ν : FiniteLaw (Marks H))
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hb : ∀ i,b i∈Icc (1:ℝ) B) (hp : p∈Icc (0:ℝ) 1)
    (hOI : Disjoint O I) (hcap : O.card+H≤ c) (hI : I.Nonempty)
    (hg : LocalGuard N H c ξ B reg O I b) :
    (mixture N H c ξ reg O I b y p ν).prob (fun S => none∈S)=p := by
  simp only [mixture,FiniteLaw.prob_eq_expect,FiniteLaw.expect_finiteMix]
  calc
    _ = ν.expect (fun _ => p) := by
      apply ν.expect_congr
      intro z
      rw [←FiniteLaw.prob_eq_expect]
      rw [(implements N H c reg O I b y p hξ hξ1 hb hp hOI hcap hI hg z).2]
      simp [FocalCapacity.marginal,fixed]
    _ = p := FiniteLaw.expect_const ν p

lemma activeMean_formula (N H c : ℕ) {ξ B : ℝ} (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (y p : ℝ) (ν : FiniteLaw (Marks H))
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hb : ∀ i,b i∈Icc (1:ℝ) B) (hp : p∈Icc (0:ℝ) 1)
    (hOI : Disjoint O I) (hcap : O.card+H≤ c) (hI : I.Nonempty)
    (hg : LocalGuard N H c ξ B reg O I b) (i : Fin N) :
    activeMean N H c ξ reg O I b y p ν i=
      if i∈O then 1 else if i∈I then
        (1-meanPrice N H c ξ reg O I b p ν/b i)/ξ else 0 := by
  have he : activeMean N H c ξ reg O I b y p ν i=
      ν.expect (fun z => if i∈O then 1 else if i∈I then
        (1-multiplier N H c ξ reg O I b y p z/b i)/ξ else 0) := by
    simp only [activeMean,mixture,FiniteLaw.prob_eq_expect,FiniteLaw.expect_finiteMix]
    apply ν.expect_congr
    intro z
    rw [←FiniteLaw.prob_eq_expect]
    rw [(implements N H c reg O I b y p hξ hξ1 hb hp hOI hcap hI hg z).2]
    simp [FocalCapacity.marginal,fixed,mixed,numericalBid,multiplier,TypicalHighPolicy.commonBid]
  rw [he]
  by_cases hO : i∈O
  · simp [hO,FiniteLaw.expect_const]
  · by_cases hI' : i∈I
    · simp only [if_neg hO,if_pos hI',div_eq_mul_inv]
      rw [FiniteLaw.expect_mul_const,FiniteLaw.expect_sub,FiniteLaw.expect_const,
        FiniteLaw.expect_mul_const,mean_multiplier _ _ _ _ _ _ _ _ _ _ _ hcap]
    · simp [hO,hI',FiniteLaw.expect_const]

theorem mixed_receipt (N H c : ℕ) {ξ B : ℝ} (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (y p : ℝ) (ν : FiniteLaw (Marks H))
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hb : ∀ i,b i∈Icc (1:ℝ) B) (hp : p∈Icc (0:ℝ) 1)
    (hOI : Disjoint O I) (hcap : O.card+H≤ c) (hI : I.Nonempty)
    (hg : LocalGuard N H c ξ B reg O I b) (i : Fin N) (hi : i∈I) :
    b i*(1-ξ*activeMean N H c ξ reg O I b y p ν i)=meanPrice N H c ξ reg O I b p ν := by
  have hn : i∉O := fun ho => (Finset.disjoint_left.mp hOI) ho hi
  rw [activeMean_formula _ _ _ _ _ _ _ _ _ _ hξ hξ1 hb hp hOI hcap hI hg i,
    if_neg hn,if_pos hi]
  have hbi : b i≠0 := ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (hb i).1)
  field_simp [hξ.ne',hbi]
  ring

def pair (N H0 H1 c : ℕ) (ξ : ℝ) (reg : Bool) (O0 O1 I : Finset (Fin N))
    (b : Fin N → ℝ) (y : ℝ) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    FocalResponse.UnitPair :=
  FocalResponse.focalPair ξ y (mixedReciprocalSum I b)
    (TypicalHighPolicy.meanMultiplier N H0 c ξ reg O0 I b ν0)
    (TypicalHighPolicy.meanMultiplier N H1 c ξ reg O1 I b ν1)

theorem pair_scalar_optimal (N H0 H1 c : ℕ) (ξ : ℝ) (reg : Bool)
    (O0 O1 I : Finset (Fin N)) (b : Fin N → ℝ) (y : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0< ξ) (hy : 0≤ y) (hW : 0< mixedReciprocalSum I b) :
    let p:=pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1
    FocalResponse.ScalarOptimal p.left
      (y*(1-ξ*p.right)-meanPrice N H1 c ξ reg O1 I b p.right ν1) ∧
    FocalResponse.ScalarOptimal p.right
      (y*(1-ξ*p.left)-meanPrice N H0 c ξ reg O0 I b p.left ν0) := by
  have hD : 0< FocalResponse.denominator ξ y (mixedReciprocalSum I b) := by
    unfold FocalResponse.denominator
    exact mul_pos hξ (add_pos_of_nonneg_of_pos hy (one_div_pos.mpr hW))
  have h := FocalResponse.focalPair_optimal ξ y (mixedReciprocalSum I b)
    (TypicalHighPolicy.meanMultiplier N H0 c ξ reg O0 I b ν0)
    (TypicalHighPolicy.meanMultiplier N H1 c ξ reg O1 I b ν1) hD
  simpa only [pair,meanPrice,FocalCapacity.crossed_focal_advantage,FocalResponse.denominator] using h

end FCAppendix.Affine.Tail04.FocalInsertion
