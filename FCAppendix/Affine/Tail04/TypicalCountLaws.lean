import FCAppendix.Affine.Tail04.TypicalPrivateReceipts
import FCAppendix.Affine.Tail04.FlagAtomPrimitives

noncomputable section
namespace FCAppendix.Affine.Tail04
open Set
open scoped BigOperators
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def boolPairCount (z : Bool × Bool) : Fin 3 :=
  ⟨(if z.1 then 1 else 0)+(if z.2 then 1 else 0), by
    rcases z with ⟨a,b⟩
    cases a <;> cases b <;> norm_num⟩

def acceptsSet (i : ι) (S : Finset ι) : Bool := decide (i ∈ S)

def selectionPairCount (i : ι) (z : Finset ι × Finset ι) : Fin 3 :=
  boolPairCount (acceptsSet i z.1,acceptsSet i z.2)

def twoSelectionCountLaw (left right : FiniteLaw (Finset ι)) (i : ι) : CountLaw 2 :=
  (left.prod right).map (selectionPairCount i)

def twoCoinCountLaw (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : CountLaw 2 :=
  ((IndependentCounts.bernoulli p hp0 hp1).prod
    (IndependentCounts.bernoulli q hq0 hq1)).map boolPairCount

theorem twoSelectionCountLaw_eq (left right : FiniteLaw (Finset ι)) (i : ι) :
    twoSelectionCountLaw left right i =
      twoCoinCountLaw (left.prob (fun S => i ∈ S)) (right.prob (fun S => i ∈ S))
        (left.prob_nonneg _) (left.prob_le_one _) (right.prob_nonneg _) (right.prob_le_one _) := by
  have he : twoSelectionCountLaw left right i =
      ((left.map (acceptsSet i)).prod (right.map (acceptsSet i))).map boolPairCount := by
    apply FiniteLaw.ext_expect
    intro f
    simp only [twoSelectionCountLaw,FiniteLaw.expect_map,FiniteLaw.expect_prod]
    rfl
  rw [he,IndependentCounts.accept_law,IndependentCounts.accept_law]
  simp only [IndependentCounts.acceptance,acceptsSet,decide_eq_true_eq]
  rfl

theorem twoCoinCountLaw_expect (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f : Fin 3 → ℝ) :
    (twoCoinCountLaw p q hp0 hp1 hq0 hq1).expect f =
      (1-p)*(1-q)*f 0+(p*(1-q)+(1-p)*q)*f 1+p*q*f 2 := by
  simp only [twoCoinCountLaw,FiniteLaw.expect_map,FiniteLaw.expect_prod,
    IndependentCounts.expect_bernoulli]
  change (1-p)*((1-q)*f 0+q*f 1)+p*((1-q)*f 1+q*f 2)=_
  ring

@[simp] theorem twoCoinCountLaw_zero (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (twoCoinCountLaw p q hp0 hp1 hq0 hq1).mass 0=(1-p)*(1-q) := by
  rw [← FiniteLaw.expect_singleton, twoCoinCountLaw_expect]
  norm_num [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,
    show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide]

@[simp] theorem twoCoinCountLaw_one (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (twoCoinCountLaw p q hp0 hp1 hq0 hq1).mass 1=p*(1-q)+(1-p)*q := by
  rw [← FiniteLaw.expect_singleton, twoCoinCountLaw_expect]
  norm_num [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,
    show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide]

@[simp] theorem twoCoinCountLaw_two (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (twoCoinCountLaw p q hp0 hp1 hq0 hq1).mass 2=p*q := by
  rw [← FiniteLaw.expect_singleton, twoCoinCountLaw_expect]
  norm_num [show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,
    show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide]

theorem twoSelectionCountLaw_moments (left right : FiniteLaw (Finset ι)) (i : ι) :
    let p := left.prob (fun S => i ∈ S)
    let q := right.prob (fun S => i ∈ S)
    (twoSelectionCountLaw left right i).success=p+q-p*q ∧
      (twoSelectionCountLaw left right i).load=p+q ∧
      (twoSelectionCountLaw left right i).duplicates=p*q := by
  dsimp only
  rw [twoSelectionCountLaw_eq]
  have hs : (twoCoinCountLaw (left.prob (fun S => i ∈ S)) (right.prob (fun S => i ∈ S))
      (left.prob_nonneg _) (left.prob_le_one _) (right.prob_nonneg _) (right.prob_le_one _)).success =
        left.prob (fun S => i ∈ S)+right.prob (fun S => i ∈ S)-
          left.prob (fun S => i ∈ S)*right.prob (fun S => i ∈ S) := by
    rw [CountLaw.success,twoCoinCountLaw_expect]
    norm_num [successIndicator]
    ring
  have hl : (twoCoinCountLaw (left.prob (fun S => i ∈ S)) (right.prob (fun S => i ∈ S))
      (left.prob_nonneg _) (left.prob_le_one _) (right.prob_nonneg _) (right.prob_le_one _)).load =
        left.prob (fun S => i ∈ S)+right.prob (fun S => i ∈ S) := by
    rw [CountLaw.load,twoCoinCountLaw_expect]
    norm_num
    ring
  refine ⟨hs,hl,?_⟩
  rw [CountLaw.duplicates,hl,hs]
  ring

theorem twoSelectionCountLaw_affine_utility (left right : FiniteLaw (Finset ι))
    (i : ι) (v bi eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    let p := left.prob (fun S => i ∈ S)
    let q := right.prob (fun S => i ∈ S)
    (twoSelectionCountLaw left right i).utility v bi 0
      (Schedule.affine 2 eta heta0 heta1) (Schedule.once 2) =
        (v-bi)*(p+q-p*q)-eta*bi*p*q := by
  dsimp only
  rw [CountLaw.utility_eq,CountLaw.charge_affine]
  obtain ⟨hs,_,hd⟩ := twoSelectionCountLaw_moments left right i
  rw [hs,hd]
  ring

theorem actual_exclusive_minus_mixed (left right : FiniteLaw (Finset ι)) (i : ι)
    (eta v bi : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    CountLaw.utility (FiniteLaw.dirac (1 : Fin 3)) v bi 0
        (Schedule.affine 2 eta heta0 heta1) (Schedule.once 2) -
      (twoSelectionCountLaw left right i).utility v bi 0
        (Schedule.affine 2 eta heta0 heta1) (Schedule.once 2) =
      twoMixedFavoredGain v bi eta
        (left.prob (fun S => i ∈ S)) (right.prob (fun S => i ∈ S)) := by
  rw [twoSelectionCountLaw_affine_utility]
  simp only [CountLaw.utility,FiniteLaw.expect_dirac,userPayoff,Schedule.affine,
    Schedule.once,successIndicator]
  norm_num
  unfold twoMixedFavoredGain
  ring

theorem twoSelectionCountLaw_exclusive (left right : FiniteLaw (Finset ι)) (i : ι)
    (hleft : left.prob (fun S => i ∈ S)=1) (hright : right.prob (fun S => i ∈ S)=0) :
    twoSelectionCountLaw left right i=FiniteLaw.dirac 1 := by
  apply FiniteLaw.ext_expect
  intro f
  rw [twoSelectionCountLaw_eq,twoCoinCountLaw_expect,hleft,hright,FiniteLaw.expect_dirac]
  ring

theorem twoSelectionCountLaw_exclusive_right (left right : FiniteLaw (Finset ι)) (i : ι)
    (hleft : left.prob (fun S => i ∈ S)=0) (hright : right.prob (fun S => i ∈ S)=1) :
    twoSelectionCountLaw left right i=FiniteLaw.dirac 1 := by
  apply FiniteLaw.ext_expect
  intro f
  rw [twoSelectionCountLaw_eq,twoCoinCountLaw_expect,hleft,hright,FiniteLaw.expect_dirac]
  ring

theorem privateTypicalMixture_marginal (mu : FiniteLaw Ω) {xi : ℝ} (hxi : 0 < xi)
    (c : ℕ) (fixed : Ω → Finset ι) (I : Finset ι) (b : ι → ℝ)
    (hdis : ∀ omega, Disjoint (fixed omega) I)
    (hfixed : ∀ omega, (fixed omega).card ≤ c)
    (hW : 0 < mixedReciprocalSum I b) (hb : ∀ i ∈ I, 0 < b i)
    (hlo : ∀ omega i, i ∈ I →
      (1-xi)*b i ≤ realizedMixedMultiplier xi c (fixed omega) I b)
    (hhi : ∀ omega i, i ∈ I →
      realizedMixedMultiplier xi c (fixed omega) I b ≤ b i) (i : ι) :
    (privateTypicalMixture mu xi c fixed I b).prob (fun S => i ∈ S) =
      mu.expect (fun omega => typicalMarginal xi c (fixed omega) I b i) := by
  rw [privateTypicalMixture,FiniteLaw.prob_eq_expect,FiniteLaw.expect_finiteMix]
  apply mu.expect_congr
  intro omega
  rw [← FiniteLaw.prob_eq_expect]
  exact (typicalLottery_implements hxi c (fixed omega) I b
    (hdis omega) (hfixed omega) hW hb (hlo omega) (hhi omega)).2 i

end FCAppendix.Affine.Tail04
