import FCAppendix.Affine.Tail04.UnusedPublicLaw
import FCAppendix.Affine.Tail04.UnusedMeanPrices
import FCAppendix.Affine.Tail04.NativeWeightedFlagBound

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedPublicPrices
open MeasureTheory ProbabilityTheory Set Classical
open PublicScenario EqualPrivateSignal LocalHighCommon JoinedHighPolicy
open NativeTypicalCount MenuError WeightedFlagBound UnusedPublicLaw
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

def price0 (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (b : Fin A→ℝ) (s : Scenario A) : ℝ :=
  meanMixedPrice Q.ξ Q.c (owner0 s).card
    (privateMean H.1 (regime s) (Q.marksLaw H.1)) (mixed s) b

def price1 (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (b : Fin A→ℝ) (s : Scenario A) : ℝ :=
  meanMixedPrice Q.ξ Q.c (owner1 s).card
    (privateMean H.2 (regime s) (Q.marksLaw H.2)) (mixed s) b

def StrongSafe (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a : ℝ) (b : Fin A→ℝ) (s : Scenario A) : Prop :=
  Safe Q A H B B0 R Rp width γ b s ∧
    |privateMean H.2 (regime s) (Q.marksLaw H.2)-
      privateMean H.1 (regime s) (Q.marksLaw H.1)|≤(A-(mixed s).card:ℕ) ∧
    price0 Q A H b s≤1-Q.ξ/2-a ∧ price1 Q A H b s≤1-Q.ξ/2-a

def Crossed (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a y : ℝ) (b : Fin A→ℝ) (s : Scenario A) : Prop :=
  StrongSafe Q A H B B0 R Rp width γ a b s ∧
    BetweenPrices (price0 Q A H b s) y (price1 Q A H b s)

lemma actual_price (A H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin A)) (b : Fin A→ℝ) (ν : FiniteLaw (Marks H))
    (hcap : O.card+H≤ c) :
    TypicalHighPolicy.meanMultiplier A H c ξ reg O I b ν=
      meanMixedPrice ξ c O.card (privateMean H reg ν) I b := by
  rw [TypicalGuardStatistics.actual_meanMultiplier,
    TypicalGuardEndpoints.meanMultiplier_eq_lambda H c O.card I.card ξ reg ν _ hcap]
  unfold TypicalGuardEndpoints.lambda meanMixedPrice
  congr 1
  ring

lemma owner_cards (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ) (reg : Bool)
    (target : Fin A) (flags : Fin A→ Bool) (AB : Finset (Fin A)×Finset (Fin A))
    (hAB : (Hybrid.ownerDivision (forcedExclusiveSet target flags)
      (PublicScenario.ownerQuota Q A H reg (target,flags))).mass AB≠0) :
    AB.1.card=(countParameters A H.1 H.2 Q.c Q.ξ reg
      (Q.marksLaw H.1) (Q.marksLaw H.2)).owner0 (targetMixedSet target flags).card ∧
    AB.2.card=(countParameters A H.1 H.2 Q.c Q.ξ reg
      (Q.marksLaw H.1) (Q.marksLaw H.2)).owner1 (targetMixedSet target flags).card := by
  obtain ⟨hsub,h0,h1,_,_⟩:=Hybrid.ownerDivision_support
    (forcedExclusiveSet_nonempty target flags) (PublicScenario.ownerQuota_le Q A H reg (target,flags)) AB.1 AB.2 hAB
  refine ⟨h0,?_⟩
  rw [h1,Finset.card_sdiff_of_subset hsub,h0,OriginalOwnerCount.exclusive_card]
  rfl

theorem output_crossed (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a y : ℝ) (b : Fin A→ℝ) (hb : ∀ j,1≤ b j)
    (reg : Bool) (target : Fin A) (flags : Fin A→ Bool)
    (AB : Finset (Fin A)×Finset (Fin A))
    (hAB : (Hybrid.ownerDivision (forcedExclusiveSet target flags)
      (PublicScenario.ownerQuota Q A H reg (target,flags))).mass AB≠0)
    (hg : Crossed Q A H B B0 R Rp width γ a y b (outputScenario reg ((target,flags),AB))) :
    GuardedIntermediate Q.ξ a y Q.c
      (privateMean H.1 reg (Q.marksLaw H.1)) (privateMean H.2 reg (Q.marksLaw H.2))
      b (forceExclusive target flags) := by
  let I:=targetMixedSet target flags
  let P:=countParameters A H.1 H.2 Q.c Q.ξ reg (Q.marksLaw H.1) (Q.marksLaw H.2)
  have hcards:=owner_cards Q A H reg target flags AB hAB
  have hbalance : |P.privateMean1-P.privateMean0|≤(A-I.card:ℕ) := hg.1.2.1
  have hIle : I.card≤A := by
    simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_univ I
  have hbalance' : |P.privateMean1-P.privateMean0|≤(P.N:ℝ)-(I.card:ℝ) := by
    change |P.privateMean1-P.privateMean0|≤(A:ℝ)-(I.card:ℝ)
    simpa only [Nat.cast_sub hIle] using hbalance
  have h0 : AB.1.card=firstOwnerCount A P.privateMean0 P.privateMean1 (forceExclusive target flags) := by
    rw [hcards.1,P.owner0_eq_nearest I.card hbalance']
    rfl
  have h1 : AB.2.card=secondOwnerCount A P.privateMean0 P.privateMean1 (forceExclusive target flags) := by
    rw [hcards.2,TypicalCountParameters.owner1,P.owner0_eq_nearest I.card hbalance']
    rfl
  have hI : I.Nonempty := hg.1.1.1.1.2.2.2.2.2
  have hW : 0< mixedReciprocalSum I b := mixedReciprocalSum_pos I b hI
    (fun j _ => (by norm_num : (0:ℝ)<1).trans_le (hb j))
  have hp0 : price0 Q A H b (outputScenario reg ((target,flags),AB))=
      meanMixedPrice Q.ξ Q.c (firstOwnerCount A P.privateMean0 P.privateMean1
        (forceExclusive target flags)) P.privateMean0 I b := by
    simp only [price0,outputScenario,owner0,regime,mixed,h0]
    rfl
  have hp1 : price1 Q A H b (outputScenario reg ((target,flags),AB))=
      meanMixedPrice Q.ξ Q.c (secondOwnerCount A P.privateMean0 P.privateMean1
        (forceExclusive target flags)) P.privateMean1 I b := by
    simp only [price1,outputScenario,owner1,regime,mixed,h1]
    rfl
  dsimp only [P,countParameters,I] at hp0 hp1 hbalance
  simp only [GuardedIntermediate,Fintype.card_fin]
  exact ⟨hW,hbalance,by simpa only [hp0] using! hg.1.2.2.1,
    by simpa only [hp1] using! hg.1.2.2.2,by simpa only [hp0,hp1] using! hg.2⟩

theorem crossed_probability (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a y : ℝ) (b : Fin A→ℝ)
    (J : Finset (Fin A)) (hJ : J.Nonempty) {epsilon : ℝ}
    (heps : 0< epsilon) (heps' : epsilon<1/2)
    (hp : ∀ reg j,j∈J → epsilon≤ sourceFlagProb (PublicScenario.e0 Q reg) Q.B0 b j)
    (hp' : ∀ reg j,j∈J → sourceFlagProb (PublicScenario.e0 Q reg) Q.B0 b j≤1-epsilon)
    (hξ0 : 0≤ Q.ξ) (hξ2 : Q.ξ≤2) (hy : 0≤ y) (ha : 0< a) (hb : ∀ j,1≤ b j)
    (r rWide : ℕ) (hcover : Q.ξ<(r:ℝ)*a) (hwidth : (r:ℝ)*a+2≤(rWide:ℝ)*a) :
    (scenarioLaw Q A H b).prob (Crossed Q A H B B0 R Rp width γ a y b)≤
      2/(epsilon*(J.card:ℝ))+(rWide:ℝ)*Real.sqrt (2/(epsilon*(J.card:ℝ)+1)) := by
  have hA : 0< A := by obtain ⟨j,_⟩:=hJ;exact Nat.zero_lt_of_lt j.isLt
  letI : Nonempty (Fin A):=⟨⟨0,hA⟩⟩
  let K:=2/(epsilon*(J.card:ℝ))+(rWide:ℝ)*Real.sqrt (2/(epsilon*(J.card:ℝ)+1))
  rw [FiniteLaw.prob_eq_expect,scenario_expect Q A hA H b]
  apply FiniteLaw.expect_le_const_of_support
  intro reg _
  have hfinite:=guarded_intermediate_probability b (sourceFlagProb (PublicScenario.e0 Q reg) Q.B0 b)
    (sourceFlagProb_nonneg _ _ b) (sourceFlagProb_le_one _ _ b) J hJ heps heps'
    (hp reg) (hp' reg) hξ0 hξ2 hy ha hb Q.c
    (privateMean H.1 reg (Q.marksLaw H.1)) (privateMean H.2 reg (Q.marksLaw H.2)) r rWide hcover hwidth
  rw [FiniteLaw.prob_eq_expect,rankForcedFlagLaw_expect] at hfinite
  apply le_trans ?_ hfinite
  apply FiniteLaw.expect_mono
  intro target
  apply FiniteLaw.expect_mono
  intro flags
  apply FiniteLaw.expect_le_const_of_support
  intro AB hAB
  by_cases hg : Crossed Q A H B B0 R Rp width γ a y b (outputScenario reg ((target,flags),AB))
  · have hh:=output_crossed Q A H B B0 R Rp width γ a y b hb reg target flags AB hAB hg
    simp only [if_pos hg,if_pos hh]
    exact le_rfl
  · simp only [if_neg hg]
    split_ifs <;> norm_num

end FCAppendix.Affine.Tail04.UnusedPublicPrices
