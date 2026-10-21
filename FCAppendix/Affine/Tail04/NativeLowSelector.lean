import FCAppendix.Affine.Tail04.NativeLowCoordinates
import FCAppendix.Affine.Hybrid.NativePayoffIntegral

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLowSelector
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid LowBody NativeContinuation NativeMenuReports NativeLowCoordinates
open Observable.Regions
open scoped BigOperators

variable {N c : ℕ} (D : NativeLocalPolicy.Data (N+1) c)
  (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed)
  (hpolicy : Γ.policy=D.completedPolicy)

def pair (X : ClassifiedContext (N+1)) (s : Fin 2→ NativeLocalPolicy.Seed) :
    Finset (Fin (N+1))×Finset (Fin (N+1)) :=
  (NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 0 X (s 0).2,
    NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 1 X (s 1).2)

include hpolicy in
theorem low_accepts (i : Fin (N+1)) (a : JointAction 2) (hk : a.routeCount=2)
    (hb : a.bid≤ D.E.d) (ω : Sample (N+1) 2 NativeLocalPolicy.Seed)
    (hr : ∀ r : Fin N,MenuAction D.E (ω.1.1 (i.succAbove r)).1.2) (j : Fin 2) :
    Accepts Γ i a.bid j ω.1 ↔
      i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c j
        (rowContextAt i a.bid (rivalRow D.E i ω.1)) (ω.1.2 j).2 := by
  have hfull : ∀ l,l≠i→ MenuAction D.E (ω.1.1 l).1.2 := by
    intro l hl
    obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq hl
    exact hr r
  have ha : MenuAction D.E a := Or.inl ⟨Or.inl hb,hk⟩
  have ho := onMenu_deviation D i a ω ha hfull j
  have hobs := observe_deviated_of_mem i a ω j (by simp [hk,firstK_full_two])
  rw [hobs] at ho
  unfold Accepts
  rw [hpolicy,D.completed_on_menu j _ ho,D.policy_low_iff]
  · change i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c j
      (lowContext D.E j (presentList ω.1 i a.bid j)) (ω.1.2 j).2 ↔ _
    rw [low_context_exact D.E i ω.1 hr a.bid hb j]
  · rw [presentList_self]
    simp [Observable.Regions.localTag,hb]

include hpolicy in
theorem low_focal_count (i : Fin (N+1)) (a : JointAction 2) (hk : a.routeCount=2)
    (hb : a.bid≤ D.E.d) (ω : Sample (N+1) 2 NativeLocalPolicy.Seed)
    (hr : ∀ r : Fin N,MenuAction D.E (ω.1.1 (i.succAbove r)).1.2) :
    focalCount Γ i a ω=focalCopy
      (pair D (rowContextAt i a.bid (rivalRow D.E i ω.1)) ω.1.2) i := by
  let X := rowContextAt i a.bid (rivalRow D.E i ω.1)
  have h0 := low_accepts D Γ hpolicy i a hk hb ω hr 0
  have h1 := low_accepts D Γ hpolicy i a hk hb ω hr 1
  have hc := focalCount_val_eq Γ i a ω
  simp only [hk,firstK_full_two,Finset.mem_univ,ite_true,one_mul,Fin.sum_univ_two,
    h0,h1] at hc
  change ((focalCount Γ i a ω).val : ℝ) = _ at hc
  change ((focalCount Γ i a ω).val : ℝ) = (if i ∈ NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 0 X (ω.1.2 0).2 then 1 else 0) + (if i ∈ NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 1 X (ω.1.2 1).2 then 1 else 0) at hc
  apply Fin.ext
  change (focalCount Γ i a ω).val = (focalCopy (pair D X ω.1.2) i).val
  have hn : (focalCount Γ i a ω).val =
      (if i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 0 X (ω.1.2 0).2 then 1 else 0) +
      (if i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 1 X (ω.1.2 1).2 then 1 else 0) := by
    exact_mod_cast hc
  by_cases ha0 : i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 0 X (ω.1.2 0).2 <;>
    by_cases ha1 : i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c 1 X (ω.1.2 1).2 <;>
    simpa [pair,focalCopy,ha0,ha1] using hn

lemma affine_copy_payoff (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hcoef : (1-η)/2=D.ξ) (v b : ℝ) (B : Fin (N+1)→ℝ)
    (S : Finset (Fin (N+1))×Finset (Fin (N+1))) (i : Fin (N+1)) (hbi : B i=b) :
    userPayoff v b 0 (Schedule.affine 2 η hη0 hη1).charge
      (Schedule.once 2).charge (focalCopy S i).val=
      purePayoff (1-D.ξ) v B S i := by
  unfold purePayoff
  rw [hbi]
  generalize focalCopy S i=r
  have hr : r=0 ∨ r=1 ∨ r=2 := by omega
  have hcharge : 1+η=2*(1-D.ξ) := by linarith [hcoef]
  rcases hr with rfl | rfl | rfl
  · norm_num [userPayoff,Schedule.affine,successIndicator,hcharge]
    intro h
    exact False.elim ((by decide : (0 : Fin 3) ≠ 2) h)
  · norm_num [userPayoff,Schedule.affine,successIndicator,hcharge]
    intro h
    exact False.elim ((by decide : (1 : Fin 3) ≠ 2) h)
  · norm_num [userPayoff,Schedule.affine,successIndicator,hcharge]
    ring

include hpolicy in
theorem low_realized_payoff (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hcoef : (1-η)/2=D.ξ) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (hG : Γ.G=Schedule.once 2) (hg : Γ.g=0)
    (i : Fin (N+1)) (v : ℝ) (a : JointAction 2) (hk : a.routeCount=2)
    (hb : a.bid≤ D.E.d) (ω : Sample (N+1) 2 NativeLocalPolicy.Seed)
    (hr : ∀ r : Fin N,MenuAction D.E (ω.1.1 (i.succAbove r)).1.2) :
    nativeRealizedPayoff Γ i v a ω=
      purePayoff (1-D.ξ) v
        (fun l=> entryBid ((rowContextAt i a.bid (rivalRow D.E i ω.1)).1 l))
        (pair D (rowContextAt i a.bid (rivalRow D.E i ω.1)) ω.1.2) i := by
  unfold nativeRealizedPayoff
  rw [low_focal_count D Γ hpolicy i a hk hb ω hr,hA,hG,hg]
  exact affine_copy_payoff D η hη0 hη1 hcoef v a.bid _ _ i (by
    rw [rowContextAt_focal]
    rfl)

include hpolicy in
theorem low_duplicate_implies_underflow (i : Fin (N+1)) (a : JointAction 2)
    (hk : a.routeCount=2) (hb : a.bid≤ D.E.d)
    (ω : Sample (N+1) 2 NativeLocalPolicy.Seed)
    (hr : ∀ r : Fin N,MenuAction D.E (ω.1.1 (i.succAbove r)).1.2)
    (hdup : (focalCount Γ i a ω).val=2) :
    BothUnderflow c (fun r=>(rivalRow D.E i ω.1 r).1) := by
  let X := rowContextAt i a.bid (rivalRow D.E i ω.1)
  have hcopy : (focalCopy (pair D X ω.1.2) i).val=2 := by
    rwa [low_focal_count D Γ hpolicy i a hk hb ω hr] at hdup
  have hin : i∈(pair D X ω.1.2).1 ∧ i∈(pair D X ω.1.2).2 := by
    by_cases h0 : i∈(pair D X ω.1.2).1 <;>
      by_cases h1 : i∈(pair D X ω.1.2).2 <;>
      simp_all [focalCopy]
  have hpos (j : Fin 2) : 0< residual c j X := by
    have hs := NativeExactLow.select_feasible D.ξ D.xi_pos D.xi_lt_one c j X (ω.1.2 j).2
    have hm : i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c j X (ω.1.2 j).2 := by
      fin_cases j
      · exact hin.1
      · exact hin.2
    exact (Finset.card_pos.mpr ⟨i,hm⟩).trans_le hs.1
  have h0 := hpos 0
  have h1 := hpos 1
  simp only [X,rowContextAt,reindexContext,rowContext,NativeContinuation.residual,contextUpper,ite_true,if_neg (by decide : (1 : Fin 2) ≠ 0)] at h0 h1
  constructor
  · rw [sum_firstHigher]
    change classCount 1 (rivalRow D.E i ω.1)+classCount 2 (rivalRow D.E i ω.1)< c
    omega
  · rw [sum_secondHigher]
    change classCount 1 (rivalRow D.E i ω.1)+classCount 3 (rivalRow D.E i ω.1)< c
    omega

end FCAppendix.Affine.Tail04.NativeLowSelector
