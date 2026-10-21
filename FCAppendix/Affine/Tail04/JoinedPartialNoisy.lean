import FCAppendix.Affine.Tail04.AtypicalPartialNoisy
import FCAppendix.Affine.Tail04.JoinedHighPolicy
import FCAppendix.Affine.Tail04.OriginalCountSampling

noncomputable section
namespace FCAppendix.Affine.Tail04.JoinedPartialNoisy
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon JoinedHighPolicy

theorem typicalSampler_private (N H c : ℕ) {ξ B R Rp Rm : ℝ}
    (reg : Bool) (O I : Finset (Fin N)) (b : Fin N → ℝ)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hb : ∀ i, b i∈Icc (1:ℝ) B)
    (hOI : Disjoint O I) (hcap : O.card+H≤ c) (hI : I.Nonempty)
    (hguard : TypicalHighPolicy.LocalGuard N H c ξ B reg O I b)
    (row : Row H R Rp Rm) (j : Fin H) (price : Icc R Rp) (hj : row j=Sum.inr price)
    (u : unitInterval) :
    Sum.inr j∈typicalSampler N H c ξ R Rp Rm reg O I (b,row) u ↔ reg=false := by
  let μ := TypicalHighPolicy.law N H c ξ reg O I b (marks (signal row))
  let S := typicalSampler N H c ξ R Rp Rm reg O I (b,row) u
  have hS : μ.mass S≠0 := (typicalSampler_support N H c ξ R Rp Rm reg O I b row u).ne'
  have hm := (TypicalHighPolicy.implements N H c reg O I b hξ hξ1 hb hOI hcap hI
    hguard (marks (signal row))).2 (Sum.inr j)
  have hmark : marks (signal row) j=false := by simp [marks,signal,signalEntry,hj,isUpper]
  cases reg
  · have h1 : μ.prob (fun S => Sum.inr j∈S)=1 := by
      simpa [μ,typicalMarginal,TypicalHighPolicy.fixed,TypicalHighPolicy.privateKept] using hm
    exact iff_of_true (Hybrid.GuardedData.support_mem_of_marginal_one μ (Sum.inr j) h1 S hS) rfl
  · have h0 : μ.prob (fun S => Sum.inr j∈S)=0 := by
      simpa [μ,typicalMarginal,TypicalHighPolicy.fixed,TypicalHighPolicy.privateKept,hmark] using hm
    exact iff_of_false (Hybrid.GuardedData.support_mem_of_nonzero_marginal μ (Sum.inr j) h0 S hS)
      (by decide)

def owner {N : ℕ} (side : Bool) (s : Scenario N) : Finset (Fin N) :=
  if side then owner1 s else owner0 s

def unequalSide (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (side : Bool) :
    (Parameters N H0 R Rp B × Row (AllCountAtypical.ownCount H0 H1 side) R Rp Rm) →
      unitInterval → Finset (Target N (AllCountAtypical.ownCount H0 H1 side)) :=
  match side with
  | false => unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1
  | true => unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1

lemma unequalSide_eq (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (side : Bool)
    (p : Parameters N H0 R Rp B) (row : Row (AllCountAtypical.ownCount H0 H1 side) R Rp Rm)
    (u : unitInterval) :
    unequalSide N H0 H1 c ξ B R Rp Rm width ν0 ν1 side (p,row) u =
      if UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p then
        typicalSampler N (AllCountAtypical.ownCount H0 H1 side) c ξ R Rp Rm
          (regime p.1.1) (owner side p.1.1) (mixed p.1.1) (publicBids p,row) u
      else AllCountAtypical.select N H0 H1 c ξ (publicBids p) side row := by
  cases side <;> rfl

theorem unequalSide_private (N H0 H1 c : ℕ) {ξ B R Rp Rm width : ℝ}
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (side : Bool)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hw : 0< width)
    (p : Parameters N H0 R Rp B) (row : Row (AllCountAtypical.ownCount H0 H1 side) R Rp Rm)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (price : Icc R Rp)
    (hj : row j=Sum.inr price) (u : unitInterval) :
    (Sum.inr j∈unequalSide N H0 H1 c ξ B R Rp Rm width ν0 ν1 side (p,row) u) ↔
      if UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p then regime p.1.1=false
      else Sum.inr j∈AllCountAtypical.select N H0 H1 c ξ (publicBids p) side row := by
  rw [unequalSide_eq]
  by_cases hu : UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p
  · rw [if_pos hu,if_pos hu]
    have hg := useTypical_guard N H0 H1 c ξ B R Rp width ν0 ν1 hw p hu
    have hs := hg.1
    have hOI : Disjoint (owner side p.1.1) (mixed p.1.1) := by
      cases side
      · exact hs.2.1.symm.mono_left Finset.subset_union_left
      · exact hs.2.1.symm.mono_left Finset.subset_union_right
    have hcap : (owner side p.1.1).card+AllCountAtypical.ownCount H0 H1 side≤ c := by
      cases side
      · exact hs.2.2.2.1
      · exact hs.2.2.2.2.1
    have hgside : TypicalHighPolicy.LocalGuard N (AllCountAtypical.ownCount H0 H1 side)
        c ξ B (regime p.1.1) (owner side p.1.1) (mixed p.1.1) (publicBids p) := by
      cases side
      · exact hg.2.1
      · exact hg.2.2.1
    exact typicalSampler_private N _ c _ _ _ _ hξ hξ1 (fun i => (p.1.2 i).2)
      hOI hcap hs.2.2.2.2.2 hgside row j price hj u
  · rw [if_neg hu,if_neg hu]

theorem integral_strict_branch (w : unitInterval) (a b : ℝ) :
    (∫ u : unitInterval, if u< w then a else b)=(w:ℝ)*a+(1-(w:ℝ))*b := by
  have h := congrArg (fun μ : FiniteLaw Bool => μ.expect (fun z => if z then a else b))
    (strictBranchFlag_law w)
  rw [FiniteLaw.expect_ofMeasure,IndependentCounts.expect_bernoulli] at h
  simpa [strictBranchFlag,add_comm] using h

def setSeed {N H : ℕ} {R Rp B : ℝ} (p : Parameters N H R Rp B) (u : unitInterval) :
    Parameters N H R Rp B := (p.1,(p.2.1,u))

def weight (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) : unitInterval :=
  ⟨publicWeight N H0 H1 c ξ B R Rp width ν0 ν1 p,
    TypicalGuard.weight_bounds N H0 H1 c ξ B R Rp width (regime p.1.1)
      (mixed p.1.1) (owner0 p.1.1) (owner1 p.1.1) (publicBids p) ν0 ν1⟩

theorem actual_common_average (N H0 H1 c : ℕ) {ξ B R Rp Rm width : ℝ}
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (side : Bool)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hw : 0< width)
    (p : Parameters N H0 R Rp B) (row : Row (AllCountAtypical.ownCount H0 H1 side) R Rp Rm)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (price : Icc R Rp)
    (hj : row j=Sum.inr price) (privateSeed : unitInterval) :
    (∫ u : unitInterval, if Sum.inr j∈unequalSide N H0 H1 c ξ B R Rp Rm width ν0 ν1 side
        (setSeed p u,row) privateSeed then (1:ℝ) else 0)=
      (weight N H0 H1 c ξ B R Rp width ν0 ν1 p:ℝ)*(if regime p.1.1 then 0 else 1)+
      (1-(weight N H0 H1 c ξ B R Rp width ν0 ν1 p:ℝ))*
        (if Sum.inr j∈AllCountAtypical.select N H0 H1 c ξ (publicBids p) side row then 1 else 0) := by
  have he (u : unitInterval) :
      (if Sum.inr j∈unequalSide N H0 H1 c ξ B R Rp Rm width ν0 ν1 side
        (setSeed p u,row) privateSeed then (1:ℝ) else 0)=
      if u< weight N H0 H1 c ξ B R Rp width ν0 ν1 p then (if regime p.1.1 then 0 else 1)
      else (if Sum.inr j∈AllCountAtypical.select N H0 H1 c ξ (publicBids p) side row then 1 else 0) := by
    simp only [unequalSide_private N H0 H1 c ν0 ν1 side hξ hξ1 hw (setSeed p u)
      row j price hj privateSeed]
    change (if (if (u:ℝ)< publicWeight N H0 H1 c ξ B R Rp width ν0 ν1 p then
      regime p.1.1=false else _) then (1:ℝ) else 0)=_
    by_cases hu : u< weight N H0 H1 c ξ B R Rp width ν0 ν1 p
    · simp only [hu,ite_true]
      have hu' : (u:ℝ)< publicWeight N H0 H1 c ξ B R Rp width ν0 ν1 p := hu
      simp only [if_pos hu']
      cases regime p.1.1 <;> norm_num
    · simp only [hu,ite_false]
      have hu' : ¬(u:ℝ)< publicWeight N H0 H1 c ξ B R Rp width ν0 ν1 p := hu
      simp only [if_neg hu']
      rfl
  simp_rw [he]
  exact integral_strict_branch _ _ _

end FCAppendix.Affine.Tail04.JoinedPartialNoisy
