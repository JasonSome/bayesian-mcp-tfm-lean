import FCAppendix.Affine.Tail04.LocalHighCommon
import FCAppendix.Affine.Tail04.TypicalPrivateReceipts
import FCAppendix.Existence.R01PayOnceRowIntegration

noncomputable section
namespace FCAppendix.Affine.Tail04.TypicalHighPolicy
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon

local instance (ι : Type*) : TopologicalSpace (Finset ι) := ⊥
local instance (ι : Type*) : DiscreteTopology (Finset ι) := ⟨rfl⟩
local instance (ι : Type*) : MeasurableSpace (Finset ι) := ⊤
local instance (ι : Type*) : BorelSpace (Finset ι) := ⟨borel_eq_top_of_discrete.symm⟩

def privateKept (N H : ℕ) (regime : Bool) (z : Marks H) : Finset (Target N H) :=
  if regime then (Finset.univ.filter fun k => z k=true).image Sum.inr else privateAll N H

def fixed (N H : ℕ) (regime : Bool) (O : Finset (Fin N)) (z : Marks H) :
    Finset (Target N H) := activeLift H O ∪ privateKept N H regime z

def commonBid {N : ℕ} (H : ℕ) (b : Fin N → ℝ) : Target N H → ℝ :=
  Sum.elim b (fun _ => 1)

def law (N H c : ℕ) (ξ : ℝ) (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (z : Marks H) : FiniteLaw (Finset (Target N H)) :=
  typicalLottery ξ c (fixed N H regime O z) (activeLift H I) (commonBid H b)

def multiplier (N H c : ℕ) (ξ : ℝ) (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (z : Marks H) : ℝ :=
  realizedMixedMultiplier ξ c (fixed N H regime O z) (activeLift H I) (commonBid H b)

def meanMultiplier (N H c : ℕ) (ξ : ℝ) (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (ν : FiniteLaw (Marks H)) : ℝ :=
  ν.expect (multiplier N H c ξ regime O I b)

def mixture (N H c : ℕ) (ξ : ℝ) (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (ν : FiniteLaw (Marks H)) : FiniteLaw (Finset (Target N H)) :=
  FiniteLaw.finiteMix ν (law N H c ξ regime O I b)

def activeMean (N H c : ℕ) (ξ : ℝ) (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (ν : FiniteLaw (Marks H)) (i : Fin N) : ℝ :=
  (mixture N H c ξ regime O I b ν).prob (fun S => Sum.inl i ∈ S)

@[simp] lemma inl_not_mem_privateKept {N H : ℕ} (regime : Bool) (z : Marks H) (i : Fin N) :
    Sum.inl i ∉ privateKept N H regime z := by cases regime <;> simp [privateKept]

@[simp] lemma inr_mem_privateKept {N H : ℕ} (regime : Bool) (z : Marks H) (k : Fin H) :
    Sum.inr k ∈ privateKept N H regime z ↔ (regime=false ∨ z k=true) := by
  cases regime <;> simp [privateKept]

@[simp] lemma inl_mem_fixed {N H : ℕ} (regime : Bool) (O : Finset (Fin N))
    (z : Marks H) (i : Fin N) : Sum.inl i ∈ fixed N H regime O z ↔ i ∈ O := by
  simp [fixed]

lemma kept_subset_private {N H : ℕ} (regime : Bool) (z : Marks H) :
    privateKept N H regime z ⊆ privateAll N H := by
  intro i hi
  cases i <;> simp_all

lemma fixed_card {N H : ℕ} (regime : Bool) (O : Finset (Fin N)) (z : Marks H) :
    (fixed N H regime O z).card=O.card+(if regime then upperCount z else H) := by
  have hd := (active_private_disjoint (H := H) O).mono_right (kept_subset_private regime z)
  rw [fixed,Finset.card_union_of_disjoint hd,activeLift_card]
  cases regime
  · simp [privateKept]
  · rw [privateKept,if_pos rfl,Finset.card_image_of_injective _ Sum.inr_injective]
    rfl

lemma fixed_card_le {N H : ℕ} (regime : Bool) (O : Finset (Fin N)) (z : Marks H) :
    (fixed N H regime O z).card ≤ O.card+H := by
  rw [fixed_card]
  cases regime
  · simp
  · have hz : upperCount z ≤ H := by
      simpa [upperCount] using Finset.card_le_univ (Finset.univ.filter fun k => z k=true)
    simp only [ite_true]
    omega

lemma fixed_disjoint {N H : ℕ} (regime : Bool) (O I : Finset (Fin N)) (z : Marks H)
    (hOI : Disjoint O I) : Disjoint (fixed N H regime O z) (activeLift H I) := by
  rw [fixed,Finset.disjoint_union_left]
  exact ⟨activeLift_disjoint hOI,
    ((active_private_disjoint (H := H) I).mono_right (kept_subset_private regime z)).symm⟩

lemma reciprocal_sum {N H : ℕ} (I : Finset (Fin N)) (b : Fin N → ℝ) :
    mixedReciprocalSum (activeLift H I) (commonBid H b)=mixedReciprocalSum I b := by
  unfold mixedReciprocalSum
  rw [sum_activeLift]
  rfl

lemma multiplier_formula {N H c : ℕ} (ξ : ℝ) (regime : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) (z : Marks H) :
    multiplier N H c ξ regime O I b z =
      ((I.card:ℝ)-ξ*(c-(O.card+(if regime then upperCount z else H)):ℕ)) /
        mixedReciprocalSum I b := by
  unfold multiplier realizedMixedMultiplier realizedResidual
  rw [activeLift_card,fixed_card,reciprocal_sum]

def Structural (N H0 H1 c : ℕ) (I O0 O1 : Finset (Fin N)) : Prop :=
  Disjoint O0 O1 ∧ Disjoint I (O0 ∪ O1) ∧ I ∪ (O0 ∪ O1)=Finset.univ ∧
    O0.card+H0 ≤ c ∧ O1.card+H1 ≤ c ∧ I.Nonempty

def LocalGuard (N H c : ℕ) (ξ B : ℝ) (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) : Prop :=
  ∀ z : Marks H, (1-ξ)*B ≤ multiplier N H c ξ regime O I b z ∧
    multiplier N H c ξ regime O I b z ≤ 1

def PartialGuard (N H0 H1 c : ℕ) (ξ R Rp : ℝ) (regime : Bool)
    (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) : Prop :=
  if regime then
    Rp ≤ meanMultiplier N H0 c ξ regime O0 I b ν0 ∧
      Rp ≤ meanMultiplier N H1 c ξ regime O1 I b ν1
  else
    meanMultiplier N H0 c ξ regime O0 I b ν0 ≤ R ∧
      meanMultiplier N H1 c ξ regime O1 I b ν1 ≤ R

def Guard (N H0 H1 c : ℕ) (ξ B R Rp : ℝ) (regime : Bool)
    (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) : Prop :=
  Structural N H0 H1 c I O0 O1 ∧ LocalGuard N H0 c ξ B regime O0 I b ∧
    LocalGuard N H1 c ξ B regime O1 I b ∧
    PartialGuard N H0 H1 c ξ R Rp regime I O0 O1 b ν0 ν1

theorem implements (N H c : ℕ) {ξ B : ℝ} (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hb : ∀ i, b i ∈ Icc (1:ℝ) B)
    (hOI : Disjoint O I) (hcap : O.card+H ≤ c) (hI : I.Nonempty)
    (hguard : LocalGuard N H c ξ B regime O I b) (z : Marks H) :
    ExactCapacity.Implements
      (typicalMarginal ξ c (fixed N H regime O z) (activeLift H I) (commonBid H b)) c
      (law N H c ξ regime O I b z) := by
  apply typicalLottery_implements hξ c _ _ _ (fixed_disjoint regime O I z hOI)
    ((fixed_card_le regime O z).trans hcap)
  · rw [reciprocal_sum]
    exact mixedReciprocalSum_pos I b hI (fun i _ => (by norm_num : (0:ℝ)<1).trans_le (hb i).1)
  · intro i hi
    cases i with
    | inl i => exact (by norm_num : (0:ℝ)<1).trans_le (hb i).1
    | inr k => simp at hi
  · intro i hi
    cases i with
    | inl i => exact (mul_le_mul_of_nonneg_left (hb i).2 (sub_nonneg.mpr hξ1)).trans (hguard z).1
    | inr k => simp at hi
  · intro i hi
    cases i with
    | inl i => exact (hguard z).2.trans (hb i).1
    | inr k => simp at hi

lemma measurable_law_mass (N H c : ℕ) (ξ : ℝ) (regime : Bool)
    (O I : Finset (Fin N)) (S : Finset (Target N H)) :
    Measurable (fun p : Marks H × (Fin N → ℝ) => (law N H c ξ regime O I p.2 p.1).mass S) := by
  apply measurable_from_prod_countable_right
  intro z
  exact (measurable_typicalLottery_mass ξ c (fixed N H regime O z) (activeLift H I) S).comp
    (measurable_pi_lambda _ fun i => by cases i <;> simp only [commonBid,Sum.elim_inl,Sum.elim_inr] <;> fun_prop)

theorem exists_sampler (N H c : ℕ) (ξ : ℝ) (regime : Bool) (O I : Finset (Fin N))
    (R Rp Rm : ℝ) :
    ∃ f : ((Fin N → ℝ) × Row H R Rp Rm) → unitInterval → Finset (Target N H),
      Measurable (Function.uncurry f) ∧
      (∀ b row u, 0 < (law N H c ξ regime O I b (marks (signal row))).mass (f (b,row) u)) ∧
      ∀ b row, volume.map (f (b,row)) =
        FiniteLaw.probabilityMeasure (law N H c ξ regime O I b (marks (signal row))) := by
  have hm (S : Finset (Target N H)) : Measurable
      (fun p : (Fin N → ℝ) × Row H R Rp Rm =>
        (law N H c ξ regime O I p.1 (marks (signal p.2))).mass S) := by
    simpa only [Function.comp_def] using (measurable_law_mass N H c ξ regime O I S).comp
      (show Measurable (fun p : (Fin N → ℝ) × Row H R Rp Rm => (marks (signal p.2),p.1)) from
        (continuous_marks.measurable.comp (continuous_signal.measurable.comp measurable_snd)).prodMk
          measurable_fst)
  obtain ⟨f,hf,hs,hlaw⟩ := Hybrid.exists_support_sampler
    (fun p : (Fin N → ℝ) × Row H R Rp Rm =>
      law N H c ξ regime O I p.1 (marks (signal p.2))) hm
  exact ⟨f,hf,(fun b row u => hs (b,row) u),(fun b row => hlaw (b,row))⟩

lemma mixture_marginal (N H c : ℕ) (ξ : ℝ) (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (ν : FiniteLaw (Marks H)) (i : Fin N) :
    activeMean N H c ξ regime O I b ν i =
      ν.expect (fun z => (law N H c ξ regime O I b z).prob (fun S => Sum.inl i ∈ S)) := by
  unfold activeMean mixture
  simp only [FiniteLaw.prob_eq_expect,FiniteLaw.expect_finiteMix]

theorem activeMean_bounds (N H c : ℕ) (ξ : ℝ) (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (ν : FiniteLaw (Marks H)) (i : Fin N) :
    activeMean N H c ξ regime O I b ν i ∈ Icc (0:ℝ) 1 :=
  ⟨FiniteLaw.prob_nonneg _ _,FiniteLaw.prob_le_one _ _⟩

lemma activeMean_formula (N H c : ℕ) {ξ B : ℝ} (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (ν : FiniteLaw (Marks H))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hb : ∀ i, b i ∈ Icc (1:ℝ) B)
    (hOI : Disjoint O I) (hcap : O.card+H ≤ c) (hI : I.Nonempty)
    (hguard : LocalGuard N H c ξ B regime O I b) (i : Fin N) :
    activeMean N H c ξ regime O I b ν i =
      if i ∈ O then 1 else if i ∈ I then
        ν.expect (fun z => (1-multiplier N H c ξ regime O I b z / b i)/ξ) else 0 := by
  rw [mixture_marginal]
  by_cases hiO : i ∈ O
  · rw [if_pos hiO,← FiniteLaw.expect_const ν 1]
    apply ν.expect_congr
    intro z
    rw [(implements N H c regime O I b hξ hξ1 hb hOI hcap hI hguard z).2]
    simp [typicalMarginal,hiO]
  · by_cases hiI : i ∈ I
    · rw [if_neg hiO,if_pos hiI]
      apply ν.expect_congr
      intro z
      rw [(implements N H c regime O I b hξ hξ1 hb hOI hcap hI hguard z).2]
      simp [typicalMarginal,realizedMixedMarginal,multiplier,hiO,hiI,commonBid]
    · rw [if_neg hiO,if_neg hiI,← FiniteLaw.expect_const ν 0]
      apply ν.expect_congr
      intro z
      rw [(implements N H c regime O I b hξ hξ1 hb hOI hcap hI hguard z).2]
      simp [typicalMarginal,hiO,hiI]

theorem mixed_receipt (N H c : ℕ) {ξ B : ℝ} (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (ν : FiniteLaw (Marks H))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hb : ∀ i, b i ∈ Icc (1:ℝ) B)
    (hOI : Disjoint O I) (hcap : O.card+H ≤ c) (hI : I.Nonempty)
    (hguard : LocalGuard N H c ξ B regime O I b) (i : Fin N) (hi : i ∈ I) :
    b i*(1-ξ*activeMean N H c ξ regime O I b ν i) =
      meanMultiplier N H c ξ regime O I b ν := by
  have hnot : i ∉ O := fun hiO => (Finset.disjoint_left.mp hOI) hiO hi
  rw [activeMean_formula N H c regime O I b ν hξ hξ1 hb hOI hcap hI hguard i,
    if_neg hnot,if_pos hi]
  rw [← FiniteLaw.expect_const ν 1,← FiniteLaw.expect_const_mul,
    ← FiniteLaw.expect_sub,← FiniteLaw.expect_const_mul]
  apply ν.expect_congr
  intro z
  have hbi : b i ≠ 0 := ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (hb i).1)
  simp only [FiniteLaw.expect_const]
  field_simp [ne_of_gt hξ,hbi]
  ring

lemma meanMultiplier_bounds (N H c : ℕ) {ξ B : ℝ} (regime : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) (ν : FiniteLaw (Marks H))
    (hguard : LocalGuard N H c ξ B regime O I b) :
    (1-ξ)*B ≤ meanMultiplier N H c ξ regime O I b ν ∧
      meanMultiplier N H c ξ regime O I b ν ≤ 1 :=
  ⟨ν.const_le_expect (fun z => (hguard z).1),ν.expect_le_const (fun z => (hguard z).2)⟩

theorem meanMultiplier_formula (N H c : ℕ) (ξ : ℝ) (regime : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) (ν : FiniteLaw (Marks H))
    (hcap : O.card+H ≤ c) :
    meanMultiplier N H c ξ regime O I b ν =
      ((I.card:ℝ)-ξ*((c:ℝ)-O.card-
        ν.expect (fun z => (((if regime then upperCount z else H):ℕ):ℝ)))) /
          mixedReciprocalSum I b := by
  have hh := expected_realizedMixedMultiplier ν ξ c (fixed N H regime O)
    (activeLift H I) (commonBid H b)
    (fun z => (fixed_card_le regime O z).trans hcap)
  change meanMultiplier N H c ξ regime O I b ν = _ at hh
  rw [activeLift_card,reciprocal_sum] at hh
  have he : ν.expect (fun z => ((fixed N H regime O z).card:ℝ)) =
      (O.card:ℝ)+ν.expect (fun z => (((if regime then upperCount z else H):ℕ):ℝ)) := by
    calc
      _ = ν.expect (fun z => (O.card:ℝ)+((if regime then upperCount z else H):ℕ)) := by
        apply ν.expect_congr
        intro z
        rw [fixed_card,Nat.cast_add]
      _ = _ := by rw [FiniteLaw.expect_add,FiniteLaw.expect_const]
  rw [he] at hh
  convert! hh using 1
  ring

theorem expected_upperCount (H : ℕ) (ν : FiniteLaw (Marks H)) (π : ℝ)
    (hπ : ∀ k, ν.prob (fun z => z k=true)=π) :
    ν.expect (fun z => (upperCount z:ℝ))=(H:ℝ)*π := by
  have hf (z : Marks H) : (upperCount z:ℝ) = ∑ k, if z k=true then (1:ℝ) else 0 := by
    simp [upperCount,← Finset.sum_boole]
  simp_rw [hf]
  rw [FiniteLaw.expect_finset_sum]
  simp_rw [← FiniteLaw.prob_eq_expect,hπ]
  simp

theorem support_optimal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ξ : ℝ} (hξ : 0 < ξ) (c : ℕ) (F I : Finset ι) (b ρ : ι → ℝ) (Λ : ℝ)
    (hdis : Disjoint F I) (hfixed : F.card ≤ c)
    (hW : 0 < mixedReciprocalSum I b) (hb : ∀ i ∈ I, 0 < b i)
    (hlo : ∀ i ∈ I, (1-ξ)*b i ≤ realizedMixedMultiplier ξ c F I b)
    (hhi : ∀ i ∈ I, realizedMixedMultiplier ξ c F I b ≤ b i)
    (hρ : ∀ i, 0 ≤ ρ i) (hF : ∀ i ∈ F, Λ ≤ ρ i)
    (hI : ∀ i ∈ I, ρ i=Λ) (hout : ∀ i ∉ F ∪ I, ρ i ≤ Λ)
    (S : Finset ι) (hS : (typicalLottery ξ c F I b).mass S ≠ 0) :
    Finite.Optimal c ρ S := by
  have hm := typicalLottery_implements hξ c F I b hdis hfixed hW hb hlo hhi
  have hc := hm.1 S hS
  have hsub := typicalLottery_support_subset hξ c F I b hdis hfixed hW hb hlo hhi S hS
  have hinc := typicalLottery_support_contains_fixed hξ c F I b hdis hfixed hW hb hlo hhi S hS
  apply Hybrid.optimal_of_order_slack c ρ S hc.le (fun i _ => hρ i)
  · intro i hi k hk
    have hkF : k ∉ F := fun h => hk (hinc h)
    have hsmall : ρ k ≤ Λ := by
      by_cases hkI : k ∈ I
      · exact (hI k hkI).le
      · exact hout k (by simp [Finset.mem_union,hkF,hkI])
    apply hsmall.trans
    rcases Finset.mem_union.mp (hsub hi) with hiF | hiI
    · exact hF i hiF
    · exact (hI i hiI).ge
  · intro h
    omega

theorem physical_support_optimal (N H K c : ℕ) {ξ B R Rp Rm : ℝ}
    (regime : Bool) (I O P : Finset (Fin N)) (b : Fin N → ℝ)
    (ν : FiniteLaw (Marks K)) (row : Row H R Rp Rm)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hB : 1 ≤ B)
    (hb : ∀ i, b i ∈ Icc (1:ℝ) B) (hR : 0 ≤ R) (_hRp : Rp < 1) (hBRm : B < Rm)
    (hOP : Disjoint O P) (hOI : Disjoint O I) (hPI : Disjoint P I)
    (hcover : I ∪ (O ∪ P)=Finset.univ)
    (hOc : O.card+H ≤ c) (hPc : P.card+K ≤ c) (hI : I.Nonempty)
    (hlocal : LocalGuard N H c ξ B regime O I b)
    (hother : LocalGuard N K c ξ B regime P I b)
    (hpartial : if regime then Rp ≤ meanMultiplier N K c ξ regime P I b ν
      else meanMultiplier N K c ξ regime P I b ν ≤ R)
    (S : Finset (Target N H))
    (hS : (law N H c ξ regime O I b (marks (signal row))).mass S ≠ 0) :
    Finite.Optimal c (receipt b (activeMean N K c ξ regime P I b ν) ξ row) S := by
  let z := marks (signal row)
  let q := activeMean N K c ξ regime P I b ν
  let L := meanMultiplier N K c ξ regime P I b ν
  have hL := meanMultiplier_bounds N K c regime P I b ν hother
  have hRm : 0 ≤ Rm := (le_trans (by norm_num) hB).trans hBRm.le
  have hq (i : Fin N) : q i ∈ Icc (0:ℝ) 1 := activeMean_bounds N K c ξ regime P I b ν i
  have hqformula (i : Fin N) :=
    activeMean_formula N K c regime P I b ν hξ hξ1 hb hPI hPc hI hother i
  have hW : 0 < mixedReciprocalSum (activeLift H I) (commonBid H b) := by
    rw [reciprocal_sum]
    exact mixedReciprocalSum_pos I b hI (fun i _ => (by norm_num : (0:ℝ)<1).trans_le (hb i).1)
  apply support_optimal (S := S) (hS := hS) hξ c (fixed N H regime O z) (activeLift H I) (commonBid H b)
    (receipt b q ξ row) L (fixed_disjoint regime O I z hOI)
    ((fixed_card_le regime O z).trans hOc) hW
  · intro i hi
    cases i with
    | inl i => exact (by norm_num : (0:ℝ)<1).trans_le (hb i).1
    | inr k => simp at hi
  · intro i hi
    cases i with
    | inl i => exact (mul_le_mul_of_nonneg_left (hb i).2 (sub_nonneg.mpr hξ1)).trans (hlocal z).1
    | inr k => simp at hi
  · intro i hi
    cases i with
    | inl i => exact (hlocal z).2.trans (hb i).1
    | inr k => simp at hi
  · exact receipt_nonneg b q ξ row ⟨hξ.le,hξ1⟩
      (fun i => (le_trans (by norm_num) (hb i).1)) hq hR hRm
  · intro i hi
    cases i with
    | inl i =>
      have hiO : i ∈ O := by simpa using hi
      have hiP : i ∉ P := fun hiP => (Finset.disjoint_left.mp hOP) hiO hiP
      have hiI : i ∉ I := fun hiI => (Finset.disjoint_left.mp hOI) hiO hiI
      have hqi : q i=0 := by simpa [q,hiP,hiI] using hqformula i
      simp only [receipt,hqi,mul_zero,sub_zero,mul_one]
      exact hL.2.trans (hb i).1
    | inr k =>
      have hk : regime=false ∨ z k=true := by simpa [fixed] using hi
      cases hrow : row k with
      | inl v =>
        simpa [receipt,numericalEntry,hrow] using hL.2.trans (hB.trans (hBRm.le.trans v.2))
      | inr v =>
        have hz : z k=false := by simp [z,marks,signal,signalEntry,hrow,isUpper]
        have hr : regime=false := hk.resolve_right (by rw [hz]; decide)
        have hpart : L ≤ R := by simpa [hr,L] using hpartial
        simpa [receipt,numericalEntry,hrow] using hpart.trans v.2.1
  · intro i hi
    cases i with
    | inl i =>
      exact mixed_receipt N K c regime P I b ν hξ hξ1 hb hPI hPc hI hother i
        (by simpa using hi)
    | inr k => simp at hi
  · intro i hi
    cases i with
    | inl i =>
      have hiO : i ∉ O := fun ho => hi (Finset.mem_union_left _ (by simpa using ho))
      have hiI : i ∉ I := fun hI => hi (Finset.mem_union_right _ (by simpa using hI))
      have hiP : i ∈ P := by
        have hcov : i ∈ I ∪ (O ∪ P) := by rw [hcover]; exact Finset.mem_univ i
        exact (Finset.mem_union.mp ((Finset.mem_union.mp hcov).resolve_left hiI)).resolve_left hiO
      have hqi : q i=1 := by simpa [q,hiP] using hqformula i
      calc
        receipt b q ξ row (Sum.inl i)=(1-ξ)*b i := by simp [receipt,hqi]; ring
        _ ≤ (1-ξ)*B := mul_le_mul_of_nonneg_left (hb i).2 (sub_nonneg.mpr hξ1)
        _ ≤ L := hL.1
    | inr k =>
      have hn : ¬ (regime=false ∨ z k=true) := by
        intro hk
        exact hi (Finset.mem_union_left _ (by simpa [fixed] using hk))
      have hr : regime=true := by cases regime <;> simp_all
      have hpart : Rp ≤ L := by simpa [hr,L] using hpartial
      cases hrow : row k with
      | inl v => exact (hn (Or.inr (by simp [z,marks,signal,signalEntry,hrow,isUpper]))).elim
      | inr v => simpa [receipt,numericalEntry,hrow] using v.2.2.trans hpart

def rowLaw (N H c : ℕ) (ξ : ℝ) (regime : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) {R Rp Rm : ℝ} (row : Row H R Rp Rm) :
    FiniteLaw (Finset (Target N H)) := law N H c ξ regime O I b (marks (signal row))

theorem original_active_mean (N H c : ℕ) (ξ : ℝ) (regime : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) {R Rp Rm : ℝ}
    (θ : Measure (Row H R Rp Rm)) [IsProbabilityMeasure θ]
    (ν : FiniteLaw (Marks H))
    (hν : θ.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν) (i : Fin N) :
    (∫ row, (rowLaw N H c ξ regime O I b row).prob (fun S => Sum.inl i ∈ S) ∂θ) =
      activeMean N H c ξ regime O I b ν i := by
  have hmeas : Measurable (fun row : Row H R Rp Rm => marks (signal row)) :=
    continuous_marks.measurable.comp continuous_signal.measurable
  have hfinite : FiniteLaw.ofMeasure θ (fun row => marks (signal row)) hmeas=ν :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure θ _ hmeas ν hν
  rw [mixture_marginal]
  rw [← hfinite,FiniteLaw.expect_ofMeasure]
  rfl

end FCAppendix.Affine.Tail04.TypicalHighPolicy
