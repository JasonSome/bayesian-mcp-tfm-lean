import FCAppendix.Affine.Tail04.FocalInsertion

noncomputable section
namespace FCAppendix.Affine.Tail04.FocalInsertion
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon
open scoped BigOperators

variable {N H : ℕ} {R Rp Rm : ℝ}

def receipt (b : Fin N → ℝ) (y : ℝ) (q : Fin N → ℝ) (p ξ : ℝ)
    (row : Row H R Rp Rm) : Target N H → ℝ :=
  fun t => Option.elim t (y*(1-ξ*p)) (EqualPrivateUpper.receipt b q ξ row)

def PartialGuard (N H c : ℕ) (ξ R Rp : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) (ν : FiniteLaw (Marks H)) : Prop :=
  if reg then Rp≤ TypicalHighPolicy.meanMultiplier N H c ξ reg O I b ν
  else TypicalHighPolicy.meanMultiplier N H c ξ reg O I b ν+ξ/mixedReciprocalSum I b≤ R

def Threshold {α : Type*} [DecidableEq α] (c : ℕ) (r : α → ℝ) (S : Finset α) (τ : ℝ) : Prop :=
  S.card=c ∧ 0≤ τ ∧ (∀ i∈S,τ≤ r i) ∧ ∀ i∉S,r i≤ τ

lemma threshold_of_marginals {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (c : ℕ) (K : FiniteLaw (Finset α)) (hK : ExactCapacity.Implements p c K)
    (r : α → ℝ) (τ : ℝ) (hτ : 0≤ τ)
    (hlo : ∀ i,p i≠0 → τ≤ r i) (hhi : ∀ i,p i≠1 → r i≤ τ)
    (S : Finset α) (hS : K.mass S≠0) : Threshold c r S τ := by
  refine ⟨hK.1 S hS,hτ,?_,?_⟩
  · intro i hi
    have hp := FiniteLaw.marginal_pos_of_support_mem K S hS i hi
    rw [hK.2 i] at hp
    exact hlo i hp.ne'
  · intro i hi
    have hp := prob_pos_of_support_event K (fun T => i∉T) S hS hi
    rw [FiniteLaw.prob_compl,hK.2 i] at hp
    apply hhi i
    intro he
    rw [he] at hp
    linarith

lemma insertion_threshold {α : Type*} [Fintype α] [DecidableEq α]
    (ξ : ℝ) (hξ : 0< ξ) (c : ℕ) (fixed I : Finset α) (b : α → ℝ)
    (focal : α) (p : ℝ) (hp : p∈Icc (0:ℝ) 1)
    (hdis : Disjoint fixed I) (hf : focal∉fixed) (hi : focal∉I)
    (hW : 0< mixedReciprocalSum I b) (hb : ∀ i∈I,0< b i)
    (hΛ : ∀ i∈I,(1-ξ)*b i≤ FocalCapacity.multiplier ξ c fixed I b p ∧
      FocalCapacity.multiplier ξ c fixed I b p≤ b i)
    (r : α → ℝ) (τ : ℝ) (hτ : 0≤ τ)
    (hrfixed : ∀ i∈fixed,τ≤ r i) (hrmixed : ∀ i∈I,r i=τ)
    (hrexcluded : ∀ i,i∉fixed → i≠focal → i∉I → r i≤ τ)
    (hrfocal : FocalResponse.ScalarOptimal p (r focal-τ))
    (S : Finset α) (hS : (FocalCapacity.lottery ξ c fixed I b focal p).mass S≠0) :
    Threshold c r S τ := by
  have hK := FocalCapacity.lottery_implements ξ hξ c fixed I b focal p hp hdis hf hi hW hb hΛ
  have hscalar := FocalCapacity.scalar_support p (r focal-τ) hp hrfocal
  apply threshold_of_marginals _ c _ hK r τ hτ ?_ ?_ S hS
  · intro i hpi
    by_cases hfix : i∈fixed
    · exact hrfixed i hfix
    by_cases heq : i=focal
    · subst i
      have hp0 : p≠0 := by simpa [FocalCapacity.marginal,hf] using hpi
      exact sub_nonneg.mp (hscalar.1 hp0)
    by_cases hmix : i∈I
    · exact (hrmixed i hmix).ge
    · simp only [FocalCapacity.marginal,if_neg hfix,if_neg heq,if_neg hmix] at hpi
      exact (hpi rfl).elim
  · intro i hpi
    by_cases hfix : i∈fixed
    · simp only [FocalCapacity.marginal,if_pos hfix] at hpi
      exact (hpi rfl).elim
    by_cases heq : i=focal
    · subst i
      have hp1 : p≠1 := by simpa [FocalCapacity.marginal,hf] using hpi
      exact sub_nonpos.mp (hscalar.2 hp1)
    by_cases hmix : i∈I
    · exact (hrmixed i hmix).le
    · exact hrexcluded i hfix heq hmix

lemma meanPrice_bounds (N H c : ℕ) {ξ B : ℝ} (reg : Bool) (O I : Finset (Fin N))
    (b : Fin N → ℝ) (p : ℝ) (ν : FiniteLaw (Marks H))
    (hξ : 0≤ ξ) (hp : p∈Icc (0:ℝ) 1) (hW : 0< mixedReciprocalSum I b)
    (hcap : O.card+H≤ c) (hg : LocalGuard N H c ξ B reg O I b) :
    (1-ξ)*B≤ meanPrice N H c ξ reg O I b p ν ∧ meanPrice N H c ξ reg O I b p ν≤1 := by
  rw [←mean_multiplier N H c ξ reg O I b 0 p ν hcap]
  exact ⟨ν.const_le_expect (fun z => (localGuard_shift N H c reg O I b hξ hW hcap hg 0 p hp z).1),
    ν.expect_le_const (fun z => (localGuard_shift N H c reg O I b hξ hW hcap hg 0 p hp z).2)⟩

lemma partialGuard_shift (N H c : ℕ) {ξ R Rp : ℝ} (reg : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) (p : ℝ) (ν : FiniteLaw (Marks H))
    (hξ : 0≤ ξ) (hp : p∈Icc (0:ℝ) 1) (hW : 0< mixedReciprocalSum I b)
    (hg : PartialGuard N H c ξ R Rp reg O I b ν) :
    if reg then Rp≤ meanPrice N H c ξ reg O I b p ν
    else meanPrice N H c ξ reg O I b p ν≤ R := by
  have hs0 : 0≤ ξ*p/mixedReciprocalSum I b := div_nonneg (mul_nonneg hξ hp.1) hW.le
  have hs1 : ξ*p/mixedReciprocalSum I b≤ ξ/mixedReciprocalSum I b :=
    div_le_div_of_nonneg_right (by nlinarith [hp.2]) hW.le
  cases reg
  · simp only [PartialGuard,Bool.false_eq_true,if_false,meanPrice] at hg ⊢
    linarith
  · simp only [PartialGuard,if_true,meanPrice] at hg ⊢
    linarith

theorem physical_support_threshold (N H K c : ℕ) {ξ B R Rp Rm : ℝ}
    (reg : Bool) (I O P : Finset (Fin N)) (b : Fin N → ℝ) (y p pOther : ℝ)
    (ν : FiniteLaw (Marks K)) (row : Row H R Rp Rm)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hB : 1≤ B)
    (hb : ∀ i,b i∈Icc (1:ℝ) B) (hp : p∈Icc (0:ℝ) 1) (hpOther : pOther∈Icc (0:ℝ) 1)
    (_hRp : Rp<1) (hBRm : B< Rm)
    (hOP : Disjoint O P) (hOI : Disjoint O I) (hPI : Disjoint P I)
    (hcover : I∪(O∪P)=Finset.univ)
    (hOc : O.card+H≤ c) (hPc : P.card+K≤ c) (hI : I.Nonempty)
    (hlocal : LocalGuard N H c ξ B reg O I b)
    (hother : LocalGuard N K c ξ B reg P I b)
    (hpartial : PartialGuard N K c ξ R Rp reg P I b ν)
    (hscalar : FocalResponse.ScalarOptimal p
      (y*(1-ξ*pOther)-meanPrice N K c ξ reg P I b pOther ν))
    (S : Finset (Target N H))
    (hS : (law N H c ξ reg O I b y p (marks (signal row))).mass S≠0) :
    Threshold c
      (receipt b y (activeMean N K c ξ reg P I b y pOther ν) pOther ξ row) S
      (meanPrice N K c ξ reg P I b pOther ν) := by
  let z := marks (signal row)
  let q := activeMean N K c ξ reg P I b y pOther ν
  let τ := meanPrice N K c ξ reg P I b pOther ν
  have hW := mixedReciprocalSum_pos I b hI
    (fun i _ => (by norm_num : (0:ℝ)<1).trans_le (hb i).1)
  have hτ := meanPrice_bounds N K c reg P I b pOther ν hξ.le hpOther hW hPc hother
  have hpartial' := partialGuard_shift N K c reg P I b pOther ν hξ.le hpOther hW hpartial
  have hlocal' := localGuard_shift N H c reg O I b hξ.le hW hOc hlocal y p hp z
  have hqformula (i : Fin N) := activeMean_formula N K c reg P I b y pOther ν
    hξ hξ1 hb hpOther hPI hPc hI hother i
  apply insertion_threshold ξ hξ c (fixed N H reg O z) (mixed H I)
    (numericalBid H b y) none p hp
    (lift_disjoint (TypicalHighPolicy.fixed_disjoint reg O I z hOI))
    (none_not_mem_lift _) (none_not_mem_lift _) ?_ ?_ ?_
    (receipt b y q pOther ξ row) τ ?_ ?_ ?_ ?_ hscalar S hS
  · rw [reciprocal_sum];exact hW
  · intro i hi
    cases i with
    | none => exact ((none_not_mem_lift _) hi).elim
    | some i =>
      cases i with
      | inl i => exact (by norm_num : (0:ℝ)<1).trans_le (hb i).1
      | inr i => simp [mixed,activeLift] at hi
  · intro i hi
    cases i with
    | none => exact ((none_not_mem_lift _) hi).elim
    | some i =>
      cases i with
      | inl i =>
        exact ⟨(mul_le_mul_of_nonneg_left (hb i).2 (sub_nonneg.mpr hξ1)).trans hlocal'.1,
          hlocal'.2.trans (hb i).1⟩
      | inr i => simp [mixed,activeLift] at hi
  · exact (mul_nonneg (sub_nonneg.mpr hξ1) ((by norm_num : (0:ℝ)≤1).trans hB)).trans hτ.1
  · intro i hi
    cases i with
    | none => exact ((none_not_mem_lift _) hi).elim
    | some i =>
      cases i with
      | inl i =>
        have hiO : i∈O := by simpa [fixed] using hi
        have hiP : i∉P := fun hh => (Finset.disjoint_left.mp hOP) hiO hh
        have hiI : i∉I := fun hh => (Finset.disjoint_left.mp hOI) hiO hh
        have hqi : q i=0 := by simpa [q,hiP,hiI] using hqformula i
        simpa [receipt,EqualPrivateUpper.receipt,hqi] using hτ.2.trans (hb i).1
      | inr i =>
        have hi' : reg=false ∨ z i=true := by
          simpa [fixed,TypicalHighPolicy.fixed] using hi
        cases hrow : row i with
        | inl v =>
          simpa [receipt,EqualPrivateUpper.receipt,numericalEntry,hrow] using
            hτ.2.trans (hB.trans (hBRm.le.trans v.2))
        | inr v =>
          have hzi : z i=false := by simp [z,marks,signal,signalEntry,hrow,isUpper]
          have hreg : reg=false := hi'.resolve_right (by rw [hzi];decide)
          have hpR : τ≤ R := by simpa [hreg,τ] using hpartial'
          simpa [receipt,EqualPrivateUpper.receipt,numericalEntry,hrow] using hpR.trans v.2.1
  · intro i hi
    cases i with
    | none => exact ((none_not_mem_lift _) hi).elim
    | some i =>
      cases i with
      | inl i =>
        have hiI : i∈I := by simpa [mixed] using hi
        exact mixed_receipt N K c reg P I b y pOther ν hξ hξ1 hb hpOther hPI hPc hI hother i hiI
      | inr i => simp [mixed,activeLift] at hi
  · intro i hfix hfocal hmix
    cases i with
    | none => exact (hfocal rfl).elim
    | some i =>
      cases i with
      | inl i =>
        have hiO : i∉O := by simpa [fixed] using hfix
        have hiI : i∉I := by simpa [mixed] using hmix
        have hiP : i∈P := by
          have hu : i∈I∪(O∪P) := by rw [hcover];simp
          simpa [hiI,hiO] using hu
        have hqi : q i=1 := by simpa [q,hiP] using hqformula i
        have hsmall := (mul_le_mul_of_nonneg_left (hb i).2 (sub_nonneg.mpr hξ1)).trans hτ.1
        simpa [receipt,EqualPrivateUpper.receipt,hqi,mul_comm] using hsmall
      | inr i =>
        have hex : ¬(reg=false ∨ z i=true) := by
          simpa [fixed,TypicalHighPolicy.fixed] using hfix
        have hreg : reg=true := by cases reg <;> simp_all
        cases hrow : row i with
        | inl v =>
          have hz : z i=true := by simp [z,marks,signal,signalEntry,hrow,isUpper]
          exact (hex (Or.inr hz)).elim
        | inr v =>
          have hpR : Rp≤ τ := by simpa [hreg,τ] using hpartial'
          simpa [receipt,EqualPrivateUpper.receipt,numericalEntry,hrow] using v.2.2.trans hpR

theorem physical_support_optimal (N H K c : ℕ) {ξ B R Rp Rm : ℝ}
    (reg : Bool) (I O P : Finset (Fin N)) (b : Fin N → ℝ) (y p pOther : ℝ)
    (ν : FiniteLaw (Marks K)) (row : Row H R Rp Rm)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hB : 1≤ B)
    (hb : ∀ i,b i∈Icc (1:ℝ) B) (hp : p∈Icc (0:ℝ) 1) (hpOther : pOther∈Icc (0:ℝ) 1)
    (hRp : Rp<1) (hBRm : B< Rm)
    (hOP : Disjoint O P) (hOI : Disjoint O I) (hPI : Disjoint P I)
    (hcover : I∪(O∪P)=Finset.univ)
    (hOc : O.card+H≤ c) (hPc : P.card+K≤ c) (hI : I.Nonempty)
    (hlocal : LocalGuard N H c ξ B reg O I b)
    (hother : LocalGuard N K c ξ B reg P I b)
    (hpartial : PartialGuard N K c ξ R Rp reg P I b ν)
    (hscalar : FocalResponse.ScalarOptimal p
      (y*(1-ξ*pOther)-meanPrice N K c ξ reg P I b pOther ν))
    (S : Finset (Target N H))
    (hS : (law N H c ξ reg O I b y p (marks (signal row))).mass S≠0) :
    Finite.Optimal c
      (receipt b y (activeMean N K c ξ reg P I b y pOther ν) pOther ξ row) S := by
  obtain ⟨hc,hτ,hsel,homit⟩ := physical_support_threshold N H K c reg I O P b y p pOther ν row
    hξ hξ1 hB hb hp hpOther hRp hBRm hOP hOI hPI hcover hOc hPc hI hlocal hother hpartial hscalar S hS
  exact FocalCapacity.optimal_of_threshold c _ S _ hc hτ hsel homit

theorem pair_physical_support_optimal (N H0 H1 c : ℕ) {ξ B R Rp Rm : ℝ}
    (reg : Bool) (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ) (y : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hB : 1≤ B) (hb : ∀ i,b i∈Icc (1:ℝ) B) (hy : 0≤ y)
    (hRp : Rp<1) (hBRm : B< Rm)
    (hs : TypicalHighPolicy.Structural N H0 H1 c I O0 O1)
    (hg0 : LocalGuard N H0 c ξ B reg O0 I b)
    (hg1 : LocalGuard N H1 c ξ B reg O1 I b)
    (hp0 : PartialGuard N H0 c ξ R Rp reg O0 I b ν0)
    (hp1 : PartialGuard N H1 c ξ R Rp reg O1 I b ν1) :
    let p:=pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1
    (∀ row : Row H0 R Rp Rm,∀ S,
      (law N H0 c ξ reg O0 I b y p.left (marks (signal row))).mass S≠0 →
      Finite.Optimal c
        (receipt b y (activeMean N H1 c ξ reg O1 I b y p.right ν1) p.right ξ row) S) ∧
    (∀ row : Row H1 R Rp Rm,∀ S,
      (law N H1 c ξ reg O1 I b y p.right (marks (signal row))).mass S≠0 →
      Finite.Optimal c
        (receipt b y (activeMean N H0 c ξ reg O0 I b y p.left ν0) p.left ξ row) S) := by
  obtain ⟨hOO,hIO,hcover,hc0,hc1,hI⟩ := hs
  have hO0I : Disjoint O0 I := (hIO.mono_right Finset.subset_union_left).symm
  have hO1I : Disjoint O1 I := (hIO.mono_right Finset.subset_union_right).symm
  have hW := mixedReciprocalSum_pos I b hI
    (fun i _ => (by norm_num : (0:ℝ)<1).trans_le (hb i).1)
  have hsc := pair_scalar_optimal N H0 H1 c ξ reg O0 O1 I b y ν0 ν1 hξ hy hW
  dsimp only
  constructor
  · intro row S hS
    exact physical_support_optimal N H0 H1 c reg I O0 O1 b y _ _ ν1 row hξ hξ1 hB hb
      (pair _ _ _ _ _ _ _ _ _ _ _ _ _).left_mem (pair _ _ _ _ _ _ _ _ _ _ _ _ _).right_mem
      hRp hBRm hOO hO0I hO1I hcover hc0 hc1 hI hg0 hg1 hp1 hsc.1 S hS
  · intro row S hS
    have hc : I∪(O1∪O0)=Finset.univ := by simpa only [Finset.union_comm O1 O0] using hcover
    exact physical_support_optimal N H1 H0 c reg I O1 O0 b y _ _ ν0 row hξ hξ1 hB hb
      (pair _ _ _ _ _ _ _ _ _ _ _ _ _).right_mem (pair _ _ _ _ _ _ _ _ _ _ _ _ _).left_mem
      hRp hBRm hOO.symm hO1I hO0I hc hc1 hc0 hI hg1 hg0 hp0 hsc.2 S hS

end FCAppendix.Affine.Tail04.FocalInsertion
