import FCAppendix.Affine.Tail04.LocalHighCommon
import FCAppendix.Affine.Tail04.AtypicalFinite

noncomputable section
namespace FCAppendix.Affine.Tail04.AllCountAtypical
open MeasureTheory Set Classical
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon AtypicalUnequal

local instance (ι : Type*) : TopologicalSpace (Finset ι) := ⊥
local instance (ι : Type*) : DiscreteTopology (Finset ι) := ⟨rfl⟩
local instance (ι : Type*) : MeasurableSpace (Finset ι) := ⊤
local instance (ι : Type*) : BorelSpace (Finset ι) := ⟨borel_eq_top_of_discrete.symm⟩

def ownCount (H0 H1 : ℕ) (j : Bool) : ℕ := if j then H1 else H0
def otherCount (H0 H1 : ℕ) (j : Bool) : ℕ := ownCount H0 H1 (!j)

lemma numerical_upper_ge {N H : ℕ} {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (ξ : ℝ) (row : Row H R Rp Rm)
    (i : Target N H) (hi : i ∈ upperPool N row) : Rm ≤ numericalBid b row i := by
  have hh := receipt_upper_ge b (fun _ => 0) ξ row i hi
  cases i <;> simpa [receipt,numericalBid] using hh

def fittingPair (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N → ℝ) :
    Finset (Fin N) × Finset (Fin N) :=
  if h : c-H0 ≤ N ∧ c-H1 ≤ N then
    let p := LowBody.CompleteInformation.selector (c-H0) (c-H1)
      (by simpa using h.1) (by simpa using h.2) (1-ξ) b
    (p.1.1,p.2.1)
  else (∅,∅)

def fittingActive (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N → ℝ) (j : Bool) :
    Finset (Fin N) := if j then (fittingPair N H0 H1 c ξ b).2
      else (fittingPair N H0 H1 c ξ b).1

def ownerPool (N c : ℕ) (b : Fin N → ℝ) : Finset (Fin N) :=
  if N ≤ 2*c then Finset.univ else topSelection Finset.univ (2*c) b

def ownerQuota (N H0 c : ℕ) : ℕ :=
  if N ≤ 2*c then overloadOwnerLeft N H0 c else c

def owners (N H0 c : ℕ) (b : Fin N → ℝ) (j : Bool) : Finset (Fin N) :=
  if j then splitRight (ownerPool N c b) (ownerQuota N H0 c)
    else splitLeft (ownerPool N c b) (ownerQuota N H0 c)

def whitelist (N H0 H1 c : ℕ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (row : Row (ownCount H0 H1 j) R Rp Rm) :
    Finset (Target N (ownCount H0 H1 j)) :=
  activeLift (ownCount H0 H1 j) (owners N H0 c b j) ∪
    if N ≤ 2*c then privateAll N (ownCount H0 H1 j) else upperPool N row

def select (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (row : Row (ownCount H0 H1 j) R Rp Rm) :
    Finset (Target N (ownCount H0 H1 j)) :=
  if EitherSlack N H0 H1 c then
    if N+ownCount H0 H1 j < c then Finset.univ
      else topSelection Finset.univ c (receipt b (fun _ => 1) ξ row)
  else if N+H0+H1 ≤ 2*c then
    activeLift (ownCount H0 H1 j) (fittingActive N H0 H1 c ξ b j) ∪
      privateAll N (ownCount H0 H1 j)
  else topSelection (whitelist N H0 H1 c b j row) c (numericalBid b row)

lemma fittingPair_cards (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N → ℝ)
    (h0 : c-H0 ≤ N) (h1 : c-H1 ≤ N) :
    (fittingPair N H0 H1 c ξ b).1.card=c-H0 ∧
      (fittingPair N H0 H1 c ξ b).2.card=c-H1 := by
  rw [fittingPair,dif_pos (show c-H0 ≤ N ∧ c-H1 ≤ N from ⟨h0,h1⟩)]
  exact ⟨(LowBody.CompleteInformation.selector (c-H0) (c-H1)
    (by simpa using h0) (by simpa using h1) (1-ξ) b).1.2,
    (LowBody.CompleteInformation.selector (c-H0) (c-H1)
    (by simpa using h0) (by simpa using h1) (1-ξ) b).2.2⟩

lemma fittingActive_card (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N → ℝ)
    (h0 : c-H0 ≤ N) (h1 : c-H1 ≤ N) (j : Bool) :
    (fittingActive N H0 H1 c ξ b j).card=c-ownCount H0 H1 j := by
  have hh := fittingPair_cards N H0 H1 c ξ b h0 h1
  cases j
  · simpa [fittingActive,ownCount] using hh.1
  · simpa [fittingActive,ownCount] using hh.2

theorem capacity (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (row : Row (ownCount H0 H1 j) R Rp Rm) :
    (select N H0 H1 c ξ b j row).card ≤ c := by
  unfold select
  split_ifs with hsl hown hfit
  · simpa [Fintype.card_sum] using hown.le
  · exact (topSelection_feasible _ _ _).1
  · have hn := nonslack_both N H0 H1 c hsl
    have hf := fitting_residual_counts N H0 H1 c hn.1 hn.2 hfit
    have hH : ownCount H0 H1 j ≤ c := by
      cases j
      · exact hf.1
      · exact hf.2.1
    rw [Finset.card_union_of_disjoint (active_private_disjoint _),activeLift_card,
      fittingActive_card N H0 H1 c ξ b hf.2.2.1 hf.2.2.2.1 j,privateAll_card]
    omega
  · exact (topSelection_feasible _ _ _).1

lemma measurable_fittingPair (N H0 H1 c : ℕ) (ξ : ℝ) :
    Measurable (fittingPair N H0 H1 c ξ) := by
  unfold fittingPair
  split_ifs with h
  · have hs := (LowBody.CompleteInformation.measurable_selector (ι := Fin N) (c-H0) (c-H1)
        (by simpa using h.1) (by simpa using h.2)).comp
        (show Measurable (fun b : Fin N → ℝ => (1-ξ,b)) from
          measurable_const.prodMk measurable_id)
    have hp : Measurable (fun p :
        LowBody.CompleteInformation.Choice (ι := Fin N) (c-H0) ×
        LowBody.CompleteInformation.Choice (ι := Fin N) (c-H1) => (p.1.val,p.2.val)) :=
      (measurable_subtype_coe.comp measurable_fst).prodMk
        (measurable_subtype_coe.comp measurable_snd)
    simpa only [Function.comp_def] using hp.comp hs
  · exact measurable_const

lemma measurable_fittingActive (N H0 H1 c : ℕ) (ξ : ℝ) (j : Bool) :
    Measurable (fun b => fittingActive N H0 H1 c ξ b j) := by
  cases j
  · exact measurable_fst.comp (measurable_fittingPair N H0 H1 c ξ)
  · exact measurable_snd.comp (measurable_fittingPair N H0 H1 c ξ)

lemma measurable_ownerPool (N c : ℕ) : Measurable (ownerPool N c) := by
  unfold ownerPool
  split_ifs
  · exact measurable_const
  · exact measurable_topSelection (2*c) (fun _ => Finset.univ) (fun b => b)
      measurable_const (fun i => measurable_pi_apply i)

lemma measurable_owners (N H0 c : ℕ) (j : Bool) :
    Measurable (fun b => owners N H0 c b j) := by
  exact (measurable_of_countable (fun A : Finset (Fin N) =>
    if j then splitRight A (ownerQuota N H0 c) else splitLeft A (ownerQuota N H0 c))).comp
      (measurable_ownerPool N c)

lemma measurable_whitelist (N H0 H1 c : ℕ) {R Rp Rm : ℝ} (j : Bool) :
    Measurable (fun z : (Fin N → ℝ) × Row (ownCount H0 H1 j) R Rp Rm =>
      whitelist N H0 H1 c z.1 j z.2) := by
  have ho : Measurable (fun z : (Fin N → ℝ) × Row (ownCount H0 H1 j) R Rp Rm =>
      activeLift (ownCount H0 H1 j) (owners N H0 c z.1 j)) := by
    simpa only [Function.comp_def] using
      (measurable_of_countable (activeLift (ownCount H0 H1 j))).comp
        ((measurable_owners N H0 c j).comp measurable_fst)
  have hp : Measurable (fun z : (Fin N → ℝ) × Row (ownCount H0 H1 j) R Rp Rm =>
      if N ≤ 2*c then privateAll N (ownCount H0 H1 j) else upperPool N z.2) := by
    split_ifs
    · exact measurable_const
    · exact continuous_upperPool.measurable.comp measurable_snd
  exact (measurable_of_countable (fun z : Finset (Target N (ownCount H0 H1 j)) ×
      Finset (Target N (ownCount H0 H1 j)) => z.1 ∪ z.2)).comp (ho.prodMk hp)

theorem measurable_select (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ} (j : Bool) :
    Measurable (fun z : (Fin N → ℝ) × Row (ownCount H0 H1 j) R Rp Rm =>
      select N H0 H1 c ξ z.1 j z.2) := by
  unfold select
  split_ifs with hsl hown hfit
  · exact measurable_const
  · apply measurable_topSelection c (fun _ => Finset.univ) _ measurable_const
    intro i
    exact (continuous_receipt ξ i).measurable.comp
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  · exact (measurable_of_countable (fun A : Finset (Fin N) =>
      activeLift (ownCount H0 H1 j) A ∪ privateAll N (ownCount H0 H1 j))).comp
      ((measurable_fittingActive N H0 H1 c ξ j).comp measurable_fst)
  · exact measurable_topSelection c _ _ (measurable_whitelist N H0 H1 c j)
      (fun i => (continuous_numericalBid i).measurable)

lemma fitting_active_optimal (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N → ℝ)
    (h0 : c-H0 ≤ N) (h1 : c-H1 ≤ N) (hξ : ξ ≤ 1) (hb : ∀ i, 0 ≤ b i)
    (j : Bool) :
    Finite.Optimal (c-ownCount H0 H1 j)
      (fun i => if i ∈ fittingActive N H0 H1 c ξ b (!j) then (1-ξ)*b i else b i)
      (fittingActive N H0 H1 c ξ b j) := by
  have hh := fitting_active_receipt_optimal (c-H0) (c-H1)
    (ι := Fin N) (by simpa using h0) (by simpa using h1)
    (1-ξ) (sub_nonneg.mpr hξ) b hb
  have ha0 : c ≤ N+H0 := by omega
  have ha1 : c ≤ N+H1 := by omega
  cases j
  · simpa [fittingActive,fittingPair,ha0,ha1,ownCount] using hh.1
  · simpa [fittingActive,fittingPair,ha0,ha1,ownCount] using hh.2

lemma fitting_cover (N H0 H1 c : ℕ) (ξ : ℝ) (b : Fin N → ℝ)
    (h0 : c-H0 ≤ N) (h1 : c-H1 ≤ N) (hslots : N ≤ (c-H0)+(c-H1))
    (hξ : ξ ≤ 1) (hb : ∀ i, 0 ≤ b i) (hfirst : ∀ i j, (1-ξ)*b j < b i)
    (j : Bool) :
    fittingActive N H0 H1 c ξ b j ∪ fittingActive N H0 H1 c ξ b (!j) = Finset.univ := by
  have hh := fitting_covers_all (c-H0) (c-H1)
    (ι := Fin N) (by simpa using h0) (by simpa using h1) (by simpa using hslots)
    (1-ξ) (sub_nonneg.mpr hξ) b hb hfirst
  have ha0 : c ≤ N+H0 := by omega
  have ha1 : c ≤ N+H1 := by omega
  cases j
  · simpa [fittingActive,fittingPair,ha0,ha1] using hh
  · simpa [fittingActive,fittingPair,ha0,ha1,Finset.union_comm] using hh

theorem fitting_full_optimal {N H : ℕ} (r c : ℕ) {R Rp Rm B ξ : ℝ}
    (b : Fin N → ℝ) (q : Fin N → ℝ) (row : Row H R Rp Rm)
    (S T : Finset (Fin N)) (hcard : S.card=r) (hcap : r+H=c)
    (hactive : Finite.Optimal r (fun i => if i ∈ T then (1-ξ)*b i else b i) S)
    (hcover : S ∪ T=Finset.univ) (hq : ∀ i, q i=if i ∈ T then 1 else 0)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hb : ∀ i, b i ∈ Icc (0:ℝ) B)
    (hR : 0 ≤ R) (hRRm : R ≤ Rm) (hgap : (1-ξ)*B ≤ R) :
    Finite.Optimal c (receipt b q ξ row) (activeLift H S ∪ privateAll N H) := by
  have hqb : ∀ i, q i ∈ Icc (0:ℝ) 1 := by
    intro i
    rw [hq i]
    split_ifs <;> norm_num
  have hnonneg := receipt_nonneg b q ξ row hξ (fun i => (hb i).1) hqb hR (hR.trans hRRm)
  apply fitting_private_union_optimal (activeAll N H) (privateAll N H) (activeLift H S)
    r c (receipt b q ξ row) R 0
    (activeLift_mono (Finset.subset_univ S)) (active_private_disjoint _)
    (by simpa using hcard) (by simpa using hcap)
  · have hl := lift_optimal (H := H) _ S hactive
    convert! hl using 1
    funext i
    cases i with
    | inl i => simp [activeAll,receipt,hq i]; split_ifs <;> ring
    | inr j => simp [activeAll]
  · exact hnonneg
  · exact hR
  · exact fun i hi => hnonneg i
  · intro i hi
    cases i with
    | inl i => simp at hi
    | inr j =>
      simpa only [receipt,numericalBid,Sum.elim_inr] using
        numerical_private_ge b row hRRm (Sum.inr j) (by simp [privateAll])
  · intro i hi hnot
    cases i with
    | inr j => simp [activeAll] at hi
    | inl i =>
      have hn : i ∉ S := by simpa using hnot
      have ht : i ∈ T := by
        have hu : i ∈ S ∪ T := by rw [hcover]; exact Finset.mem_univ i
        exact (Finset.mem_union.mp hu).resolve_left hn
      calc
        receipt b q ξ row (Sum.inl i) = (1-ξ)*b i := by simp [receipt,hq i,ht]; ring
        _ ≤ (1-ξ)*B := mul_le_mul_of_nonneg_left (hb i).2 (sub_nonneg.mpr hξ.2)
        _ ≤ R := hgap
  · intro i hi
    exact (hi (by rw [active_private_cover]; exact Finset.mem_univ i)).elim

lemma owners_partition (N H0 H1 c : ℕ) (b : Fin N → ℝ)
    (hn : ¬ EitherSlack N H0 H1 c) (hover : 2*c ≤ N+H0+H1)
    (hb : ∀ i, 0 < b i) (j : Bool) :
    Disjoint (owners N H0 c b j) (owners N H0 c b (!j)) ∧
    owners N H0 c b j ∪ owners N H0 c b (!j) = ownerPool N c b ∧
    (owners N H0 c b j).card ≤ c ∧
    (if N ≤ 2*c then c-ownCount H0 H1 j ≤ (owners N H0 c b j).card
      else (owners N H0 c b j).card=c) := by
  have hh := nonslack_both N H0 H1 c hn
  by_cases hN : N ≤ 2*c
  · have ho := overload_owner_partition (ι := Fin N) H0 H1 c
      (by simpa using hh.1) (by simpa using hh.2) (by simpa using hN) (by simpa using hover)
    cases j
    · simpa [owners,ownerPool,ownerQuota,hN,ownCount] using
        (show _ ∧ _ ∧ _ ∧ _ from ⟨ho.1,ho.2.1,ho.2.2.2.1,ho.2.2.1⟩)
    · simpa [owners,ownerPool,ownerQuota,hN,ownCount,Finset.union_comm] using
        (show _ ∧ _ ∧ _ ∧ _ from ⟨ho.1.symm,ho.2.1,ho.2.2.2.2.2,ho.2.2.2.2.1⟩)
  · have ho := top_two_capacity_owners (ι := Fin N) c (by simp; omega) b hb
    cases j
    · simpa [owners,ownerPool,ownerQuota,hN] using
        (show _ ∧ _ ∧ _ ∧ _ from ⟨ho.2.1,ho.2.2.1,ho.2.2.2.1.le,ho.2.2.2.1⟩)
    · simpa [owners,ownerPool,ownerQuota,hN,Finset.union_comm] using
        (show _ ∧ _ ∧ _ ∧ _ from ⟨ho.2.1.symm,ho.2.2.1,ho.2.2.2.2.1.le,ho.2.2.2.2.1⟩)

def OpponentBounds (N H0 H1 c : ℕ) (ξ : ℝ) (b q : Fin N → ℝ)
    (j : Bool) (e : ℝ) : Prop :=
  if EitherSlack N H0 H1 c then
    (¬ N+ownCount H0 H1 j < c → ∀ i, q i=1)
  else if N+H0+H1 ≤ 2*c then
    ∀ i, q i=if i ∈ fittingActive N H0 H1 c ξ b (!j) then 1 else 0
  else
    (∀ i ∈ owners N H0 c b j, q i=0) ∧
    (∀ i ∈ owners N H0 c b (!j), 1-e ≤ q i)

theorem optimal (N H0 H1 c : ℕ) {R Rp Rm B ξ : ℝ}
    (b q : Fin N → ℝ) (j : Bool) (row : Row (ownCount H0 H1 j) R Rp Rm) (e : ℝ)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hb : ∀ i, b i ∈ Icc (1:ℝ) B)
    (hB : 1 ≤ B)
    (hq : ∀ i, q i ∈ Icc (0:ℝ) 1)
    (hR : 0 < R) (hRRp : R ≤ Rp) (hRp : Rp < 1) (hBRm : B < Rm)
    (he : 0 ≤ e) (hrare : (1-ξ)*B+ξ*B*e ≤ R)
    (hfirst : (1-ξ)*B < 1)
    (hpost : OpponentBounds N H0 H1 c ξ b q j e) :
    Finite.Optimal c (receipt b q ξ row) (select N H0 H1 c ξ b j row) := by
  have hRm : 0 < Rm := ((by norm_num : (0:ℝ)<1).trans_le hB).trans hBRm
  have hRRm : R ≤ Rm := hRRp.trans (hRp.le.trans (hB.trans hBRm.le))
  have hnonneg := receipt_nonneg b q ξ row hξ (fun i => (le_trans (by norm_num) (hb i).1))
    hq hR.le hRm.le
  have hgap : (1-ξ)*B ≤ R := by
    have hxBe : 0 ≤ ξ*B*e := mul_nonneg (mul_nonneg hξ.1 (by linarith)) he
    linarith
  unfold select OpponentBounds at *
  split_ifs at hpost ⊢ with hsl hown hfit
  · exact univ_optimal c _ hown.le hnonneg
  · have heq : receipt b q ξ row = receipt b (fun _ => 1) ξ row := by
      funext i
      cases i with
      | inl i => simp [receipt,hpost hown i]
      | inr i => rfl
    rw [heq]
    have hh := topSelection_optimal (Finset.univ : Finset (Target N (ownCount H0 H1 j))) c
      (receipt b (fun _ => 1) ξ row)
    convert! hh using 1
    funext i
    simp only [topValue,Finset.mem_univ,if_true]
    exact (max_eq_left (by simpa [← heq] using hnonneg i)).symm
  · have hn := nonslack_both N H0 H1 c hsl
    have hf := fitting_residual_counts N H0 H1 c hn.1 hn.2 hfit
    have hH : ownCount H0 H1 j ≤ c := by
      cases j
      · exact hf.1
      · exact hf.2.1
    apply fitting_full_optimal (c-ownCount H0 H1 j) c b q row
      (fittingActive N H0 H1 c ξ b j) (fittingActive N H0 H1 c ξ b (!j))
      (fittingActive_card N H0 H1 c ξ b hf.2.2.1 hf.2.2.2.1 j) (by omega)
      (fitting_active_optimal N H0 H1 c ξ b hf.2.2.1 hf.2.2.2.1 hξ.2
        (fun i => (by linarith [(hb i).1])) j)
      (fitting_cover N H0 H1 c ξ b hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2 hξ.2
        (fun i => by linarith [(hb i).1]) (fun i k =>
          (mul_le_mul_of_nonneg_left (hb k).2 (sub_nonneg.mpr hξ.2)).trans_lt
            (hfirst.trans_le (hb i).1)) j)
      hpost hξ (fun i => ⟨by linarith [(hb i).1],(hb i).2⟩) hR.le hRRm hgap
  · have hp := owners_partition N H0 H1 c b hsl (by omega)
      (fun i => by linarith [(hb i).1]) j
    have hownReceipt : ∀ i ∈ activeLift (ownCount H0 H1 j) (owners N H0 c b j) ∪
        privateAll N (ownCount H0 H1 j),
        receipt b q ξ row i=numericalBid b row i := by
      intro i hi
      cases i with
      | inl i =>
        have hiO : i ∈ owners N H0 c b j := by simpa using hi
        simp [receipt,numericalBid,hpost.1 i hiO]
      | inr i => rfl
    have hnonowner : ∀ i ∈ owners N H0 c b (!j), receipt b q ξ row (Sum.inl i) ≤ R := by
      intro i hi
      exact (nonowner_receipt_bound (b i) B ξ e (q i)
        (by linarith [(hb i).1]) (hb i).2 hξ.1 hξ.2 he (hpost.2 i hi)).trans hrare
    by_cases hN : N ≤ 2*c
    · simp only [whitelist,if_pos hN]
      apply topSelection_receipt_optimal _ c (numericalBid b row) (receipt b q ξ row)
      · rw [Finset.card_union_of_disjoint (active_private_disjoint _),activeLift_card,privateAll_card]
        have ho := hp.2.2.2
        rw [if_pos hN] at ho
        omega
      · intro i hi
        rcases Finset.mem_union.mp hi with hiO | hiP
        · cases i with
          | inl i => exact (by norm_num : (0:ℝ)<1).trans_le (hb i).1
          | inr i => simp at hiO
        · exact hR.trans_le (numerical_private_ge b row hRRm i hiP)
      · exact hnonneg
      · exact hownReceipt
      · intro i hi k hk
        have hbi : R ≤ numericalBid b row i := by
          rcases Finset.mem_union.mp hi with hiO | hiP
          · cases i with
            | inl i => exact hRRp.trans (hRp.le.trans (hb i).1)
            | inr i => simp at hiO
          · exact numerical_private_ge b row hRRm i hiP
        cases k with
        | inr k => exact (hk (by simp)).elim
        | inl k =>
          have hkO : k ∉ owners N H0 c b j := by simpa using hk
          have hkp : k ∈ owners N H0 c b j ∪ owners N H0 c b (!j) := by
            rw [hp.2.1,ownerPool,if_pos hN]
            exact Finset.mem_univ k
          exact (hnonowner k ((Finset.mem_union.mp hkp).resolve_left hkO)).trans hbi
    · simp only [whitelist,if_neg hN]
      have hOcard : (owners N H0 c b j).card=c := by
        simpa [hN] using hp.2.2.2
      have hpO : owners N H0 c b j ⊆ ownerPool N c b := by
        rw [← hp.2.1]
        exact Finset.subset_union_left
      suffices hopt : Finite.Optimal c (receipt b q ξ row)
          (ownerPrioritySelection (activeLift (ownCount H0 H1 j) (owners N H0 c b j))
            (upperPool N row) ∅ c (numericalBid b row)) by
        simpa only [ownerPrioritySelection,Finset.union_empty] using hopt
      apply top_two_local_receipt_optimal (activeAll N (ownCount H0 H1 j))
        (activeLift _ (ownerPool N c b)) (activeLift _ (owners N H0 c b j)) (upperPool N row)
        c (numericalBid b row) (receipt b q ξ row)
      · exact activeLift_mono (Finset.subset_univ _)
      · exact activeLift_mono hpO
      · simpa using hOcard
      · intro i hi
        cases i with
        | inl i => exact (hb i).1
        | inr i => simp at hi
      · intro i hi
        exact hB.trans (hBRm.le.trans (numerical_upper_ge b ξ row i hi))
      · intro i hi k hk hnot
        cases i with
        | inr i => simp at hi
        | inl i =>
          cases k with
          | inr k => simp [activeAll] at hk
          | inl k =>
            exact topSelection_order Finset.univ (2*c) b
              (fun l _ => by linarith [(hb l).1]) i k
              (by simpa [ownerPool,hN] using hi) (Finset.mem_univ k)
              (by simpa [ownerPool,hN] using hnot)
      · intro i hi k hk
        have hiR := numerical_upper_ge b ξ row i hi
        cases k with
        | inr k => simp [activeAll] at hk
        | inl k => exact (hb k).2.trans (hBRm.le.trans hiR)
      · exact hnonneg
      · intro i hi
        exact hownReceipt i ((Finset.mem_union.mp hi).elim
          (Finset.mem_union_left _) (fun hi => Finset.mem_union_right _ (upperPool_subset_private row hi)))
      · intro i hi hn
        cases i with
        | inr i => simp at hi
        | inl i =>
          have hiP : i ∈ ownerPool N c b := by simpa using hi
          have hiO : i ∉ owners N H0 c b j := by simpa using hn
          rw [← hp.2.1] at hiP
          exact (hnonowner i ((Finset.mem_union.mp hiP).resolve_left hiO)).trans
            (hRRp.trans hRp.le)
      · intro i hi hn
        cases i with
        | inr i => simp [activeAll] at hi
        | inl i =>
          exact mul_le_of_le_one_right (by linarith [(hb i).1])
            (by nlinarith [mul_nonneg hξ.1 (hq i).1])
      · intro i hi
        cases i with
        | inl i => exact (hi (by simp [activeAll])).elim
        | inr i =>
          have hn : Sum.inr i ∉ upperPool N row := fun hn => hi (Finset.mem_union_right _ hn)
          exact (private_nonupper_le b row _ (by simp) hn).trans hRp.le

end FCAppendix.Affine.Tail04.AllCountAtypical
