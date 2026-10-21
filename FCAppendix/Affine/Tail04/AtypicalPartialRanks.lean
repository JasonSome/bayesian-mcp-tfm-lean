import FCAppendix.Affine.Tail04.AllCountAtypical
import FCAppendix.Affine.Tail04.AllNoiseFiniteSelector

noncomputable section
namespace FCAppendix.Affine.Tail04.AtypicalPartialRanks
open MeasureTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon AtypicalUnequal AllCountAtypical
open scoped BigOperators

def list {N H : ℕ} (O : Finset (Fin N)) (K : Finset (Fin H)) : Finset (Target N H) :=
  activeLift H O ∪ K.image Sum.inr

theorem list_disjoint {N H : ℕ} (O : Finset (Fin N)) (K : Finset (Fin H)) :
    Disjoint (activeLift H O) (K.image Sum.inr) := by
  apply Finset.disjoint_left.mpr
  intro q hq hk
  cases q <;> simp_all [activeLift]

theorem higher_card {N H : ℕ} (O : Finset (Fin N)) (K : Finset (Fin H))
    (b : Fin N → ℝ) (r : Fin H → ℝ) (price : ℝ) :
    ((list O K).filter (fun q => price < Sum.elim b r q)).card =
      (O.filter (fun i => price < b i)).card+(K.filter (fun j => price < r j)).card := by
  have he : (list O K).filter (fun q => price < Sum.elim b r q) =
      activeLift H (O.filter (fun i => price < b i)) ∪
        (K.filter (fun j => price < r j)).image Sum.inr := by
    ext q
    cases q <;> simp [list,activeLift]
  rw [he,Finset.card_union_of_disjoint (list_disjoint _ _),activeLift_card,
    Finset.card_image_of_injective _ Sum.inr_injective]

theorem private_top_iff {N H : ℕ} (O : Finset (Fin N)) (K : Finset (Fin H))
    (c : ℕ) (b : Fin N → ℝ) (r : Fin H → ℝ) (j : Fin H) (hj : j ∈ K)
    (hb : ∀ i ∈ O, 0 ≤ b i) (hr : ∀ k ∈ K, 0 ≤ r k) (hrj : 0 < r j)
    (hactive : ∀ i ∈ O, b i ≠ r j) (hprivate : ∀ k ∈ K, k ≠ j → r k ≠ r j) :
    Sum.inr j ∈ topSelection (list O K) c (Sum.elim b r) ↔
      (O.filter (fun i => r j < b i)).card+(K.filter (fun k => r j < r k)).card < c := by
  have hm : Sum.inr j ∈ list O K := by simp [list,hj]
  have hnon : ∀ q ∈ list O K, 0 ≤ Sum.elim b r q := by
    intro q hq
    cases q with
    | inl i => exact hb i (by simpa [list] using hq)
    | inr k => exact hr k (by simpa [list] using hq)
  have hno : ∀ q ∈ list O K, q ≠ Sum.inr j → Sum.elim b r q ≠ r j := by
    intro q hq hqj
    cases q with
    | inl i => exact hactive i (by simpa [list] using hq)
    | inr k => exact hprivate k (by simpa [list] using hq) (fun hk => hqj (congrArg Sum.inr hk))
  have he := topSelection_iff_strict_rank (list O K) c (Sum.elim b r) hnon
    (Sum.inr j) hm hrj hno
  simpa only [Sum.elim_inr,higher_card] using he

def privateHigher {H : ℕ} {R Rp Rm : ℝ} (row : Row H R Rp Rm) (price : ℝ) : ℕ :=
  (Finset.univ.filter (fun k : Fin H => price < numericalEntry (row k))).card

def partialRule (N H0 H1 c : ℕ) {R Rp Rm : ℝ} (b : Fin N → ℝ)
    (side : Bool) (row : Row (ownCount H0 H1 side) R Rp Rm) (price : ℝ) : Prop :=
  if EitherSlack N H0 H1 c then
    if N+ownCount H0 H1 side < c then True else privateHigher row price < c
  else if N+H0+H1 ≤ 2*c then True
  else if N ≤ 2*c then (owners N H0 c b side).card+privateHigher row price < c else False

theorem selected_partial_iff (N H0 H1 c : ℕ) {ξ B R Rp Rm : ℝ}
    (side : Bool) (b : Fin N → ℝ) (row : Row (ownCount H0 H1 side) R Rp Rm)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hb : ∀ i, b i ∈ Icc (1:ℝ) B)
    (hR : 0 < R) (hRRm : R ≤ Rm) (hRp : Rp < 1) (hgap : (1-ξ)*B < R)
    (j : Fin (ownCount H0 H1 side)) (price : Icc R Rp) (hj : row j=Sum.inr price)
    (hno : ∀ k, k≠j → numericalEntry (row k) ≠ (price:ℝ)) :
    Sum.inr j ∈ AllCountAtypical.select N H0 H1 c ξ b side row ↔
      partialRule N H0 H1 c b side row price := by
  let r : Fin (ownCount H0 H1 side) → ℝ := fun k => numericalEntry (row k)
  have hr : ∀ k, 0 ≤ r k := by
    intro k
    cases he : row k with
    | inl v => exact (hR.le.trans hRRm).trans (by simp only [r,he,numericalEntry]; exact v.2)
    | inr v => exact hR.le.trans (by simpa [r,he,numericalEntry] using v.2.1)
  have hrj : r j=(price:ℝ) := by simp [r,hj,numericalEntry]
  have hprice : 0 < (price:ℝ) := hR.trans_le price.2.1
  have hprivate : ∀ k ∈ (Finset.univ : Finset (Fin (ownCount H0 H1 side))),
      k≠j → r k ≠ r j := by
    intro k _ hk
    rw [hrj]
    exact hno k hk
  have hlist : list (Finset.univ : Finset (Fin N))
      (Finset.univ : Finset (Fin (ownCount H0 H1 side)))=Finset.univ :=
    active_private_cover N (ownCount H0 H1 side)
  unfold AllCountAtypical.select partialRule
  split_ifs with hsl hown hfit hN
  · simp
  · have hkb (i : Fin N) : (1-ξ)*b i < (price:ℝ) :=
      ((mul_le_mul_of_nonneg_left (hb i).2 (sub_nonneg.mpr hξ.2)).trans_lt hgap).trans_le price.2.1
    have hn (i : Fin N) : 0 ≤ (1-ξ)*b i :=
      mul_nonneg (sub_nonneg.mpr hξ.2) ((by norm_num : (0:ℝ)≤1).trans (hb i).1)
    have he := private_top_iff (Finset.univ : Finset (Fin N)) Finset.univ c
      (fun i => (1-ξ)*b i) r j (Finset.mem_univ j) (fun i _ => hn i)
      (fun k _ => hr k) (by rwa [hrj]) (fun i _ => by rw [hrj]; exact (hkb i).ne) hprivate
    have hempty : (Finset.univ.filter (fun i : Fin N => (price:ℝ)<(1-ξ)*b i))=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _
      exact not_lt.mpr (hkb i).le
    have hrec : receipt b (fun _ => 1) ξ row=Sum.elim (fun i => (1-ξ)*b i) r := by
      funext q
      cases q
      · simp [receipt,r]
        ring
      · simp [receipt,r]
    rw [hlist,hrj,hempty,Finset.card_empty,zero_add] at he
    simpa only [hrec,privateHigher,r] using he
  · simp
  · have hab (i : Fin N) : (price:ℝ)< b i :=
      (price.2.2.trans_lt hRp).trans_le (hb i).1
    have he := private_top_iff (owners N H0 c b side) Finset.univ c b r j
      (Finset.mem_univ j) (fun i _ => (by norm_num : (0:ℝ)≤1).trans (hb i).1)
      (fun k _ => hr k) (by rwa [hrj]) (fun i _ => by rw [hrj]; exact (hab i).ne') hprivate
    have hall : (owners N H0 c b side).filter (fun i => (price:ℝ)< b i)=owners N H0 c b side :=
      Finset.filter_true_of_mem (fun i _ => hab i)
    rw [hrj,hall] at he
    simpa only [whitelist,hN,ite_true,list,privateAll,numericalBid,r,privateHigher] using he
  · have hn : Sum.inr j ∉ whitelist N H0 H1 c b side row := by
      simp [whitelist,hN,upperPool,signal,signalEntry,hj,isUpper]
    constructor
    · intro hi
      exact hn ((topSelection_feasible _ _ _).2 hi)
    · exact False.elim

theorem partialRule_congr_bids (N H0 H1 c : ℕ) {R Rp Rm : ℝ}
    (b a : Fin N → ℝ) (side : Bool)
    (row : Row (ownCount H0 H1 side) R Rp Rm) (price : ℝ) :
    partialRule N H0 H1 c b side row price ↔ partialRule N H0 H1 c a side row price := by
  unfold partialRule
  split_ifs with hsl hown hfit hN
  · rfl
  · rfl
  · rfl
  · simp [owners,ownerPool,hN]
  · rfl

end FCAppendix.Affine.Tail04.AtypicalPartialRanks
