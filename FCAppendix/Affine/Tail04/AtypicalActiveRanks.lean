import FCAppendix.Affine.Tail04.AtypicalPartialRanks

noncomputable section
namespace FCAppendix.Affine.Tail04.AtypicalActiveRanks
open MeasureTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon AtypicalUnequal AllCountAtypical
open AtypicalPartialRanks
open scoped BigOperators

lemma active_top_iff {N H : ℕ} (O : Finset (Fin N)) (K : Finset (Fin H))
    (c : ℕ) (b : Fin N → ℝ) (r : Fin H → ℝ) (i : Fin N)
    (hb : ∀ j∈O, 0≤ b j) (hr : ∀ k∈K, 0≤ r k) (hbi : 0< b i)
    (hactive : ∀ j∈O, j≠i → b j≠b i) (hprivate : ∀ k∈K, r k≠b i) :
    Sum.inl i∈topSelection (list O K) c (Sum.elim b r) ↔
      i∈O ∧ (O.filter (fun j => b i< b j)).card+(K.filter (fun k => b i< r k)).card< c := by
  by_cases hi : i∈O
  · have hm : Sum.inl i∈list O K := by simp [list,hi]
    have hnon : ∀ q∈list O K, 0≤ Sum.elim b r q := by
      intro q hq
      cases q with
      | inl j => exact hb j (by simpa [list] using hq)
      | inr k => exact hr k (by simpa [list] using hq)
    have hno : ∀ q∈list O K, q≠Sum.inl i → Sum.elim b r q≠b i := by
      intro q hq hqi
      cases q with
      | inl j => exact hactive j (by simpa [list] using hq) (fun hj => hqi (congrArg Sum.inl hj))
      | inr k => exact hprivate k (by simpa [list] using hq)
    have hh := topSelection_iff_strict_rank (list O K) c (Sum.elim b r) hnon
      (Sum.inl i) hm hbi hno
    simpa only [Sum.elim_inl,higher_card,hi,true_and] using hh
  · have hm : Sum.inl i∉list O K := by simp [list,hi]
    exact iff_of_false (fun hh => hm ((topSelection_feasible _ _ _).2 hh)) (by simp [hi])

def activeRule (N H0 H1 c : ℕ) (ξ : ℝ) (side : Bool) (b : Fin N → ℝ)
    (upperCount : ℕ) (i : Fin N) : Prop :=
  if EitherSlack N H0 H1 c then
    if N+ownCount H0 H1 side< c then True
    else ownCount H0 H1 side+(Finset.univ.filter fun k => b i< b k).card< c
  else if N+H0+H1≤2*c then i∈fittingActive N H0 H1 c ξ b side
  else i∈owners N H0 c b side ∧
    upperCount+((owners N H0 c b side).filter fun k => b i< b k).card< c

lemma row_nonnegative {H : ℕ} {R Rp Rm : ℝ} (hR : 0≤ R) (hRRm : R≤ Rm)
    (row : Row H R Rp Rm) (k : Fin H) : 0≤ numericalEntry (row k) := by
  cases hk : row k with
  | inl b => exact hR.trans (hRRm.trans (by simp only [numericalEntry]; exact b.2))
  | inr b => exact hR.trans (by simpa [hk,numericalEntry] using b.2.1)

lemma row_ge_R {H : ℕ} {R Rp Rm : ℝ} (hRRm : R≤ Rm)
    (row : Row H R Rp Rm) (k : Fin H) : R≤ numericalEntry (row k) := by
  cases hk : row k with
  | inl b => exact hRRm.trans (by simp only [numericalEntry]; exact b.2)
  | inr b => simpa [hk,numericalEntry] using b.2.1

lemma numerical_above_active_iff_upper {H : ℕ} {R Rp Rm t : ℝ}
    (row : Row H R Rp Rm) (ht : Rp< t) (hfloor : t< Rm) (k : Fin H) :
    t< numericalEntry (row k) ↔ isUpper (signal row k)=true := by
  cases hk : row k with
  | inl upper =>
    have hh : t<(upper:ℝ) := hfloor.trans_le upper.2
    simp [hk,numericalEntry,signal,signalEntry,isUpper,hh]
  | inr partialBidValue =>
    have hh : (partialBidValue:ℝ)< t := partialBidValue.2.2.trans_lt ht
    simp [hk,numericalEntry,signal,signalEntry,isUpper,not_lt.mpr hh.le]

lemma numerical_ne_active {H : ℕ} {R Rp Rm t : ℝ}
    (row : Row H R Rp Rm) (ht : Rp< t) (hfloor : t< Rm) (k : Fin H) :
    numericalEntry (row k)≠t := by
  cases hk : row k with
  | inl upper =>
    have hh : t<(upper:ℝ) := hfloor.trans_le upper.2
    simpa [hk,numericalEntry] using hh.ne'
  | inr partialBidValue =>
    have hh : (partialBidValue:ℝ)< t := partialBidValue.2.2.trans_lt ht
    simpa [hk,numericalEntry] using hh.ne

theorem selected_active_iff (N H0 H1 c : ℕ) {ξ B R Rp Rm : ℝ}
    (side : Bool) (b : Fin N → ℝ) (row : Row (ownCount H0 H1 side) R Rp Rm)
    (hξ : ξ∈Ico (0:ℝ) 1) (hb : ∀ j, b j∈Icc (1:ℝ) B)
    (hR : 0< R) (hRRm : R≤ Rm) (hRp : Rp<1) (hgap : (1-ξ)*B< R) (hfloor : B< Rm)
    (i : Fin N) (hno : ∀ j, j≠i → b j≠b i) :
    Sum.inl i∈AllCountAtypical.select N H0 H1 c ξ b side row ↔
      activeRule N H0 H1 c ξ side b (upperCount (marks (signal row))) i := by
  let r : Fin (ownCount H0 H1 side) → ℝ := fun k => numericalEntry (row k)
  have hκ : 0<1-ξ := sub_pos.mpr hξ.2
  have hbpos (j : Fin N) : 0< b j := (by norm_num : (0:ℝ)<1).trans_le (hb j).1
  have hr : ∀ k, 0≤ r k := row_nonnegative hR.le hRRm row
  have ht : Rp< b i := hRp.trans_le (hb i).1
  have hifloor : b i< Rm := (hb i).2.trans_lt hfloor
  have hpriv : ∀ k, r k≠b i := numerical_ne_active row ht hifloor
  have hlist : list (Finset.univ : Finset (Fin N))
      (Finset.univ : Finset (Fin (ownCount H0 H1 side)))=Finset.univ :=
    active_private_cover N (ownCount H0 H1 side)
  unfold AllCountAtypical.select activeRule
  split_ifs with hsl hown hfit
  · simp
  · have hless (k : Fin (ownCount H0 H1 side)) : (1-ξ)*b i< r k :=
      ((mul_le_mul_of_nonneg_left (hb i).2 hκ.le).trans_lt hgap).trans_le
        (row_ge_R hRRm row k)
    have he := active_top_iff (Finset.univ : Finset (Fin N)) Finset.univ c
      (fun j => (1-ξ)*b j) r i (fun j _ => (mul_pos hκ (hbpos j)).le)
      (fun k _ => hr k) (mul_pos hκ (hbpos i))
      (fun j _ hji heq => hno j hji (mul_left_cancel₀ hκ.ne' heq))
      (fun k _ => (hless k).ne')
    have heR : (Finset.univ.filter (fun k => (1-ξ)*b i< r k))=Finset.univ :=
      Finset.filter_true_of_mem (fun k _ => hless k)
    have heB : (Finset.univ.filter (fun j => (1-ξ)*b i<(1-ξ)*b j))=
        Finset.univ.filter (fun j => b i< b j) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact mul_lt_mul_iff_right₀ hκ
    have hrec : receipt b (fun _ => 1) ξ row=Sum.elim (fun j => (1-ξ)*b j) r := by
      funext q
      cases q
      · simp [receipt,r]
        ring
      · simp [receipt,r]
    rw [hlist,heR,heB] at he
    simpa only [hrec,Finset.mem_univ,true_and,Finset.card_univ,Fintype.card_fin,Nat.add_comm] using he
  · simp
  · let K : Finset (Fin (ownCount H0 H1 side)) :=
      if N≤2*c then Finset.univ else Finset.univ.filter fun k => isUpper (signal row k)=true
    have hwhite : whitelist N H0 H1 c b side row=list (owners N H0 c b side) K := by
      unfold whitelist list K
      split_ifs <;> simp only [privateAll,upperPool]
    have he := active_top_iff (owners N H0 c b side) K c b r i
      (fun j _ => (hbpos j).le) (fun k _ => hr k) (hbpos i)
      (fun j _ hji => hno j hji) (fun k _ => hpriv k)
    have heK : K.filter (fun k => b i< r k)=
        Finset.univ.filter (fun k => isUpper (signal row k)=true) := by
      ext k
      have hh := numerical_above_active_iff_upper row ht hifloor k
      by_cases hN : N≤2*c <;> simp [K,hN,Finset.mem_filter,r,hh]
    rw [heK] at he
    simpa only [hwhite,numericalBid,r,upperCount,marks,Nat.add_comm] using he

end FCAppendix.Affine.Tail04.AtypicalActiveRanks
