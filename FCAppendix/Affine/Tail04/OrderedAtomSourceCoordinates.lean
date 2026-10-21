import FCAppendix.Affine.Tail04.OrderedAtomOriginalMarks
import FCAppendix.Affine.Tail04.OrderedAtomRestoredBeta

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomSourceCoordinates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open OriginalValues FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeNoisySource
open OrderedAtomActiveCompression OriginalActiveCrossingCarrier OrderedAtomTwoPrefix
open OrderedAtomCountExceptions OrderedAtomTwoFocalExpectation OriginalFlagCompression
open SourceMenuPopulation SourceMenuError MenuError ActiveGainUniformModulus
open scoped BigOperators

lemma count_privateSize (D : Data) (E : Observable.Regions) {N : ℕ}
    (row : Fin N→ UserDraw 2) (k : Fin 4) :
    D.count (tags (E).coarseTag row) k=privateSize E row k := by
  simp only [Data.count,tags,privateSize,privateCount,boolCount,categoryFlag,
    markZero,Function.comp_apply,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : E.coarseTag (row i)=k <;> simp [h]

lemma count_lowPresent (D : Data) (E : Observable.Regions) {N : ℕ}
    (row : Fin N→ UserDraw 2) :
    decide (0< D.count (tags (E).coarseTag row) 0)=lowPresent E row := by
  unfold lowPresent
  congr 1
  simp only [Data.count,tags,Finset.card_pos,Finset.filter_nonempty_iff,
    Finset.mem_univ,true_and,Function.comp_apply]

lemma prefixActive_eq (E : Observable.Regions) {N : ℕ} (row : Fin N→ UserDraw 2) :
    OrderedAtomTwoPrefix.prefixActive (E).coarseTag row=
      OrderedAtomTwoFocalExpectation.prefixActive E row := rfl

lemma activeEnumeration_zero (D : Data) (E : Observable.Regions) {N : ℕ}
    (j : Fin (N+1)) (w : UserDraw 2) (hw : (E).coarseTag w=1)
    (row : Fin N→ UserDraw 2) :
    (activeEnumeration D (E).coarseTag j w hw row 0).val=0 := by
  apply (prefixIndex j).injective
  rw [activeEnumeration_index,consEnumeration_zero,prefixIndex_zero]

variable (D : Data) (P : ValueParameters) (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
local notation "E" => regions D P hdR H hBH
local notation "decode" => NoisyNativeFiberProduct.commonProjection D P hdR H hBH

lemma commonProjection_eq (x : UserDraw 2) (hx : NativeMenuReports.MenuAction E x.1.2)
    (ha : (E).coarseTag x=1) : (decode x:ℝ)=nativeBid x := by
  have hb := PartialSortedCompression.menu_active_box E x hx (by simpa [categoryFlag] using ha)
  exact clipToBand_eq 1 (E).U (E).one_le_U hb

theorem compressed_native_eq {N : ℕ} (j : Fin (N+1))
    (w : UserDraw 2) (hw : (E).coarseTag w=1) (row : Fin N→ UserDraw 2)
    (hrow : ∀ k,NativeMenuReports.MenuAction E (row k).1.2) (b : Icc (1:ℝ) D.B) :
    compressedBids (OrderedAtomTwoFocalExpectation.prefixActive E row)
      (activeEnumeration D (E).coarseTag j w hw row)
      (prefixBid row nativeBid b (decode w))=
      fun k => (focalRow D (tags (E).coarseTag (restore j w row)) decode b (restore j w row) k:ℝ) := by
  rw [←compressed_focal_row D (E).coarseTag decode j w hw row b]
  funext k
  let i := (activeEnumeration D (E).coarseTag j w hw row k).val
  have hi : OrderedAtomTwoFocalExpectation.prefixActive E row i=true :=
    (activeEnumeration D (E).coarseTag j w hw row k).property
  change prefixBid row nativeBid b (decode w) i=
    (Fin.cons (b:ℝ) (Fin.cons (decode w:ℝ) (fun k => (decode (row k):ℝ))) : Fin (N+2)→ℝ) i
  revert hi
  refine Fin.cases ?_ (fun l => ?_) i
  · intro _
    rfl
  · refine Fin.cases ?_ (fun l => ?_) l
    · intro _
      rfl
    · intro hi
      exact (commonProjection_eq D P hdR H hBH (row l) (hrow l)
        (by simpa [OrderedAtomTwoFocalExpectation.prefixActive,TwoFocalCompression.fullActive,
          markZero,categoryFlag] using hi)).symm

theorem compressed_raised {N : ℕ} (j : Fin (N+1))
    (w : UserDraw 2) (hw : (E).coarseTag w=1) (row : Fin N→ UserDraw 2)
    (hrow : ∀ k,NativeMenuReports.MenuAction E (row k).1.2) (b y : Icc (1:ℝ) D.B) :
    compressedBids (OrderedAtomTwoFocalExpectation.prefixActive E row)
      (activeEnumeration D (E).coarseTag j w hw row)
      (prefixBid row nativeBid y (decode w))=
      Function.update
        (fun k => (focalRow D (tags (E).coarseTag (restore j w row)) decode b (restore j w row) k:ℝ))
        0 (y:ℝ) := by
  rw [compressed_native_eq D P hdR H hBH j w hw row hrow y]
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp only [focalRow,Fin.cons_zero,Function.update_self]
  · simp only [focalRow,Fin.cons_succ,Function.update_of_ne (Fin.succ_ne_zero k)]

lemma compressed_prefix_mem {N A : ℕ} (row : Fin N→ UserDraw 2)
    (e : Fin A≃Active (OrderedAtomTwoFocalExpectation.prefixActive E row))
    (bid : UserDraw 2→ℝ) (hb : ∀ k,(E).coarseTag (row k)=1 → bid (row k)∈Icc (1:ℝ) D.B)
    {b0 b1 : ℝ} (hb0 : b0∈Icc (1:ℝ) D.B) (hb1 : b1∈Icc (1:ℝ) D.B) (k : Fin A) :
    compressedBids (OrderedAtomTwoFocalExpectation.prefixActive E row) e (prefixBid row bid b0 b1) k
      ∈Icc (1:ℝ) D.B := by
  let i := (e k).val
  have hi : OrderedAtomTwoFocalExpectation.prefixActive E row i=true := (e k).property
  change prefixBid row bid b0 b1 i∈_
  revert hi
  refine Fin.cases ?_ (fun l => ?_) i
  · exact fun _ => hb0
  · refine Fin.cases ?_ (fun l => ?_) l
    · exact fun _ => hb1
    · intro hi
      exact hb l (by simpa [OrderedAtomTwoFocalExpectation.prefixActive,
        TwoFocalCompression.fullActive,markZero,categoryFlag] using hi)

def freezeScalar (b y x : ℝ) : ℝ := if x∈Icc b y then b else x

lemma freezeScalar_bounds {b y x B : ℝ} (hb : b∈Icc (1:ℝ) B) (hx : x∈Icc (1:ℝ) B) :
    freezeScalar b y x∈Icc (1:ℝ) B := by
  unfold freezeScalar
  split_ifs
  · exact hb
  · exact hx

lemma freezeScalar_close {b y x : ℝ} (hby : b≤ y) :
    |freezeScalar b y x-x|≤ y-b := by
  unfold freezeScalar
  split_ifs with hx
  · rw [abs_of_nonpos (by linarith [hx.1])]
    linarith [hx.2]
  · rw [sub_self,abs_zero]
    linarith

lemma freezeScalar_self {b y : ℝ} (hby : b≤ y) : freezeScalar b y b=b := by
  simp [freezeScalar,hby]

lemma freezeScalar_idempotent (b y x : ℝ) :
    freezeScalar b y (freezeScalar b y x)=freezeScalar b y x := by
  unfold freezeScalar
  split_ifs <;> rfl

theorem compressed_freeze {N : ℕ} (j : Fin (N+1))
    (w : UserDraw 2) (hw : (E).coarseTag w=1) (row : Fin N→ UserDraw 2)
    (hrow : ∀ k,NativeMenuReports.MenuAction E (row k).1.2) (b y : Icc (1:ℝ) D.B) :
    compressedBids (OrderedAtomTwoFocalExpectation.prefixActive E row)
      (activeEnumeration D (E).coarseTag j w hw row)
      (prefixBid row (fun x => freezeScalar b y (nativeBid x))
        (freezeScalar b y b) (freezeScalar b y (decode w)))=
      freezeFocal
        (fun k => (focalRow D (tags (E).coarseTag (restore j w row)) decode b (restore j w row) k:ℝ))
        0 y := by
  rw [←compressed_native_eq D P hdR H hBH j w hw row hrow b]
  funext k
  have he0 := activeEnumeration_zero D E j w hw row
  change prefixBid row (fun x => freezeScalar b y (nativeBid x))
      (freezeScalar b y b) (freezeScalar b y (decode w))
      (activeEnumeration D (E).coarseTag j w hw row k).val=
    freezeScalar (prefixBid row nativeBid b (decode w)
        (activeEnumeration D (E).coarseTag j w hw row 0).val) y
      (prefixBid row nativeBid b (decode w)
        (activeEnumeration D (E).coarseTag j w hw row k).val)
  rw [he0]
  let i := (activeEnumeration D (E).coarseTag j w hw row k).val
  change prefixBid row (fun x => freezeScalar b y (nativeBid x))
      (freezeScalar b y b) (freezeScalar b y (decode w)) i=
    freezeScalar b y (prefixBid row nativeBid b (decode w) i)
  refine Fin.cases ?_ (fun l => ?_) i
  · rfl
  · exact Fin.cases rfl (fun _ => rfl) l

end FCAppendix.Affine.Tail04.OrderedAtomSourceCoordinates
