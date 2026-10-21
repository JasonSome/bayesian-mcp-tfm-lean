import FCAppendix.Affine.Tail04.EqualPrivateAmbient
import FCAppendix.Affine.Tail04.PrivateRowSorting

noncomputable section
namespace FCAppendix.Affine.Tail04.AmbientSignalSort
open MeasureTheory Set Classical
open EqualPrivateSignal EqualPrivateAmbient PrivateRowSorting SortedCoordinates

lemma permutation_eq_of_before {H : ℕ} (b d : Fin H→ℝ)
    (h : ∀ i j,before b i j↔before d i j) : permutation b=permutation d := by
  have hr : rankFin Finset.univ b=rankFin Finset.univ d := by
    funext i
    apply Fin.ext
    change (preceding Finset.univ b i).card=(preceding Finset.univ d i).card
    congr 1
    ext j
    simp only [preceding,Finset.mem_filter,h j i]
  have he : rankEquiv Finset.univ b=rankEquiv Finset.univ d :=
    Equiv.ext (fun i=> congrFun hr i)
  apply Equiv.ext
  intro i
  change (SortedCoordinates.enumerate Finset.univ b (Fin.cast (by simp) i)).val=
    (SortedCoordinates.enumerate Finset.univ d (Fin.cast (by simp) i)).val
  simp only [SortedCoordinates.enumerate,he]

def region (E : Observable.Regions) (W : ℝ) (hVW : E.Rp≤ W) (hW : W<1) :
    Observable.Regions :=
  { E with Rp:=W, R_le_Rp:=E.R_le_Rp.trans hVW, Rp_lt_one:=hW }

lemma key_le_iff (E : Observable.Regions) (W : ℝ) (hVW : E.Rp≤ W) (hW : W<1)
    (x y : Unit⊕Icc E.R E.Rp) :
    LocalCoordinates.signalKey (region E W hVW hW) (entry hVW x)≤
        LocalCoordinates.signalKey (region E W hVW hW) (entry hVW y)↔LocalCoordinates.signalKey E x≤ LocalCoordinates.signalKey E y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => simp only [LocalCoordinates.signalKey,entry,le_refl]
    | inr y =>
      have hy:=y.2.2
      simp only [LocalCoordinates.signalKey,entry,Sum.map_inl,Sum.map_inr,widen,region]
      constructor <;> intro h <;> linarith
  | inr x =>
    cases y with
    | inl y =>
      have hx:=x.2.2
      simp only [LocalCoordinates.signalKey,entry,Sum.map_inl,Sum.map_inr,widen,region]
      constructor <;> intro h <;> linarith
    | inr y => rfl

lemma key_eq_iff (E : Observable.Regions) (W : ℝ) (hVW : E.Rp≤ W) (hW : W<1)
    (x y : Unit⊕Icc E.R E.Rp) :
    LocalCoordinates.signalKey (region E W hVW hW) (entry hVW x)=
        LocalCoordinates.signalKey (region E W hVW hW) (entry hVW y)↔LocalCoordinates.signalKey E x=LocalCoordinates.signalKey E y := by
  constructor
  · intro h
    exact le_antisymm ((key_le_iff E W hVW hW x y).mp h.le)
      ((key_le_iff E W hVW hW y x).mp h.ge)
  · intro h
    exact le_antisymm ((key_le_iff E W hVW hW x y).mpr h.le)
      ((key_le_iff E W hVW hW y x).mpr h.ge)

lemma key_lt_iff (E : Observable.Regions) (W : ℝ) (hVW : E.Rp≤ W) (hW : W<1)
    (x y : Unit⊕Icc E.R E.Rp) :
    LocalCoordinates.signalKey (region E W hVW hW) (entry hVW x)<
        LocalCoordinates.signalKey (region E W hVW hW) (entry hVW y)↔LocalCoordinates.signalKey E x< LocalCoordinates.signalKey E y := by
  simp only [lt_iff_not_ge,key_le_iff]

theorem permutation_signal (E : Observable.Regions) (W : ℝ)
    (hVW : E.Rp≤ W) (hW : W<1) (H : ℕ) (s : Signal H E.R E.Rp) :
    permutation (fun i=>LocalCoordinates.signalKey (region E W hVW hW) (signal hVW s i))=
      permutation (fun i=> LocalCoordinates.signalKey E (s i)) := by
  apply permutation_eq_of_before
  intro i j
  simp only [before,signal,key_lt_iff,key_eq_iff]

theorem sortSignal_signal (E : Observable.Regions) (W : ℝ)
    (hVW : E.Rp≤ W) (hW : W<1) (H : ℕ) (s : Signal H E.R E.Rp) :
    sortSignal (region E W hVW hW) H (signal hVW s)=
      signal hVW (sortSignal E H s) := by
  funext i
  simp only [sortSignal]
  rw [permutation_signal]
  rfl

end FCAppendix.Affine.Tail04.AmbientSignalSort
