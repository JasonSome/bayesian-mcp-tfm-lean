import FCAppendix.Affine.Hybrid.CountRegionData
import FCAppendix.Affine.Hybrid.FavoredNoisyFixedPoint
import FCAppendix.Affine.LowBody.NoisyRow

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology Classical
open scoped BigOperators
variable {N : ℕ}

def activePatternPred (kind : Fin N→Fin 4) (i : Fin (N+1)) : Prop :=
  Fin.cases True (fun j=>kind j=1) i

abbrev ActivePatternIndex (kind : Fin N→Fin 4) := {i : Fin (N+1) // activePatternPred kind i}

instance activePatternIndex_nonempty (kind : Fin N→Fin 4) : Nonempty (ActivePatternIndex kind) :=
  ⟨⟨0,by simp [activePatternPred]⟩⟩

def activePatternFocal (kind : Fin N→Fin 4) : ActivePatternIndex kind := ⟨0,by simp [activePatternPred]⟩

def activePatternUpper (kind : Fin N→Fin 4) (j : Fin 2) : ℕ :=
  LowBody.classCount ⟨2+j.val,by omega⟩ (LowBody.patternRow kind)

def activePatternCapacity (c : ℕ) (kind : Fin N→Fin 4) (j : Fin 2) : ℕ :=
  min (Fintype.card (ActivePatternIndex kind)) (c-activePatternUpper kind j)

def activePatternSmall (c : ℕ) (kind : Fin N→Fin 4) : ℕ :=
  min (activePatternCapacity c kind 0) (activePatternCapacity c kind 1)

def activePatternGap (c : ℕ) (kind : Fin N→Fin 4) : ℕ :=
  residualDifference (activePatternCapacity c kind 0) (activePatternCapacity c kind 1)

def activePatternQuota (z : ℝ) (kind : Fin N→Fin 4) : ℕ :=
  exclusiveQuota z (Fintype.card (ActivePatternIndex kind))

def activePatternOwner (c : ℕ) (z : ℝ) (kind : Fin N→Fin 4) (j : Fin 2) : ℕ :=
  activePatternQuota z kind+
    (if activePatternCapacity c kind (1-j)<activePatternCapacity c kind j then activePatternGap c kind else 0)

def activePatternResidual (c : ℕ) (z : ℝ) (kind : Fin N→Fin 4) : ℕ :=
  activePatternSmall c kind-activePatternQuota z kind

def activePatternGuarded (xi L U : ℝ) (c : ℕ) (z : ℝ) (kind : Fin N→Fin 4) : Prop :=
  2≤Fintype.card (ActivePatternIndex kind) ∧
  activePatternCapacity c kind 0≠activePatternCapacity c kind 1 ∧
  0<activePatternOwner c z kind 0+activePatternOwner c z kind 1 ∧
  activePatternOwner c z kind 0+activePatternOwner c z kind 1<Fintype.card (ActivePatternIndex kind) ∧
  NormalizedGuardRegion xi L U (finiteCountPoint (N+1)
    (Fintype.card (ActivePatternIndex kind)) (activePatternSmall c kind)
    (activePatternQuota z kind) (activePatternGap c kind)) ∧
  0 < LowBody.classCount 0 (LowBody.patternRow kind)

def lowerPatternPred (kind : Fin N→Fin 4) (i : Fin (N+1)) : Prop :=
  Fin.cases True (fun j=>kind j=0 ∨ kind j=1) i

def activePatternTemplate (c : ℕ) (kind : Fin N→Fin 4) : LowBody.PureTemplate (Fin (N+1)) where
  support:=Finset.univ.filter (lowerPatternPred kind)
  residual₀:=min (Finset.univ.filter (lowerPatternPred kind)).card (c-activePatternUpper kind 0)
  residual₁:=min (Finset.univ.filter (lowerPatternPred kind)).card (c-activePatternUpper kind 1)

abbrev ActivePatternInput (N : ℕ) (d vlo vhi L U eps : ℝ) :=
  (ActiveValue vlo vhi × ActiveBaseBid L U) ×
    ((Fin N→LowBody.LowValue d) × (Fin N→ActivePhysicalBid L U eps))

def activePatternBids {d vlo vhi L U eps : ℝ} (kind : Fin N→Fin 4)
    (t : ActivePatternInput N d vlo vhi L U eps) : Fin (N+1)→ℝ :=
  Fin.cons t.1.2 (fun j=>if kind j=0 then (t.2.1 j:ℝ) else if kind j=1 then (t.2.2 j:ℝ) else 0)

lemma continuous_activePatternBids {d vlo vhi L U eps : ℝ} (kind : Fin N→Fin 4) :
    Continuous (activePatternBids (d:=d) (vlo:=vlo) (vhi:=vhi) (L:=L) (U:=U) (eps:=eps) kind) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change Continuous (fun t : ActivePatternInput N d vlo vhi L U eps=>(t.1.2:ℝ))
    fun_prop
  · by_cases h0 : kind j=0
    · simp only [activePatternBids,Fin.cons_succ,if_pos h0]
      fun_prop
    · by_cases h1 : kind j=1
      · simp only [activePatternBids,Fin.cons_succ,if_neg h0,if_pos h1]
        fun_prop
      · simp only [activePatternBids,Fin.cons_succ,if_neg h0,if_neg h1]
        fun_prop

lemma activePatternBids_nonneg {d vlo vhi L U eps : ℝ} (hL : 0<L)
    (kind : Fin N→Fin 4) (t : ActivePatternInput N d vlo vhi L U eps) :
    ∀i,0≤activePatternBids kind t i := by
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (hL.trans_le t.1.2.property.1).le
  · by_cases h0 : kind j=0
    · simpa only [activePatternBids,Fin.cons_succ,if_pos h0] using (t.2.1 j).property.1
    · by_cases h1 : kind j=1
      · simpa only [activePatternBids,Fin.cons_succ,if_neg h0,if_pos h1] using
          (hL.trans_le (t.2.2 j).property.1).le
      · simp only [activePatternBids,Fin.cons_succ,if_neg h0,if_neg h1,le_refl]

def activePatternGuardedInput {d vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (kind : Fin N→Fin 4) (t : ActivePatternInput N d vlo vhi L U eps) :
    GuardedNoiseInput (ActivePatternIndex kind) vlo vhi L U eps :=
  (t.1,fun i=>Fin.cases (activeNoisyBid hL heps (t.1,0)) (fun j=>t.2.2 j) i.val)

lemma continuous_activePatternGuardedInput {d vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (kind : Fin N→Fin 4) :
    Continuous (activePatternGuardedInput (d:=d) (vlo:=vlo) (vhi:=vhi) (U:=U) hL heps kind) := by
  apply continuous_fst.prodMk
  apply continuous_pi
  intro i
  have haux (k : Fin (N+1)) : Continuous
      (fun t : ActivePatternInput N d vlo vhi L U eps=>
        (Fin.cases (activeNoisyBid hL heps (t.1,0)) (fun j=>t.2.2 j) k : ActivePhysicalBid L U eps)) := by
    refine Fin.cases ?_ (fun j=>?_) k
    · exact (continuous_activeNoisyBid hL heps).comp (continuous_fst.prodMk continuous_const)
    · exact (continuous_apply j).comp (continuous_snd.comp continuous_snd)
  exact haux i.val

end FCAppendix.Affine.Hybrid
