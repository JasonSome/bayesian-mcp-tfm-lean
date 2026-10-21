import FCAppendix.Affine.Hybrid.ActivePatternBounds
import FCAppendix.Affine.LowBody.NoisyClusterIC

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology Classical Game
open scoped BigOperators
variable {N : ℕ}

abbrev ActivePhysicalData (N : ℕ) := ℝ×ℝ×((Fin N→ℝ)×(Fin N→ℝ))

def activePhysicalBids (kind : Fin N→ Fin 4) (t : ActivePhysicalData N) : Fin (N+1)→ℝ:=
  Fin.cons t.2.1 (fun j=>if kind j=0 then t.2.2.1 j else if kind j=1 then t.2.2.2 j else 0)

def activePhysicalActiveBids (kind : Fin N→ Fin 4) (t : ActivePhysicalData N) : ActivePatternIndex kind→ℝ:=
  fun i=>Fin.cases t.2.1 (fun j=>t.2.2.2 j) i.val

lemma continuous_activePhysicalBids (kind : Fin N→ Fin 4) : Continuous (activePhysicalBids kind) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · change Continuous (fun t : ActivePhysicalData N=>t.2.1)
    fun_prop
  · by_cases h0 : kind j=0
    · simp only [activePhysicalBids,Fin.cons_succ,if_pos h0]
      fun_prop
    · by_cases h1 : kind j=1
      · simp only [activePhysicalBids,Fin.cons_succ,if_neg h0,if_pos h1]
        fun_prop
      · simp only [activePhysicalBids,Fin.cons_succ,if_neg h0,if_neg h1]
        exact continuous_const

lemma continuous_activePhysicalActiveBids (kind : Fin N→ Fin 4) :
    Continuous (activePhysicalActiveBids kind) := by
  apply continuous_pi
  intro i
  have hh (j : Fin (N+1)) : Continuous
      (fun t : ActivePhysicalData N=>(Fin.cases t.2.1 (fun k=>t.2.2.2 k) j : ℝ)) := by
    refine Fin.cases ?_ (fun k=>?_) j
    · simp only [Fin.cases_zero];fun_prop
    · simp only [Fin.cases_succ];fun_prop
  exact hh i.val

def activePhysicalPatternPayoff (xi z L W : ℝ) (c : ℕ) (kind : Fin N→ Fin 4)
    (t : ActivePhysicalData N) : ℝ:=
  let T:=activePatternTemplate c kind
  let b:=activePhysicalBids kind t
  if activePatternGuarded xi L W c z kind then
    sourceOwnerPayoff xi (1-2*xi) t.1 (activePhysicalActiveBids kind t)
      (activePatternResidual c z kind) (activePatternOwner c z kind 0) (activePatternOwner c z kind 1)
      (activePatternFocal kind)
  else if T.residual₀=T.residual₁ then LowBody.equalPayoff xi T.residual₀ 0 t.1 b
  else LowBody.purePayoff (1-xi) t.1 b (T.selection (1-xi) b) 0

attribute [local irreducible] sourceOwnerPayoff

lemma measurable_activePhysicalPatternPayoff {xi : ℝ} (hxi : 0<xi) (hxi1 : xi<1)
    (z L W : ℝ) (c : ℕ) (kind : Fin N→ Fin 4) :
    Measurable (activePhysicalPatternPayoff xi z L W c kind) := by
  let T:=activePatternTemplate c kind
  have hb:=continuous_activePhysicalBids kind
  have hact:=continuous_activePhysicalActiveBids kind
  have hg : Measurable (fun t : ActivePhysicalData N=>
      sourceOwnerPayoff xi (1-2*xi) t.1 (activePhysicalActiveBids kind t)
        (activePatternResidual c z kind) (activePatternOwner c z kind 0) (activePatternOwner c z kind 1)
        (activePatternFocal kind)) :=
    (measurable_joint_sourceOwnerPayoff xi (1-2*xi) _ _ _ _).comp (measurable_fst.prodMk hact.measurable)
  have hp : Measurable (fun t : ActivePhysicalData N=>EqualCapacity.positiveMarginal xi T.residual₀
      (activePhysicalBids kind t) 0):=(measurable_pi_apply 0).comp
    ((EqualCapacity.measurable_positiveMarginal xi T.residual₀ hxi hxi1).comp hb.measurable)
  have he : Measurable (fun t : ActivePhysicalData N=>LowBody.equalPayoff xi T.residual₀ 0 t.1
      (activePhysicalBids kind t)) := by
    unfold LowBody.equalPayoff
    fun_prop
  letI : MeasurableSpace T.Candidate:=⊤
  have hs : Measurable (fun t : ActivePhysicalData N=>FiniteSelector.select
      (fun P : T.Candidate=>LowBody.CompleteInformation.potential (1-xi) (activePhysicalBids kind t) P.val.1 P.val.2)) :=
    FiniteSelector.measurable_select _ (fun P=>((LowBody.continuous_potential (1-xi) P.val).comp hb).measurable)
  have hl : Measurable (fun t : ActivePhysicalData N=>LowBody.focalCopy
      (T.selection (1-xi) (activePhysicalBids kind t)) 0):=
    (measurable_of_countable (fun P : T.Candidate=>LowBody.focalCopy P.val 0)).comp hs
  have hu : Measurable (fun t : ActivePhysicalData N=>LowBody.purePayoff (1-xi) t.1 (activePhysicalBids kind t)
      (T.selection (1-xi) (activePhysicalBids kind t)) 0) := by
    unfold LowBody.purePayoff
    exact Measurable.ite (measurableSet_eq_fun hl measurable_const) (by fun_prop)
      (Measurable.ite (measurableSet_eq_fun hl measurable_const) (by fun_prop) measurable_const)
  unfold activePhysicalPatternPayoff
  dsimp only
  split_ifs
  · exact hg
  · exact he
  · exact hu

def activeNoisyPhysicalData {d vlo vhi L U eps : ℝ} (_kind : Fin N→ Fin 4)
    (t : ActivePatternInput N d vlo vhi L U eps) (noise : unitInterval) : ActivePhysicalData N:=
  (t.1.1,activeNoisyRealBid eps t.1.2 noise,
    (fun j=>(t.2.1 j:ℝ)),fun j=>(t.2.2 j:ℝ))

lemma activePatternNoisyPayoff_eq_physical {d vlo vhi L U eps : ℝ}
    (hL : 0<L) (heps : 0≤ eps) (xi z : ℝ) (c : ℕ) (kind : Fin N→ Fin 4)
    (t : ActivePatternInput N d vlo vhi L U eps) (noise : unitInterval) :
    activePatternNoisyPayoff hL heps xi z c kind t noise=
      activePhysicalPatternPayoff xi z L (U*(1+eps)) c kind (activeNoisyPhysicalData kind t noise) := by
  have hb : LowBody.noisyFocal (0:Fin (N+1)) eps (activePatternBids kind t) noise=
      activePhysicalBids kind (activeNoisyPhysicalData kind t noise) := by
    ext i
    refine Fin.cases ?_ (fun j=>?_) i <;>
      simp [LowBody.noisyFocal,activePatternBids,activePhysicalBids,activeNoisyPhysicalData,activeNoisyRealBid]
  have ha : (guardedNoisyInput eps (activePatternFocal kind)
      (activePatternGuardedInput hL heps kind t) noise).2=
      activePhysicalActiveBids kind (activeNoisyPhysicalData kind t noise) := by
    ext i
    by_cases hi : i=activePatternFocal kind
    · subst i
      simp [guardedNoisyInput,activePhysicalActiveBids,activeNoisyPhysicalData,activePatternFocal,activeNoisyRealBid,activePatternGuardedInput]
    · have hi0 : i.val≠0 := by
        intro hh
        apply hi
        apply Subtype.ext
        exact hh
      obtain ⟨j,hj⟩:=Fin.eq_succ_of_ne_zero hi0
      simp [guardedNoisyInput,Function.update_of_ne hi,activePhysicalActiveBids,activeNoisyPhysicalData,
        activePatternGuardedInput,hj]
  unfold activePatternNoisyPayoff activePhysicalPatternPayoff
  dsimp only
  split_ifs
  · unfold guardedNoisyPayoff
    rw [ha]
    rfl
  · unfold LowBody.equalNoisyPayoff
    rw [hb]
    rfl
  · unfold LowBody.PureTemplate.noisyUserPayoff
    rw [hb]
    rfl

end FCAppendix.Affine.Hybrid
