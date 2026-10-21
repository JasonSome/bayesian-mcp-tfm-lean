import FCAppendix.Affine.UniformFinite.NativeRowLaw

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.NativeRow
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Uniform05 SourceContinuity ClippedResidual WeightedSampling
open scoped BigOperators
variable {M : ℕ} [NeZero M]

def eraseState (i : Row) (S : Finset (Fin M)) (x : State i M) : State i M :=
  (x.1,fun a=> if a∈S then ⟨0,le_rfl,(cap_pos i).le⟩ else x.2 a)

omit [NeZero M] in
lemma eraseState_bids (i : Row) (S : Finset (Fin M)) (x : State i M) :
    bids i (eraseState i S x)=SeedErasure.erase S (bids i x) := by
  funext a
  by_cases ha : a∈S <;> simp [eraseState,bids,SeedErasure.erase,ha]

omit [NeZero M] in
lemma measurable_eraseState (i : Row) (S : Finset (Fin M)) :
    Measurable (eraseState i S) := by
  have hb : Continuous (fun x : State i M=>fun a=>
      if a∈S then (⟨0,le_rfl,(cap_pos i).le⟩ : Bid i) else x.2 a) := by
    apply continuous_pi
    intro a
    by_cases ha : a∈S
    · simp only [if_pos ha]; exact continuous_const
    · simp only [if_neg ha]; exact (continuous_apply a).comp continuous_snd
  have hc : Continuous (eraseState i S) := continuous_fst.prodMk hb
  exact hc.measurable

omit [NeZero M] in
lemma rawWeight_erase (i : Row) (row : Source.CountRow M)
    (S : Finset (Fin M)) (x : State i M) (hS : ∀a∈S,bids i x a≤ t i/2) :
    rawWeight i row (eraseState i S x)=rawWeight i row x := by
  have hG : (eraseState i S x).1=x.1 := rfl
  simp only [rawWeight,hG,eraseState_bids]
  exact SeedErasure.rawAlpha_erase i x.1 row S (bids i x) hS

lemma commonLaw_erase (i : Row) (row : Source.CountRow M)
    (S : Finset (Fin M)) (x : State i M) (hS : ∀a∈S,bids i x a≤ t i/2) :
    commonLaw i row (eraseState i S x)=commonLaw i row x := by
  have hG : (eraseState i S x).1=x.1 := rfl
  simp only [commonLaw,eraseState_bids,hG,
    SeedErasure.sourceWeights_erase i x.1 row S (bids i x) hS,
    SeedErasure.guardAlpha_erase i x.1 row S (bids i x) hS]

omit [NeZero M] in
lemma actualRoot_erase (i : Row) (row : Source.CountRow M)
    (S : Finset (Fin M)) (x : State i M) (hS : ∀a∈S,bids i x a≤ t i/2)
    (p : Path (Fin M) (Source.imbalance row)) :
    actualRoot i row p (eraseState i S x)=actualRoot i row p x := by
  unfold actualRoot
  rw [eraseState_bids]
  apply SeedErasure.root_congr
  intro z hz
  rw [SeedErasure.lowerBids_erase]
  exact SeedErasure.remainingDemand_erase S _ _
    (SeedErasure.lower_seed_bound i row S (bids i x) hS)
    (by linarith [t_pos i]) ((SeedErasure.seed_le_rootLo i x.1).trans hz.1)

lemma smallLaw_erase (i : Row) (row : Source.CountRow M)
    (S : Finset (Fin M)) (x : State i M) (hS : ∀a∈S,bids i x a≤ t i/2)
    (hraw : 0< rawWeight i row x) (p : Path (Fin M) (Source.imbalance row)) :
    smallLaw i row p (eraseState i S x)=smallLaw i row p x := by
  have he : 0< rawWeight i row (eraseState i S x) := by rwa [rawWeight_erase i row S x hS]
  unfold smallLaw
  rw [usableRoot_eq i row p _ he,usableRoot_eq i row p _ hraw,actualRoot_erase i row S x hS p]
  have hz : Source.rootLo i x.1≤ actualRoot i row p x :=
    (pathRoot_spec i row p ⟨x,hraw⟩).1.1
  unfold Literal.completion
  congr 1
  funext a
  unfold smallMarginal
  by_cases ha : a∈finalSet (Source.imbalance row) ∅ p
  · simp only [if_pos ha]
  · simp only [if_neg ha,eraseState_bids,SeedErasure.lowerBids_erase]
    exact SeedErasure.exposure_erase S _
      (SeedErasure.lower_seed_bound i row S (bids i x) hS)
      (by linarith [t_pos i]) ((SeedErasure.seed_le_rootLo i x.1).trans hz) a

lemma largeLaw_erase (i : Row) (row : Source.CountRow M)
    (S : Finset (Fin M)) (x : State i M) (hS : ∀a∈S,bids i x a≤ t i/2)
    (hraw : 0< rawWeight i row x) (p : Path (Fin M) (Source.imbalance row)) :
    largeLaw i row p (eraseState i S x)=largeLaw i row p x := by
  simp only [largeLaw,smallLaw_erase i row S x hS hraw p]

lemma pureSet_erase (i : Row) (row : Source.CountRow M)
    (S : Finset (Fin M)) (x : State i M) (hS : ∀a∈S,bids i x a≤ t i/2)
    (hraw : 0< rawWeight i row x) (j : Fin 2) :
    pureSet i row j (eraseState i S x)=pureSet i row j x := by
  have hp : (Source.lowerTemplate row).selection (kappa i)
      (Source.lowerBids row (bids i (eraseState i S x))) =
      (Source.lowerTemplate row).selection (kappa i) (Source.lowerBids row (bids i x)) := by
    rw [eraseState_bids,SeedErasure.lowerBids_erase]
    apply SeedErasure.pure_selection_erase (Source.lowerTemplate row)
      (kappa_range i).1.le (kappa_range i).2.le
    · intro a
      by_cases ha : a∈row.lower
      · simpa only [Source.lowerBids_of_mem row _ ha] using (bids_bounds i x a).1
      · simp [Source.lowerBids,ha]
    · intro a ha
      exact (SeedErasure.lower_seed_bound i row S (bids i x) hS a ha).trans
        (SeedErasure.seed_le_rejectionRoot i x.1)
    · exact SeedRejection.raw_guard_high_count i x.1 row (bids i x) hraw
  simp only [pureSet,hp]

lemma privateLaw_erase (i : Row) (row : Source.CountRow M)
    (hne : Source.residual row 0≠Source.residual row 1)
    (S : Finset (Fin M)) (x : State i M) (hS : ∀a∈S,bids i x a≤ t i/2)
    (hraw : 0< rawWeight i row x) (j : Fin 2) (q : Signal row) :
    privateLaw i row j (eraseState i S x) q=privateLaw i row j x q := by
  cases q with
  | none => simp only [privateLaw,if_neg hne,pureSet_erase i row S x hS hraw j]
  | some p => simp only [privateLaw,if_neg hne,
      smallLaw_erase i row S x hS hraw p,largeLaw_erase i row S x hS hraw p]

theorem select_erase (i : Row) (row : Source.CountRow M)
    (hne : Source.residual row 0≠Source.residual row 1)
    (S : Finset (Fin M)) (x : State i M) (hS : ∀a∈S,bids i x a≤ t i/2)
    (hraw : 0< rawWeight i row x) (j : Fin 2) (u s : unitInterval) :
    select i row j (eraseState i S x) u s=select i row j x u s := by
  simp only [select,commonSample,commonLaw_erase i row S x hS,privateSample,
    privateLaw_erase i row hne S x hS hraw j]

theorem draw_erase (i : Row) (row : Source.CountRow M)
    (hne : Source.residual row 0≠Source.residual row 1)
    (S : Finset (Fin M)) (x : State i M) (hS : ∀a∈S,bids i x a≤ t i/2)
    (hraw : 0< rawWeight i row x) (s : Seeds) :
    draw i row (eraseState i S x) s=draw i row x s := by
  simp only [draw,select_erase i row hne S x hS hraw]

lemma commonSample_none (i : Row) (row : Source.CountRow M) (x : State i M)
    (h : Source.residual row 0=Source.residual row 1 ∨
      Source.guardAlpha i x.1 row (bids i x)=0) (u : unitInterval) :
    commonSample i row x u=none := by
  have hP : commonLaw i row x=FiniteLaw.dirac none := by
    rcases h with he|ha
    · simp [commonLaw,he]
    · by_cases he : Source.residual row 0=Source.residual row 1
      · simp [commonLaw,he]
      · apply FiniteLaw.ext
        intro q
        simp [commonLaw,he,Literal.signalLaw,FiniteLaw.mixture,ha]
  simp only [commonSample,hP,ExtensionalSampler.dirac]

theorem draw_common_irrelevant (i : Row) (row : Source.CountRow M) (x : State i M)
    (h : Source.residual row 0=Source.residual row 1 ∨
      Source.guardAlpha i x.1 row (bids i x)=0)
    (u u' : unitInterval) (s : unitInterval×unitInterval) :
    draw i row x (u,s)=draw i row x (u',s) := by
  simp only [draw,select,commonSample_none i row x h]

end FCAppendix.Affine.UniformFinite.NativeRow
