import FCAppendix.Affine.Tail04.MissingRowPosterior
import FCAppendix.Affine.Tail04.PrivateIdentitySort
import FCAppendix.Affine.Tail04.OriginalPrivateSource

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePrivatePosterior
open MeasureTheory ProbabilityTheory Set Classical Filter Game Bayes
open OriginalPopulation OriginalValues OriginalPrivateSource LocalCoordinates
open EqualPrivateSignal EqualPrivateUpper Hybrid MissingRowPosterior
open scoped BigOperators

def observedEntry (j : Fin 2) (x : UserDraw 2) : Option ℝ :=
  if j∈firstK x.2 x.1.2.routeCount then some x.1.2.bid else none

lemma measurable_observedEntry (j : Fin 2) : Measurable (observedEntry j) := by
  apply Measurable.ite
    (((measurable_snd).prodMk ((measurable_routeCount 2).comp measurable_fst.snd))
      (measurableSet_mem_firstK j))
  · exact measurable_some.comp ((measurable_bid 2).comp measurable_fst.snd)
  · exact measurable_const

lemma observation_native {m : ℕ} (j : Fin 2) (d : UserProfile m 2) :
    observation (observedEntry j) d=observe (drawsRealization d) j := rfl

lemma singleton_missing_iff_other (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    j∉firstK τ 1 ↔ otherProposer j∈firstK τ 1 := by
  have h := Hybrid.NativeContinuation.singleton_two_complement (firstK τ 1)
    (card_firstK τ 1 (by norm_num))
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with hj | hj <;> subst j
  · simpa only [otherProposer,if_pos rfl,ite_true] using h.symm
  · simpa only [otherProposer,if_neg (by decide : (1:Fin 2)≠0),not_not] using not_congr h

lemma sourceBands_missing_iff (P : ValueParameters) (E : Observable.Regions)
    (t : ℝ) (x : UserDraw 2) (hx : sourceBands P E t x.1) (j : Fin 2) :
    observedEntry j x=none ↔
      E.coarseTag x=Hybrid.NativeContinuation.upperTag (otherProposer j) := by
  have htag := OriginalPrivateEntry.private_tag_event E (otherProposer j)
  have hprivate : (E.coarseTag x=Hybrid.NativeContinuation.upperTag (otherProposer j)) ↔
      x.1.2.bid∈E.privateBids ∧ otherProposer j∈firstK x.2 1 := by
    change (x∈E.coarseTag ⁻¹' {Hybrid.NativeContinuation.upperTag (otherProposer j)}) ↔ _
    rw [htag]
    rfl
  rw [hprivate]
  rcases hx with hx | hx | hx | hx
  · have hp : x.1.2.bid∉E.privateBids :=
      fun hh => not_lt_of_ge hx.2.1 (E.private_above_low hh)
    simp [observedEntry,hx.2.2,firstK_full_two,hp]
  · have hp : x.1.2.bid∈E.privateBids := Or.inl hx.2.1
    rw [observedEntry,hx.2.2]
    simpa only [hp,true_and,ite_eq_right_iff,Option.some_ne_none,imp_false] using
      singleton_missing_iff_other x.2 j

  · have hp : x.1.2.bid∉E.privateBids := by
      rintro (hh | hh)
      · linarith [hh.2,hx.2.1.1,E.Rp_lt_one]
      · linarith [hx.2.1.2,E.U_lt_H,show E.H≤x.1.2.bid from hh]
    simp [observedEntry,hx.2.2,firstK_full_two,hp]
  · have hp : x.1.2.bid∈E.privateBids := Or.inr hx.2.1
    rw [observedEntry,hx.2.2]
    simpa only [hp,true_and,ite_eq_right_iff,Option.some_ne_none,imp_false] using
      singleton_missing_iff_other x.2 j

lemma sourceBands_missing_other_visible (P : ValueParameters) (E : Observable.Regions)
    (t : ℝ) (x : UserDraw 2) (hx : sourceBands P E t x.1) (j : Fin 2)
    (hmissing : observedEntry j x=none) :
    observedEntry (otherProposer j) x=some x.1.2.bid := by
  rcases hx with hx | hx | hx | hx
  · simp [observedEntry,hx.2.2,firstK_full_two] at hmissing
  · have hj : j∉firstK x.2 1 := by simpa [observedEntry,hx.2.2] using hmissing
    have ho := (singleton_missing_iff_other x.2 j).mp hj
    simp [observedEntry,hx.2.2,ho]
  · simp [observedEntry,hx.2.2,firstK_full_two] at hmissing
  · have hj : j∉firstK x.2 1 := by simpa [observedEntry,hx.2.2] using hmissing
    have ho := (singleton_missing_iff_other x.2 j).mp hj
    simp [observedEntry,hx.2.2,ho]

def identityMask {m : ℕ} (S : Finset (Fin m)) (i : Fin m) : Bool :=
  if i∈S then true else false

def identityMaskEquiv {m : ℕ} (S : Finset (Fin m)) :
    {i : Fin m // i∈S} ≃ {i : Fin m // identityMask S i=true} where
  toFun i := ⟨i,by simp [identityMask,i.2]⟩
  invFun i := ⟨i,by simpa [identityMask] using i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def identityEnumeration {m : ℕ} (S : Finset (Fin m)) :
    Fin S.card ≃ {i : Fin m // identityMask S i=true} :=
  (PrivateIdentitySort.baseline S).trans (identityMaskEquiv S)

lemma identityPattern_iff {m : ℕ} (S : Finset (Fin m)) (L : LocalList m) :
    L∈patternEvent (identityMask S) ↔ ∀ i,L i=none ↔ i∈S := by
  simp only [patternEvent,mem_setOf_eq]
  constructor
  · intro h i
    have hi := h i
    by_cases hs : i∈S <;> simpa [identityMask,hs,missing] using hi
  · intro h i
    by_cases hs : i∈S
    · have hn := (h i).mpr hs
      simp [identityMask,hs,missing,hn]
    · have hn : L i≠none := fun he => hs ((h i).mp he)
      simp [identityMask,hs,missing,hn]

lemma cond_congr_events {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (h : ∀ᵐ x ∂μ,x∈S ↔ x∈T) : cond μ S=cond μ T := by
  ext A hA
  have he : S=ᵐ[μ]T := h.mono fun _ hx=>propext hx
  rw [cond_apply hS,cond_apply hT,measure_congr he]
  congr 1
  apply measure_congr
  filter_upwards [h] with x hx
  exact propext (and_congr hx Iff.rfl)

variable (E : Observable.Regions) (P : ValueParameters) (hd : E.d=P.d0)
    (t : ℝ) (ht : P.M≤ t)
local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht
variable (πL : Existence.Distributional.Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (πP : Existence.Distributional.Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
    (πA : Existence.Distributional.Law (A:=Icc (1:ℝ) E.U) (P.originalMovingActiveLaw t ht))
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v,t< v → E.H≤ upperBid v)

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed)
    (hjoint : Γ.F ⊗ₘ Γ.σ=((originalJoint P t ht E.R E.Rp E.U (E.d_nonneg.trans E.d_lt_R.le) πL πP πA upperBid hupperBid) : Measure (ℝ × JointAction 2)))

include hd ht πL πP πA upperBid hupperBid hfloor hjoint in
theorem original_user_sourceBands :
    ∀ᵐ x ∂userLaw Γ,sourceBands P E t x.1 := by
  change ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ).prod (permLaw 2),sourceBands P E t x.1
  rw [hjoint]
  exact (measurePreserving_fst (μ:=((originalJoint P t ht E.R E.Rp E.U (E.d_nonneg.trans E.d_lt_R.le) πL πP πA upperBid hupperBid) : Measure (ℝ × JointAction 2)))
    (ν:=permLaw 2)).quasiMeasurePreserving.ae
      (originalJoint_sourceBands P E hd t ht πL πP πA upperBid hupperBid hfloor)

include hjoint in
theorem original_missing_entry (j : Fin 2) :
    (cond (userLaw Γ) (observedEntry j ⁻¹' {none})).map
      (fun x : UserDraw 2 => LocalCoordinates.decode E x.1.2.bid)=((originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor) : Measure (Ici E.H⊕Icc E.R E.Rp)) := by
  have hset : ∀ᵐ x ∂userLaw Γ,
      x∈(observedEntry j ⁻¹' {none}) ↔
        x∈(E.coarseTag ⁻¹' {Hybrid.NativeContinuation.upperTag (otherProposer j)}) := by
    filter_upwards [original_user_sourceBands E P hd t ht πL πP πA upperBid hupperBid hfloor Γ hjoint]
      with x hx
    exact sourceBands_missing_iff P E t x hx j
  rw [cond_congr_events (userLaw Γ) _ _
    ((measurable_observedEntry j) (measurableSet_singleton none))
    (E.measurable_coarseTag (measurableSet_singleton _)) hset]
  exact native_originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor Γ hjoint
    (otherProposer j)

include hjoint in
theorem original_finite_private_posterior (B : PosteriorSystem Γ) (j : Fin 2)
    (k : Fin m → Bool) (H : ℕ) (e : Fin H ≃ {i : Fin m // k i=true}) :
    ∀ᵐ L ∂observedListLaw Γ j,L∈patternEvent k →
      (B.posterior j L).map
        (sortedMissingRow E (observedEntry j) k H e
          (fun x : UserDraw 2 => LocalCoordinates.decode E x.1.2.bid))=
        (originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor H : Measure _) := by
  exact original_missing_posterior E (userLaw Γ) (observedEntry j) (measurable_observedEntry j)
    (B.posterior j) (B.on_path j) k H e
    (fun x : UserDraw 2 => LocalCoordinates.decode E x.1.2.bid)
    ((LocalCoordinates.measurable_decode E).comp ((measurable_bid 2).comp measurable_fst.snd)) (originalEntryLaw E P hd t ht πL πP πA upperBid hupperBid hfloor)
    (original_missing_entry E P hd t ht πL πP πA upperBid hupperBid hfloor Γ hjoint j)

include hjoint in
theorem original_finite_private_posterior_all (B : PosteriorSystem Γ)
    (H : (Fin m→ Bool) → ℕ)
    (e : ∀ k,Fin (H k) ≃ {i : Fin m // k i=true}) :
    ∀ j : Fin 2,∀ᵐ L ∂observedListLaw Γ j,∀ k,L∈patternEvent k →
      (B.posterior j L).map
        (sortedMissingRow E (observedEntry j) k (H k) (e k)
          (fun x : UserDraw 2 => LocalCoordinates.decode E x.1.2.bid))=
        (originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor (H k) : Measure _) := by
  intro j
  exact ae_all_iff.mpr (fun k => original_finite_private_posterior E P hd t ht πL πP πA
    upperBid hupperBid hfloor Γ hjoint B j k (H k) (e k))

include hd ht πL πP πA upperBid hupperBid hfloor hjoint in
theorem posterior_original_sourceBands (B : PosteriorSystem Γ) (j : Fin 2) :
    ∀ᵐ L ∂observedListLaw Γ j,∀ᵐ d ∂B.posterior j L,
      ∀ i,sourceBands P E t (d i).1 := by
  have hm : MeasurableSet {d : UserProfile m 2 | ∀ i,sourceBands P E t (d i).1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i =>
      (measurable_fst.comp (measurable_pi_apply i)) (measurableSet_sourceBands P E t))
  have hp : ∀ᵐ d ∂userProfileLaw Γ,∀ i,sourceBands P E t (d i).1 :=
    ae_all_iff.mpr (fun i =>
      (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae
        (original_user_sourceBands E P hd t ht πL πP πA upperBid hupperBid hfloor Γ hjoint))
  exact B.ae_posterior_of_ae Γ j _ hm hp

include hjoint in
theorem original_native_private_posterior (B : PosteriorSystem Γ) (j : Fin 2)
    (S : Finset (Fin m)) :
    ∀ᵐ L ∂observedListLaw Γ j,(∀ i,L i=none ↔ i∈S) →
      (B.posterior j L).map
        (fun d : UserProfile m 2 => LocalCoordinates.privateRow E S
          (observe (drawsRealization d) (otherProposer j)))=
        (originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor S.card : Measure _) := by
  have hr := original_finite_private_posterior E P hd t ht πL πP πA upperBid hupperBid hfloor
    Γ hjoint B j (identityMask S) S.card (identityEnumeration S)
  filter_upwards [hr,posterior_original_sourceBands E P hd t ht πL πP πA upperBid hupperBid hfloor
    Γ hjoint B j,B.ae_observation Γ j] with L hrow hsource hobs
  intro hS
  have hpattern : L∈patternEvent (identityMask S) := (identityPattern_iff S L).mpr hS
  have he : (fun d : UserProfile m 2 => LocalCoordinates.privateRow E S
      (observe (drawsRealization d) (otherProposer j)))=ᵐ[B.posterior j L]
      sortedMissingRow E (observedEntry j) (identityMask S) S.card (identityEnumeration S)
        (fun x : UserDraw 2 => LocalCoordinates.decode E x.1.2.bid) := by
    filter_upwards [hsource,hobs] with d hd ho
    rw [PrivateIdentitySort.native_privateRow_eq_sorted]
    apply congrArg (PrivateRowSorting.sortRow E S.card)
    funext a
    let i := PrivateIdentitySort.baselineEmbedding S a
    have hi : i∈S := (PrivateIdentitySort.baseline S a).2
    have hm : observedEntry j (d i)=none := by
      change observe (drawsRealization d) j i=none
      rw [ho]
      exact (hS i).mpr hi
    have hv := sourceBands_missing_other_visible P E t (d i) (hd i) j hm
    change LocalCoordinates.decode E (entryBid (observedEntry (otherProposer j) (d i)))=
      LocalCoordinates.decode E (d (identityEnumeration S a)).1.2.bid
    rw [hv]
    rfl
  exact (Measure.map_congr he).trans (hrow hpattern)

include hjoint in
theorem original_native_private_posterior_all (B : PosteriorSystem Γ) (j : Fin 2) :
    ∀ᵐ L ∂observedListLaw Γ j,∀ S : Finset (Fin m),(∀ i,L i=none ↔ i∈S) →
      (B.posterior j L).map
        (fun d : UserProfile m 2 => LocalCoordinates.privateRow E S
          (observe (drawsRealization d) (otherProposer j)))=
        (originalPrivateRow E P hd t ht πL πP πA upperBid hupperBid hfloor S.card : Measure _) :=
  ae_all_iff.mpr (fun S => original_native_private_posterior E P hd t ht πL πP πA
    upperBid hupperBid hfloor Γ hjoint B j S)

end FCAppendix.Affine.Tail04.NativePrivatePosterior
