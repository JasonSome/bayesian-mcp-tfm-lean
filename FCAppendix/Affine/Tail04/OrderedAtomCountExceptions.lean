import FCAppendix.Affine.Tail04.OrderedAtomActiveGeometry
import FCAppendix.Affine.Tail04.NativeCountGuards

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomCountExceptions
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint LatentNoisyPopulation LatentSpeciesCalculus
open OrderedAtomActiveLaw OrderedAtomActiveCompression OriginalActiveCrossingCarrier
open Hybrid LowBody
open scoped BigOperators

lemma restore_succAbove {X : Type*} [MeasurableSpace X] {N : ℕ}
    (j : Fin (N+1)) (y : X) (row : Fin N→ X) (k : Fin N) :
    restore j y row (j.succAbove k)=row k := by
  have h := congrArg (fun p : X×(Fin N→ X) => p.2 k)
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => X) j).apply_symm_apply (y,row))
  exact h

lemma count_eq_categoryCount (D : Data) {N : ℕ} (kind : Fin N→ Fin 4) (k : Fin 4) :
    D.count kind k=categoryCount k kind := by
  simp only [Data.count,categoryCount,hitCount,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : kind i=k <;> simp only [h,ite_true,ite_false]

lemma count_restore {X : Type*} [MeasurableSpace X] (D : Data) {N : ℕ}
    (tag : X→ Fin 4) (j : Fin (N+1)) (y : X) (row : Fin N→ X) (k : Fin 4) :
    D.count (tags tag (restore j y row)) k=
      (if tag y=k then 1 else 0)+D.count (tags tag row) k := by
  simp only [count_eq_categoryCount,categoryCount,hitCount]
  rw [Fin.sum_univ_succAbove _ j]
  simp only [tags,Function.comp_apply,restore_self,restore_succAbove]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : tag (row r)=k <;> simp only [h,ite_true,ite_false]

lemma count_restore_active {X : Type*} [MeasurableSpace X] (D : Data) {N : ℕ}
    (tag : X→ Fin 4) (j : Fin (N+1)) (y : X) (hy : tag y=1)
    (row : Fin N→ X) (k : Fin 4) (hk : k≠1) :
    D.count (tags tag (restore j y row)) k=D.count (tags tag row) k := by
  rw [count_restore,hy,if_neg (Ne.symm hk),zero_add]

def equalCounts (D : Data) {X : Type*} [MeasurableSpace X] {N : ℕ}
    (tag : X→ Fin 4) (z : X×(Fin N→ X)) : Prop :=
  D.count (tags tag z.2) 2=D.count (tags tag z.2) 3

lemma measurableSet_equalCounts (D : Data) {X : Type*} [MeasurableSpace X] {N : ℕ}
    (tag : X→ Fin 4) (htag : Measurable tag) :
    MeasurableSet {z : X×(Fin N→ X) | equalCounts D tag z} :=
  (((Set.to_countable {kind : Fin N→ Fin 4 | D.count kind 2=D.count kind 3}).measurableSet).preimage
    ((measurable_tags tag htag).comp measurable_snd))

lemma equalCounts_restore_active {X : Type*} [MeasurableSpace X] (D : Data) {N : ℕ}
    (tag : X→ Fin 4) (j : Fin (N+1)) (x y : X) (hy : tag y=1) (row : Fin N→ X) :
    equalCounts D tag (x,restore j y row) ↔
      categoryCount 2 (tags tag row)=categoryCount 3 (tags tag row) := by
  simp only [equalCounts,count_restore_active D tag j y hy row 2 (by decide),
    count_restore_active D tag j y hy row 3 (by decide),count_eq_categoryCount]

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v→ H≤ upperBid v)
  (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+2:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "Ds" => installOriginal D P t ht
local notation "E" => NativeNoisySource.regions D P hdR H hBH
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid
local notation "Γ" => NativeNoisySource.game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+2) hrare
local notation "tag" => latentTag D P hdR H hBH

include hfloor hrare in
include P t ht πL π upperBid hupperBid hdR H hBH hfloor hrare in
lemma original_remaining_realize :
    (Measure.pi (fun _ : Fin N => μ)).map (fun row j => realize D (row j))=
      Measure.pi (fun _ : Fin N => userLaw Γ) := by
  rw [Measure.pi_map_pi (fun _ => (measurable_realize D).aemeasurable)]
  simp only [realize_original_user D P t ht πL π upperBid hupperBid hdR H hBH hfloor (N+2) hrare]

include hfloor hrare in
include D P t ht πL π upperBid hupperBid hdR H hBH hfloor hrare in
theorem original_equalCounts_conditional (hN : 0< N)
    (j : Fin (N+1)) (x y : Draw) (hy : tag y=1) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {row | equalCounts Ds tag (x,restore j y row)}≤(75/4:ℝ)/Real.sqrt N := by
  have hc := OriginalPopulation.originalJoint_role_correspondence P E rfl t ht.le πL
    (NativeNoisySource.partialPhysical D P t ht π) (NativeNoisySource.activePhysical D P t ht π)
    upperBid hupperBid hfloor
  have hj := NativeNoisySource.game_original_joint D P t ht hdR H hBH πL π
    upperBid hupperBid hfloor (N+2) hrare
  have hl : ∀ᵐ z ∂(Γ).F⊗ₘ(Γ).σ,z.2.bid≤ (E).d ↔ z.1≤ P.d0 := by
    rw [hj]
    exact hc.mono fun _ h => h.1
  have hp : ∀ᵐ z ∂(Γ).F⊗ₘ(Γ).σ,z.2.bid∈(E).privateBids ↔ z.1∈P.privateValues t := by
    rw [hj]
    exact hc.mono fun _ h => h.2.1
  have he := NativeCountGuards.source_private_tie_bound Γ E P rfl t ht.le hl hp
    (fun _ : Fin 0 => 1) N hN
  have hm : Measurable (fun row : Fin N→ Draw => fun k => realize D (row k)) :=
    measurable_pi_lambda _ fun k => (measurable_realize D).comp (measurable_pi_apply k)
  have hs : MeasurableSet {row : Fin N→ UserDraw 2 |
      categoryCount 2 (fun k => (E).coarseTag (row k))=
        categoryCount 3 (fun k => (E).coarseTag (row k))} :=
    ((Set.to_countable {kind : Fin N→ Fin 4 | categoryCount 2 kind=categoryCount 3 kind}).measurableSet).preimage
      (measurable_pi_lambda _ fun k => (E).measurable_coarseTag.comp (measurable_pi_apply k))
  have hevent : {row : Fin N→ Draw | equalCounts Ds tag (x,restore j y row)}=
      (fun row : Fin N→ Draw => fun k => realize D (row k)) ⁻¹'
        {row : Fin N→ UserDraw 2 | categoryCount 2 (fun k => (E).coarseTag (row k))=
          categoryCount 3 (fun k => (E).coarseTag (row k))} := by
    ext row
    exact equalCounts_restore_active Ds tag j x y hy row
  rw [measureReal_def,hevent,←Measure.map_apply hm hs,
    original_remaining_realize D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare]
  simpa only [measureReal_def,fullCategoryCount,categoryCount,hitCount,Fin.sum_univ_zero,zero_add] using he

include hfloor hrare in
include D t ht πL π upperBid hupperBid hdR H hBH hfloor hrare in
theorem original_noLow_conditional (hN : 0< N)
    (j : Fin (N+1)) (y : Draw) (hy : tag y=1) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {row | (Ds).count (tags tag (restore j y row)) 0=0}≤
        Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2) := by
  let L : Set Draw := tag ⁻¹' {0}
  have hL : MeasurableSet L := (measurable_latentTag D P hdR H hBH) (measurableSet_singleton 0)
  have hm : (μ).real L=lowMass P.theta := by
    rw [measureReal_def,original_category_mass D P t ht πL π upperBid hupperBid
      hdR H hBH hfloor (N+1) hrare 0]
    exact ENNReal.toReal_ofReal P.low_mass_pos.le
  have hc (row : Fin N→ Draw) : (Ds).count (tags tag row) 0=Probability.sampleCount L row := by
    simp only [Data.count,tags,Probability.sampleCount,L,mem_preimage,mem_singleton_iff,
      Function.comp_apply]
  have hsub : {row : Fin N→ Draw | (Ds).count (tags tag (restore j y row)) 0=0}⊆
      {row | (Probability.sampleCount L row:ℝ)< lowMass P.theta*(N:ℝ)/2} := by
    intro row hr
    change (Ds).count (tags tag (restore j y row)) 0=0 at hr
    change (Probability.sampleCount L row:ℝ)<lowMass P.theta*(N:ℝ)/2
    rw [count_restore_active Ds tag j y hy row 0 (by decide),hc] at hr
    rw [hr,Nat.cast_zero]
    exact div_pos (mul_pos P.low_mass_pos (Nat.cast_pos.mpr hN)) (by norm_num)
  exact (measureReal_mono hsub).trans
    (NativeFlag.iid_bulk_count_lower_tail μ L hL N hN P.low_mass_pos hm.ge)

end FCAppendix.Affine.Tail04.OrderedAtomCountExceptions
