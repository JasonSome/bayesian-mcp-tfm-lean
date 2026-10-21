import FCAppendix.Affine.Tail04.FiniteReceiptLevels
import FCAppendix.Affine.Tail04.EqualPrivateAmbient

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualReceiptLevels
open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateFrontier EqualPrivateSignal EqualPrivateContinuity
open scoped BigOperators

local instance (J : Type*) : TopologicalSpace (Finset J) := ⊥
local instance (J : Type*) : DiscreteTopology (Finset J) := ⟨rfl⟩
local instance (J : Type*) : MeasurableSpace (Finset J) := ⊤
local instance (J : Type*) : BorelSpace (Finset J) := ⟨borel_eq_top_of_discrete.symm⟩

section Energy
variable {ι T A : Type*} [Fintype ι]
  [TopologicalSpace T] [MeasurableSpace T] [CompactSpace T] [PolishSpace T] [BorelSpace T]
  [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A] [MetrizableSpace A]
  [BorelSpace A] [Nonempty A]
  (μ : Measure T) [IsProbabilityMeasure μ]

omit [PolishSpace T] [Nonempty A] [IsProbabilityMeasure μ] in
theorem other_means_of_same_receipt (x : ι→ C(T×A,ℝ)) (r : C(T×A,ℝ))
    (b b' : ι→ℝ) (ξ : ℝ) (hξ : 0< ξ) (hb : ∀ j,0< b j)
    (i : ι) (hother : ∀ j,j≠i→ b' j=b j)
    (π τ : Plan (A:=A) μ)
    (hπ : IntegralOptimal π (score x r b (marginal x π) ξ))
    (hτ : IntegralOptimal τ (score x r b' (marginal x τ) ξ))
    (hown : b i*(1-ξ*marginal x π i)=b' i*(1-ξ*marginal x τ i)) :
    ∀ j,j≠i→ marginal x π j=marginal x τ j := by
  let d := fun j => marginal x π j-marginal x τ j
  have he := response_energy μ x r b b' ξ π τ hπ hτ
  have hc : (∑ j,(b j-b' j)*(1-ξ*marginal x τ j)*d j)=
      (b i-b' i)*(1-ξ*marginal x τ i)*d i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hother j hji]
      ring
    · simp
  change ξ*(∑ j,b j*(d j)^2)≤∑ j,(b j-b' j)*(1-ξ*marginal x τ j)*d j at he
  rw [hc] at he
  have hid : (b i-b' i)*(1-ξ*marginal x τ i)*d i=ξ*(b i*(d i)^2) := by
    have ha : (b i-b' i)*(1-ξ*marginal x τ i)=ξ*b i*d i := by
      dsimp only [d]
      nlinarith [hown]
    rw [ha]
    ring
  rw [hid] at he
  have hs : (∑ j,b j*(d j)^2)≤ b i*(d i)^2 := by nlinarith
  have hn : 0≤∑ j∈Finset.univ.erase i,b j*(d j)^2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hb j).le (sq_nonneg _))
  have hh := Finset.sum_erase_add Finset.univ (fun j => b j*(d j)^2) (Finset.mem_univ i)
  have hz : (∑ j∈Finset.univ.erase i,b j*(d j)^2)=0 := by linarith
  intro j hji
  have hj := Finset.single_le_sum (fun k _ => mul_nonneg (hb k).le (sq_nonneg (d k)))
    (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
  change b j*(d j)^2≤∑ k∈Finset.univ.erase i,b k*(d k)^2 at hj
  rw [hz] at hj
  have hprod : b j * (d j)^2 = 0 :=
    le_antisymm hj (mul_nonneg (hb j).le (sq_nonneg _))
  have hsq : (d j)^2 = 0 := (mul_eq_zero.mp hprod).resolve_left (hb j).ne'
  have hd : d j = 0 := sq_eq_zero_iff.mp hsq
  exact sub_eq_zero.mp hd

end Energy

section LevelSets
variable {N H c : ℕ} {R V : ℝ}

lemma card_filter_real {J : Type*} [Fintype J] (S : Finset J) (P : J→ Prop) :
    ((S.filter P).card:ℝ)=∑ j : J,if j∈S ∧ P j then (1:ℝ) else 0 := by
  let f : J→ℝ := fun j => if j∈S ∧ P j then 1 else 0
  have he : (∑ j∈S,f j)=∑ j : J,f j :=
    Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by simp [f,hj])
  rw [←he]
  have hs : (∑ j∈S,f j)=∑ j∈S,if P j then (1:ℝ) else 0 :=
    Finset.sum_congr rfl (fun j hj => by simp only [f,hj,true_and])
  rw [hs,←Finset.sum_filter]
  simp

def activeLevel (b q : Fin N→ℝ) (ξ a : ℝ) :
    C(Signal H R V×Action N H c,ℝ) :=
  ∑ i∈Finset.univ.filter (fun i => b i*(1-ξ*q i)=a),activeIndicator N H c R V i

lemma activeLevel_eq_card (b q : Fin N→ℝ) (ξ a : ℝ) (s : Signal H R V)
    (hprivate : ∀ j,partialBid (s j)≠a) (A : Action N H c) :
    activeLevel (H:=H) (c:=c) (R:=R) (V:=V) b q ξ a (s,A)=
      (((selected s A).filter fun j => itemReceipt b q ξ s j=a).card:ℝ) := by
  rw [card_filter_real,Fintype.sum_sum_type]
  simp only [itemReceipt,hprivate,and_false,ite_false,Finset.sum_const_zero,add_zero,
    activeLevel,ContinuousMap.sum_apply,activeIndicator,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : b i*(1-ξ*q i)=a <;> by_cases hs : Sum.inl i∈selected s A <;> simp [hi,hs]

lemma activeLevel_unique (b q : Fin N→ℝ) (ξ a : ℝ) (ha : 0< a)
    (s : Signal H R V) (hprivate : ∀ j,partialBid (s j)≠a)
    (A A' : Action N H c)
    (hA : PrivatePayoffContinuity.Best ξ (b,q,s) A)
    (hA' : PrivatePayoffContinuity.Best ξ (b,q,s) A') :
    activeLevel (c:=c) b q ξ a (s,A)=activeLevel (c:=c) b q ξ a (s,A') := by
  rw [activeLevel_eq_card b q ξ a s hprivate A,activeLevel_eq_card b q ξ a s hprivate A']
  exact congrArg Nat.cast (FiniteReceiptLevels.level_card_eq
    (c-upperCount (marks s)) (itemReceipt b q ξ s) a ha (selected s A) (selected s A')
    (finiteOptimal_of_residualOptimal b q ξ s (selected s A) (selected_feasible s A)
      (PrivatePayoffContinuity.residualOptimal_of_best ξ (b,q,s) A hA))
    (finiteOptimal_of_residualOptimal b q ξ s (selected s A') (selected_feasible s A')
      (PrivatePayoffContinuity.residualOptimal_of_best ξ (b,q,s) A' hA')))

variable (μ : Measure (Signal H R V)) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in

theorem mean_activeLevel_eq (b q : Fin N→ℝ) (ξ a : ℝ) (ha : 0< a)
    (hprivate : ∀ᵐ s ∂μ,∀ j,partialBid (s j)≠a)
    (π τ : Plan (A:=Action N H c) μ)
    (hπ : AllActionOptimal π (score (activeIndicator N H c R V)
      (privateReceipt N H c R V) b q ξ))
    (hτ : AllActionOptimal τ (score (activeIndicator N H c R V)
      (privateReceipt N H c R V) b q ξ)) :
    (∑ i∈Finset.univ.filter (fun i => b i*(1-ξ*q i)=a),marginal (activeIndicator N H c R V) π i)=
      ∑ i∈Finset.univ.filter (fun i => b i*(1-ξ*q i)=a),marginal (activeIndicator N H c R V) τ i := by
  let F := activeLevel (H:=H) (c:=c) (R:=R) (V:=V) b q ξ a
  let G : Signal H R V→ℝ := fun s => F (s,PrivatePayoffContinuity.chosen ξ (b,q,s))
  have hG : Measurable G := F.continuous.measurable.comp
    (measurable_id.prodMk ((PrivatePayoffContinuity.measurable_chosen ξ).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))))
  have hset : MeasurableSet {s : Signal H R V | ∀ j,partialBid (s j)≠a} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun j => (measurableSet_eq_fun
      (continuous_partialBid.comp (continuous_apply j)).measurable measurable_const).compl)
  have hm (η : Plan (A:=Action N H c) μ)
      (hη : AllActionOptimal η (score (activeIndicator N H c R V)
        (privateReceipt N H c R V) b q ξ)) :
      mean η F=∫ s,G s ∂μ := by
    have hp : ∀ᵐ z ∂(η.1 : Measure (Signal H R V × Action N H c)),∀ j,partialBid (z.1 j)≠a := by
      have h := hprivate
      rw [←η.2] at h
      exact (ae_map_iff measurable_fst.aemeasurable hset).mp h
    calc
      mean η F=∫ z,G z.1 ∂(η.1 : Measure (Signal H R V × Action N H c)) := by
        apply integral_congr_ae
        filter_upwards [hη,hp] with z hz hpz
        change activeLevel (c := c) b q ξ a (z.1,z.2) =
          activeLevel (c := c) b q ξ a (z.1,PrivatePayoffContinuity.chosen ξ (b,q,z.1))
        apply activeLevel_unique b q ξ a ha z.1 hpz z.2
          (PrivatePayoffContinuity.chosen ξ (b,q,z.1))
        · intro A
          have hh := hz A
          change score (activeIndicator N H c R V) (privateReceipt N H c R V) b q ξ
            (z.1,A) ≤ score (activeIndicator N H c R V) (privateReceipt N H c R V) b q ξ
            (z.1,z.2) at hh
          simpa only [PrivatePayoffContinuity.Best,PrivatePayoffContinuity.inputScore,
            score_eq_revenue] using hh
        · exact PrivatePayoffContinuity.chosen_best ξ (b,q,z.1)
      _=∫ s,G s ∂μ := by
        have h := integral_map (μ:=(η.1 : Measure (Signal H R V × Action N H c))) measurable_fst.aemeasurable hG.aestronglyMeasurable
        rw [η.2] at h
        exact h.symm
  have he := (hm π hπ).trans (hm τ hτ).symm
  simpa only [F,activeLevel,mean_sum,marginal] using he

end LevelSets

section Injectivity
variable {N H c : ℕ} {R V : ℝ}
  (μ : Measure (Signal H R V)) [IsProbabilityMeasure μ]
  (hlevels : ∀ a : ℝ,0< a→∀ᵐ s ∂μ,∀ j,partialBid (s j)≠a)

include hlevels in
theorem own_bid_eq_of_receipt_eq (b b' : Fin N→ℝ) (ξ : ℝ)
    (hξ : 0< ξ) (hξ1 : ξ<1) (hb : ∀ j,0< b j) (_hb' : ∀ j,0< b' j)
    (i : Fin N) (hother : ∀ j,j≠i→ b' j=b j)
    (π τ : Plan (A:=Action N H c) μ)
    (hπ : IntegralOptimal π (score (activeIndicator N H c R V)
      (privateReceipt N H c R V) b (marginal (activeIndicator N H c R V) π) ξ))
    (hτ : IntegralOptimal τ (score (activeIndicator N H c R V)
      (privateReceipt N H c R V) b' (marginal (activeIndicator N H c R V) τ) ξ))
    (hown : b i*(1-ξ*marginal (activeIndicator N H c R V) π i)=
      b' i*(1-ξ*marginal (activeIndicator N H c R V) τ i)) : b i=b' i := by
  let x := activeIndicator N H c R V
  let r := privateReceipt N H c R V
  let q := marginal x π
  let q' := marginal x τ
  let a := b i*(1-ξ*q i)
  have hqi := marginal_mem_Icc μ x (fun j z => activeIndicator_bounds j z) π i
  have hpositive : 0<1-ξ*q i := by dsimp only [q];nlinarith [hqi.2]
  have ha : 0< a := mul_pos (hb i) hpositive
  have hothers := other_means_of_same_receipt μ x r b b' ξ hξ hb i hother π τ hπ hτ hown
  have hw : ∀ j,b' j*(1-ξ*q' j)=b j*(1-ξ*q j) := by
    intro j
    by_cases hji : j=i
    · subst j
      exact hown.symm
    · dsimp only [q, q']
      rw [hother j hji,hothers j hji]
  have hu : score x r b' q' ξ=score x r b q ξ := by
    ext z
    simp only [score,ContinuousMap.add_apply,ContinuousMap.sum_apply,
      ContinuousMap.smul_apply,smul_eq_mul,hw]
  have hπall := allAction_of_integralOptimal μ π _ (score x r b q ξ).continuous hπ
  have hτall := allAction_of_integralOptimal μ τ _ (score x r b' q' ξ).continuous hτ
  rw [hu] at hτall
  have he := mean_activeLevel_eq μ b q ξ a ha (hlevels a ha) π τ hπall hτall
  let C := Finset.univ.filter (fun j => b j*(1-ξ*q j)=a)
  have hi : i∈C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
  have hrest : (∑ j∈C.erase i,q j)=∑ j∈C.erase i,q' j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hothers j (Finset.mem_erase.mp hj).1
  have hs := Finset.sum_erase_add C q hi
  have hs' := Finset.sum_erase_add C q' hi
  have hq : q i=q' i := by
    change (∑ j∈C,q j)=∑ j∈C,q' j at he
    linarith
  change b i*(1-ξ*q i)=b' i*(1-ξ*q' i) at hown
  rw [←hq] at hown
  have hz : (b i-b' i)*(1-ξ*q i)=0 := by nlinarith [hown]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt hpositive))

end Injectivity
end FCAppendix.Affine.Tail04.EqualReceiptLevels
