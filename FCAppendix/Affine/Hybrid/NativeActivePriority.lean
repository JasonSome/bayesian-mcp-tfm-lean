import FCAppendix.Affine.Hybrid.NativeContinuation

noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes
open scoped BigOperators
variable {m : ℕ}

theorem acceptance_bounds (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (i : Fin m) :
    0 ≤ acceptance ξ hξ hξ1 c j X i ∧ acceptance ξ hξ hξ1 c j X i ≤ 1:=by
  constructor
  · exact integral_nonneg (fun _=>by dsimp only;split <;> norm_num)
  · have hh:=integral_mono_of_nonneg
      (μ:=(volume : Measure unitInterval))
      (f:=fun s=>if i∈select ξ hξ hξ1 c j X s then (1:ℝ) else 0)
      (g:=fun _=> (1:ℝ)) (ae_of_all _ (fun _=>by dsimp only;split <;> norm_num))
      (integrable_const 1) (ae_of_all _ (fun _=>by dsimp only;split <;> norm_num))
    simpa only [acceptance,integral_const,probReal_univ,smul_eq_mul,mul_one] using hh

theorem receipt_bounds (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (j : Fin 2) (X : ClassifiedContext m) (hX : NonnegativeList X.1) (i : Fin m) :
    (1-ξ)*entryBid (X.1 i) ≤ receipt ξ hξ hξ1 c j X i ∧
      receipt ξ hξ hξ1 c j X i ≤ entryBid (X.1 i):=by
  obtain ⟨hp0,hp1⟩:=acceptance_bounds ξ hξ hξ1 c (otherProposer j) X i
  have hb:=hX i
  dsimp only [receipt]
  constructor <;> nlinarith [mul_nonneg hb (mul_nonneg hξ.le hp0),mul_nonneg hb (mul_nonneg hξ.le (sub_nonneg.mpr hp1))]

theorem active_included_when_fit (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1) (j : Fin 2) (s : unitInterval)
    (d : ℝ) (hd : 0 ≤ d) (A : Finset (Fin m))
    (hA : ∀i∈A,d<(1-ξ)*entryBid (X.1 i))
    (hlow : ∀i∉A,entryBid (X.1 i) ≤ d) (hfit : A.card ≤ residual c j X) :
    A⊆select ξ hξ hξ1 c j X s:=by
  intro i hi
  have ho:=select_numerical_optimal ξ hξ hξ1 c X hX j s
  have hri : d<receipt ξ hξ hξ1 c j X i:=
    (hA i hi).trans_le (receipt_bounds ξ hξ hξ1 c j X hX i).1
  apply Finite.included_of_few_competitors _ _ _ ho i (hd.trans_lt hri)
  have hsub : (Finset.univ.filter (fun k=>k≠i ∧ receipt ξ hξ hξ1 c j X i ≤
      receipt ξ hξ hξ1 c j X k))⊆A.erase i:=by
    intro k hk
    obtain ⟨hki,hik⟩:=(Finset.mem_filter.mp hk).2
    refine Finset.mem_erase.mpr ⟨hki,?_⟩
    by_contra hka
    have hh:=(receipt_bounds ξ hξ hξ1 c j X hX k).2.trans (hlow k hka)
    linarith
  have hh:=Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hi] at hh
  have hpos : 0<A.card:=Finset.card_pos.mpr ⟨i,hi⟩
  omega

theorem low_excluded_under_active_overload (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1) (j : Fin 2) (s : unitInterval)
    (d : ℝ) (A : Finset (Fin m)) (hA : ∀i∈A,d<(1-ξ)*entryBid (X.1 i))
    (hlow : ∀i∉A,entryBid (X.1 i) ≤ d) (hover : residual c j X ≤ A.card) :
    select ξ hξ hξ1 c j X s⊆A:=by
  intro i hi
  by_contra hia
  have ho:=select_numerical_optimal ξ hξ hξ1 c X hX j s
  have hr : receipt ξ hξ hξ1 c j X i ≤ d:=
    (receipt_bounds ξ hξ hξ1 c j X hX i).2.trans (hlow i hia)
  have hsub : A⊆Finset.univ.filter (fun k=>receipt ξ hξ hξ1 c j X i<receipt ξ hξ hξ1 c j X k):=by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr.trans_lt
      ((hA k hk).trans_le (receipt_bounds ξ hξ hξ1 c j X hX k).1)⟩
  exact Finite.excluded_of_many_better _ _ _ ho i (hover.trans (Finset.card_le_card hsub)) hi

theorem active_priority_from_floor (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1) (j : Fin 2) (s : unitInterval)
    (d R : ℝ) (hd : 0 ≤ d) (hgap : d<(1-ξ)*R) (A : Finset (Fin m))
    (hfloor : ∀i∈A,R ≤ entryBid (X.1 i)) (hlow : ∀i∉A,entryBid (X.1 i) ≤ d) :
    (A.card ≤ residual c j X→A⊆select ξ hξ hξ1 c j X s) ∧
    (residual c j X ≤ A.card→select ξ hξ hξ1 c j X s⊆A):=by
  have hA : ∀i∈A,d<(1-ξ)*entryBid (X.1 i):=fun i hi=>
    hgap.trans_le (mul_le_mul_of_nonneg_left (hfloor i hi) (by linarith))
  exact ⟨active_included_when_fit ξ hξ hξ1 c X hX j s d hd A hA hlow,
    low_excluded_under_active_overload ξ hξ hξ1 c X hX j s d A hA hlow⟩

end FCAppendix.Affine.Hybrid.NativeContinuation
