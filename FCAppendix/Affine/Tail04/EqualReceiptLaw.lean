import FCAppendix.Affine.Tail04.EqualReceiptLevels

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualReceiptLaw
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional EqualPrivateSignal EqualPrivateFrontier EqualPrivateContinuity

local instance (J : Type*) : TopologicalSpace (Finset J) := ⊥
local instance (J : Type*) : DiscreteTopology (Finset J) := ⟨rfl⟩
local instance (J : Type*) : MeasurableSpace (Finset J) := ⊤
local instance (J : Type*) : BorelSpace (Finset J) := ⟨borel_eq_top_of_discrete.symm⟩

variable {N H c : ℕ} {R V B ξ : ℝ}

def plan (p : PolicyParameters N H R V 1 B) :
    Plan (A:=Action N H c) (WeakProbability.toMeasure p.2) :=
  ⟨(policyLaw N H c R V ξ 1 B p).val,
    congrArg (fun μ : ProbabilityMeasure (Signal H R V) => (μ : Measure (Signal H R V)))
      (EqualPrivateMeasurable.planLaw_spec (activeIndicator N H c R V)
        (privateReceipt N H c R V) ξ 1 B p).1⟩

lemma plan_optimal (p : PolicyParameters N H R V 1 B) :
    IntegralOptimal (plan (c:=c) (ξ:=ξ) p)
      (score (activeIndicator N H c R V) (privateReceipt N H c R V)
        (EqualPrivateMeasurable.bids p) (policyMean N H c R V ξ 1 B p) ξ) :=
  integralOptimal_of_gap_eq_zero (activeIndicator N H c R V) (privateReceipt N H c R V)
    (EqualPrivateMeasurable.bids p) ξ (WeakProbability.toMeasure p.2) (plan p)
      (EqualPrivateMeasurable.planLaw_spec (activeIndicator N H c R V)
        (privateReceipt N H c R V) ξ 1 B p).2

def receipt (μ : WeakProbability.Law (Signal H R V)) (b : Fin N→ Icc (1:ℝ) B)
    (i : Fin N) : ℝ := (b i:ℝ)*(1-ξ*policyMean N H c R V ξ 1 B (b,μ) i)

lemma continuous_receipt (hξ : 0< ξ) (μ : WeakProbability.Law (Signal H R V)) (i : Fin N) :
    Continuous (fun b : Fin N→ Icc (1:ℝ) B => receipt (c:=c) (ξ:=ξ) μ b i) :=
  ((continuous_subtype_val.comp (continuous_apply i)).mul
    (continuous_const.sub (continuous_const.mul
      ((continuous_apply i).comp ((continuous_policyMean N H c R V ξ 1 B hξ (by norm_num)).comp
        (continuous_id.prodMk continuous_const))))))

theorem own_bid_eq_of_receipt_eq (hξ : 0< ξ) (hξ1 : ξ<1)
    (μ : WeakProbability.Law (Signal H R V))
    (hlevels : ∀ a : ℝ,0< a→∀ᵐ s ∂WeakProbability.toMeasure μ,∀ j,partialBid (s j)≠a)
    (b b' : Fin N→ Icc (1:ℝ) B) (i : Fin N)
    (hother : ∀ j,j≠i→ b' j=b j)
    (he : receipt (c:=c) (ξ:=ξ) μ b i=receipt (c:=c) (ξ:=ξ) μ b' i) : b i=b' i := by
  apply Subtype.ext
  exact EqualReceiptLevels.own_bid_eq_of_receipt_eq (WeakProbability.toMeasure μ) hlevels
    (fun j => (b j:ℝ)) (fun j => (b' j:ℝ)) ξ hξ hξ1
    (fun j => (by norm_num : (0:ℝ)<1).trans_le (b j).2.1)
    (fun j => (by norm_num : (0:ℝ)<1).trans_le (b' j).2.1)
    i (fun j hj => congrArg Subtype.val (hother j hj)) (plan (b,μ)) (plan (b',μ))
    (plan_optimal (b,μ)) (plan_optimal (b',μ)) he

theorem own_receipt_injective (hξ : 0< ξ) (hξ1 : ξ<1)
    (μ : WeakProbability.Law (Signal H R V))
    (hlevels : ∀ a : ℝ,0< a→∀ᵐ s ∂WeakProbability.toMeasure μ,∀ j,partialBid (s j)≠a)
    (b : Fin N→ Icc (1:ℝ) B) (i : Fin N) :
    Function.Injective (fun z : Icc (1:ℝ) B =>
      receipt (c:=c) (ξ:=ξ) μ (Function.update b i z) i) := by
  intro x y he
  have h := own_bid_eq_of_receipt_eq hξ hξ1 μ hlevels
    (Function.update b i x) (Function.update b i y) i
    (fun j hj => by simp only [Function.update_of_ne hj]) he
  simpa only [Function.update_self] using h

lemma ae_ne_of_injective {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [NullSingletonClass ν] (f : X→ℝ) (hf : Function.Injective f) (a : ℝ) :
    ∀ᵐ x ∂ν,f x≠a := by
  apply ae_iff.mpr
  change ν {x | ¬f x≠a}=0
  by_cases h : ∃ x,f x=a
  · obtain ⟨x,hx⟩ := h
    have he : {y | ¬f y≠a}=({x} : Set X) := by
      ext y
      simp only [not_not,mem_setOf_eq,mem_singleton_iff]
      exact ⟨fun hy => hf (hy.trans hx.symm),fun hy => hy ▸ hx⟩
    rw [he,measure_singleton]
  · have he : {x | ¬f x≠a}=(∅ : Set X) := by
      ext x
      simp only [mem_setOf_eq,not_not,mem_empty_iff_false,iff_false]
      exact fun hx => h ⟨x,hx⟩
    rw [he,measure_empty]

theorem ae_receipts_ne (hξ : 0< ξ) (hξ1 : ξ<1)
    (μ : WeakProbability.Law (Signal H R V))
    (hlevels : ∀ a : ℝ,0< a→∀ᵐ s ∂WeakProbability.toMeasure μ,∀ j,partialBid (s j)≠a)
    (ν : ProbabilityMeasure (Icc (1:ℝ) B)) [NullSingletonClass (ν : Measure (Icc (1:ℝ) B))] (a : ℝ) :
    ∀ᵐ b ∂Measure.pi (fun _ : Fin N => (ν : Measure (Icc (1:ℝ) B))),∀ i : Fin N,
      receipt (c:=c) (ξ:=ξ) μ b i≠a := by
  cases N with
  | zero => exact ae_of_all _ fun _ i => Fin.elim0 i
  | succ n =>
    apply ae_all_iff.mpr
    intro i
    let M := Measure.pi (fun _ : Fin n => (ν : Measure (Icc (1:ℝ) B)))
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Icc (1:ℝ) B) i
    have he0 (p : Icc (1:ℝ) B×(Fin n→ Icc (1:ℝ) B)) : e.symm p i=p.1 :=
      congrArg Prod.fst (e.apply_symm_apply p)
    have he1 (p : Icc (1:ℝ) B×(Fin n→ Icc (1:ℝ) B)) (j : Fin n) :
        e.symm p (i.succAbove j)=p.2 j :=
      congrArg (fun z => z.2 j) (e.apply_symm_apply p)
    have hj (row : Fin n→ Icc (1:ℝ) B) : Function.Injective
        (fun x : Icc (1:ℝ) B => receipt (c:=c) (ξ:=ξ) μ (e.symm (x,row)) i) := by
      intro x y hxy
      have he := own_bid_eq_of_receipt_eq hξ hξ1 μ hlevels (e.symm (x,row)) (e.symm (y,row)) i
        (fun j hji => by
          obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
          rw [he1,he1]) hxy
      simpa only [he0] using he
    have hsrc : ∀ᵐ p ∂M.prod (ν : Measure (Icc (1:ℝ) B)),
        receipt (c:=c) (ξ:=ξ) μ (e.symm (p.2,p.1)) i≠a :=
      (Measure.ae_prod_iff_ae_ae ((measurableSet_eq_fun
        ((continuous_receipt hξ μ i).measurable.comp
          (e.symm.measurable.comp measurable_swap)) measurable_const).compl)).mpr
        (ae_of_all _ fun row =>
          ae_ne_of_injective (ν : Measure (Icc (1:ℝ) B)) _ (hj row) a)
    have hmp : MeasurePreserving (fun p : (Fin n→ Icc (1:ℝ) B)×Icc (1:ℝ) B => e.symm (p.2,p.1))
        (M.prod (ν : Measure (Icc (1:ℝ) B))) (Measure.pi (fun _ : Fin (n+1) => (ν : Measure (Icc (1:ℝ) B)))) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (ν : Measure (Icc (1:ℝ) B))) i).symm.comp
        (Measure.measurePreserving_swap (μ:=M) (ν:=(ν : Measure (Icc (1:ℝ) B))))
    have hs : MeasurableSet {b : Fin (n+1)→ Icc (1:ℝ) B |
        receipt (c:=c) (ξ:=ξ) μ b i≠a} :=
      (measurableSet_eq_fun (continuous_receipt hξ μ i).measurable measurable_const).compl
    have hp := (ae_map_iff hmp.measurable.aemeasurable hs).mpr hsrc
    rwa [hmp.map_eq] at hp

end FCAppendix.Affine.Tail04.EqualReceiptLaw
