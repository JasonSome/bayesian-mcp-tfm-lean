import FCAppendix.Affine.Hybrid.SelectorSampling
import FCAppendix.Affine.Hybrid.OwnerLaw

noncomputable section
namespace FCAppendix.Affine.Hybrid
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def broadcastPayoff (eta v bid : ℝ) (i : ι) (ST : Finset ι × Finset ι) : ℝ :=
  (v-bid)*(if i∈ST.1 ∨ i∈ST.2 then 1 else 0)-
    eta*bid*(if i∈ST.1 ∧ i∈ST.2 then 1 else 0)

lemma expect_product_broadcastPayoff (mu nu : FiniteLaw (Finset ι))
    (eta v bid : ℝ) (i : ι) :
    (mu.prod nu).expect (broadcastPayoff eta v bid i)=
      (v-bid)*(mu.prob (fun S=>i∈S)+nu.prob (fun S=>i∈S)-
        mu.prob (fun S=>i∈S)*nu.prob (fun S=>i∈S))-
      eta*bid*(mu.prob (fun S=>i∈S)*nu.prob (fun S=>i∈S)) := by
  have hpoint (ST : Finset ι × Finset ι) : broadcastPayoff eta v bid i ST=
      (v-bid)*((if i∈ST.1 then (1:ℝ) else 0)+(if i∈ST.2 then (1:ℝ) else 0)-
        (if i∈ST.1 then (1:ℝ) else 0)*(if i∈ST.2 then (1:ℝ) else 0))-
      eta*bid*((if i∈ST.1 then (1:ℝ) else 0)*(if i∈ST.2 then (1:ℝ) else 0)) := by
    unfold broadcastPayoff
    split_ifs <;> simp_all
  rw [FiniteLaw.expect_congr _ hpoint,FiniteLaw.expect_sub,
    FiniteLaw.expect_const_mul,FiniteLaw.expect_const_mul,
    FiniteLaw.expect_sub,FiniteLaw.expect_add]
  have hfst : (mu.prod nu).expect (fun ST=>if i∈ST.1 then (1:ℝ) else 0)=
      mu.prob (fun S=>i∈S) := by
    simpa only [mul_one,FiniteLaw.expect_const,FiniteLaw.prob_eq_expect] using
      FiniteLaw.expect_prod_mul mu nu (fun S=>if i∈S then (1:ℝ) else 0) (fun _=>1)
  have hsnd : (mu.prod nu).expect (fun ST=>if i∈ST.2 then (1:ℝ) else 0)=
      nu.prob (fun S=>i∈S) := by
    simpa only [one_mul,FiniteLaw.expect_const,FiniteLaw.prob_eq_expect] using
      FiniteLaw.expect_prod_mul mu nu (fun _=>1) (fun S=>if i∈S then (1:ℝ) else 0)
  have hprod : (mu.prod nu).expect
      (fun ST=>(if i∈ST.1 then (1:ℝ) else 0)*(if i∈ST.2 then (1:ℝ) else 0))=
      mu.prob (fun S=>i∈S)*nu.prob (fun S=>i∈S) := by
    simp only [FiniteLaw.prob_eq_expect]
    exact FiniteLaw.expect_prod_mul mu nu (fun S=>if i∈S then (1:ℝ) else 0)
      (fun S=>if i∈S then (1:ℝ) else 0)
  rw [hfst,hsnd,hprod]

def ownerSetPayoff (xi eta v : ℝ) (b : ι→ℝ) (r : ℕ) (i : ι) (E : Finset ι) : ℝ :=
  if i∈E then v-b i else
    independentTwo eta v (b i)
      (exposure xi (finiteMultiplier xi b (Finset.univ\E) r) (b i))

namespace GuardedData

theorem expected_broadcastPayoff (G : GuardedData ι) (eta v : ℝ) (i : ι) :
    G.jointLaw.expect (broadcastPayoff eta v (G.bid i) i)=
      ownerSetPayoff G.xi eta v G.bid G.residual i (G.owner₁∪G.owner₂) := by
  rw [jointLaw,expect_product_broadcastPayoff,G.law₁_implements.2,G.law₂_implements.2]
  by_cases h1 : i∈G.owner₁
  · have h2 : i∉G.owner₂ := fun hi=>(Finset.disjoint_left.mp G.owners_disjoint) h1 hi
    have hD : i∉G.mixed := fun hi=>(G.mixed_iff i).mp hi |>.1 h1
    simp [ownerSetPayoff,p₁,p₂,ownerMixedMarginal,h1,h2,hD]
  · by_cases h2 : i∈G.owner₂
    · have hD : i∉G.mixed := fun hi=>(G.mixed_iff i).mp hi |>.2 h2
      simp [ownerSetPayoff,p₁,p₂,ownerMixedMarginal,h1,h2,hD]
    · have hD : i∈G.mixed := (G.mixed_iff i).mpr ⟨h1,h2⟩
      simp only [ownerSetPayoff,Finset.mem_union,h1,h2,false_or,
        ↓reduceIte,p₁,p₂,ownerMixedMarginal,if_pos hD]
      unfold independentTwo multiplier mixed
      ring

end GuardedData

lemma expect_congr_on_support {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    {f g : Ω→ℝ} (h : ∀x,P.mass x≠0→f x=g x) : P.expect f=P.expect g := by
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P.mass x=0
  · rw [hx,zero_mul,zero_mul]
  · rw [h x hx]

lemma ownerDivision_expect_union {E : Finset ι} (hE : E.Nonempty) {K1 : ℕ}
    (hK : K1≤E.card) (f : Finset ι→ℝ) :
    (ownerDivision E K1).expect (fun AB=>f (AB.1∪AB.2))=f E := by
  rw [←FiniteLaw.expect_const (ownerDivision E K1) (f E)]
  apply expect_congr_on_support
  intro AB hAB
  rw [(ownerDivision_support hE hK AB.1 AB.2 hAB).2.2.2.2]

theorem sourceOwnersLaw_expect_ownerSetPayoff [Nonempty ι]
    (xi eta v : ℝ) (b : ι→ℝ) (r K1 K2 : ℕ) (i : ι)
    (hN : 2≤Fintype.card ι) (hK0 : 0<K1+K2) (hKN : K1+K2≤Fintype.card ι) :
    (sourceOwnersLaw b K1 K2).expect
      (fun AB=>ownerSetPayoff xi eta v b r i (AB.1∪AB.2))=
      (rankLaw b).expect (fun t=>(conditionalFill (K1+K2) t).expect
        (ownerSetPayoff xi eta v b r i)) := by
  rw [sourceOwnersLaw,if_neg (by omega),exclusiveOwnersLaw,FiniteLaw.expect_finiteMix]
  have he : (favoredSetLaw b (K1+K2)).expect
      (fun E=>(ownerDivision E K1).expect
        (fun AB=>ownerSetPayoff xi eta v b r i (AB.1∪AB.2)))=
      (favoredSetLaw b (K1+K2)).expect (ownerSetPayoff xi eta v b r i) := by
    apply expect_congr_on_support
    intro E hE
    have hcard := favoredSetLaw_support b hN (by omega) hKN E hE
    apply ownerDivision_expect_union (Finset.card_pos.mp (by omega))
    omega
  rw [he,favoredSetLaw,FiniteLaw.expect_finiteMix]

end FCAppendix.Affine.Hybrid
