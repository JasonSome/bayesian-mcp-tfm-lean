import FCAppendix.Affine.Hybrid.GuardedPayoff

noncomputable section
namespace FCAppendix.Affine.Hybrid
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def singletonPayoff (v bid : ℝ) (i : ι) (ST : Finset ι × Finset ι) : ℝ :=
  ((v-bid)/2)*((if i∈ST.1 then 1 else 0)+(if i∈ST.2 then 1 else 0))

lemma expect_product_singletonPayoff (mu nu : FiniteLaw (Finset ι))
    (v bid : ℝ) (i : ι) :
    (mu.prod nu).expect (singletonPayoff v bid i)=
      ((v-bid)/2)*(mu.prob (fun S=>i∈S)+nu.prob (fun S=>i∈S)) := by
  have hfst : (mu.prod nu).expect (fun ST=>if i∈ST.1 then (1:ℝ) else 0)=
      mu.prob (fun S=>i∈S) := by
    simpa only [mul_one,FiniteLaw.expect_const,FiniteLaw.prob_eq_expect] using
      FiniteLaw.expect_prod_mul mu nu (fun S=>if i∈S then (1:ℝ) else 0) (fun _=>1)
  have hsnd : (mu.prod nu).expect (fun ST=>if i∈ST.2 then (1:ℝ) else 0)=
      nu.prob (fun S=>i∈S) := by
    simpa only [one_mul,FiniteLaw.expect_const,FiniteLaw.prob_eq_expect] using
      FiniteLaw.expect_prod_mul mu nu (fun _=>1) (fun S=>if i∈S then (1:ℝ) else 0)
  change (mu.prod nu).expect (fun ST => ((v-bid)/2)*
    ((if i∈ST.1 then (1:ℝ) else 0)+(if i∈ST.2 then (1:ℝ) else 0))) = _
  rw [FiniteLaw.expect_const_mul,FiniteLaw.expect_add,hfst,hsnd]

def ownerSetSingletonPayoff (xi v : ℝ) (b : ι→ℝ) (r : ℕ) (i : ι) (E : Finset ι) : ℝ :=
  if i∈E then (v-b i)/2 else
    (v-b i)*exposure xi (finiteMultiplier xi b (Finset.univ\E) r) (b i)

namespace GuardedData

theorem expected_singletonPayoff (G : GuardedData ι) (v : ℝ) (i : ι) :
    G.jointLaw.expect (singletonPayoff v (G.bid i) i)=
      ownerSetSingletonPayoff G.xi v G.bid G.residual i (G.owner₁∪G.owner₂) := by
  rw [jointLaw,expect_product_singletonPayoff,G.law₁_implements.2,G.law₂_implements.2]
  by_cases h1 : i∈G.owner₁
  · have h2 : i∉G.owner₂ := fun hi=>(Finset.disjoint_left.mp G.owners_disjoint) h1 hi
    have hD : i∉G.mixed := fun hi=>(G.mixed_iff i).mp hi |>.1 h1
    simp [ownerSetSingletonPayoff,p₁,p₂,ownerMixedMarginal,h1,h2,hD]
  · by_cases h2 : i∈G.owner₂
    · have hD : i∉G.mixed := fun hi=>(G.mixed_iff i).mp hi |>.2 h2
      simp [ownerSetSingletonPayoff,p₁,p₂,ownerMixedMarginal,h1,h2,hD]
    · have hD : i∈G.mixed := (G.mixed_iff i).mpr ⟨h1,h2⟩
      simp only [ownerSetSingletonPayoff,Finset.mem_union,h1,h2,false_or,
        ↓reduceIte,p₁,p₂,ownerMixedMarginal,if_pos hD]
      unfold multiplier mixed
      ring

end GuardedData

lemma sourceOwnersLaw_expect_union [Nonempty ι] (b : ι→ℝ) (K1 K2 : ℕ)
    (hN : 2≤Fintype.card ι) (hK0 : 0<K1+K2) (hKN : K1+K2≤Fintype.card ι)
    (f : Finset ι→ℝ) :
    (sourceOwnersLaw b K1 K2).expect (fun AB=>f (AB.1∪AB.2))=
      (favoredSetLaw b (K1+K2)).expect f := by
  rw [sourceOwnersLaw,if_neg (by omega),exclusiveOwnersLaw,FiniteLaw.expect_finiteMix]
  apply expect_congr_on_support
  intro E hE
  have hcard := favoredSetLaw_support b hN (by omega) hKN E hE
  apply ownerDivision_expect_union (Finset.card_pos.mp (by omega))
  omega

def sourceSingletonPayoff [Nonempty ι] (xi v : ℝ) (b : ι→ℝ)
    (r K1 K2 : ℕ) (i : ι) : ℝ :=
  (sourceOwnersLaw b K1 K2).expect
    (fun AB=>ownerSetSingletonPayoff xi v b r i (AB.1∪AB.2))

lemma sourceSingletonPayoff_eq_favored [Nonempty ι] (xi v : ℝ) (b : ι→ℝ)
    (r K1 K2 : ℕ) (i : ι) (hN : 2≤Fintype.card ι)
    (hK0 : 0<K1+K2) (hKN : K1+K2≤Fintype.card ι) :
    sourceSingletonPayoff xi v b r K1 K2 i=
      (favoredSetLaw b (K1+K2)).expect (ownerSetSingletonPayoff xi v b r i) :=
  sourceOwnersLaw_expect_union b K1 K2 hN hK0 hKN _

end FCAppendix.Affine.Hybrid
