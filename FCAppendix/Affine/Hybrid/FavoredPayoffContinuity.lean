import FCAppendix.Affine.Hybrid.FavoredCrossing

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma continuousAt_ownerSetPayoff (xi : ℝ) (eta v : ℝ)
    (b : ι→ℝ) (r : ℕ) (i : ι) (E : Finset ι) (hE : E.card<Fintype.card ι)
    (hb : ∀j,0<b j) : ContinuousAt (fun a=>ownerSetPayoff xi eta v a r i E) b := by
  by_cases hi : i∈E
  · simp only [ownerSetPayoff,if_pos hi]
    change Tendsto (fun a : ι→ℝ=>v-a i) (𝓝 b) (𝓝 (v-b i))
    exact tendsto_const_nhds.sub ((continuous_apply i).tendsto b)
  · let D:=Finset.univ\E
    have hD : D.Nonempty := Finset.sdiff_nonempty_of_card_lt_card (by simpa using hE)
    have hsum : 0<∑j∈D,(b j)⁻¹ := reciprocal_sum_pos b D hD (fun j _=>hb j)
    have hs : ContinuousAt (fun a : ι→ℝ=>∑j∈D,(a j)⁻¹) b :=
      tendsto_finsetSum _ (fun j _=>(continuous_apply j).continuousAt.inv₀ (hb j).ne')
    have hl : ContinuousAt (fun a : ι→ℝ=>finiteMultiplier xi a D r) b :=
      continuousAt_const.div hs hsum.ne'
    have hbi : ContinuousAt (fun a : ι→ℝ=>a i) b := (continuous_apply i).continuousAt
    have hq : ContinuousAt (fun a : ι→ℝ=>exposure xi (finiteMultiplier xi a D r) (a i)) b :=
      (continuousAt_const.sub (hl.div hbi (hb i).ne')).div_const xi
    simp only [ownerSetPayoff,if_neg hi]
    unfold independentTwo
    exact (continuousAt_const.mul ((continuousAt_const.mul hq).sub (hq.pow 2))).sub
      (hbi.mul ((continuousAt_const.mul hq).sub (continuousAt_const.mul (hq.pow 2))))

lemma continuousAt_favoredTargetPayoff (xi : ℝ) (eta v : ℝ)
    (b : ι→ℝ) (r K : ℕ) (i t : ι) (hN : 2≤Fintype.card ι)
    (hK : 1≤K) (hKN : K<Fintype.card ι) (hb : ∀j,0<b j) :
    ContinuousAt (fun a=>favoredTargetPayoff xi eta v a r K i t) b := by
  unfold favoredTargetPayoff FiniteLaw.expect
  apply tendsto_finsetSum
  intro E _
  by_cases hE : (conditionalFill K t).mass E=0
  · simpa only [hE,zero_mul] using (tendsto_const_nhds :
      Tendsto (fun _ : ι→ℝ=>(0:ℝ)) (𝓝 b) (𝓝 0))
  · have hcard := (conditionalFill_implements hN hK hKN.le t).1 E hE
    exact continuousAt_const.mul
      (continuousAt_ownerSetPayoff xi eta v b r i E (by omega) hb)

def sourceOwnerPayoff [Nonempty ι] (xi eta v : ℝ) (b : ι→ℝ)
    (r K1 K2 : ℕ) (i : ι) : ℝ :=
  (sourceOwnersLaw b K1 K2).expect
    (fun AB=>ownerSetPayoff xi eta v b r i (AB.1∪AB.2))

lemma sourceOwnerPayoff_eq_rank [Nonempty ι] (xi eta v : ℝ) (b : ι→ℝ)
    (r K1 K2 : ℕ) (i : ι) (hN : 2≤Fintype.card ι)
    (hK0 : 0<K1+K2) (hKN : K1+K2≤Fintype.card ι) :
    sourceOwnerPayoff xi eta v b r K1 K2 i=
      (rankLaw b).expect (fun t=>favoredTargetPayoff xi eta v b r (K1+K2) i t) :=
  sourceOwnersLaw_expect_ownerSetPayoff xi eta v b r K1 K2 i hN hK0 hKN

theorem continuousAt_sourceOwnerPayoff [Nonempty ι] (xi : ℝ)
    (eta v : ℝ) (b : ι→ℝ) (r K1 K2 : ℕ) (i : ι)
    (hN : 2≤Fintype.card ι) (hK0 : 0<K1+K2)
    (hKN : K1+K2<Fintype.card ι) (hb : ∀j,0<b j)
    (hnotie : ∀j,j≠i→b j≠b i) :
    ContinuousAt (fun a=>sourceOwnerPayoff xi eta v a r K1 K2 i) b := by
  have he (a : ι→ℝ) := sourceOwnerPayoff_eq_rank xi eta v a r K1 K2 i hN hK0 hKN.le
  simp_rw [he]
  apply continuousAt_rankLaw_expect (fun j=>(continuous_apply j).continuousAt)
    (fun t=>continuousAt_favoredTargetPayoff xi eta v b r (K1+K2) i t
      hN (by omega) hKN hb)
  intro t u htu
  by_cases htu' : t=u
  · rw [htu']
  · have hit : i≠t := by
      intro h
      subst t
      exact hnotie u (Ne.symm htu') htu.symm
    have hiu : i≠u := by
      intro h
      subst u
      exact hnotie t htu' htu
    exact favoredTargetPayoff_rival_tie xi eta v b r (K1+K2) i t u hit hiu htu

end FCAppendix.Affine.Hybrid
