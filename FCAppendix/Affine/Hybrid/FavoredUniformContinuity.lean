import FCAppendix.Affine.Hybrid.FavoredFiniteRank

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma favoredTargetPayoff_affine_value (xi eta v : ℝ) (b : ι→ℝ) (r K : ℕ) (i t : ι) :
    favoredTargetPayoff xi eta v b r K i t=
      v*(favoredTargetPayoff xi eta 1 b r K i t-favoredTargetPayoff xi eta 0 b r K i t)+
        favoredTargetPayoff xi eta 0 b r K i t := by
  unfold favoredTargetPayoff
  have he : ownerSetPayoff xi eta v b r i=(fun E=>v*(ownerSetPayoff xi eta 1 b r i E-
      ownerSetPayoff xi eta 0 b r i E)+ownerSetPayoff xi eta 0 b r i E) := by
    funext E
    exact ownerSetPayoff_affine_value xi eta v b r i E
  rw [he,FiniteLaw.expect_add,FiniteLaw.expect_const_mul,FiniteLaw.expect_sub]

lemma continuous_box_favoredTargetPayoff {L U : ℝ} (hL : 0<L) (xi eta v : ℝ)
    (r K : ℕ) (i t : ι) (hN : 2≤Fintype.card ι) (hK : 1≤K) (hKN : K<Fintype.card ι) :
    Continuous (fun x : ι→Icc L U=>favoredTargetPayoff xi eta v (fun j=>(x j:ℝ)) r K i t) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto (fun y : ι→Icc L U=>favoredTargetPayoff xi eta v (fun j=>(y j:ℝ)) r K i t)
    (𝓝 x) (𝓝 (favoredTargetPayoff xi eta v (fun j=>(x j:ℝ)) r K i t))
  have hf:=continuousAt_favoredTargetPayoff xi eta v (fun j=>(x j:ℝ)) r K i t hN hK hKN
    (fun j=>hL.trans_le (x j).property.1)
  have hb : Tendsto (fun y : ι→Icc L U=>fun j=>(y j:ℝ)) (𝓝 x) (𝓝 (fun j=>(x j:ℝ))) :=
    continuous_boxBids.tendsto x
  simpa only [Function.comp_def] using hf.tendsto.comp hb

abbrev FavoredBoxInput (ι : Type*) (vlo vhi L U : ℝ) := Icc vlo vhi × (ι→Icc L U)

def boxTargetPayoff {vlo vhi L U : ℝ} (xi eta : ℝ) (r K : ℕ) (i t : ι)
    (x : FavoredBoxInput ι vlo vhi L U) : ℝ :=
  favoredTargetPayoff xi eta x.1 (fun j=>(x.2 j:ℝ)) r K i t

lemma continuous_boxTargetPayoff {vlo vhi L U : ℝ} (hL : 0<L) (xi eta : ℝ)
    (r K : ℕ) (i t : ι) (hN : 2≤Fintype.card ι) (hK : 1≤K) (hKN : K<Fintype.card ι) :
    Continuous (boxTargetPayoff (vlo:=vlo) (vhi:=vhi) (L:=L) (U:=U) xi eta r K i t) := by
  have h0:=(continuous_box_favoredTargetPayoff hL xi eta 0 r K i t hN hK hKN).comp
    (continuous_snd : Continuous (Prod.snd : FavoredBoxInput ι vlo vhi L U→(ι→Icc L U)))
  have h1:=(continuous_box_favoredTargetPayoff hL xi eta 1 r K i t hN hK hKN).comp
    (continuous_snd : Continuous (Prod.snd : FavoredBoxInput ι vlo vhi L U→(ι→Icc L U)))
  have he : boxTargetPayoff (vlo:=vlo) (vhi:=vhi) (L:=L) (U:=U) xi eta r K i t=
      (fun x : FavoredBoxInput ι vlo vhi L U=>(x.1:ℝ)*
        (favoredTargetPayoff xi eta 1 (fun j=>(x.2 j:ℝ)) r K i t-
          favoredTargetPayoff xi eta 0 (fun j=>(x.2 j:ℝ)) r K i t)+
          favoredTargetPayoff xi eta 0 (fun j=>(x.2 j:ℝ)) r K i t) := by
    funext x
    exact favoredTargetPayoff_affine_value xi eta x.1 (fun j=>(x.2 j:ℝ)) r K i t
  rw [he]
  exact ((show Continuous (fun x : FavoredBoxInput ι vlo vhi L U=>(x.1:ℝ)) from by fun_prop).mul
    (h1.sub h0)).add h0

theorem exists_favoredTargetPayoff_modulus {vlo vhi L U : ℝ} (hL : 0<L)
    (xi eta : ℝ) (r K : ℕ) (i : ι) (hN : 2≤Fintype.card ι) (hK : 1≤K)
    (hKN : K<Fintype.card ι) {e : ℝ} (he : 0<e) :
    ∃delta : ℝ,0<delta ∧ ∀x y : FavoredBoxInput ι vlo vhi L U,dist x y<delta→
      ∀t:ι,|boxTargetPayoff xi eta r K i t x-boxTargetPayoff xi eta r K i t y|<e := by
  have hc : Continuous (fun x : FavoredBoxInput ι vlo vhi L U=>
      fun t:ι=>boxTargetPayoff xi eta r K i t x) :=
    continuous_pi (fun t=>continuous_boxTargetPayoff hL xi eta r K i t hN hK hKN)
  obtain ⟨delta,hdelta,hmod⟩:=Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) e he
  refine ⟨delta,hdelta,?_⟩
  intro x y hxy t
  simpa only [Real.dist_eq] using (dist_pi_lt_iff he).mp (hmod hxy) t

lemma dist_update_box_le {L U : ℝ} (x : ι→Icc L U) (i : ι) (y : Icc L U) :
    dist x (Function.update x i y)≤dist (x i) y := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro j
  by_cases hj : j=i
  · subst j;simp
  · simp [Function.update_of_ne hj,dist_nonneg]

theorem exists_favored_near_tie_advantage {xi eta vlo vhi L U : ℝ}
    (hL : 0<L) (heta : 0<eta) (hUv : U<vlo) (r K : ℕ) (i : ι)
    (hN : 2≤Fintype.card ι) (hK : 1≤K) (hKN : K<Fintype.card ι) :
    let G:=(1-fillFraction (ι:=ι) K)*(min (vlo-U) (eta*L)/2)
    ∃delta : ℝ,0<delta ∧ ∀x : FavoredBoxInput ι vlo vhi L U,∀j:ι,j≠i→
      |(x.2 j:ℝ)-(x.2 i:ℝ)|<delta→
      G/2≤boxTargetPayoff xi eta r K i i x-boxTargetPayoff xi eta r K i j x := by
  dsimp only
  let G:=(1-fillFraction (ι:=ι) K)*(min (vlo-U) (eta*L)/2)
  have hNr : 1<(Fintype.card ι:ℝ) := by exact_mod_cast (show 1<Fintype.card ι by omega)
  have hKr : (K:ℝ)<Fintype.card ι := by exact_mod_cast hKN
  have hf : fillFraction (ι:=ι) K<1 := by
    unfold fillFraction
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hm : 0 < min (vlo-U) (eta*L) := lt_min (sub_pos.mpr hUv) (mul_pos heta hL)
  have hG : 0<G := by positivity
  obtain ⟨delta,hdelta,hmod⟩:=exists_favoredTargetPayoff_modulus (vlo:=vlo) (vhi:=vhi) hL xi eta r K i
    hN hK hKN (show 0<G/4 by positivity)
  refine ⟨delta,hdelta,?_⟩
  intro x j hji hclose
  let y : FavoredBoxInput ι vlo vhi L U:=(x.1,Function.update x.2 j (x.2 i))
  have hdist : dist x y<delta := by
    have hp:=dist_update_box_le x.2 j (x.2 i)
    have he : dist x y=dist x.2 (Function.update x.2 j (x.2 i)) := by simp [y,Prod.dist_eq]
    rw [he]
    exact hp.trans_lt (by simpa only [Subtype.dist_eq,Real.dist_eq] using hclose)
  have hi:=hmod x y hdist i
  have hj:=hmod x y hdist j
  have htie : (fun k=>(y.2 k:ℝ)) i=(fun k=>(y.2 k:ℝ)) j := by
    simp [y,Function.update_of_ne hji.symm]
  have hgain:=favoredTargetPayoff_tie_gain (xi:=xi) (eta:=eta) (v:=(y.1:ℝ))
    (L:=L) (U:=U) (vmin:=vlo) (fun k=>(y.2 k:ℝ)) r K i j hji.symm htie hN hK hKN.le heta hL
    (y.2 i).property.1 (y.2 i).property.2 hUv y.1.property.1
  change G≤boxTargetPayoff xi eta r K i i y-boxTargetPayoff xi eta r K i j y at hgain
  have hi':=abs_le.mp hi.le
  have hj':=abs_le.mp hj.le
  change G/2≤_
  linarith [hi'.1,hj'.2]

end FCAppendix.Affine.Hybrid
