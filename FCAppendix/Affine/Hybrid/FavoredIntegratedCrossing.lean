import FCAppendix.Affine.Hybrid.FavoredFiniteCrossing
import FCAppendix.Probability.FiniteAveraging

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def boxSourceOwnerPayoff {vlo vhi L U : ℝ} (xi eta : ℝ) (r K1 K2 : ℕ) (i : ι)
    (x : FavoredBoxInput ι vlo vhi L U) : ℝ :=
  sourceOwnerPayoff xi eta x.1 (fun j=>(x.2 j:ℝ)) r K1 K2 i

attribute [local irreducible] sourceOwnerPayoff

lemma measurable_boxSourceOwnerPayoff {vlo vhi L U : ℝ} (xi eta : ℝ) (r K1 K2 : ℕ) (i : ι) :
    Measurable (boxSourceOwnerPayoff (vlo:=vlo) (vhi:=vhi) (L:=L) (U:=U) xi eta r K1 K2 i) := by
  have hm : Measurable (fun x : FavoredBoxInput ι vlo vhi L U=>
      ((x.1:ℝ),fun j=>(x.2 j:ℝ))) := by fun_prop
  exact (measurable_joint_sourceOwnerPayoff xi eta r K1 K2 i).comp hm

lemma integrable_boxSourceOwnerPayoff_comp {X : Type*} [MeasurableSpace X]
    {vlo vhi L U : ℝ} (hL : 0<L) (xi eta : ℝ) (r K1 K2 : ℕ) (i : ι)
    (hN : 2≤ Fintype.card ι) (hK : 0<K1+K2) (hKN : K1+K2<Fintype.card ι)
    (mu : Measure X) [IsFiniteMeasure mu] (x : X→ FavoredBoxInput ι vlo vhi L U) (hx : Measurable x) :
    Integrable (fun p=>boxSourceOwnerPayoff xi eta r K1 K2 i (x p)) mu := by
  let u : ι→ C(FavoredBoxInput ι vlo vhi L U,ℝ):=fun t=>
    ⟨boxTargetPayoff xi eta r (K1+K2) i t,continuous_boxTargetPayoff hL xi eta r (K1+K2) i t hN (by omega) hKN⟩
  apply Integrable.of_bound ((measurable_boxSourceOwnerPayoff xi eta r K1 K2 i).comp hx).aestronglyMeasurable
    (∑t:ι,‖u t‖)
  exact ae_of_all _ (fun p=>by
    rw [Real.norm_eq_abs]
    change |sourceOwnerPayoff xi eta (x p).1 (fun j=>((x p).2 j:ℝ)) r K1 K2 i|≤ _
    rw [sourceOwnerPayoff_eq_rank xi eta (x p).1 _ r K1 K2 i hN hK hKN.le]
    calc
      _≤∑t:ι,‖favoredTargetPayoff xi eta (x p).1 (fun j=>((x p).2 j:ℝ)) r (K1+K2) i t‖:=
        FiniteLaw.norm_expect_le_sum_norm _ _
      _≤∑t:ι,‖u t‖:=Finset.sum_le_sum (fun t _=>(u t).norm_coe_le_norm (x p)))

theorem exists_integrated_sourceOwnerPayoff_finite_crossing {xi eta vlo vhi L U : ℝ}
    (hL : 0<L) (heta : 0<eta) (hUv : U<vlo) (r K1 K2 : ℕ) (i : ι)
    (hN : 2≤ Fintype.card ι) (hK : 0<K1+K2) (hKN : K1+K2<Fintype.card ι)
    {e : ℝ} (he : 0<e) :
    let G:=(1-fillFraction (ι:=ι) (K1+K2))*(min (vlo-U) (eta*L)/2)
    ∃delta : ℝ,0<delta ∧ ∀(X : Type*) [MeasurableSpace X]
      (mu : Measure X) [IsFiniteMeasure mu]
      (x : X→ FavoredBoxInput ι vlo vhi L U) (y : X→ Icc L U),
      Measurable x→ Measurable y→
      (∀ᵐp ∂mu,(x p).2 i<y p ∧ (y p:ℝ)-((x p).2 i:ℝ)<delta)→
      (G/(4*rankDenominator ι))*(∑j:ι,mu.real {p | j≠i ∧ ((x p).2 j:ℝ)∈ Icc ((x p).2 i:ℝ) (y p:ℝ)})-
          e*mu.real univ ≤
        ∫p,(sourceOwnerPayoff xi eta (x p).1 (Function.update (fun j=>((x p).2 j:ℝ)) i (y p)) r K1 K2 i-
          sourceOwnerPayoff xi eta (x p).1 (fun j=>((x p).2 j:ℝ)) r K1 K2 i) ∂mu := by
  dsimp only
  let G:=(1-fillFraction (ι:=ι) (K1+K2))*(min (vlo-U) (eta*L)/2)
  obtain ⟨delta,hdelta,hgain⟩:=exists_sourceOwnerPayoff_finite_crossing (xi:=xi) (vhi:=vhi)
    hL heta hUv r K1 K2 i hN hK hKN he
  refine ⟨delta,hdelta,?_⟩
  intro X _ mu _ x y hx hy hgeo
  let xp : X→ FavoredBoxInput ι vlo vhi L U:=fun p=>((x p).1,Function.update (x p).2 i (y p))
  have hupdate : Measurable (fun p=>Function.update (x p).2 i (y p)) := by
    apply measurable_pi_lambda
    intro j
    by_cases hji : j=i
    · simpa only [hji,Function.update_self] using hy
    · simpa only [Function.update_of_ne hji,Function.comp_def] using ((measurable_pi_apply j).comp hx.snd)
  have hxp : Measurable xp:=hx.fst.prodMk hupdate
  have hnew:=integrable_boxSourceOwnerPayoff_comp hL xi eta r K1 K2 i hN hK hKN mu xp hxp
  have hold:=integrable_boxSourceOwnerPayoff_comp hL xi eta r K1 K2 i hN hK hKN mu x hx
  let E : ι→ Set X:=fun j=>{p | j≠i ∧ ((x p).2 j:ℝ)∈ Icc ((x p).2 i:ℝ) (y p:ℝ)}
  have hE (j : ι) : MeasurableSet (E j):=(MeasurableSet.const (j≠i)).inter
    ((measurableSet_le ((((measurable_pi_apply i).comp hx.snd)).subtype_coe) ((((measurable_pi_apply j).comp hx.snd)).subtype_coe)).inter
      (measurableSet_le ((((measurable_pi_apply j).comp hx.snd)).subtype_coe) hy.subtype_coe))
  have hterm (j : ι) : Integrable ((E j).indicator (fun _=>G/4)) mu:=
    (integrable_const (G/4)).indicator (hE j)
  have hi : Integrable (fun p=>(∑j:ι,(E j).indicator (fun _=>G/4) p)/rankDenominator ι-e) mu:=
    ((integrable_finsetSum Finset.univ (fun j _=>hterm j)).div_const _).sub (integrable_const e)
  have hup (p : X) : (fun j=>((xp p).2 j:ℝ))=
      Function.update (fun j=>((x p).2 j:ℝ)) i (y p) := by
    funext j
    by_cases hji : j=i <;> simp [xp,hji]
  have hg:=integral_mono_ae hi (hnew.sub hold) (hgeo.mono (fun p hp=>by
    have hh:=hgain (x p) (y p) hp.1 hp.2
    change _ ≤ boxSourceOwnerPayoff xi eta r K1 K2 i (xp p)-boxSourceOwnerPayoff xi eta r K1 K2 i (x p)
    unfold boxSourceOwnerPayoff
    rw [hup]
    simpa only [E,Set.indicator,Set.mem_setOf_eq,G] using hh))
  simp only [Pi.sub_apply] at hg
  have heq : (fun p=>boxSourceOwnerPayoff xi eta r K1 K2 i (xp p)-
      boxSourceOwnerPayoff xi eta r K1 K2 i (x p))=
      fun p=>sourceOwnerPayoff xi eta (x p).1 (Function.update (fun j=>((x p).2 j:ℝ)) i (y p)) r K1 K2 i-
        sourceOwnerPayoff xi eta (x p).1 (fun j=>((x p).2 j:ℝ)) r K1 K2 i := by
    funext p
    unfold boxSourceOwnerPayoff
    rw [hup]
  rw [heq] at hg
  rw [integral_sub ((integrable_finsetSum Finset.univ (fun j _=>hterm j)).div_const _) (integrable_const e)] at hg
  simp only [integral_div,integral_const,smul_eq_mul] at hg
  rw [integral_finsetSum Finset.univ (fun j _=>hterm j)] at hg
  simp_rw [integral_indicator_const _ (hE _)] at hg
  have hs : (∑j:ι,mu.real (E j) • (G/4))/rankDenominator ι-mu.real univ * e=
      G/(4*rankDenominator ι)*(∑j:ι,mu.real (E j))-e*mu.real univ := by
    simp only [smul_eq_mul,←Finset.sum_mul]
    ring
  rw [hs] at hg
  exact hg

end FCAppendix.Affine.Hybrid
