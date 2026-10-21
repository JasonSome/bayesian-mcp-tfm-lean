import FCAppendix.Affine.Hybrid.GuardedPayoff
import FCAppendix.Affine.Hybrid.FavoredContinuity

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma finiteMultiplier_map (xi : ℝ) (b : ι→ℝ) (D : Finset ι) (r : ℕ)
    (e : Equiv.Perm ι) :
    finiteMultiplier xi b (D.map e.toEmbedding) r=
      finiteMultiplier xi (b∘e) D r := by
  simp [finiteMultiplier,Finset.sum_map]

lemma ownerSetPayoff_relabel (xi eta v : ℝ) (b : ι→ℝ) (r : ℕ) (i : ι)
    (E : Finset ι) (e : Equiv.Perm ι) :
    ownerSetPayoff xi eta v (b∘e.symm) r (e i) (E.map e.toEmbedding)=
      ownerSetPayoff xi eta v b r i E := by
  have hD : Finset.univ\E.map e.toEmbedding=(Finset.univ\E).map e.toEmbedding := by
    rw [Finset.map_sdiff,Finset.map_univ_equiv]
  have hb : (b∘e.symm)∘e=b := by funext j; simp
  simp only [ownerSetPayoff,Finset.mem_map_equiv,Equiv.symm_apply_apply,Function.comp_apply]
  rw [hD,finiteMultiplier_map,hb]

omit [Fintype ι] in
lemma bid_comp_swap_of_eq (b : ι→ℝ) (i j : ι) (hij : b i=b j) :
    b∘Equiv.swap i j=b := by
  funext k
  by_cases hki : k=i
  · subst k; simp [hij]
  · by_cases hkj : k=j
    · subst k; simp [hij]
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]

def favoredTargetPayoff (xi eta v : ℝ) (b : ι→ℝ) (r K : ℕ) (i t : ι) : ℝ :=
  (conditionalFill K t).expect (ownerSetPayoff xi eta v b r i)

lemma favoredTargetPayoff_swap (xi eta v : ℝ) (b : ι→ℝ) (r K : ℕ)
    (i j : ι) (hij : b i=b j) :
    favoredTargetPayoff xi eta v b r K i j=
      favoredTargetPayoff xi eta v b r K j i := by
  let e:=Equiv.swap i j
  have hb : b∘e.symm=b := by simpa [e] using bid_comp_swap_of_eq b i j hij
  unfold favoredTargetPayoff
  have hfill := conditionalFill_relabel K i e
  simp only [e,Equiv.swap_apply_left] at hfill
  rw [hfill,FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro E
  have he := ownerSetPayoff_relabel xi eta v b r j E e
  simpa only [hb,e,Equiv.swap_apply_right] using he

lemma conditionalFill_target_mem {K : ℕ} (hN : 2≤Fintype.card ι)
    (hK : 1≤K) (hKN : K≤Fintype.card ι) (i : ι) (E : Finset ι)
    (hE : (conditionalFill K i).mass E≠0) : i∈E := by
  apply GuardedData.support_mem_of_marginal_one (conditionalFill K i) i _ E hE
  rw [(conditionalFill_implements hN hK hKN i).2]
  simp [fillMarginal]

theorem favoredTargetPayoff_tie_gain {xi eta v L U vmin : ℝ} (b : ι→ℝ)
    (r K : ℕ) (i j : ι) (hij : i≠j) (hbid : b i=b j)
    (hN : 2≤Fintype.card ι) (hK : 1≤K) (hKN : K≤Fintype.card ι)
    (heta : 0<eta) (hL : 0<L) (hbL : L≤b i) (hbU : b i≤U)
    (hUv : U<vmin) (hvv : vmin≤v) :
    (1-fillFraction (ι:=ι) K)*(min (vmin-U) (eta*L)/2)≤
      favoredTargetPayoff xi eta v b r K i i-
        favoredTargetPayoff xi eta v b r K i j := by
  rw [favoredTargetPayoff_swap xi eta v b r K i j hbid]
  unfold favoredTargetPayoff
  rw [←FiniteLaw.expect_sub]
  let g:=min (vmin-U) (eta*L)/2
  have hpoint (E : Finset ι) (hE : (conditionalFill K i).mass E≠0) :
      g*(if j∉E then (1:ℝ) else 0)≤
        ownerSetPayoff xi eta v b r i E-ownerSetPayoff xi eta v b r j E := by
    have hi:=conditionalFill_target_mem hN hK hKN i E hE
    by_cases hj : j∈E
    · simp [ownerSetPayoff,hi,hj,hbid]
    · simp only [ownerSetPayoff,if_pos hi,if_neg hj,if_pos hj,mul_one]
      rw [←hbid]
      exact exclusive_gain_uniform heta hL hbL hbU hUv hvv
  have hexpect : (conditionalFill K i).expect (fun E=>g*(if j∉E then (1:ℝ) else 0))≤
      (conditionalFill K i).expect
        (fun E=>ownerSetPayoff xi eta v b r i E-ownerSetPayoff xi eta v b r j E) := by
    unfold FiniteLaw.expect
    apply Finset.sum_le_sum
    intro E _
    by_cases hE : (conditionalFill K i).mass E=0
    · rw [hE,zero_mul,zero_mul]
    · exact mul_le_mul_of_nonneg_left (hpoint E hE) ((conditionalFill K i).nonneg E)
  have hp : (conditionalFill K i).prob (fun E=>j∉E)=1-fillFraction (ι:=ι) K := by
    rw [show (fun E : Finset ι=>j∉E)=(fun E=>¬j∈E) by rfl,FiniteLaw.prob_compl,
      (conditionalFill_implements hN hK hKN i).2]
    simp [fillMarginal,hij.symm]
  rw [FiniteLaw.expect_const_mul,←FiniteLaw.prob_eq_expect,hp] at hexpect
  simpa only [g,mul_comm] using hexpect

lemma favoredTargetPayoff_rival_tie (xi eta v : ℝ) (b : ι→ℝ) (r K : ℕ)
    (i t u : ι) (hit : i≠t) (hiu : i≠u) (htu : b t=b u) :
    favoredTargetPayoff xi eta v b r K i t=
      favoredTargetPayoff xi eta v b r K i u := by
  let e:=Equiv.swap t u
  have hb : b∘e.symm=b := by simpa [e] using bid_comp_swap_of_eq b t u htu
  have hei : e i=i := Equiv.swap_apply_of_ne_of_ne hit hiu
  unfold favoredTargetPayoff
  have hfill := conditionalFill_relabel K t e
  simp only [e,Equiv.swap_apply_left] at hfill
  rw [hfill,FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro E
  have he := ownerSetPayoff_relabel xi eta v b r i E e
  rw [hb,hei] at he
  exact he.symm

end FCAppendix.Affine.Hybrid
