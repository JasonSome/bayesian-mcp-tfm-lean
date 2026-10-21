import FCAppendix.Affine.Hybrid.Finishing01Definitions

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open MeasureTheory Set Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

def binomialTwoMass (q : ℝ) (j : Fin 3) : ℝ :=
  if j=0 then (1-q)^2 else if j=1 then 2*q*(1-q) else q^2

def pointMass (k j : Fin 3) : ℝ := if j=k then 1 else 0

def limitingCountMass (z q : ℝ) (j : Fin 3) : ℝ :=
  z*pointMass 1 j+(1-z)*binomialTwoMass q j

lemma binomialTwoMass_total (q : ℝ) : ∑j:Fin 3,binomialTwoMass q j=1 := by
  simp [Fin.sum_univ_three,binomialTwoMass]
  ring

lemma binomialTwoMass_nonneg {q : ℝ} (hq:q∈ Icc (0:ℝ) 1) (j:Fin 3) :
    0≤ binomialTwoMass q j := by
  fin_cases j
  · change 0 ≤ (1-q)^2
    exact sq_nonneg _
  · change 0 ≤ 2*q*(1-q)
    exact mul_nonneg (mul_nonneg (by norm_num) hq.1) (sub_nonneg.mpr hq.2)
  · change 0 ≤ q^2
    exact sq_nonneg _

lemma pointMass_total (k:Fin 3) : ∑j:Fin 3,pointMass k j=1 := by
  simp [pointMass]

lemma limitingCountMass_total (z q:ℝ) : ∑j:Fin 3,limitingCountMass z q j=1 := by
  simp only [limitingCountMass,Finset.sum_add_distrib,←Finset.mul_sum,
    pointMass_total,binomialTwoMass_total]
  ring

def countPayoff (eta v b:ℝ) (p:Fin 3→ℝ) : ℝ :=
  (v-b)*(p 1+p 2)-eta*b*p 2

lemma countPayoff_binomial (eta v b q:ℝ) :
    countPayoff eta v b (binomialTwoMass q)=independentTwo eta v b q := by
  simp [countPayoff,binomialTwoMass,independentTwo]
  ring

lemma countPayoff_single (eta v b:ℝ) : countPayoff eta v b (pointMass 1)=v-b := by
  simp [countPayoff,pointMass]

lemma countPayoff_limit (eta z v b q:ℝ) :
    countPayoff eta v b (limitingCountMass z q)=
      z*(v-b)+(1-z)*independentTwo eta v b q := by
  simp [countPayoff,limitingCountMass,pointMass,binomialTwoMass,independentTwo]
  ring

def reconstructCountMass (eta b u0 u1:ℝ) (j:Fin 3) : ℝ :=
  let success:=u1-u0
  let duplicate:=(-u0/b-success)/eta
  if j=0 then 1-success else if j=1 then success-duplicate else duplicate

lemma reconstructCountMass_eq (eta b:ℝ) (heta:eta≠0) (hb:b≠0)
    (p:Fin 3→ℝ) (hp:∑j:Fin 3,p j=1) :
    reconstructCountMass eta b (countPayoff eta 0 b p) (countPayoff eta 1 b p)=p := by
  have hsum:p 0+p 1+p 2=1 := by simpa [Fin.sum_univ_three,add_assoc] using hp
  funext j
  fin_cases j <;> simp [reconstructCountMass,countPayoff]
  all_goals field_simp [heta,hb]
  all_goals nlinarith [hsum]

def ownerSetCountMass {ι:Type*} [Fintype ι] [DecidableEq ι]
    (xi:ℝ) (b:ι→ℝ) (r:ℕ) (i:ι) (E:Finset ι) (j:Fin 3) : ℝ :=
  if i∈ E then pointMass 1 j else
    binomialTwoMass (exposure xi (finiteMultiplier xi b (Finset.univ\E) r) (b i)) j

lemma ownerSetCountMass_total {ι:Type*} [Fintype ι] [DecidableEq ι]
    (xi:ℝ) (b:ι→ℝ) (r:ℕ) (i:ι) (E:Finset ι) :
    ∑j:Fin 3,ownerSetCountMass xi b r i E j=1 := by
  unfold ownerSetCountMass
  split_ifs <;> simp [pointMass_total,binomialTwoMass_total]

lemma ownerSetCountMass_payoff {ι:Type*} [Fintype ι] [DecidableEq ι]
    (xi eta v:ℝ) (b:ι→ℝ) (r:ℕ) (i:ι) (E:Finset ι) :
    countPayoff eta v (b i) (ownerSetCountMass xi b r i E)=
      ownerSetPayoff xi eta v b r i E := by
  unfold ownerSetCountMass ownerSetPayoff
  split_ifs
  · exact countPayoff_single _ _ _
  · exact countPayoff_binomial _ _ _ _

def sourceCountMass {ι:Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (xi:ℝ) (b:ι→ℝ) (r K1 K2:ℕ) (i:ι) (j:Fin 3) : ℝ :=
  (sourceOwnersLaw b K1 K2).expect
    (fun AB=> ownerSetCountMass xi b r i (AB.1∪AB.2) j)

lemma sourceCountMass_total {ι:Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (xi:ℝ) (b:ι→ℝ) (r K1 K2:ℕ) (i:ι) :
    ∑j:Fin 3,sourceCountMass xi b r K1 K2 i j=1 := by
  unfold sourceCountMass FiniteLaw.expect
  rw [Finset.sum_comm]
  simp only [←Finset.mul_sum,ownerSetCountMass_total,mul_one,FiniteLaw.total]

lemma sourceCountMass_payoff {ι:Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (xi eta v:ℝ) (b:ι→ℝ) (r K1 K2:ℕ) (i:ι) :
    countPayoff eta v (b i) (sourceCountMass xi b r K1 K2 i)=
      sourceOwnerPayoff xi eta v b r K1 K2 i := by
  unfold countPayoff sourceCountMass sourceOwnerPayoff
  simp only [←FiniteLaw.expect_add,←FiniteLaw.expect_const_mul,←FiniteLaw.expect_sub]
  apply FiniteLaw.expect_congr
  intro AB
  exact ownerSetCountMass_payoff xi eta v b r i (AB.1∪AB.2)

abbrev ActiveCountRows (N:ℕ) := (Fin N→ℝ)×(Fin N→ℝ)

def activePhysicalPatternCountMass {N:ℕ} (xi z L W:ℝ) (c:ℕ)
    (kind:Fin N→ Fin 4) (bid:ℝ) (rows:ActiveCountRows N) (j:Fin 3) : ℝ :=
  let t:ActivePhysicalData N := (0,bid,rows)
  let T:=activePatternTemplate c kind
  let b:=activePhysicalBids kind t
  if activePatternGuarded xi L W c z kind then
    sourceCountMass xi (activePhysicalActiveBids kind t)
      (activePatternResidual c z kind) (activePatternOwner c z kind 0)
      (activePatternOwner c z kind 1) (activePatternFocal kind) j
  else if T.residual₀=T.residual₁ then
    binomialTwoMass (EqualCapacity.positiveMarginal xi T.residual₀ b 0) j
  else pointMass (LowBody.focalCopy (T.selection (1-xi) b) 0) j

lemma activePhysicalPatternCountMass_total {N:ℕ} (xi z L W:ℝ) (c:ℕ)
    (kind:Fin N→ Fin 4) (bid:ℝ) (rows:ActiveCountRows N) :
    ∑j:Fin 3,activePhysicalPatternCountMass xi z L W c kind bid rows j=1 := by
  unfold activePhysicalPatternCountMass
  dsimp only
  split_ifs <;> simp [sourceCountMass_total,binomialTwoMass_total,pointMass_total]

lemma activePhysicalPatternCountMass_payoff {N:ℕ} (xi z L W:ℝ) (c:ℕ)
    (kind:Fin N→ Fin 4) (v bid:ℝ) (rows:ActiveCountRows N) :
    countPayoff (1-2*xi) v bid
      (activePhysicalPatternCountMass xi z L W c kind bid rows)=
      activePhysicalPatternPayoff xi z L W c kind (v,bid,rows) := by
  unfold activePhysicalPatternCountMass activePhysicalPatternPayoff
  dsimp only
  split_ifs with hg hequal
  · change countPayoff (1-2*xi) v bid
        (sourceCountMass xi (activePhysicalActiveBids kind (0,bid,rows))
          (activePatternResidual c z kind) (activePatternOwner c z kind 0)
          (activePatternOwner c z kind 1) (activePatternFocal kind)) =
      sourceOwnerPayoff xi (1-2*xi) v (activePhysicalActiveBids kind (0,bid,rows))
        (activePatternResidual c z kind) (activePatternOwner c z kind 0)
        (activePatternOwner c z kind 1) (activePatternFocal kind)
    exact
      sourceCountMass_payoff xi (1-2*xi) v
        (activePhysicalActiveBids kind (0,bid,rows))
        (activePatternResidual c z kind) (activePatternOwner c z kind 0)
        (activePatternOwner c z kind 1) (activePatternFocal kind)
  · simp [countPayoff,binomialTwoMass,LowBody.equalPayoff,activePhysicalBids]
    ring
  · let T:=activePatternTemplate c kind
    let b:=activePhysicalBids kind (0,bid,rows)
    change countPayoff (1-2*xi) v bid
      (pointMass (LowBody.focalCopy (T.selection (1-xi) b) 0)) =
        LowBody.purePayoff (1-xi) v b (T.selection (1-xi) b) 0
    unfold LowBody.purePayoff
    generalize hcopy:LowBody.focalCopy (T.selection (1-xi) b) 0=k
    by_cases hk0 : k=0
    · rw [hk0]
      simp [countPayoff,pointMass,
        show (2:Fin 3)≠0 by decide,show (0:Fin 3)≠2 by decide]
    · by_cases hk1 : k=1
      · rw [hk1]
        simp [countPayoff,pointMass,b,activePhysicalBids,
          show (2:Fin 3)≠1 by decide,show (1:Fin 3)≠2 by decide]
      · have hk2 : k=2 := Fin.ext (by have h:=k.isLt; omega)
        rw [hk2]
        norm_num [countPayoff,pointMass,b,activePhysicalBids]
        rw [if_neg (by decide : (1:Fin 3)≠2)]
        ring

lemma activePhysicalPatternCountMass_reconstruct {N:ℕ} (xi z L W:ℝ) (c:ℕ)
    (kind:Fin N→ Fin 4) (bid:ℝ) (rows:ActiveCountRows N)
    (heta:1-2*xi≠0) (hb:bid≠0) :
    activePhysicalPatternCountMass xi z L W c kind bid rows=
      reconstructCountMass (1-2*xi) bid
        (activePhysicalPatternPayoff xi z L W c kind (0,bid,rows))
        (activePhysicalPatternPayoff xi z L W c kind (1,bid,rows)) := by
  rw [←activePhysicalPatternCountMass_payoff xi z L W c kind 0 bid rows,
    ←activePhysicalPatternCountMass_payoff xi z L W c kind 1 bid rows]
  exact (reconstructCountMass_eq _ _ heta hb _
    (activePhysicalPatternCountMass_total xi z L W c kind bid rows)).symm

def pairCountMass {ι:Type*} [Fintype ι] [DecidableEq ι]
    (Q:FiniteLaw (Finset ι×Finset ι)) (i:ι) (j:Fin 3) : ℝ :=
  Q.prob (fun ST=> LowBody.focalCopy ST i=j)

lemma pairCountMass_total {ι:Type*} [Fintype ι] [DecidableEq ι]
    (Q:FiniteLaw (Finset ι×Finset ι)) (i:ι) : ∑j:Fin 3,pairCountMass Q i j=1 := by
  unfold pairCountMass FiniteLaw.prob FiniteLaw.expect
  simp only [mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  have hh (ST:Finset ι×Finset ι):
      (∑j:Fin 3,if LowBody.focalCopy ST i=j then Q.mass ST else 0)=Q.mass ST := by simp
  simp only [hh,FiniteLaw.total]

lemma pairCountMass_payoff {ι:Type*} [Fintype ι] [DecidableEq ι]
    (Q:FiniteLaw (Finset ι×Finset ι)) (i:ι) (eta v b:ℝ) :
    countPayoff eta v b (pairCountMass Q i)=Q.expect (broadcastPayoff eta v b i) := by
  unfold countPayoff pairCountMass
  simp only [FiniteLaw.prob_eq_expect,←FiniteLaw.expect_add,
    ←FiniteLaw.expect_const_mul,←FiniteLaw.expect_sub]
  apply FiniteLaw.expect_congr
  intro ST
  by_cases h0:i∈ ST.1 <;> by_cases h1:i∈ ST.2 <;>
    simp [LowBody.focalCopy,broadcastPayoff,h0,h1]

lemma countMass_eq_of_two_payoffs {eta b:ℝ} (heta:eta≠0) (hb:b≠0)
    (p q:Fin 3→ℝ) (hp:∑j:Fin 3,p j=1) (hq:∑j:Fin 3,q j=1)
    (h0:countPayoff eta 0 b p=countPayoff eta 0 b q)
    (h1:countPayoff eta 1 b p=countPayoff eta 1 b q) : p=q := by
  rw [←reconstructCountMass_eq eta b heta hb p hp,h0,h1]
  exact reconstructCountMass_eq eta b heta hb q hq

lemma guarded_actual_count_mass {ι:Type*} [Fintype ι] [DecidableEq ι]
    (G:GuardedData ι) (i:ι) :
    pairCountMass G.jointLaw i=
      ownerSetCountMass G.xi G.bid G.residual i (G.owner₁∪G.owner₂) := by
  apply countMass_eq_of_two_payoffs (eta:=1) (b:=G.bid i) (by norm_num) (G.bid_pos i).ne'
    _ _ (pairCountMass_total G.jointLaw i)
    (ownerSetCountMass_total G.xi G.bid G.residual i (G.owner₁∪G.owner₂))
  · rw [pairCountMass_payoff,G.expected_broadcastPayoff,ownerSetCountMass_payoff]
  · rw [pairCountMass_payoff,G.expected_broadcastPayoff,ownerSetCountMass_payoff]

lemma product_count_mass {ι:Type*} [Fintype ι] [DecidableEq ι]
    (mu nu:FiniteLaw (Finset ι)) (i:ι) (q:ℝ)
    (hmu:mu.prob (fun S=> i∈ S)=q) (hnu:nu.prob (fun S=> i∈ S)=q) (j:Fin 3) :
    (mu.prod nu).prob (fun ST=> LowBody.focalCopy ST i=j)=binomialTwoMass q j := by
  let p:Fin 3→ℝ:=fun k=>(mu.prod nu).prob (fun ST=> LowBody.focalCopy ST i=k)
  have hp:∑k:Fin 3,p k=1 := by
    unfold p FiniteLaw.prob FiniteLaw.expect
    simp only [mul_ite,mul_one,mul_zero]
    rw [Finset.sum_comm]
    have hpoint (ST:Finset ι×Finset ι):
        (∑k:Fin 3,if LowBody.focalCopy ST i=k then (mu.prod nu).mass ST else 0)=
        (mu.prod nu).mass ST := by simp
    simp only [hpoint,FiniteLaw.total]
  have hpay (v:ℝ):countPayoff 1 v 1 p=independentTwo 1 v 1 q := by
    have he:=expect_product_broadcastPayoff mu nu 1 v 1 i
    rw [hmu,hnu] at he
    have hid:countPayoff 1 v 1 p=(mu.prod nu).expect (broadcastPayoff 1 v 1 i) := by
      unfold countPayoff p
      simp only [FiniteLaw.prob_eq_expect,←FiniteLaw.expect_add,
        ←FiniteLaw.expect_const_mul,←FiniteLaw.expect_sub]
      apply FiniteLaw.expect_congr
      intro ST
      by_cases h0:i∈ ST.1 <;> by_cases h1:i∈ ST.2 <;>
        simp [LowBody.focalCopy,broadcastPayoff,h0,h1]
    rw [hid,he]
    unfold independentTwo
    ring
  have hrec:=congrFun (reconstructCountMass_eq 1 1 (by norm_num) (by norm_num) p hp) j
  rw [hpay 0,hpay 1] at hrec
  have hbin:=congrFun (reconstructCountMass_eq 1 1 (by norm_num) (by norm_num)
    (binomialTwoMass q) (binomialTwoMass_total q)) j
  rw [countPayoff_binomial,countPayoff_binomial] at hbin
  exact hrec.symm.trans hbin

lemma equal_actual_count_mass {ι:Type*} [Fintype ι] [DecidableEq ι]
    {xi:ℝ} (hxi:0< xi) (hxi1:xi<1) (c:ℕ) (b:ι→ℝ) (i:ι) (j:Fin 3) :
    pairCountMass ((EqualCapacity.canonicalLottery xi c b).prod
      (EqualCapacity.canonicalLottery xi c b)) i j=
      binomialTwoMass (EqualCapacity.positiveMarginal xi c b i) j := by
  have hm:=(EqualCapacity.canonicalLottery_implements hxi hxi1 c b).2 i
  exact product_count_mass _ _ i _ hm hm j

lemma reconstructCountMass_error {eta L b u0 u1 w0 w1 eps:ℝ}
    (heta:0< eta) (hL:0< L) (hb:L≤ b) (heps:0≤ eps)
    (h0:|u0-w0|≤ eps) (h1:|u1-w1|≤ eps) (j:Fin 3) :
    |reconstructCountMass eta b u0 u1 j-
      reconstructCountMass eta b w0 w1 j| ≤
      (2+(1/L+2)/eta)*eps := by
  have hb0:=hL.trans_le hb
  let S:=u1-u0
  let T:=w1-w0
  have hST:|S-T|≤2*eps := by
    have he:S-T=(u1-w1)-(u0-w0) := by dsimp [S,T];ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  have hdiv:|u0/b-w0/b|≤ eps/L := by
    rw [←sub_div,abs_div,abs_of_pos hb0]
    exact (div_le_div_of_nonneg_right h0 hb0.le).trans
      (div_le_div_of_nonneg_left heps hL hb)
  have hD:|(-u0/b-S)/eta-(-w0/b-T)/eta|≤(1/L+2)*eps/eta := by
    rw [←sub_div,abs_div,abs_of_pos heta]
    apply (div_le_div_iff_of_pos_right heta).mpr
    have he:(-u0/b-S)-(-w0/b-T)=-(u0/b-w0/b)-(S-T) := by ring
    rw [he]
    have hh:=abs_sub (-(u0/b-w0/b)) (S-T)
    rw [abs_neg] at hh
    calc
      _≤|u0/b-w0/b|+|S-T|:=hh
      _≤ eps/L+2*eps:=add_le_add hdiv hST
      _=(1/L+2)*eps:=by ring
  have hterm:0≤(1/L+2)/eta*eps := by positivity
  have hD' : |(-u0/b-S)/eta-(-w0/b-T)/eta| ≤ (1/L+2)/eta*eps := by
    convert! hD using 1
    ring
  fin_cases j
  · change |(1-(u1-u0))-(1-(w1-w0))| ≤ _
    have he:(1-(u1-u0))-(1-(w1-w0))=-(S-T) := by dsimp [S,T];ring
    rw [he,abs_neg]
    nlinarith [hST]
  · change |(u1-u0-(-u0/b-(u1-u0))/eta)-(w1-w0-(-w0/b-(w1-w0))/eta)| ≤ _
    have he:(u1-u0-(-u0/b-(u1-u0))/eta)-(w1-w0-(-w0/b-(w1-w0))/eta)=
        (S-T)-((-u0/b-S)/eta-(-w0/b-T)/eta) := by dsimp [S,T];ring
    rw [he]
    exact (abs_sub _ _).trans (by nlinarith [hST,hD'])
  · change |(-u0/b-S)/eta-(-w0/b-T)/eta|≤ _
    nlinarith [hD']

end FCAppendix.Affine.Hybrid.Finish01
