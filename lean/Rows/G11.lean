import Rows.G10

/-!
# G11 — 族 4 の 328 行目 `(0,0)(1,1)(2,1)(2,1)(2,0)(1,1)(2,1)(2,1)`

値は φ̄(3, ω+1)。`table/diff.md` の族 4 で未決の 2 行のうちの 1 つで、決着には
`oR` を `n` で量化した等式が要る。

**リンク 1 と 3 が定理になっている。残るのはリンク 2 だけである。**

    展開 --ofMatrix--> 梯子 --transPort--> BT --dict--> 値
            ✅ ofMatrix_M      🚧 未着手      ✅ dict_LBT

この行は `G10` の梯子に **1 ブロックあたり 1 列足したもの**である (周期 6 → 7、
基底も 1 列長い)。だからリンク 1 と 3 は `Rows/G10.lean` をなぞれば通る。

**dict 側で `G10` と実質的に違うのは 2 箇所だけだった。**

  * 塔の第 1 引数が `1` ではなく `2` — `t` が φ̄(3, ω+1) なので基本列は φ̄(2,·) の塔
  * `collapse 1` に入る項の `Ω` が 1 つではなく 2 つ — 足した `(2,1)` 列の像

後者のために `phiNF` の三項和の場合 (`splitFin_add_triple` / `phiNF_add_triple`) が
要った。`Evidence/StageB.lean` の `splitFin_add_pair` は二項和までしか扱わない。

リンク 2 は `runAux` 自身の再帰に沿った帰納で、`Rows/G10.lean` の「Six-phase reduction」
以下を周期 7 で取り直す作業になる。`++` に沿った帰納は使えない
(`Evidence/Cert.lean` §21.2)。
-/

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected
namespace G11

def M : BMS.Matrix := [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1],[2,1],[2,1]]
def t : Term := phi (add (phi zero zero) (add (phi zero zero) (phi zero zero)))
  (add (phi zero (phi zero zero)) (phi zero zero))

/-- Row-zero value of the `0,1,1,1,0,1,1` seven-column tail. -/
def p (k : Nat) : Int :=
  if k%7=0 then ((2*(k/7)+2:Nat):Int)
  else if k%7=1 ∨ k%7=5 then ((2*(k/7)+3:Nat):Int)
  else ((2*(k/7)+4:Nat):Int)

/-- Row-one value of the seven-column tail. -/
def q (k : Nat) : Int := if k%7=0 ∨ k%7=4 then 0 else 1

def T (m : Nat) : Trans.Recal.PS :=
  (List.range m).map fun k => (p k,q k)

/-- The parsed expansion after `m` individual tail columns. -/
def L (m : Nat) : Trans.Recal.PS :=
  [(0,0),(1,1),(2,1),(2,1),(2,0),(1,1),(2,1)]++T m

abbrev D0z : Trans.Dict.BT := .D 0 .zero
abbrev D1z : Trans.Dict.BT := .D 1 .zero
abbrev D11z : Trans.Dict.BT := .D 1 D1z
abbrev D1ss : Trans.Dict.BT := .D 1 (.sum D1z D1z)
abbrev C : Trans.Dict.BT := .sum D1z (.sum D1z D0z)
abbrev A0 : Trans.Dict.BT := .D 1 C
abbrev B0 : Trans.Dict.BT := .sum A0 D1z
abbrev B1 : Trans.Dict.BT := .sum A0 D11z

/-- A complete block wraps the unfinished suffix in the reader output.  One `.sum D1z`
    deeper than `G10.W`: that is the extra column. -/
def W : Nat → Trans.Dict.BT → Trans.Dict.BT
  | 0,b => b
  | n+1,b => .sum A0 (.D 1 (.sum D1z (.D 0 (W n b))))

def Part : Nat → Trans.Dict.BT
  | 0 => B1
  | 1 => .sum A0 (.D 1 (.sum D1z D0z))
  | 2 => .sum A0 (.D 1 (.sum D1z (.D 0 D1z)))
  | 3 => .sum A0 (.D 1 (.sum D1z (.D 0 D11z)))
  | 4 => .sum A0 (.D 1 (.sum D1z (.D 0 D1ss)))
  | 5 => .sum A0 (.D 1 (.sum D1z (.D 0 A0)))
  | _ => .sum A0 (.D 1 (.sum D1z (.D 0 B0)))

/-- Reader output on every one-column prefix of the seven-phase ladder. -/
def LBT (m : Nat) : Trans.Dict.BT := .D 0 (W (m/7) (Part (m%7)))

theorem T_succ (m : Nat) : T (m+1)=T m++[(p m,q m)] := by
  unfold T
  rw [List.range_succ,List.map_append]
  rfl

theorem L_succ (m : Nat) : L (m+1)=L m++[(p m,q m)] := by
  unfold L
  rw [T_succ,List.append_assoc]

theorem length_T (m : Nat) : (T m).length=m := by simp [T]

theorem length_L (m : Nat) : (L m).length=m+7 := by simp [L,length_T]

theorem lenI_L (m : Nat) : Trans.Recal.lenI (L m)=(m:Int)+7 := by
  unfold Trans.Recal.lenI
  rw [length_L]
  omega

theorem predP_L (m : Nat) : Trans.Recal.predP (L (m+1))=L m := by
  rw [L_succ]
  unfold Trans.Recal.predP
  rw [show ((L m++[(p m,q m)]).length==1)=false from by
    rw [List.length_append,length_L]
    simp]
  simp

/-! ### Link 1: expansion and parsing. -/

theorem expand_block_first : (fun a : Nat =>
      ([[0+a*2*1,0+a*0*1],[1+a*2*1,1+a*0*1],
        [2+a*2*1,1+a*0*1],[2+a*2*1,1+a*0*1],
        [2+a*2*1,0+a*0*1],[1+a*2*1,1+a*0*1],
        [2+a*2*1,1+a*0*1]] : BMS.Matrix))=
      fun a => [[2*a,0],[1+2*a,1],[2+2*a,1],[2+2*a,1],[2+2*a,0],
        [1+2*a,1],[2+2*a,1]] := by
  funext a
  simp [Nat.mul_comm]

theorem expand_block_succ : ((fun a : Nat =>
      ([[2*a,0],[1+2*a,1],[2+2*a,1],[2+2*a,1],[2+2*a,0],
        [1+2*a,1],[2+2*a,1]]:BMS.Matrix)) ∘ Nat.succ)=
      fun a => [[2+2*a,0],[3+2*a,1],[4+2*a,1],[4+2*a,1],[4+2*a,0],
        [3+2*a,1],[4+2*a,1]] := by
  funext a
  simp only [Function.comp_apply]
  rw [show 2*(a+1)=2+2*a by omega,
    show 1+(2+2*a)=3+2*a by omega,
    show 2+(2+2*a)=4+2*a by omega]

theorem expand_M (n : Nat) :
    BMS.expand M n=[[0,0],[1,1],[2,1],[2,1],[2,0],[1,1],[2,1]]++
      ((List.range n).map fun a =>
        ([[2+2*a,0],[3+2*a,1],[4+2*a,1],[4+2*a,1],[4+2*a,0],
          [3+2*a,1],[4+2*a,1]] : BMS.Matrix)).flatten := by
  show (BMS.expand? M n).getD []=_
  have h : BMS.expand? M n=some (M.take 0++
      ((List.range (n+1)).map fun a =>
        ([[0+a*2*1,0+a*0*1],[1+a*2*1,1+a*0*1],
          [2+a*2*1,1+a*0*1],[2+a*2*1,1+a*0*1],
          [2+a*2*1,0+a*0*1],[1+a*2*1,1+a*0*1],
          [2+a*2*1,1+a*0*1]] : BMS.Matrix)).flatten) := rfl
  rw [h,expand_block_first,List.range_succ_eq_map]
  simp only [Option.getD_some,M,List.take,List.map_cons,List.flatten_cons,
    List.map_map,List.singleton_append,List.nil_append]
  rw [expand_block_succ]

theorem p_phase0 (a : Nat) : p (7*a)=((2*a+2:Nat):Int) := by simp [p]
theorem p_phase1 (a : Nat) : p (7*a+1)=((2*a+3:Nat):Int) := by simp [p]; omega
theorem p_phase2 (a : Nat) : p (7*a+2)=((2*a+4:Nat):Int) := by simp [p]; omega
theorem p_phase3 (a : Nat) : p (7*a+3)=((2*a+4:Nat):Int) := by simp [p]; omega
theorem p_phase4 (a : Nat) : p (7*a+4)=((2*a+4:Nat):Int) := by simp [p]; omega
theorem p_phase5 (a : Nat) : p (7*a+5)=((2*a+3:Nat):Int) := by simp [p]; omega
theorem p_phase6 (a : Nat) : p (7*a+6)=((2*a+4:Nat):Int) := by simp [p]; omega
theorem q_phase0 (a : Nat) : q (7*a)=0 := by simp [q]
theorem q_phase1 (a : Nat) : q (7*a+1)=1 := by simp [q]
theorem q_phase2 (a : Nat) : q (7*a+2)=1 := by simp [q]
theorem q_phase3 (a : Nat) : q (7*a+3)=1 := by simp [q]
theorem q_phase4 (a : Nat) : q (7*a+4)=0 := by simp [q]
theorem q_phase5 (a : Nat) : q (7*a+5)=1 := by simp [q]
theorem q_phase6 (a : Nat) : q (7*a+6)=1 := by simp [q]

theorem T_seven_mul (n : Nat) :
    T (7*n)=((List.range n).map fun a =>
      ([(((2*a+2:Nat):Int),(0:Int)),(((2*a+3:Nat):Int),(1:Int)),
        (((2*a+4:Nat):Int),(1:Int)),(((2*a+4:Nat):Int),(1:Int)),
        (((2*a+4:Nat):Int),(0:Int)),(((2*a+3:Nat):Int),(1:Int)),
        (((2*a+4:Nat):Int),(1:Int))]
        : Trans.Recal.PS)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 7*(n+1)=7*n+7 by omega,T_succ,T_succ,T_succ,T_succ,T_succ,T_succ,T_succ,ih,
      List.range_succ,List.map_append,List.flatten_append]
    simp only [List.map_singleton,List.flatten_singleton,List.append_assoc,
      List.singleton_append]
    rw [p_phase0 n,q_phase0 n,p_phase1 n,q_phase1 n,p_phase2 n,q_phase2 n,
      p_phase3 n,q_phase3 n,p_phase4 n,q_phase4 n,p_phase5 n,q_phase5 n,
      p_phase6 n,q_phase6 n]
    simp only [List.cons_append,List.nil_append]

theorem map_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[2+2*a,0],[3+2*a,1],[4+2*a,1],[4+2*a,1],[4+2*a,0],
        [3+2*a,1],[4+2*a,1]] : BMS.Matrix)).flatten).map
        (fun c => ((c.getD 0 0:Int),(c.getD 1 0:Int)))=T (7*n) := by
  rw [T_seven_mul,List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  change [(((2+2*a:Nat):Int),0),(((3+2*a:Nat):Int),1),
    (((4+2*a:Nat):Int),1),(((4+2*a:Nat):Int),1),
    (((4+2*a:Nat):Int),0),(((3+2*a:Nat):Int),1),
    (((4+2*a:Nat):Int),1)]=_
  rw [show 2+2*a=2*a+2 by omega,show 3+2*a=2*a+3 by omega,
    show 4+2*a=2*a+4 by omega]

theorem all_len_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[2+2*a,0],[3+2*a,1],[4+2*a,1],[4+2*a,1],[4+2*a,0],
        [3+2*a,1],[4+2*a,1]] : BMS.Matrix)).flatten).all
        (fun c => decide (c.length≤2))=true := by simp

/-- Link 1: each expansion lands on a seven-column-complete prefix. -/
theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n)=some (L (7*n)) := by
  rw [expand_M]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1],[2,1],[2,1],[2,0],[1,1],[2,1]]:BMS.Matrix)++
      ((List.range n).map fun a =>
        ([[2+2*a,0],[3+2*a,1],[4+2*a,1],[4+2*a,1],[4+2*a,0],
          [3+2*a,1],[4+2*a,1]]:BMS.Matrix)).flatten).isEmpty=false
      from by rfl]
  rw [List.all_append,all_len_blocks]
  simp only [List.all_cons,List.length_cons,List.length_nil,Bool.and_true,
    Bool.not_false,Bool.true_and,List.map_append,List.map_cons,List.map_nil]
  rw [map_blocks]
  rfl

#guard (List.range 8).all fun n =>
  Trans.Recal.ofMatrix (BMS.expand M n)==some (L (7*n))
#guard (List.range 22).all fun m => Trans.Recal.predP (L (m+1))==L m
#guard (List.range 30).all fun m => Trans.Recal.transPort (L m)==LBT m
#guard rest12.any fun r => r.m==M && r.t==t

/-! ### Link 3: the dictionary and the shifted fundamental sequence. -/

abbrev Z0t : Term := Z zero

/-- The term-side iteration exposed by complete seven-column blocks.  One Veblen level
    above `G10.Jt`: `t` is φ̄(3, ω+1), whose fundamental sequence is the φ̄(2,·) tower. -/
def Jt : Nat → Term
  | 0 => Bph
  | n+1 => phi (ofNat 2) (Jt n)

theorem Jt_cnv : ∀ n : Nat, Evidence.WF.CNV (Jt n)=true
  | 0 => by decide
  | n+1 => by
    show (Evidence.WF.CNV (ofNat 2) && Evidence.WF.CNV (Jt n))=true
    rw [Jt_cnv n]
    rfl

theorem Jt_inT (n : Nat) : inT (Jt n)=true :=
  Evidence.WF.inT_of_cnv _ (Jt_cnv n)

theorem Jt_lt_Jt_succ (n : Nat) : lt (Jt n) (Jt (n+1))=true := by
  rw [Jt]
  exact Evidence.WF.lt_phi_self (Jt_cnv n) (ofNat 2)

theorem Bph_lt_Jt_succ : ∀ n : Nat, lt Bph (Jt (n+1))=true
  | 0 => Jt_lt_Jt_succ 0
  | n+1 => Evidence.WF.lt_trans_inT
      (by decide) (Jt_inT (n+1)) (Jt_inT (n+2))
      (Bph_lt_Jt_succ n) (Jt_lt_Jt_succ (n+1))

theorem Jt_succ_toList (n : Nat) : (Jt (n+1)).toList=[Jt (n+1)] := by
  rw [Jt]
  rfl

theorem Jt_succ_isAP (n : Nat) : (Jt (n+1)).isAP=true := by rw [Jt]; rfl

theorem Jt_succ_bne_one (n : Nat) : ((Jt (n+1))==one)=false := by rw [Jt]; rfl

theorem Jt_lt_Z0t : ∀ n : Nat, lt (Jt n) Z0t=true
  | 0 => by decide
  | n+1 => by
    rw [Jt]
    unfold lt
    cases h:fuelOf (phi (ofNat 2) (Jt n)) Z0t with
    | zero => simp [fuelOf] at h
    | succ f =>
      rw [Evidence.WF.ltF_succ_phi_Z]
      simp only [Bool.and_eq_true]
      have hf : (ofNat 2).deg+Z0t.deg≤f := by
        unfold fuelOf at h
        simp only [Term.deg] at h ⊢
        omega
      have hfj : (Jt n).deg+Z0t.deg≤f := by
        unfold fuelOf at h
        simp only [Term.deg] at h ⊢
        omega
      constructor
      · rw [← Evidence.WF.lt_eq_ltF (ofNat 2) Z0t f hf]
        decide
      · rw [← Evidence.WF.lt_eq_ltF (Jt n) Z0t f hfj]
        exact Jt_lt_Z0t n

theorem Jt_lt_Z1 (n : Nat) : lt (Jt n) (Z one)=true :=
  Evidence.WF.lt_trans_inT (Jt_inT n) (by decide) (by decide)
    (Jt_lt_Z0t n) (by decide)

theorem plus_Bph_Jt_succ (n : Nat) : plus Bph (Jt (n+1))=Jt (n+1) := by
  unfold plus
  rw [show Bph.toList=[Bph] from rfl,Jt_succ_toList]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (Jt (n+1)) Bph=false from by
    unfold le
    rw [show ((Jt (n+1)==Bph))=false from beq_eq_false_iff_ne.mpr
      (Ne.symm (Evidence.WF.ne_of_ltF (Bph_lt_Jt_succ n)))]
    simp only [Bool.false_or]
    exact Evidence.WF.lt_asymm_inT (by decide) (Jt_inT (n+1))
      (Bph_lt_Jt_succ n)]
  rfl

theorem omegaNF_Jt_succ (n : Nat) : omegaNF (Jt (n+1))=Jt (n+1) := by
  rw [Jt]
  exact (Rows.ProofsB.omegaNF_phi (ofNat 2) (Jt n)).trans
    (Rows.ProofsB.phiNF_collapse (by decide))

theorem plus_Z0t_Jt_succ (n : Nat) :
    plus Z0t (Jt (n+1))=add Z0t (Jt (n+1)) := by
  unfold plus
  rw [show Z0t.toList=[Z0t] from rfl,Jt_succ_toList]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (Jt (n+1)) Z0t=true from Evidence.WF.le_of_lt (Jt_lt_Z0t (n+1))]
  rfl

theorem toList_add_Z0t_Jt_succ (n : Nat) :
    (add Z0t (Jt (n+1))).toList=[Z0t,Jt (n+1)] := by
  change Z0t::(Jt (n+1)).toList=_
  rw [Jt_succ_toList]

theorem toList_addZZJ (n : Nat) :
    (add Z0t (add Z0t (Jt (n+1)))).toList=[Z0t,Z0t,Jt (n+1)] := by
  change Z0t::(add Z0t (Jt (n+1))).toList=_
  rw [toList_add_Z0t_Jt_succ]

/-- `splitFin` on a three-term sum whose last summand is not `1`. -/
theorem splitFin_add_triple {x y z : Term} (hz : z.isAP=true) (h1 : (z==one)=false) :
    splitFin (add x (add y z))=(add x (add y z),0) := by
  have hl : toList (add x (add y z))=[x,y,z] := by
    show x::(add y z).toList=[x,y,z]
    show x::y::toList z=[x,y,z]
    rw [toList_of_isAP hz]
  unfold splitFin
  simp only [hl]
  simp [h1,ofList]

theorem phiNF_add_triple {a x y z : Term} (ha : a.isSC=false) (hz : z.isAP=true)
    (h1 : (z==one)=false) :
    phiNF a (add x (add y z))=phi a (add x (add y z)) := by
  unfold phiNF
  simp only [isSC,Bool.false_and,Bool.false_eq_true,if_false]
  show phiNFsucc a (add x (add y z))=phi a (add x (add y z))
  unfold phiNFsucc
  rw [splitFin_add_triple hz h1]
  show phiNFdefault a (add x (add y z))=phi a (add x (add y z))
  exact Rows.ProofsB.phiNFdefault_phi ha

theorem lt_M_addZZJ (n : Nat) :
    lt TM.Term.M (add Z0t (add Z0t (Jt (n+1))))=false := by
  unfold lt
  rw [show fuelOf TM.Term.M (add Z0t (add Z0t (Jt (n+1))))=
      (2*(TM.Term.M.deg+(add Z0t (add Z0t (Jt (n+1)))).deg)+6)+1+1 from by
        unfold fuelOf
        omega,
    Evidence.WF.ltF_succ_M_add]
  simp only [show ((TM.Term.M:Term)==Z0t)=false from rfl,Bool.false_or,
    Evidence.WF.ltF_succ_M_Z]

theorem omegaNF_addZZJ (n : Nat) :
    omegaNF (add Z0t (add Z0t (Jt (n+1))))
      =phi zero (add Z0t (add Z0t (Jt (n+1)))) := by
  rw [omegaNF_of_le_M (lt_M_addZZJ n)]
  exact phiNF_add_triple rfl (Jt_succ_isAP n) (Jt_succ_bne_one n)

theorem plus_zero_addZJ (n : Nat) :
    plus zero (add Z0t (Jt (n+1)))=add Z0t (Jt (n+1)) := by
  unfold plus
  rw [toList_add_Z0t_Jt_succ]
  rfl

theorem plus_Z0t_addZJ (n : Nat) :
    plus Z0t (add Z0t (Jt (n+1)))=add Z0t (add Z0t (Jt (n+1))) := by
  unfold plus
  rw [show Z0t.toList=[Z0t] from rfl,toList_add_Z0t_Jt_succ]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le Z0t Z0t=true from Evidence.WF.le_self Z0t]
  rfl

/-- The value a complete block hands to `collapse 0`.  **Two `Ω`s, where `G10.Kt` has
    one** — the extra `(2,1)` column is the extra `Ω`. -/
def Kt (n : Nat) : Term := phi zero (add Z0t (add Z0t (Jt (n+1))))

theorem collapse_one_addZJ (n : Nat) :
    Trans.Dict.collapse 1 (add Z0t (Jt (n+1)))=Kt n := by
  have hw : Trans.Dict.wcnf (Z one) [Z0t,Jt (n+1)]=([],add Z0t (Jt (n+1))) := by
    rw [Trans.Dict.wcnf,if_pos (show lt Z0t (Z one)=true from by decide)]
    rfl
  unfold Trans.Dict.collapse
  rw [show Trans.Dict.reg (1+1)=Z one from rfl,
    show Trans.Dict.reg 1=Z0t from rfl,
    show ((1:Nat)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [toList_add_Z0t_Jt_succ,hw]
  simp only [List.foldl_nil,Option.getD_none]
  rw [plus_zero_addZJ,plus_Z0t_addZJ,omegaNF_addZZJ]
  rfl

theorem Jt_succ_lt_Htail (n : Nat) :
    lt (Jt (n+1)) (add Z0t one)=true :=
  Evidence.WF.lt_trans_inT (Jt_inT (n+1)) (by decide) (by decide)
    (Jt_lt_Z0t (n+1)) (by decide)

theorem addZJ_lt_Htail2 (n : Nat) :
    lt (add Z0t (Jt (n+1))) (add Z0t (add Z0t one))=true := by
  rw [Evidence.WF.lt_add_add (by
    intro h
    injection h with _ hj
    exact Evidence.WF.ne_of_ltF (Jt_succ_lt_Htail n) hj),if_pos rfl]
  exact Jt_succ_lt_Htail n

theorem addZZJ_lt_Hexp (n : Nat) :
    lt (add Z0t (add Z0t (Jt (n+1)))) (add Z0t (add Z0t (add Z0t one)))=true := by
  rw [Evidence.WF.lt_add_add (by
    intro h
    injection h with _ hj
    exact Evidence.WF.ne_of_ltF (addZJ_lt_Htail2 n) hj),if_pos rfl]
  exact addZJ_lt_Htail2 n

theorem Kt_lt_H (n : Nat) : lt (Kt n) G9Dict.H=true := by
  change lt (phi zero (add Z0t (add Z0t (Jt (n+1)))))
    (phi zero (add Z0t (add Z0t (add Z0t one))))=true
  rw [Evidence.WF.lt_pow]
  exact addZZJ_lt_Hexp n

theorem plus_H_Kt (n : Nat) : plus G9Dict.H (Kt n)=add G9Dict.H (Kt n) := by
  unfold plus
  rw [show G9Dict.H.toList=[G9Dict.H] from rfl,
    show (Kt n).toList=[Kt n] from by rw [Kt]; rfl]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (Kt n) G9Dict.H=true from Evidence.WF.le_of_lt (Kt_lt_H n)]
  rfl

theorem addZZJ_not_lt_Z0t (n : Nat) :
    lt (add Z0t (add Z0t (Jt (n+1)))) Z0t=false := by
  unfold lt
  rw [show fuelOf (add Z0t (add Z0t (Jt (n+1)))) Z0t=
      (2*((add Z0t (add Z0t (Jt (n+1)))).deg+Z0t.deg)+7)+1 from by
        unfold fuelOf
        omega,
    Evidence.WF.ltF_succ_add_nsum _ (by exact Term.noConfusion) (by rfl)]
  rw [← Evidence.WF.lt_eq_ltF Z0t Z0t _ (by simp only [Term.deg]; omega)]
  exact Evidence.WF.lt_irrefl Z0t

theorem Kt_not_lt_Z0t (n : Nat) : lt (Kt n) Z0t=false := by
  unfold Kt lt
  rw [show fuelOf (phi zero (add Z0t (add Z0t (Jt (n+1))))) Z0t=
      (2*((phi zero (add Z0t (add Z0t (Jt (n+1))))).deg+Z0t.deg)+7)+1 from by
        unfold fuelOf
        omega,
    Evidence.WF.ltF_succ_phi_Z]
  rw [← Evidence.WF.lt_eq_ltF (add Z0t (add Z0t (Jt (n+1)))) Z0t _ (by
    simp only [Term.deg]
    omega),addZZJ_not_lt_Z0t]
  simp only [Bool.and_false]

theorem phiShifted_addZZJ (n : Nat) :
    phiShifted zero (add Z0t (add Z0t (Jt (n+1))))=false := by
  unfold phiShifted
  rw [splitFin_add_triple (Jt_succ_isAP n) (Jt_succ_bne_one n)]
  rfl

theorem logOm_Kt (n : Nat) :
    Trans.Dict.logOm (Kt n)=add Z0t (add Z0t (Jt (n+1))) := by
  unfold Kt Trans.Dict.logOm
  change (if phiShifted zero (add Z0t (add Z0t (Jt (n+1)))) then
    plus (add Z0t (add Z0t (Jt (n+1)))) one
    else add Z0t (add Z0t (Jt (n+1))))=_
  rw [phiShifted_addZZJ]
  rfl

theorem wcnf_Kt (n : Nat) : Trans.Dict.wcnf Z0t [Kt n]=
    ([(ofNat 2,Jt (n+1))],zero) := by
  unfold Trans.Dict.wcnf
  rw [Kt_not_lt_Z0t]
  simp only [Bool.false_eq_true,if_false,logOm_Kt]
  rw [toList_addZZJ]
  simp only [List.filter_cons,List.filter_nil,
    show lt Z0t Z0t=false from Evidence.WF.lt_irrefl Z0t,Jt_lt_Z0t,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false,
    List.map_cons,List.map_nil,
    show Trans.Dict.divAP Z0t Z0t=one from rfl,TM.Term.ofList,
    omegaNF_Jt_succ,Trans.Dict.wcnf]
  rfl

theorem wcnf_H_Kt (n : Nat) : Trans.Dict.wcnf Z0t [G9Dict.H,Kt n]=
    ([(ofNat 3,omega),(ofNat 2,Jt (n+1))],zero) := by
  rw [Trans.Dict.wcnf,if_neg (by decide)]
  simp only [G9Dict.H,Trans.Dict.logOm,TM.Term.phiShifted,TM.Term.splitFin,
    Bool.false_or,Bool.false_eq_true,if_false,TM.Term.toList,List.filter_cons,
    List.filter_nil,List.map_cons,List.map_nil,Trans.Dict.divAP,
    Trans.Dict.subAP]
  rw [wcnf_Kt]
  rfl

theorem phiNF_Jt_succ (n : Nat) : phiNF (ofNat 2) (Jt (n+1))=Jt (n+2) := by
  rw [show Jt (n+1)=phi (ofNat 2) (Jt n) from by rw [Jt],
    Rows.ProofsB.phiNF_phi_arg (a := ofNat 2) (by rfl),Jt,Jt]

theorem collapse_H_Kt (n : Nat) :
    Trans.Dict.collapse 0 (plus G9Dict.H (Kt n))=Jt (n+2) := by
  have hap : (Jt (n+2)).isAP=true := by
    rw [show n+2=(n+1)+1 by omega,Jt_succ_isAP]
  have hom : omegaNF (Jt (n+2))=Jt (n+2) := by
    rw [show n+2=(n+1)+1 by omega,omegaNF_Jt_succ]
  rw [plus_H_Kt]
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg,TM.Term.ofNat]
  rw [show (add G9Dict.H (Kt n)).toList=[G9Dict.H,Kt n] from by
    rw [G9Dict.H,Kt]
    rfl,wcnf_H_Kt]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show le Z0t (TM.Term.ofNat 3)=false from by decide,
    show le Z0t (TM.Term.ofNat 2)=false from by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show Trans.Dict.sub1 omega=omega from rfl]
  simp only [Option.getD_some]
  rw [show (if (0==0) then zero else plus zero one)=zero from rfl,
    show phiNF (ofNat 3) (plus zero omega)=Bph from rfl,
    plus_Bph_Jt_succ,phiNF_Jt_succ,
    show plus (Jt (n+2)) zero=Jt (n+2) from rfl,
    Rows.ProofsB.plus_zero_left hap,hom]

theorem fs_raw (k : Nat) : fsN t k=iterPhiAt (ofNat 2) (plus Bph one) k := by
  rw [t,fsN]
  rfl

theorem fs_Jt : ∀ n : Nat, fsN t (n+1)=Jt (n+1)
  | 0 => by rw [fs_raw]; rfl
  | n+1 => by
    have h : fsN t (n+2)=phiNF (ofNat 2) (fsN t (n+1)) := by
      rw [fs_raw,fs_raw]
      rfl
    rw [h,fs_Jt n,Jt]
    exact Rows.ProofsB.phiNF_phi_arg (a := ofNat 2) (by rfl)

theorem dict_D1z : Trans.Dict.dict D1z=Z0t := rfl

theorem dict_D0_B1 : Trans.Dict.dict (.D 0 B1)=Jt 1 := by rfl

theorem dict_D0_W : ∀ n : Nat,
    Trans.Dict.dict (.D 0 (W n B1))=Jt (n+1)
  | 0 => dict_D0_B1
  | n+1 => by
    rw [W,Trans.Dict.dict_D,Trans.Dict.dict_sum,G9Dict.dict_A0,
      Trans.Dict.dict_D,Trans.Dict.dict_sum,dict_D1z,dict_D0_W n,
      plus_Z0t_Jt_succ,collapse_one_addZJ]
    exact collapse_H_Kt n

theorem LBT_phase0 (a : Nat) : LBT (7*a)=.D 0 (W a (Part 0)) := by
  unfold LBT
  rw [show 7*a/7=a by omega,show 7*a%7=0 by omega]

/-- Link 3: every complete seven-column block advances the shifted family-four sequence. -/
theorem dict_LBT (n : Nat) :
    Trans.Dict.dict (LBT (7*n))=fsN t (n+1) := by
  rw [LBT_phase0]
  change Trans.Dict.dict (.D 0 (W n B1))=_
  rw [dict_D0_W,← fs_Jt]

#guard (List.range 5).all fun n => Trans.Dict.wcnf Z0t [Kt n]==([(ofNat 2,Jt (n+1))],zero)
#guard (List.range 5).all fun n =>
  Trans.Dict.collapse 0 (plus G9Dict.H (Kt n))==Jt (n+2)
#guard (List.range 5).all fun n =>
  Trans.Dict.collapse 1 (add Z0t (Jt (n+1)))==Kt n
-- リンク 2 はまだ定理ではない。閉じた形が合っていることだけを測ってある
#guard (List.range 30).all fun m => Trans.Recal.transPort (L m)==LBT m
#guard (List.range 30).all fun m => Trans.Recal.redP (L m)==L m
#guard (List.range 8).all fun n => Trans.oR (BMS.expand M n)==some (fsN t (n+1))

#print axioms ofMatrix_M
#print axioms dict_LBT

end G11
end Rows.Selected
