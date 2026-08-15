import Rows.G10
import Rows.Ladder

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

/-! ### Link 2, step 1: the ladder's two rows in closed form.

Base and tail obey the same formula, which is what makes the parent structure uniform.
The period is 7 and the row-zero value steps by 2 per block. -/

/-- Row-zero value at index `k`, base and tail alike. -/
def Gp (k : Nat) : Int :=
  ((2*(k/7) : Nat) : Int) + (if k%7=0 then 0 else if k%7=1 ∨ k%7=5 then 1 else 2)

/-- Row-one value at index `k`.  Identical to the tail's `q`. -/
def Gq (k : Nat) : Int := if k%7=0 ∨ k%7=4 then 0 else 1

theorem Gp_val (a r : Nat) (hr : r<7) :
    Gp (7*a+r)=((2*a : Nat) : Int)+(if r=0 then 0 else if r=1 ∨ r=5 then 1 else 2) := by
  unfold Gp
  rw [show (7*a+r)/7=a by omega,show (7*a+r)%7=r by omega]

theorem Gp_r (a : Nat) :
    Gp (7*a+0)=((2*a:Nat):Int) ∧ Gp (7*a+1)=((2*a:Nat):Int)+1
    ∧ Gp (7*a+2)=((2*a:Nat):Int)+2 ∧ Gp (7*a+3)=((2*a:Nat):Int)+2
    ∧ Gp (7*a+4)=((2*a:Nat):Int)+2 ∧ Gp (7*a+5)=((2*a:Nat):Int)+1
    ∧ Gp (7*a+6)=((2*a:Nat):Int)+2 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [Gp_val a 0 (by omega),if_pos rfl,Int.add_zero]
  · rw [Gp_val a 1 (by omega),if_neg (by omega),if_pos (Or.inl rfl)]
  · rw [Gp_val a 2 (by omega),if_neg (by omega),if_neg (by omega)]
  · rw [Gp_val a 3 (by omega),if_neg (by omega),if_neg (by omega)]
  · rw [Gp_val a 4 (by omega),if_neg (by omega),if_neg (by omega)]
  · rw [Gp_val a 5 (by omega),if_neg (by omega),if_pos (Or.inr rfl)]
  · rw [Gp_val a 6 (by omega),if_neg (by omega),if_neg (by omega)]

theorem p_eq_Gp (k : Nat) : p k=Gp (k+7) := by
  unfold p Gp
  rw [show (k+7)%7=k%7 by omega,show (k+7)/7=k/7+1 by omega]
  by_cases h0 : k%7=0
  · rw [if_pos h0,if_pos h0]; push_cast; omega
  · rw [if_neg h0,if_neg h0]
    by_cases h1 : k%7=1 ∨ k%7=5
    · rw [if_pos h1,if_pos h1]; push_cast; omega
    · rw [if_neg h1,if_neg h1]; push_cast; omega

theorem q_eq_Gq (k : Nat) : q k=Gq (k+7) := by
  unfold q Gq
  rw [show (k+7)%7=k%7 by omega]

theorem getD_T (m k : Nat) (hk : k<m) : (T m).getD k (0,0)=(p k,q k) := by
  unfold T
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

theorem getD_L_tail (m k : Nat) : (L m).getD (k+7) (0,0)=(T m).getD k (0,0) := by
  show (((0,0)::(1,1)::(2,1)::(2,1)::(2,0)::(1,1)::(2,1)::T m : Trans.Recal.PS)).getD
    (k+7) (0,0)=(T m).getD k (0,0)
  rw [show k+7=k+1+1+1+1+1+1+1 by omega]
  simp only [List.getD_cons_succ]

theorem gp0_L (m k : Nat) (hk : k<m+7) : Trans.Recal.gp0 (L m) ((k:Nat):Int)=Gp k := by
  show (if (((k:Nat):Int)<0) then 0 else ((L m).getD k (0,0)).1)=Gp k
  rw [if_neg (by omega)]
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | (j+7), h =>
    rw [getD_L_tail,getD_T m j (by omega)]
    exact p_eq_Gp j

theorem gp1_L (m k : Nat) (hk : k<m+7) : Trans.Recal.gp1 (L m) ((k:Nat):Int)=Gq k := by
  show (if (((k:Nat):Int)<0) then 0 else ((L m).getD k (0,0)).2)=Gq k
  rw [if_neg (by omega)]
  match k, hk with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | (j+7), h =>
    rw [getD_L_tail,getD_T m j (by omega)]
    exact q_eq_Gq j

#guard (List.range 12).all fun m => (List.range (m+7)).all fun k =>
  Trans.Recal.gp0 (L m) ((k:Nat):Int)==Gp k
#guard (List.range 12).all fun m => (List.range (m+7)).all fun k =>
  Trans.Recal.gp1 (L m) ((k:Nat):Int)==Gq k

/-! ### Link 2, step 2: the row-zero parent, as arithmetic on `Gp`.

The step back depends only on the residue: `[2,1,1,2,3,5,1]`. -/

def parN (k : Nat) : Nat :=
  if k%7=0 ∨ k%7=3 then k-2 else if k%7=4 then k-3
  else if k%7=5 then k-5 else k-1

theorem parN_lt (k : Nat) (hk : 1 ≤ k) : parN k<k := by
  unfold parN
  by_cases h1 : k%7=0 ∨ k%7=3
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : k%7=4
    · rw [if_pos h2]; omega
    · rw [if_neg h2]
      by_cases h3 : k%7=5
      · rw [if_pos h3]; omega
      · rw [if_neg h3]; omega

theorem Gp_parN_lt (k : Nat) (hk : 1 ≤ k) : Gp (parN k)<Gp k := by
  obtain ⟨a,r,hr,rfl⟩ : ∃ a r, r<7 ∧ k=7*a+r := ⟨k/7,k%7,by omega,by omega⟩
  unfold parN
  rw [show (7*a+r)%7=r by omega]
  rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · obtain ⟨b,rfl⟩ : ∃ b, a=b+1 := ⟨a-1,by omega⟩
    rw [if_pos (by omega),show 7*(b+1)+0-2=7*b+5 by omega]
    obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := Gp_r b
    obtain ⟨f0,f1,f2,f3,f4,f5,f6⟩ := Gp_r (b+1)
    rw [e5,f0]
    push_cast
    omega
  · rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),
      show 7*a+1-1=7*a+0 by omega]
    obtain ⟨e0,e1,_,_,_,_,_⟩ := Gp_r a
    rw [e0,e1]; omega
  · rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),
      show 7*a+2-1=7*a+1 by omega]
    obtain ⟨_,e1,e2,_,_,_,_⟩ := Gp_r a
    rw [e1,e2]; omega
  · rw [if_pos (by omega),show 7*a+3-2=7*a+1 by omega]
    obtain ⟨_,e1,_,e3,_,_,_⟩ := Gp_r a
    rw [e1,e3]; omega
  · rw [if_neg (by omega),if_pos (by omega),show 7*a+4-3=7*a+1 by omega]
    obtain ⟨_,e1,_,_,e4,_,_⟩ := Gp_r a
    rw [e1,e4]; omega
  · rw [if_neg (by omega),if_neg (by omega),if_pos (by omega),
      show 7*a+5-5=7*a+0 by omega]
    obtain ⟨e0,_,_,_,_,e5,_⟩ := Gp_r a
    rw [e0,e5]; omega
  · rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),
      show 7*a+6-1=7*a+5 by omega]
    obtain ⟨_,_,_,_,_,e5,e6⟩ := Gp_r a
    rw [e5,e6]; omega

theorem Gp_parN_keep (k j : Nat) (h1 : parN k<j) (h2 : j<k) : Gp k ≤ Gp j := by
  obtain ⟨a,r,hr,rfl⟩ : ∃ a r, r<7 ∧ k=7*a+r := ⟨k/7,k%7,by omega,by omega⟩
  unfold parN at h1
  rw [show (7*a+r)%7=r by omega] at h1
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := Gp_r a
  rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [if_pos (by omega)] at h1
    obtain ⟨b,rfl⟩ : ∃ b, a=b+1 := ⟨a-1,by omega⟩
    have hj : j=7*b+6 := by omega
    subst hj
    obtain ⟨g0,g1,g2,g3,g4,g5,g6⟩ := Gp_r b
    rw [g6,show 7*(b+1)+0=7*(b+1)+0 from rfl]
    obtain ⟨f0,_,_,_,_,_,_⟩ := Gp_r (b+1)
    rw [f0]
    push_cast
    omega
  · rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)] at h1; omega
  · rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)] at h1; omega
  · rw [if_pos (by omega)] at h1
    have hj : j=7*a+2 := by omega
    subst hj
    rw [e2,e3]; omega
  · rw [if_neg (by omega),if_pos (by omega)] at h1
    rcases (show j=7*a+2 ∨ j=7*a+3 by omega) with rfl|rfl
    · rw [e2,e4]; omega
    · rw [e3,e4]; omega
  · rw [if_neg (by omega),if_neg (by omega),if_pos (by omega)] at h1
    rcases (show j=7*a+1 ∨ j=7*a+2 ∨ j=7*a+3 ∨ j=7*a+4 by omega)
      with rfl|rfl|rfl|rfl
    · rw [e1,e5]; omega
    · rw [e2,e5]; omega
    · rw [e3,e5]; omega
    · rw [e4,e5]; omega
  · rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)] at h1; omega

#guard (List.range 40).all fun k =>
  (k==0) || (decide (Gp (parN k)<Gp k)
    && (List.range k).all fun j => !(decide (parN k<j)) || decide (Gp k ≤ Gp j))

/-! ### Link 2, step 3: every ladder in the recursion is a window of one sequence. -/

/-- The ladder read from offset `i`, shifted by `d`, of length `n`. -/
def Win (i : Nat) (d : Int) (n : Nat) : Trans.Recal.PS :=
  (List.range n).map fun j => (Gp (j+i)+d,Gq (j+i))

theorem length_Win (i : Nat) (d : Int) (n : Nat) : (Win i d n).length=n := by
  simp [Win]

theorem getD_Win (i : Nat) (d : Int) (n k : Nat) (hk : k<n) :
    (Win i d n).getD k (0,0)=(Gp (k+i)+d,Gq (k+i)) := by
  unfold Win
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

theorem Win_succ (i : Nat) (d : Int) (n : Nat) :
    Win i d (n+1)=Win i d n++[(Gp (n+i)+d,Gq (n+i))] := by
  unfold Win
  rw [List.range_succ,List.map_append]
  rfl

theorem Gp_add_seven (k : Nat) : Gp (k+7)=Gp k+2 := by
  obtain ⟨a,r,hr,rfl⟩ : ∃ a r, r<7 ∧ k=7*a+r := ⟨k/7,k%7,by omega,by omega⟩
  rw [show 7*a+r+7=7*(a+1)+r by omega,Gp_val (a+1) r hr,Gp_val a r hr]
  push_cast
  omega

theorem Gq_add_seven (k : Nat) : Gq (k+7)=Gq k := by
  unfold Gq
  rw [show (k+7)%7=k%7 by omega]

theorem Win_add_seven (i : Nat) (d : Int) (n : Nat) : Win (i+7) d n=Win i (d+2) n := by
  unfold Win
  apply List.map_congr_left
  intro j _
  show (Gp (j+(i+7))+d,Gq (j+(i+7)))=(Gp (j+i)+(d+2),Gq (j+i))
  rw [show j+(i+7)=(j+i)+7 by omega,Gp_add_seven,Gq_add_seven]
  congr 1
  omega

theorem Win_drop (i : Nat) (d : Int) (n : Nat) :
    (Win i d (n+1)).drop 1=Win (i+1) d n := by
  unfold Win
  rw [List.range_succ_eq_map,List.map_cons,List.drop_succ_cons,List.drop_zero,
    List.map_map]
  apply List.map_congr_left
  intro j _
  show (Gp (j+1+i)+d,Gq (j+1+i))=(Gp (j+(i+1))+d,Gq (j+(i+1)))
  rw [show j+1+i=j+(i+1) by omega]

theorem Win_cons (i : Nat) (d : Int) (n : Nat) :
    Win i d (n+1)=(Gp i+d,Gq i) :: Win (i+1) d n := by
  unfold Win
  rw [List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1
  · rw [Nat.zero_add]
  · apply List.map_congr_left
    intro j _
    show (Gp (j+1+i)+d,Gq (j+1+i))=(Gp (j+(i+1))+d,Gq (j+(i+1)))
    rw [show j+1+i=j+(i+1) by omega]

theorem incrFirst_Win (i : Nat) (d e : Int) (n : Nat) :
    Trans.Recal.incrFirst (Win i d n) e=Win i (d+e) n := by
  unfold Trans.Recal.incrFirst Win
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  show ((Gp (j+i)+d)+e,Gq (j+i))=(Gp (j+i)+(d+e),Gq (j+i))
  rw [Int.add_assoc]

theorem Win_append (i : Nat) (d : Int) (a b : Nat) :
    Win i d a++Win (i+a) d b=Win i d (a+b) := by
  induction b with
  | zero => simp [Win]
  | succ b ih =>
    rw [Win_succ (i+a) d b,← List.append_assoc,ih,show a+(b+1)=(a+b)+1 by omega,
      Win_succ i d (a+b),show b+(i+a)=(a+b)+i by omega]

theorem L_eq_Win (m : Nat) : L m=Win 0 0 (m+7) := by
  unfold Win
  have h : ∀ n : Nat, (List.range n).map (fun j => (Gp (j+0)+(0:Int),Gq (j+0)))
      =(List.range n).map (fun j => (Gp j,Gq j)) := by
    intro n
    apply List.map_congr_left
    intro j _
    show (Gp (j+0)+(0:Int),Gq (j+0))=(Gp j,Gq j)
    rw [Nat.add_zero,Int.add_zero]
  rw [h]
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show m+1+7=(m+7)+1 by omega,List.range_succ,List.map_append,← ih,
      show L (m+1)=L m++[(p m,q m)] from L_succ m]
    congr 1
    show [(p m,q m)]=[(Gp (m+7),Gq (m+7))]
    rw [← p_eq_Gp,← q_eq_Gq]

#guard (List.range 12).all fun m => L m==Win 0 0 (m+7)
#guard (List.range 8).all fun n => (List.range 8).all fun i =>
  Win (i+7) 0 n==Win i 2 n

/-! ### Link 2, step 4: where `Gp` attains its minimum from an offset on.

`Gp`'s residue profile is `[0,1,2,2,2,1,2]`, which is not monotone: the `1` at
residue 5 dips back below residues 2, 3, 4.  So the minimum-from-here property
holds only at residues 0, 1, 5, 6, and strictly only at 0 and 5. -/

theorem Gp_min_le (i t : Nat) (hi : i%7=0 ∨ i%7=1 ∨ i%7=5 ∨ i%7=6) (h : i ≤ t) :
    Gp i ≤ Gp t := by
  obtain ⟨a,r,hr,rfl⟩ : ∃ a r, r<7 ∧ i=7*a+r := ⟨i/7,i%7,by omega,by omega⟩
  obtain ⟨b,ss,hs,rfl⟩ : ∃ b ss, ss<7 ∧ t=7*b+ss := ⟨t/7,t%7,by omega,by omega⟩
  rw [show (7*a+r)%7=r by omega] at hi
  have hab : a ≤ b := by omega
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := Gp_r a
  obtain ⟨f0,f1,f2,f3,f4,f5,f6⟩ := Gp_r b
  rcases (show r=0 ∨ r=1 ∨ r=5 ∨ r=6 by omega) with rfl|rfl|rfl|rfl <;>
    rcases (show ss=0 ∨ ss=1 ∨ ss=2 ∨ ss=3 ∨ ss=4 ∨ ss=5 ∨ ss=6 by omega)
      with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [e0,e1,e2,e3,e4,e5,e6,f0,f1,f2,f3,f4,f5,f6] <;> push_cast <;> omega

theorem Gp_min_lt (i t : Nat) (hi : i%7=0 ∨ i%7=5) (h : i<t) : Gp i<Gp t := by
  obtain ⟨a,r,hr,rfl⟩ : ∃ a r, r<7 ∧ i=7*a+r := ⟨i/7,i%7,by omega,by omega⟩
  obtain ⟨b,ss,hs,rfl⟩ : ∃ b ss, ss<7 ∧ t=7*b+ss := ⟨t/7,t%7,by omega,by omega⟩
  rw [show (7*a+r)%7=r by omega] at hi
  have hab : a ≤ b := by omega
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := Gp_r a
  obtain ⟨f0,f1,f2,f3,f4,f5,f6⟩ := Gp_r b
  rcases (show r=0 ∨ r=5 by omega) with rfl|rfl <;>
    rcases (show ss=0 ∨ ss=1 ∨ ss=2 ∨ ss=3 ∨ ss=4 ∨ ss=5 ∨ ss=6 by omega)
      with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [e0,e1,e2,e3,e4,e5,e6,f0,f1,f2,f3,f4,f5,f6] <;> push_cast <;> omega

#guard (List.range 25).all fun i => (List.range 25).all fun t =>
  !(decide ((i%7=0 ∨ i%7=1 ∨ i%7=5 ∨ i%7=6) ∧ i ≤ t)) || decide (Gp i ≤ Gp t)
#guard (List.range 25).all fun i => (List.range 25).all fun t =>
  !(decide ((i%7=0 ∨ i%7=5) ∧ i<t)) || decide (Gp i<Gp t)

/-! ### Link 2, step 5: one exceptional head over a window. -/

def Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) : Trans.Recal.PS := h :: Win i d n

theorem length_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) :
    (Hd h i d n).length=n+1 := by
  unfold Hd
  rw [List.length_cons,length_Win]

theorem lenI_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.lenI (Hd h i d n)=((n:Nat):Int)+1 := by
  unfold Trans.Recal.lenI
  rw [length_Hd]
  omega

theorem gp0_Hd (h : Int × Int) (i : Nat) (d : Int) (n k : Nat) (hk : k<n+1) :
    Trans.Recal.gp0 (Hd h i d n) ((k:Nat):Int)
      = if k=0 then h.1 else Gp (k-1+i)+d := by
  show (if (((k:Nat):Int)<0) then 0 else ((Hd h i d n).getD k (0,0)).1)=_
  rw [if_neg (by omega)]
  cases k with
  | zero => rw [if_pos rfl]; rfl
  | succ j =>
    rw [if_neg (by omega)]
    show ((Win i d n).getD j (0,0)).1=Gp (j+1-1+i)+d
    rw [getD_Win i d n j (by omega),show j+1-1=j from rfl]

theorem gp1_Hd (h : Int × Int) (i : Nat) (d : Int) (n k : Nat) (hk : k<n+1) :
    Trans.Recal.gp1 (Hd h i d n) ((k:Nat):Int)
      = if k=0 then h.2 else Gq (k-1+i) := by
  show (if (((k:Nat):Int)<0) then 0 else ((Hd h i d n).getD k (0,0)).2)=_
  rw [if_neg (by omega)]
  cases k with
  | zero => rw [if_pos rfl]; rfl
  | succ j =>
    rw [if_neg (by omega)]
    show ((Win i d n).getD j (0,0)).2=Gq (j+1-1+i)
    rw [getD_Win i d n j (by omega),show j+1-1=j from rfl]

def GH (c : Int) (i : Nat) (d : Int) (k : Nat) : Int :=
  if k=0 then c else Gp (k-1+i)+d

def parHd (i k : Nat) : Nat := if i ≤ parN (k-1+i) then parN (k-1+i)-i+1 else 0

theorem parHd_lt (i k : Nat) (hi : 1 ≤ i) (hk : 1 ≤ k) : parHd i k<k := by
  unfold parHd
  by_cases hc : i ≤ parN (k-1+i)
  · rw [if_pos hc]
    have := parN_lt (k-1+i) (by omega)
    omega
  · rw [if_neg hc]
    omega

theorem GH_drop (c : Int) (i : Nat) (d : Int) (n k : Nat) (hi : 1 ≤ i) (hk : 1 ≤ k)
    (hkn : k<n+1) (hh : ∀ t, i ≤ t → t<i+n → c<Gp t+d) :
    GH c i d (parHd i k)<GH c i d k := by
  have ht : 1 ≤ k-1+i := by omega
  unfold parHd
  by_cases hc : i ≤ parN (k-1+i)
  · rw [if_pos hc]
    have he : parN (k-1+i)-i+1-1+i=parN (k-1+i) := by omega
    unfold GH
    rw [if_neg (by omega),if_neg (by omega),he]
    have := Gp_parN_lt (k-1+i) ht
    omega
  · rw [if_neg hc]
    unfold GH
    rw [if_pos rfl,if_neg (by omega)]
    exact hh (k-1+i) (by omega) (by omega)

theorem GH_keep (c : Int) (i : Nat) (d : Int) (k j : Nat) (hk : 1 ≤ k)
    (h1 : parHd i k<j) (h2 : j<k) : GH c i d k ≤ GH c i d j := by
  have hj : 1 ≤ j := by omega
  have hpar : parN (k-1+i)<j-1+i := by
    unfold parHd at h1
    by_cases hc : i ≤ parN (k-1+i)
    · rw [if_pos hc] at h1; omega
    · rw [if_neg hc] at h1; omega
  unfold GH
  rw [if_neg (by omega),if_neg (by omega)]
  have := Gp_parN_keep (k-1+i) (j-1+i) hpar (by omega)
  omega

theorem gp0_Hd_GH (h : Int × Int) (i : Nat) (d : Int) (n k : Nat) (hk : k<(Hd h i d n).length) :
    Trans.Recal.gp0 (Hd h i d n) ((k:Nat):Int)=GH h.1 i d k := by
  rw [length_Hd] at hk
  rw [gp0_Hd h i d n k hk]
  rfl

theorem chain_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hi : 1 ≤ i)
    (hh : ∀ t, i ≤ t → t<i+n → h.1<Gp t+d) :
    ∀ k, 1 ≤ k → k<(Hd h i d n).length →
      Trans.Recal.fpar (Hd h i d n) 0 ((k:Nat):Int) 0=((parHd i k : Nat) : Int) :=
  Rows.Ladder.fpar_of_gap
    (G := GH h.1 i d) (par := parHd i)
    (gp0_Hd_GH h i d n)
    (fun k hk1 _ => parHd_lt i k hi hk1)
    (fun k hk1 hk => by
      rw [length_Hd] at hk
      exact GH_drop h.1 i d n k hi hk1 hk hh)
    (fun k j hk1 _ h1 h2 => GH_keep h.1 i d k j hk1 h1 h2)

theorem root_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.fpar (Hd h i d n) 0 ((0:Nat):Int) 0=-1 :=
  Rows.Ladder.fpar_zero_of_gap
    (G := GH h.1 i d) (gp0_Hd_GH h i d n) (by rw [length_Hd]; omega)

theorem isPrincipalP_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hi : 1 ≤ i)
    (hn : 1 ≤ n) (hh : ∀ t, i ≤ t → t<i+n → h.1<Gp t+d) :
    Trans.Recal.isPrincipalP (Hd h i d n)=true :=
  Rows.Ladder.isPrincipalP_of_chain (chain_Hd h i d n hi hh)
    (fun k hk1 _ => parHd_lt i k hi hk1) (root_Hd h i d n)
    (by rw [length_Hd]; omega)

theorem ppair_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hi : 1 ≤ i)
    (hh : ∀ t, i ≤ t → t<i+n → h.1<Gp t+d) :
    Trans.Recal.ppair (Hd h i d n)=[Hd h i d n] :=
  Rows.Ladder.ppair_of_chain (chain_Hd h i d n hi hh)
    (fun k hk1 _ => parHd_lt i k hi hk1) (root_Hd h i d n)
    (by rw [length_Hd]; omega)

theorem Win_eq_Hd (i : Nat) (d : Int) (n : Nat) :
    Win i d (n+1)=Hd (Gp i+d,Gq i) (i+1) d n := by
  unfold Hd
  rw [Win_cons]

theorem ppair_Win (i : Nat) (d : Int) (n : Nat) (hi : i%7=0 ∨ i%7=5) :
    Trans.Recal.ppair (Win i d (n+1))=[Win i d (n+1)] := by
  rw [Win_eq_Hd]
  exact ppair_Hd _ (i+1) d n (by omega)
    (fun t ht _ => by
      have := Gp_min_lt i t hi (by omega)
      show Gp i+d<Gp t+d
      omega)

theorem isPrincipalP_Win (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n)
    (hi : i%7=0 ∨ i%7=5) : Trans.Recal.isPrincipalP (Win i d (n+1))=true := by
  rw [Win_eq_Hd]
  exact isPrincipalP_Hd _ (i+1) d n (by omega) hn
    (fun t ht _ => by
      have := Gp_min_lt i t hi (by omega)
      show Gp i+d<Gp t+d
      omega)

#guard (List.range 8).all fun i => (List.range 8).all fun n =>
  !(decide (i%7=0 ∨ i%7=5)) || (Trans.Recal.ppair (Win i 1 (n+1))==[Win i 1 (n+1)])

/-! ### Link 2, step 6: slices of a window are windows. -/

theorem Win_drop1 (i : Nat) (d : Int) (n : Nat) :
    (Win i d n).drop 1=Win (i+1) d (n-1) := by
  cases n with
  | zero => rfl
  | succ u =>
    rw [Win_drop]
    rfl

theorem Win_drop_n (i : Nat) (d : Int) (n a : Nat) :
    (Win i d n).drop a=Win (i+a) d (n-a) := by
  induction a generalizing i n with
  | zero => rfl
  | succ a ih =>
    rw [show a+1=1+a by omega,← List.drop_drop,Win_drop1,ih,
      show i+1+a=i+(1+a) by omega,show n-1-a=n-(1+a) by omega]

theorem Win_take (i : Nat) (d : Int) (n c : Nat) (h : c ≤ n) :
    (Win i d n).take c=Win i d c := by
  rw [show n=c+(n-c) by omega,← Win_append i d c (n-c),
    List.take_append_of_le_length (by rw [length_Win]; omega),
    List.take_of_length_le (by rw [length_Win]; omega)]

theorem slice_Win (i : Nat) (d : Int) (n a b : Nat) (hab : a ≤ b) (hb : b ≤ n) :
    Trans.Recal.slice (Win i d n) ((a:Nat):Int) ((b:Nat):Int)=Win (i+a) d (b-a) := by
  unfold Trans.Recal.slice
  rw [show (((a:Nat)):Int).toNat=a from by omega,Win_drop_n,
    show ((((b:Nat)):Int)-((a:Nat):Int)).toNat=b-a from by omega,
    Win_take (i+a) d (n-a) (b-a) (by omega)]

/-! ### Link 2, step 7: `parN` never drops below an offset ≡ 0 or 5. -/

theorem parN_ge (i t : Nat) (hi : i%7=0 ∨ i%7=5) (h : i<t) : i ≤ parN t := by
  unfold parN
  rcases hi with hi|hi <;>
    (by_cases h1 : t%7=0 ∨ t%7=3
     · rw [if_pos h1]; omega
     · rw [if_neg h1]
       by_cases h2 : t%7=4
       · rw [if_pos h2]; omega
       · rw [if_neg h2]
         by_cases h3 : t%7=5
         · rw [if_pos h3]; omega
         · rw [if_neg h3]; omega)

#guard (List.range 30).all fun i => (List.range 30).all fun t =>
  !(decide ((i%7=0 ∨ i%7=5) ∧ i<t)) || decide (i ≤ parN t)

/-! ### Link 2, step 8: the branch list.

`ppair` of the ladder below `trMax` is NOT one block.  At an offset ≡ 2 (mod 7) it is
three one-column roots and then one block; at ≡ 6 (mod 7) it is one root and one block.
That is where the four-way and two-way folds come from. -/

theorem Gp_eq_r2 (i : Nat) (h : i%7=2) :
    Gp (i+1)=Gp i ∧ Gp (i+2)=Gp i ∧ Gp (i+3)+1=Gp i := by
  obtain ⟨a,rfl⟩ : ∃ a, i=7*a+2 := ⟨i/7,by omega⟩
  obtain ⟨_,_,e2,e3,e4,e5,_⟩ := Gp_r a
  rw [show 7*a+2+1=7*a+3 by omega,show 7*a+2+2=7*a+4 by omega,
    show 7*a+2+3=7*a+5 by omega,e2,e3,e4,e5]
  refine ⟨rfl,rfl,by omega⟩

theorem Gp_eq_r6 (i : Nat) (h : i%7=6) : Gp (i+1)=Gp i := by
  obtain ⟨a,rfl⟩ : ∃ a, i=7*a+6 := ⟨i/7,by omega⟩
  obtain ⟨_,_,_,_,_,_,e6⟩ := Gp_r a
  obtain ⟨f0,_,_,_,_,_,_⟩ := Gp_r (a+1)
  rw [show 7*a+6+1=7*(a+1)+0 by omega,e6,f0]
  push_cast
  omega

theorem gp0_Win_G (i : Nat) (d : Int) (n : Nat) :
    ∀ k, k<(Win i d n).length →
      Trans.Recal.gp0 (Win i d n) ((k:Nat):Int)=Gp (k+i)+d := by
  intro k hk
  rw [length_Win] at hk
  show (if (((k:Nat):Int)<0) then 0 else ((Win i d n).getD k (0,0)).1)=_
  rw [if_neg (by omega),getD_Win i d n k hk]

theorem ppair_Win_r2 (i : Nat) (d : Int) (n : Nat) (hi : i%7=2) (hn : 4 ≤ n) :
    Trans.Recal.ppair (Win i d n)
      = [Win i d 1,Win (i+1) d 1,Win (i+2) d 1,Win (i+3) d (n-3)] := by
  obtain ⟨g1,g2,g3⟩ := Gp_eq_r2 i hi
  have hlen : (Win i d n).length=n := length_Win i d n
  have hres : (Win i d n)=(Win i d n) := rfl
  have key := Rows.Ladder.ppair_roots_then_block
    (M := Win i d n) (par := fun k => parN (k+i)-i) 3
    (by rw [hlen]; omega)
    (fun j hj => Rows.Ladder.fpar_root_of_min (G := fun k => Gp (k+i)+d)
      (gp0_Win_G i d n) (by rw [hlen]; omega)
      (fun i' hi' => by
        rcases (show j=0 ∨ j=1 ∨ j=2 by omega) with rfl|rfl|rfl
        · omega
        · have : i'=0 := by omega
          subst this
          show Gp (1+i)+d ≤ Gp (0+i)+d
          rw [show (1+i)=i+1 by omega,Nat.zero_add,g1]
          omega
        · rcases (show i'=0 ∨ i'=1 by omega) with rfl|rfl
          · show Gp (2+i)+d ≤ Gp (0+i)+d
            rw [show (2+i)=i+2 by omega,Nat.zero_add,g2]
            omega
          · show Gp (2+i)+d ≤ Gp (1+i)+d
            rw [show (2+i)=i+2 by omega,show (1+i)=i+1 by omega,g1,g2]
            omega))
    (Rows.Ladder.fpar_of_gap_at (G := fun k => Gp (k+i)+d)
      (par := fun k => parN (k+i)-i) (gp0_Win_G i d n)
      (fun k _ hk => by
        show parN (k+i)-i<k
        rw [hlen] at hk
        have := parN_lt (k+i) (by omega)
        omega)
      (fun k hk3 hk => by
        show 3 ≤ parN (k+i)-i
        have := parN_ge (i+3) (k+i) (by omega) (by omega)
        omega)
      (fun k hk3 hk => by
        have hge := parN_ge (i+3) (k+i) (by omega) (by omega)
        have hd := Gp_parN_lt (k+i) (by omega)
        show Gp (parN (k+i)-i+i)+d<Gp (k+i)+d
        rw [show parN (k+i)-i+i=parN (k+i) by omega]
        omega)
      (fun k i' hk3 hk h1 h2 => by
        have h1' : parN (k+i)-i<i' := h1
        have hge := parN_ge (i+3) (k+i) (by omega) (by omega)
        have := Gp_parN_keep (k+i) (i'+i) (by omega) (by omega)
        show Gp (k+i)+d ≤ Gp (i'+i)+d
        omega))
    (fun k _ hk => by
      show parN (k+i)-i<k
      rw [hlen] at hk
      have := parN_lt (k+i) (by omega)
      omega)
    (fun k hk3 hk => by
      show 3 ≤ parN (k+i)-i
      have := parN_ge (i+3) (k+i) (by omega) (by omega)
      omega)
    (Rows.Ladder.fpar_root_of_min (G := fun k => Gp (k+i)+d)
      (gp0_Win_G i d n) (by rw [hlen]; omega)
      (fun i' hi' => by
        rcases (show i'=0 ∨ i'=1 ∨ i'=2 by omega) with rfl|rfl|rfl
        · show Gp (3+i)+d ≤ Gp (0+i)+d
          rw [show (3+i)=i+3 by omega,Nat.zero_add]
          omega
        · show Gp (3+i)+d ≤ Gp (1+i)+d
          rw [show (3+i)=i+3 by omega,show (1+i)=i+1 by omega,g1]
          omega
        · show Gp (3+i)+d ≤ Gp (2+i)+d
          rw [show (3+i)=i+3 by omega,show (2+i)=i+2 by omega,g2]
          omega))
  rw [key,hlen]
  rw [show (List.range 3)=[0,1,2] from rfl]
  simp only [List.map_cons,List.map_nil]
  rw [show ((0:Nat):Int)=((0:Nat):Int) from rfl]
  rw [show Trans.Recal.slice (Win i d n) ((0:Nat):Int) (((0:Nat):Int)+1)
      =Win i d 1 from by
    rw [show (((0:Nat):Int)+1)=((1:Nat):Int) from by omega,slice_Win i d n 0 1
      (by omega) (by omega)]
    rfl]
  rw [show Trans.Recal.slice (Win i d n) ((1:Nat):Int) (((1:Nat):Int)+1)
      =Win (i+1) d 1 from by
    rw [show (((1:Nat):Int)+1)=((2:Nat):Int) from by omega,slice_Win i d n 1 2
      (by omega) (by omega)]]
  rw [show Trans.Recal.slice (Win i d n) ((2:Nat):Int) (((2:Nat):Int)+1)
      =Win (i+2) d 1 from by
    rw [show (((2:Nat):Int)+1)=((3:Nat):Int) from by omega,slice_Win i d n 2 3
      (by omega) (by omega)]]
  rw [show Trans.Recal.slice (Win i d n) ((3:Nat):Int) ((n:Nat):Int)
      =Win (i+3) d (n-3) from slice_Win i d n 3 n (by omega) (by omega)]
  rfl

#guard (List.range 5).all fun a => (List.range 6).all fun n =>
  Trans.Recal.ppair (Win (7*a+2) 1 (n+4))
    ==[Win (7*a+2) 1 1,Win (7*a+3) 1 1,Win (7*a+4) 1 1,Win (7*a+5) 1 (n+1)]

theorem ppair_Win_r6 (i : Nat) (d : Int) (n : Nat) (hi : i%7=6) (hn : 2 ≤ n) :
    Trans.Recal.ppair (Win i d n)=[Win i d 1,Win (i+1) d (n-1)] := by
  have g1 := Gp_eq_r6 i hi
  have hlen : (Win i d n).length=n := length_Win i d n
  have key := Rows.Ladder.ppair_roots_then_block
    (M := Win i d n) (par := fun k => parN (k+i)-i) 1
    (by rw [hlen]; omega)
    (fun j hj => by
      have hj0 : j=0 := by omega
      subst hj0
      exact Rows.Ladder.fpar_root_of_min (G := fun k => Gp (k+i)+d)
        (gp0_Win_G i d n) (by rw [hlen]; omega) (fun i' hi' => absurd hi' (by omega)))
    (Rows.Ladder.fpar_of_gap_at (G := fun k => Gp (k+i)+d)
      (par := fun k => parN (k+i)-i) (gp0_Win_G i d n)
      (fun k _ hk => by
        show parN (k+i)-i<k
        rw [hlen] at hk
        have := parN_lt (k+i) (by omega)
        omega)
      (fun k hk1 hk => by
        show 1 ≤ parN (k+i)-i
        have := parN_ge (i+1) (k+i) (by omega) (by omega)
        omega)
      (fun k hk1 hk => by
        have hge := parN_ge (i+1) (k+i) (by omega) (by omega)
        have hd := Gp_parN_lt (k+i) (by omega)
        show Gp (parN (k+i)-i+i)+d<Gp (k+i)+d
        rw [show parN (k+i)-i+i=parN (k+i) by omega]
        omega)
      (fun k i' hk1 hk h1 h2 => by
        have h1' : parN (k+i)-i<i' := h1
        have hge := parN_ge (i+1) (k+i) (by omega) (by omega)
        have := Gp_parN_keep (k+i) (i'+i) (by omega) (by omega)
        show Gp (k+i)+d ≤ Gp (i'+i)+d
        omega))
    (fun k _ hk => by
      show parN (k+i)-i<k
      rw [hlen] at hk
      have := parN_lt (k+i) (by omega)
      omega)
    (fun k hk1 hk => by
      show 1 ≤ parN (k+i)-i
      have := parN_ge (i+1) (k+i) (by omega) (by omega)
      omega)
    (Rows.Ladder.fpar_root_of_min (G := fun k => Gp (k+i)+d)
      (gp0_Win_G i d n) (by rw [hlen]; omega)
      (fun i' hi' => by
        have : i'=0 := by omega
        subst this
        show Gp (1+i)+d ≤ Gp (0+i)+d
        rw [show (1+i)=i+1 by omega,Nat.zero_add,g1]
        omega))
  rw [key,hlen,show (List.range 1)=[0] from rfl]
  simp only [List.map_cons,List.map_nil]
  rw [show Trans.Recal.slice (Win i d n) ((0:Nat):Int) (((0:Nat):Int)+1)
      =Win i d 1 from by
    rw [show (((0:Nat):Int)+1)=((1:Nat):Int) from by omega,
      slice_Win i d n 0 1 (by omega) (by omega)]
    rfl]
  rw [show Trans.Recal.slice (Win i d n) ((1:Nat):Int) ((n:Nat):Int)
      =Win (i+1) d (n-1) from slice_Win i d n 1 n (by omega) (by omega)]
  rfl

#guard (List.range 5).all fun a => (List.range 6).all fun n =>
  Trans.Recal.ppair (Win (7*a+6) 1 (n+2))==[Win (7*a+6) 1 1,Win (7*a+7) 1 (n+1)]

/-! ### Link 2, step 9: two exceptional heads over a window. -/

def A2 (c : Int) (i : Nat) (d : Int) (n : Nat) : Trans.Recal.PS :=
  ((0:Int),(0:Int)) :: Hd (c,1) i d n

theorem length_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) : (A2 c i d n).length=n+2 := by
  unfold A2
  rw [List.length_cons,length_Hd]

theorem lenI_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.lenI (A2 c i d n)=((n:Nat):Int)+2 := by
  unfold Trans.Recal.lenI
  rw [length_A2]
  omega

theorem gp0_A2 (c : Int) (i : Nat) (d : Int) (n k : Nat) (hk : k<n+2) :
    Trans.Recal.gp0 (A2 c i d n) ((k:Nat):Int)
      = if k=0 then 0 else if k=1 then c else Gp (k-2+i)+d := by
  show (if (((k:Nat):Int)<0) then 0 else ((A2 c i d n).getD k (0,0)).1)=_
  rw [if_neg (by omega)]
  cases k with
  | zero => rw [if_pos rfl]; rfl
  | succ j =>
    rw [if_neg (by omega)]
    show ((Hd (c,1) i d n).getD j (0,0)).1=_
    have h := gp0_Hd (c,1) i d n j (by omega)
    rw [show Trans.Recal.gp0 (Hd (c,1) i d n) ((j:Nat):Int)
        = (if (((j:Nat):Int)<0) then 0 else ((Hd (c,1) i d n).getD j (0,0)).1) from rfl,
      if_neg (by omega)] at h
    rw [h,show j+1-2=j-1 from rfl]
    cases j with
    | zero => rw [if_pos rfl,if_pos rfl]
    | succ jj => rw [if_neg (by omega),if_neg (by omega)]

theorem gp1_A2 (c : Int) (i : Nat) (d : Int) (n k : Nat) (hk : k<n+2) :
    Trans.Recal.gp1 (A2 c i d n) ((k:Nat):Int)
      = if k=0 then 0 else if k=1 then 1 else Gq (k-2+i) := by
  show (if (((k:Nat):Int)<0) then 0 else ((A2 c i d n).getD k (0,0)).2)=_
  rw [if_neg (by omega)]
  cases k with
  | zero => rw [if_pos rfl]; rfl
  | succ j =>
    rw [if_neg (by omega)]
    show ((Hd (c,1) i d n).getD j (0,0)).2=_
    have h := gp1_Hd (c,1) i d n j (by omega)
    rw [show Trans.Recal.gp1 (Hd (c,1) i d n) ((j:Nat):Int)
        = (if (((j:Nat):Int)<0) then 0 else ((Hd (c,1) i d n).getD j (0,0)).2) from rfl,
      if_neg (by omega)] at h
    rw [h,show j+1-2=j-1 from rfl]
    cases j with
    | zero => rw [if_pos rfl,if_pos rfl]
    | succ jj => rw [if_neg (by omega),if_neg (by omega)]

def GA (c : Int) (i : Nat) (d : Int) (k : Nat) : Int :=
  if k=0 then 0 else if k=1 then c else Gp (k-2+i)+d

theorem GA_succ (c : Int) (i : Nat) (d : Int) (j : Nat) : GA c i d (j+1)=GH c i d j := by
  unfold GA GH
  cases j with
  | zero => rfl
  | succ jj => rfl

def parA (i k : Nat) : Nat := if k ≤ 1 then 0 else parHd i (k-1)+1

theorem parA_lt (i k : Nat) (hi : 1 ≤ i) (hk : 1 ≤ k) : parA i k<k := by
  unfold parA
  by_cases h1 : k ≤ 1
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    have := parHd_lt i (k-1) hi (by omega)
    omega

theorem GA_drop (c : Int) (i : Nat) (d : Int) (n k : Nat) (hi : 1 ≤ i) (hc : 0<c)
    (hk : 1 ≤ k) (hkn : k<n+2) (hh : ∀ t, i ≤ t → t<i+n → c<Gp t+d) :
    GA c i d (parA i k)<GA c i d k := by
  unfold parA
  by_cases h1 : k ≤ 1
  · rw [if_pos h1]
    have hk1 : k=1 := by omega
    subst hk1
    show GA c i d 0<GA c i d 1
    unfold GA
    rw [if_pos rfl]
    rw [show (if (1:Nat)=0 then (0:Int) else if (1:Nat)=1 then c else Gp (1-2+i)+d)=c
      from rfl]
    exact hc
  · rw [if_neg h1]
    obtain ⟨j,rfl⟩ : ∃ j, k=j+1 := ⟨k-1,by omega⟩
    rw [show j+1-1=j from rfl,GA_succ,GA_succ]
    exact GH_drop c i d n j hi (by omega) (by omega) hh

theorem GA_keep (c : Int) (i : Nat) (d : Int) (k j : Nat) (hk : 1 ≤ k)
    (h1 : parA i k<j) (h2 : j<k) : GA c i d k ≤ GA c i d j := by
  unfold parA at h1
  by_cases hone : k ≤ 1
  · rw [if_pos hone] at h1; omega
  · rw [if_neg hone] at h1
    obtain ⟨k1,rfl⟩ : ∃ k1, k=k1+1 := ⟨k-1,by omega⟩
    obtain ⟨j1,rfl⟩ : ∃ j1, j=j1+1 := ⟨j-1,by omega⟩
    rw [GA_succ,GA_succ]
    rw [show k1+1-1=k1 from rfl] at h1
    exact GH_keep c i d k1 j1 (by omega) (by omega) (by omega)

theorem gp0_A2_GA (c : Int) (i : Nat) (d : Int) (n : Nat) :
    ∀ k, k<(A2 c i d n).length → Trans.Recal.gp0 (A2 c i d n) ((k:Nat):Int)=GA c i d k := by
  intro k hk
  rw [length_A2] at hk
  rw [gp0_A2 c i d n k hk]
  rfl

theorem chain_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) (hi : 1 ≤ i) (hc : 0<c)
    (hh : ∀ t, i ≤ t → t<i+n → c<Gp t+d) :
    ∀ k, 1 ≤ k → k<(A2 c i d n).length →
      Trans.Recal.fpar (A2 c i d n) 0 ((k:Nat):Int) 0=((parA i k : Nat) : Int) :=
  Rows.Ladder.fpar_of_gap
    (G := GA c i d) (par := parA i) (gp0_A2_GA c i d n)
    (fun k hk1 _ => parA_lt i k hi hk1)
    (fun k hk1 hk => by
      rw [length_A2] at hk
      exact GA_drop c i d n k hi hc hk1 hk hh)
    (fun k j hk1 _ h1 h2 => GA_keep c i d k j hk1 h1 h2)

theorem root_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.fpar (A2 c i d n) 0 ((0:Nat):Int) 0=-1 :=
  Rows.Ladder.fpar_zero_of_gap (G := GA c i d) (gp0_A2_GA c i d n)
    (by rw [length_A2]; omega)

theorem isPrincipalP_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) (hi : 1 ≤ i) (hc : 0<c)
    (hh : ∀ t, i ≤ t → t<i+n → c<Gp t+d) :
    Trans.Recal.isPrincipalP (A2 c i d n)=true :=
  Rows.Ladder.isPrincipalP_of_chain (chain_A2 c i d n hi hc hh)
    (fun k hk1 _ => parA_lt i k hi hk1) (root_A2 c i d n)
    (by rw [length_A2]; omega)

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
