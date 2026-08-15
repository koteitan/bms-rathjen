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

/-! ### Link 2, step 10: short windows are all roots. -/

theorem ppair_Win_roots (i : Nat) (e : Int) (n : Nat) (hn : 1 ≤ n)
    (hmin : ∀ a b, a<b → b<n → Gp (b+i) ≤ Gp (a+i)) :
    Trans.Recal.ppair (Win i e n)=(List.range n).map (fun j => Win (i+j) e 1) := by
  have hl : (Win i e n).length=n := length_Win i e n
  have key := Rows.Ladder.ppair_roots_then_block
    (M := Win i e n) (par := fun k => k) (n-1)
    (by rw [hl]; omega)
    (fun j hj => Rows.Ladder.fpar_root_of_min (G := fun k => Gp (k+i)+e)
      (gp0_Win_G i e n) (by rw [hl]; omega)
      (fun i' hi' => by
        have := hmin i' j hi' (by omega)
        show Gp (j+i)+e ≤ Gp (i'+i)+e
        omega))
    (fun k hk _ => absurd hk (by omega))
    (fun k hk _ => absurd hk (by omega))
    (fun k hk _ => absurd hk (by omega))
    (Rows.Ladder.fpar_root_of_min (G := fun k => Gp (k+i)+e)
      (gp0_Win_G i e n) (by rw [hl]; omega)
      (fun i' hi' => by
        have := hmin i' (n-1) hi' (by omega)
        show Gp (n-1+i)+e ≤ Gp (i'+i)+e
        omega))
  rw [key,hl]
  have hs : ∀ j : Nat, j<n →
      Trans.Recal.slice (Win i e n) ((j:Nat):Int) (((j:Nat):Int)+1)=Win (i+j) e 1 := by
    intro j hj
    rw [show (((j:Nat):Int)+1)=(((j+1:Nat)):Int) from by omega,
      slice_Win i e n j (j+1) (by omega) (by omega),show j+1-j=1 by omega]
  obtain ⟨u,rfl⟩ : ∃ u, n=u+1 := ⟨n-1,by omega⟩
  rw [show u+1-1=u from rfl,List.range_succ,List.map_append]
  congr 1
  · exact List.map_congr_left (fun j hj => hs j (by
      have := List.mem_range.mp hj
      omega))
  · simp only [List.map_cons,List.map_nil]
    rw [slice_Win i e (u+1) u (u+1) (by omega) (by omega),show u+1-u=1 by omega]

#guard (List.range 5).all fun a => (List.range 4).all fun n =>
  Trans.Recal.ppair (Win (7*a+2) 1 (n+1))
    ==(List.range (n+1)).map (fun j => Win (7*a+2+j) 1 1)

/-! ### Link 2, step 11: the small indices. -/

theorem gp0_Hd_0 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp0 (Hd h i d n) 0=h.1 := rfl
theorem gp1_Hd_0 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp1 (Hd h i d n) 0=h.2 := rfl

theorem gp0_Hd_1 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp0 (Hd h i d n) 1=Gp i+d := by
  show (if ((1:Int)<0) then 0 else ((Hd h i d n).getD 1 (0,0)).1)=Gp i+d
  rw [if_neg (by omega)]
  show ((Win i d n).getD 0 (0,0)).1=Gp i+d
  rw [getD_Win i d n 0 (by omega),Nat.zero_add]

theorem gp1_Hd_1 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp1 (Hd h i d n) 1=Gq i := by
  show (if ((1:Int)<0) then 0 else ((Hd h i d n).getD 1 (0,0)).2)=Gq i
  rw [if_neg (by omega)]
  show ((Win i d n).getD 0 (0,0)).2=Gq i
  rw [getD_Win i d n 0 (by omega),Nat.zero_add]

theorem gp0_Hd_2 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 2 ≤ n) :
    Trans.Recal.gp0 (Hd h i d n) 2=Gp (1+i)+d := by
  show (if ((2:Int)<0) then 0 else ((Hd h i d n).getD 2 (0,0)).1)=Gp (1+i)+d
  rw [if_neg (by omega)]
  show ((Win i d n).getD 1 (0,0)).1=Gp (1+i)+d
  rw [getD_Win i d n 1 (by omega)]

theorem gp1_Hd_2 (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 2 ≤ n) :
    Trans.Recal.gp1 (Hd h i d n) 2=Gq (1+i) := by
  show (if ((2:Int)<0) then 0 else ((Hd h i d n).getD 2 (0,0)).2)=Gq (1+i)
  rw [if_neg (by omega)]
  show ((Win i d n).getD 1 (0,0)).2=Gq (1+i)
  rw [getD_Win i d n 1 (by omega)]

theorem gp0_A2_0 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp0 (A2 c i d n) 0=0 := rfl
theorem gp1_A2_0 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp1 (A2 c i d n) 0=0 := rfl
theorem gp0_A2_1 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp0 (A2 c i d n) 1=c := rfl
theorem gp1_A2_1 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.gp1 (A2 c i d n) 1=1 := rfl

theorem gp0_A2_2 (c : Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp0 (A2 c i d n) 2=Gp i+d := by
  show (if ((2:Int)<0) then 0 else ((A2 c i d n).getD 2 (0,0)).1)=Gp i+d
  rw [if_neg (by omega)]
  show ((Win i d n).getD 0 (0,0)).1=Gp i+d
  rw [getD_Win i d n 0 (by omega),Nat.zero_add]

theorem gp1_A2_2 (c : Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp1 (A2 c i d n) 2=Gq i := by
  show (if ((2:Int)<0) then 0 else ((A2 c i d n).getD 2 (0,0)).2)=Gq i
  rw [if_neg (by omega)]
  show ((Win i d n).getD 0 (0,0)).2=Gq i
  rw [getD_Win i d n 0 (by omega),Nat.zero_add]

theorem gp0_Win_0 (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp0 (Win i d n) 0=Gp i+d := by
  show (if ((0:Int)<0) then 0 else ((Win i d n).getD 0 (0,0)).1)=Gp i+d
  rw [if_neg (by omega),getD_Win i d n 0 (by omega),Nat.zero_add]

theorem gp1_Win_0 (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.gp1 (Win i d n) 0=Gq i := by
  show (if ((0:Int)<0) then 0 else ((Win i d n).getD 0 (0,0)).2)=Gq i
  rw [if_neg (by omega),getD_Win i d n 0 (by omega),Nat.zero_add]

theorem isZeroP_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) :
    Trans.Recal.isZeroP (Hd h i d n)=false := by
  unfold Trans.Recal.isZeroP
  rw [show ((Hd h i d n).length==1)=false from by rw [length_Hd]; simp; omega]
  rfl

theorem isZeroP_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) :
    Trans.Recal.isZeroP (A2 c i d n)=false := by
  unfold Trans.Recal.isZeroP
  rw [show ((A2 c i d n).length==1)=false from by rw [length_A2]; simp]
  rfl

/-! #### `trMax` はどの形でも 1。 -/

theorem trMax_Hd (h : Int × Int) (i : Nat) (d : Int) (n : Nat) (hn : 2 ≤ n)
    (h1 : h.1<Gp i+d) (h2 : h.2<Gq i)
    (h3 : Gp i<Gp (1+i)) (h4 : ¬(Gq i<Gq (1+i))) :
    Trans.Recal.trMax (Hd h i d n)=1 := by
  have e1 : Trans.Recal.trMax (Hd h i d n)=(((1:Nat)):Int) →
      Trans.Recal.trMax (Hd h i d n)=1 := fun hx => by rw [hx]; rfl
  apply e1
  refine Rows.Ladder.trMax_eq _ 1 (by rw [length_Hd]; omega) ?_ ?_
  · intro j hj
    have hj0 : j=0 := by omega
    subst hj0
    refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega)
      (by rw [lenI_Hd]; omega) ?_
    have hx : Trans.Recal.fpar (Hd h i d n) 1 1 0=0 :=
      Rows.Ladder.fpar1_one _ (by rw [length_Hd]; omega)
        (by rw [gp0_Hd_0,gp0_Hd_1 h i d n (by omega)]; exact h1)
        (by rw [gp1_Hd_0,gp1_Hd_1 h i d n (by omega)]; exact h2)
    simpa using hx
  · refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
    have hx : Trans.Recal.fpar (Hd h i d n) 1 2 1=-1 :=
      Rows.Ladder.fpar1_two_lb _ (by rw [length_Hd]; omega)
        (by rw [gp0_Hd_1 h i d n (by omega),gp0_Hd_2 h i d n (by omega)]; omega)
        (by rw [gp1_Hd_1 h i d n (by omega),gp1_Hd_2 h i d n (by omega)]; exact h4)
    simpa using hx

theorem trMax_A2 (c : Int) (i : Nat) (d : Int) (n : Nat) (hn : 1 ≤ n) (hc : 0<c)
    (h2 : c<Gp i+d) (h4 : ¬((1:Int)<Gq i)) :
    Trans.Recal.trMax (A2 c i d n)=1 := by
  have e1 : Trans.Recal.trMax (A2 c i d n)=(((1:Nat)):Int) →
      Trans.Recal.trMax (A2 c i d n)=1 := fun hx => by rw [hx]; rfl
  apply e1
  refine Rows.Ladder.trMax_eq _ 1 (by rw [length_A2]; omega) ?_ ?_
  · intro j hj
    have hj0 : j=0 := by omega
    subst hj0
    refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega)
      (by rw [lenI_A2]; omega) ?_
    have hx : Trans.Recal.fpar (A2 c i d n) 1 1 0=0 :=
      Rows.Ladder.fpar1_one _ (by rw [length_A2]; omega)
        (by rw [gp0_A2_0,gp0_A2_1]; exact hc)
        (by rw [gp1_A2_0,gp1_A2_1]; omega)
    simpa using hx
  · refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
    have hx : Trans.Recal.fpar (A2 c i d n) 1 2 1=-1 :=
      Rows.Ladder.fpar1_two_lb _ (by rw [length_A2]; omega)
        (by rw [gp0_A2_1,gp0_A2_2 c i d n (by omega)]; exact h2)
        (by rw [gp1_A2_1,gp1_A2_2 c i d n (by omega)]; exact h4)
    simpa using hx

/-! ### Link 2, step 12: the six shapes.

    L m      = Win 0 0 (m+7)                     the ladder itself
    V m      = Win 5 0 (m+2)                     what is left after the first fold
    A5 d n   = (0,0) :: Win 5 d n
    Zr d t   = (2,0) :: Win 8 d t
    Cw e t   = (0,0) :: Win 1 e t                the cycle's fixed point shape
    Q e s    = (1,1) :: Win 6 e s
    A6 d s   = (0,0) :: (2,1) :: Win 6 d s
-/

def V (m : Nat) : Trans.Recal.PS := Win 5 0 (m+2)
def A5 (d : Int) (n : Nat) : Trans.Recal.PS := Hd ((0:Int),(0:Int)) 5 d n
def Zr (d : Int) (t : Nat) : Trans.Recal.PS := Hd ((2:Int),(0:Int)) 8 d t
def Cw (e : Int) (t : Nat) : Trans.Recal.PS := Hd ((0:Int),(0:Int)) 1 e t
def Q (e : Int) (s : Nat) : Trans.Recal.PS := Hd ((1:Int),(1:Int)) 6 e s
def A6 (d : Int) (s : Nat) : Trans.Recal.PS := A2 2 6 d s

theorem Gp_0 : Gp 0=0 := by decide
theorem Gp_1 : Gp 1=1 := by decide
theorem Gp_2 : Gp 2=2 := by decide
theorem Gp_5 : Gp 5=1 := by decide
theorem Gp_6 : Gp 6=2 := by decide
theorem Gp_7 : Gp 7=2 := by decide
theorem Gp_8 : Gp 8=3 := by decide
theorem Gq_0 : Gq 0=0 := by decide
theorem Gq_1 : Gq 1=1 := by decide
theorem Gq_2 : Gq 2=1 := by decide
theorem Gq_3 : Gq 3=1 := by decide
theorem Gq_4 : Gq 4=0 := by decide
theorem Gq_5 : Gq 5=1 := by decide
theorem Gq_6 : Gq 6=1 := by decide
theorem Gq_7 : Gq 7=0 := by decide

theorem head_one (t : Nat) (ht : 1 ≤ t) : (1:Int) ≤ Gp t := by
  have := Gp_min_le 1 t (by omega) ht
  rw [Gp_1] at this
  omega

theorem head_five (t : Nat) (ht : 5 ≤ t) : (1:Int) ≤ Gp t := by
  have := Gp_min_le 5 t (by omega) ht
  rw [Gp_5] at this
  omega

theorem head_six (t : Nat) (ht : 6 ≤ t) : (2:Int) ≤ Gp t := by
  have := Gp_min_le 6 t (by omega) ht
  rw [Gp_6] at this
  omega

theorem head_eight (t : Nat) (ht : 8 ≤ t) : (3:Int) ≤ Gp t := by
  have := Gp_min_le 8 t (by omega) ht
  rw [Gp_8] at this
  omega

theorem prin_Cw (e : Int) (t : Nat) (he : 0 ≤ e) (ht : 1 ≤ t) :
    Trans.Recal.isPrincipalP (Cw e t)=true :=
  isPrincipalP_Hd _ 1 e t (by omega) ht
    (fun u hu _ => by
      have := head_one u hu
      show (0:Int)<Gp u+e
      omega)

theorem prin_A5 (d : Int) (n : Nat) (hd : 0 ≤ d) (hn : 1 ≤ n) :
    Trans.Recal.isPrincipalP (A5 d n)=true :=
  isPrincipalP_Hd _ 5 d n (by omega) hn
    (fun u hu _ => by
      have := head_five u hu
      show (0:Int)<Gp u+d
      omega)

theorem prin_Zr (d : Int) (t : Nat) (hd : 0 ≤ d) (ht : 1 ≤ t) :
    Trans.Recal.isPrincipalP (Zr d t)=true :=
  isPrincipalP_Hd _ 8 d t (by omega) ht
    (fun u hu _ => by
      have := head_eight u hu
      show (2:Int)<Gp u+d
      omega)

theorem prin_Q (e : Int) (s : Nat) (he : 0 ≤ e) (hs : 1 ≤ s) :
    Trans.Recal.isPrincipalP (Q e s)=true :=
  isPrincipalP_Hd _ 6 e s (by omega) hs
    (fun u hu _ => by
      have := head_six u hu
      show (1:Int)<Gp u+e
      omega)

theorem prin_A6 (d : Int) (s : Nat) (hd : 1 ≤ d) :
    Trans.Recal.isPrincipalP (A6 d s)=true :=
  isPrincipalP_A2 2 6 d s (by omega) (by omega)
    (fun u hu _ => by
      have := head_six u hu
      show (2:Int)<Gp u+d
      omega)

theorem prin_L (m : Nat) : Trans.Recal.isPrincipalP (L m)=true := by
  rw [L_eq_Win]
  exact isPrincipalP_Win 0 0 (m+6) (by omega) (Or.inl rfl)

theorem prin_V (m : Nat) : Trans.Recal.isPrincipalP (V m)=true := by
  unfold V
  rw [show m+2=(m+1)+1 from rfl]
  exact isPrincipalP_Win 5 0 (m+1) (by omega) (Or.inr rfl)

#guard (List.range 8).all fun m => Trans.Recal.isPrincipalP (L m)
#guard (List.range 8).all fun t => Trans.Recal.isPrincipalP (Cw 1 (t+1))
#guard (List.range 8).all fun t => Trans.Recal.isPrincipalP (Zr 1 (t+1))
#guard (List.range 8).all fun t => Trans.Recal.isPrincipalP (Q 1 (t+1))
#guard (List.range 8).all fun t => Trans.Recal.isPrincipalP (A6 2 t)

/-! ### Link 2, step 13: the four-branch fold. -/

theorem drop_Hd_two (h : Int × Int) (i : Nat) (d : Int) (n : Nat) :
    (Hd h i d n).drop 2=Win (i+1) d (n-1) := by
  show (Win i d n).drop 1=_
  exact Win_drop1 i d n

theorem drop_A2_two (c : Int) (i : Nat) (d : Int) (n : Nat) :
    (A2 c i d n).drop 2=Win i d n := rfl

theorem brF_Cw (e : Int) (t : Nat) (he : 0 ≤ e) (ht : 5 ≤ t) :
    Trans.Recal.brF (Cw e t)=[Win 2 e 1,Win 3 e 1,Win 4 e 1,Win 5 e (t-4)] := by
  unfold Trans.Recal.brF Cw
  rw [trMax_Hd ((0:Int),(0:Int)) 1 e t (by omega)
      (by rw [Gp_1]; omega) (by rw [Gq_1]; omega)
      (by rw [show (1+1)=2 from rfl,Gp_1,Gp_2]; omega)
      (by rw [show (1+1)=2 from rfl,Gq_1,Gq_2]; omega),
    show ((1:Int)+1).toNat=2 from by rfl,drop_Hd_two,
    show (1+1)=2 from rfl,ppair_Win_r2 2 e (t-1) (by omega) (by omega),
    show 2+1=3 from rfl,show 2+2=4 from rfl,show 2+3=5 from rfl,
    show t-1-3=t-4 by omega]

theorem joint_Cw (e : Int) (t : Nat) (he : 0 ≤ e) (k : Nat) (hk : 1 ≤ k) (hkt : k<t+1) :
    Trans.Recal.fpar (Cw e t) 0 ((k:Nat):Int) 0=((parHd 1 k : Nat) : Int) := by
  unfold Cw
  exact chain_Hd _ 1 e t (by omega)
    (fun u hu _ => by
      have := head_one u hu
      show (0:Int)<Gp u+e
      omega) k hk (by rw [length_Hd]; omega)

theorem parHd_1_2 : parHd 1 2=1 := by decide
theorem parHd_1_3 : parHd 1 3=1 := by decide
theorem parHd_1_4 : parHd 1 4=1 := by decide
theorem parHd_1_5 : parHd 1 5=0 := by decide

theorem trMax_Cw (e : Int) (t : Nat) (he : 0 ≤ e) (ht : 2 ≤ t) :
    Trans.Recal.trMax (Cw e t)=1 :=
  trMax_Hd ((0:Int),(0:Int)) 1 e t ht
    (by rw [Gp_1]; omega) (by rw [Gq_1]; omega)
    (by rw [show (1+1)=2 from rfl,Gp_1,Gp_2]; omega)
    (by rw [show (1+1)=2 from rfl,Gq_1,Gq_2]; omega)

theorem joints_Cw (e : Int) (t : Nat) (he : 0 ≤ e) (ht : 5 ≤ t) :
    Trans.Recal.joints (Cw e t)=[1,1,1,0] := by
  rw [Rows.Ladder.joints_four _ _ _ _ _ (brF_Cw e t he ht),
    trMax_Cw e t he (by omega)]
  simp only [length_Win]
  have e2 : Trans.Recal.fpar (Cw e t) 0 2 0=1 := by
    have := joint_Cw e t he 2 (by omega) (by omega)
    rw [parHd_1_2] at this
    simpa using this
  have e3 : Trans.Recal.fpar (Cw e t) 0 3 0=1 := by
    have := joint_Cw e t he 3 (by omega) (by omega)
    rw [parHd_1_3] at this
    simpa using this
  have e4 : Trans.Recal.fpar (Cw e t) 0 4 0=1 := by
    have := joint_Cw e t he 4 (by omega) (by omega)
    rw [parHd_1_4] at this
    simpa using this
  have e5 : Trans.Recal.fpar (Cw e t) 0 5 0=0 := by
    have := joint_Cw e t he 5 (by omega) (by omega)
    rw [parHd_1_5] at this
    simpa using this
  rw [show ((1:Int)+1+0)=2 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)))=3 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)+((1:Nat):Int)))=4 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)+((1:Nat):Int)+((1:Nat):Int)))=5 from by omega,
    e2,e3,e4,e5]

#guard (List.range 8).all fun t => Trans.Recal.joints (Cw 1 (t+5))==[1,1,1,0]
#guard (List.range 8).all fun t =>
  Trans.Recal.brF (Cw 1 (t+5))==[Win 2 1 1,Win 3 1 1,Win 4 1 1,Win 5 1 (t+1)]

theorem gp1_Hd_at (h : Int × Int) (i : Nat) (d : Int) (n k : Nat) (hk : 1 ≤ k)
    (hkn : k<n+1) : Trans.Recal.gp1 (Hd h i d n) ((k:Nat):Int)=Gq (k-1+i) := by
  rw [gp1_Hd h i d n k hkn,if_neg (by omega)]

theorem gp0_Hd_at (h : Int × Int) (i : Nat) (d : Int) (n k : Nat) (hk : 1 ≤ k)
    (hkn : k<n+1) : Trans.Recal.gp0 (Hd h i d n) ((k:Nat):Int)=Gp (k-1+i)+d := by
  rw [gp0_Hd h i d n k hkn,if_neg (by omega)]

theorem firstNodes_Cw (e : Int) (t : Nat) (he : 0 ≤ e) (ht : 5 ≤ t) :
    Trans.Recal.firstNodes (Cw e t)=[2,3,4,5,((t+1:Nat):Int)] := by
  rw [Rows.Ladder.firstNodes_four _ _ _ _ _ (brF_Cw e t he ht),
    trMax_Cw e t he (by omega)]
  simp only [length_Win]
  rw [show ((1:Int)+1+0)=2 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)))=3 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)+((1:Nat):Int)))=4 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)+((1:Nat):Int)+((1:Nat):Int)))=5 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)+((1:Nat):Int)+((1:Nat):Int)+(((t-4:Nat)):Int)))
      =((t+1:Nat):Int) from by omega]

theorem nJ_Cw_two (e : Int) (t : Nat) (he : 0 ≤ e) (ht : 2 ≤ t) :
    Trans.Recal.fpar (Cw e t) 1 2 0=0 := by
  refine Rows.Ladder.fpar1_via_one _ 2 (by omega)
    (by unfold Cw; rw [lenI_Hd]; omega) (by unfold Cw; rw [length_Hd]; omega) ?_ ?_ ?_ ?_
  · have := joint_Cw e t he 2 (by omega) (by omega)
    rw [parHd_1_2] at this
    simpa using this
  · unfold Cw
    rw [gp0_Hd_0,gp0_Hd_1 _ 1 e t (by omega),Gp_1]
    show (0:Int)<1+e
    omega
  · unfold Cw
    rw [show (1:Int)=((1:Nat):Int) from rfl,show (2:Int)=((2:Nat):Int) from rfl,
      gp1_Hd_at _ 1 e t 1 (by omega) (by omega),gp1_Hd_at _ 1 e t 2 (by omega) (by omega),
      show 1-1+1=1 from rfl,show 2-1+1=2 from rfl,Gq_1,Gq_2]
    omega
  · unfold Cw
    rw [gp1_Hd_0,show (2:Int)=((2:Nat):Int) from rfl,
      gp1_Hd_at _ 1 e t 2 (by omega) (by omega),show 2-1+1=2 from rfl,Gq_2]
    omega

theorem nJ_Cw_three (e : Int) (t : Nat) (he : 0 ≤ e) (ht : 3 ≤ t) :
    Trans.Recal.fpar (Cw e t) 1 3 0=0 := by
  refine Rows.Ladder.fpar1_via_one _ 3 (by omega)
    (by unfold Cw; rw [lenI_Hd]; omega) (by unfold Cw; rw [length_Hd]; omega) ?_ ?_ ?_ ?_
  · have := joint_Cw e t he 3 (by omega) (by omega)
    rw [parHd_1_3] at this
    simpa using this
  · unfold Cw
    rw [gp0_Hd_0,gp0_Hd_1 _ 1 e t (by omega),Gp_1]
    show (0:Int)<1+e
    omega
  · unfold Cw
    rw [show (1:Int)=((1:Nat):Int) from rfl,show (3:Int)=((3:Nat):Int) from rfl,
      gp1_Hd_at _ 1 e t 1 (by omega) (by omega),gp1_Hd_at _ 1 e t 3 (by omega) (by omega),
      show 1-1+1=1 from rfl,show 3-1+1=3 from rfl,Gq_1,Gq_3]
    omega
  · unfold Cw
    rw [gp1_Hd_0,show (3:Int)=((3:Nat):Int) from rfl,
      gp1_Hd_at _ 1 e t 3 (by omega) (by omega),show 3-1+1=3 from rfl,Gq_3]
    omega

theorem nJ_Cw_five (e : Int) (t : Nat) (he : 0 ≤ e) (ht : 5 ≤ t) :
    Trans.Recal.fpar (Cw e t) 1 5 0=0 := by
  refine Rows.Ladder.fpar1_at_zero _ 5 (by omega)
    (by unfold Cw; rw [lenI_Hd]; omega) (by unfold Cw; rw [length_Hd]; omega) ?_ ?_
  · have := joint_Cw e t he 5 (by omega) (by omega)
    rw [parHd_1_5] at this
    simpa using this
  · unfold Cw
    rw [gp1_Hd_0,show (5:Int)=((5:Nat):Int) from rfl,
      gp1_Hd_at _ 1 e t 5 (by omega) (by omega),show 5-1+1=5 from rfl,Gq_5]
    omega

/-- 4 枝の畳み込み。3 本は 1 列で終わり、4 本目が輪を回す。 -/
theorem fold_Cw (e : Int) (t f : Nat) (he : 0 ≤ e) (ht : 5 ≤ t) :
    Trans.Recal.red (f+1) (Cw e t)
      = Trans.Recal.jjSeq 0 1
        ++ Trans.Recal.incrFirst (Trans.Recal.red f [((2:Int),(1:Int))]) 1
        ++ Trans.Recal.incrFirst (Trans.Recal.red f [((2:Int),(1:Int))]) 1
        ++ Trans.Recal.incrFirst (Trans.Recal.red f [((2:Int),(0:Int))]) 2
        ++ Trans.Recal.incrFirst (Trans.Recal.red f (Q e (t-5))) 0 := by
  rw [Rows.Ladder.red_fold_open (Cw e t) f 1
    (by unfold Cw; exact isZeroP_Hd _ 1 e t (by omega))
    (prin_Cw e t he (by omega))
    (by unfold Cw; exact gp0_Hd_0 _ 1 e t) (by unfold Cw; exact gp1_Hd_0 _ 1 e t)
    (trMax_Cw e t he (by omega))
    (by unfold Cw; rw [lenI_Hd]; exact beq_eq_false_iff_ne.mpr (by omega))]
  rw [brF_Cw e t he ht,firstNodes_Cw e t he ht,joints_Cw e t he ht]
  simp only [List.length_cons,List.length_nil,show (List.range 4)=[0,1,2,3] from rfl,
    List.foldl_cons,List.foldl_nil,List.getD_cons_zero,List.getD_cons_succ]
  rw [gp1_Win_0 2 e 1 (by omega),gp1_Win_0 3 e 1 (by omega),
    gp1_Win_0 4 e 1 (by omega),gp1_Win_0 5 e (t-4) (by omega),
    Gq_2,Gq_3,Gq_4,Gq_5,
    show ((1:Int)==0)=false from rfl,show ((0:Int)==0)=true from rfl]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [nJ_Cw_two e t he (by omega),nJ_Cw_three e t he (by omega),nJ_Cw_five e t he ht]
  rw [show ((1:Int)+1,(0:Int)+1)=((2:Int),(1:Int)) from by congr 1 <;> omega,
    show ((1:Int)+1,(-1:Int)+1)=((2:Int),(0:Int)) from by congr 1 <;> omega,
    show ((0:Int)+1,(0:Int)+1)=((1:Int),(1:Int)) from by congr 1 <;> omega,
    show (1:Int)-0=1 from by omega,show (1:Int)-(-1)=2 from by omega,
    show (0:Int)-0=0 from by omega]
  rw [show Trans.Recal.derp (Win 2 e 1)=[] from by
      show (Win 2 e 1).drop 1=[]
      rw [Win_drop1]
      rfl,
    show Trans.Recal.derp (Win 3 e 1)=[] from by
      show (Win 3 e 1).drop 1=[]
      rw [Win_drop1]
      rfl,
    show Trans.Recal.derp (Win 4 e 1)=[] from by
      show (Win 4 e 1).drop 1=[]
      rw [Win_drop1]
      rfl,
    show ((1:Int),(1:Int)) :: Trans.Recal.derp (Win 5 e (t-4))=Q e (t-5) from by
      show ((1:Int),(1:Int)) :: (Win 5 e (t-4)).drop 1=_
      rw [Win_drop1,show t-4-1=t-5 by omega]
      rfl]

#guard (List.range 6).all fun t =>
  Trans.Recal.brF (Cw 1 (t+5))==[Win 2 1 1,Win 3 1 1,Win 4 1 1,Win 5 1 (t+1)]

/-! ### Link 2, step 14: the other three steps of the cycle. -/

theorem incrFirst_Hd (a b : Int) (i : Nat) (d c : Int) (n : Nat) :
    Trans.Recal.incrFirst (Hd (a,b) i d n) c=Hd (a+c,b) i (d+c) n := by
  unfold Trans.Recal.incrFirst Hd
  rw [List.map_cons]
  congr 1
  show Trans.Recal.incrFirst (Win i d n) c=_
  rw [incrFirst_Win]

theorem trMax_A6 (d : Int) (s : Nat) (hd : 1 ≤ d) (hs : 1 ≤ s) :
    Trans.Recal.trMax (A6 d s)=1 :=
  trMax_A2 2 6 d s hs (by omega) (by rw [Gp_6]; omega) (by rw [Gq_6]; omega)

theorem brF_A6 (d : Int) (s : Nat) (hd : 1 ≤ d) (hs : 2 ≤ s) :
    Trans.Recal.brF (A6 d s)=[Win 6 d 1,Win 7 d (s-1)] := by
  unfold Trans.Recal.brF A6
  rw [trMax_A2 2 6 d s (by omega) (by omega) (by rw [Gp_6]; omega)
      (by rw [Gq_6]; omega),
    show ((1:Int)+1).toNat=2 from by rfl,drop_A2_two,
    ppair_Win_r6 6 d s (by omega) hs]

theorem joint_A6 (d : Int) (s : Nat) (hd : 1 ≤ d) (k : Nat) (hk : 1 ≤ k) (hks : k<s+2) :
    Trans.Recal.fpar (A6 d s) 0 ((k:Nat):Int) 0=((parA 6 k : Nat) : Int) := by
  unfold A6
  exact chain_A2 2 6 d s (by omega) (by omega)
    (fun u hu _ => by
      have := head_six u hu
      show (2:Int)<Gp u+d
      omega) k hk (by rw [length_A2]; omega)

theorem parA_6_2 : parA 6 2=1 := by decide
theorem parA_6_3 : parA 6 3=1 := by decide

theorem joints_A6 (d : Int) (s : Nat) (hd : 1 ≤ d) (hs : 2 ≤ s) :
    Trans.Recal.joints (A6 d s)=[1,1] := by
  rw [Rows.Ladder.joints_two _ _ _ (brF_A6 d s hd hs),trMax_A6 d s hd (by omega)]
  simp only [length_Win]
  have e2 : Trans.Recal.fpar (A6 d s) 0 2 0=1 := by
    have := joint_A6 d s hd 2 (by omega) (by omega)
    rw [parA_6_2] at this
    simpa using this
  have e3 : Trans.Recal.fpar (A6 d s) 0 3 0=1 := by
    have := joint_A6 d s hd 3 (by omega) (by omega)
    rw [parA_6_3] at this
    simpa using this
  rw [show ((1:Int)+1+0)=2 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)))=3 from by omega,e2,e3]

theorem firstNodes_A6 (d : Int) (s : Nat) (hd : 1 ≤ d) (hs : 2 ≤ s) :
    Trans.Recal.firstNodes (A6 d s)=[2,3,((s+2:Nat):Int)] := by
  rw [Rows.Ladder.firstNodes_two _ _ _ (brF_A6 d s hd hs),trMax_A6 d s hd (by omega)]
  simp only [length_Win]
  rw [show ((1:Int)+1+0)=2 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)))=3 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)+(((s-1:Nat)):Int)))=((s+2:Nat):Int) from by omega]

theorem nJ_A6_two (d : Int) (s : Nat) (hd : 1 ≤ d) (hs : 1 ≤ s) :
    Trans.Recal.fpar (A6 d s) 1 2 0=0 := by
  refine Rows.Ladder.fpar1_via_one _ 2 (by omega)
    (by unfold A6; rw [lenI_A2]; omega) (by unfold A6; rw [length_A2]; omega) ?_ ?_ ?_ ?_
  · have := joint_A6 d s hd 2 (by omega) (by omega)
    rw [parA_6_2] at this
    simpa using this
  · unfold A6
    rw [gp0_A2_0,gp0_A2_1]
    omega
  · unfold A6
    rw [gp1_A2_1,gp1_A2_2 2 6 d s (by omega),Gq_6]
    omega
  · unfold A6
    rw [gp1_A2_0,gp1_A2_2 2 6 d s (by omega),Gq_6]
    omega

/-- 2 枝の畳み込み。 -/
theorem fold_A6 (d : Int) (s f : Nat) (hd : 1 ≤ d) (hs : 2 ≤ s) :
    Trans.Recal.red (f+1) (A6 d s)
      = Trans.Recal.jjSeq 0 1
        ++ Trans.Recal.incrFirst (Trans.Recal.red f [((2:Int),(1:Int))]) 1
        ++ Trans.Recal.incrFirst (Trans.Recal.red f (Zr d (s-2))) 2 := by
  rw [Rows.Ladder.red_fold_open (A6 d s) f 1
    (by unfold A6; exact isZeroP_A2 2 6 d s)
    (prin_A6 d s hd)
    (by unfold A6; exact gp0_A2_0 2 6 d s) (by unfold A6; exact gp1_A2_0 2 6 d s)
    (trMax_A6 d s hd (by omega))
    (by unfold A6; rw [lenI_A2]; exact beq_eq_false_iff_ne.mpr (by omega))]
  rw [brF_A6 d s hd hs,firstNodes_A6 d s hd hs,joints_A6 d s hd hs]
  simp only [List.length_cons,List.length_nil,show (List.range 2)=[0,1] from rfl,
    List.foldl_cons,List.foldl_nil,List.getD_cons_zero,List.getD_cons_succ]
  rw [gp1_Win_0 6 d 1 (by omega),gp1_Win_0 7 d (s-1) (by omega),Gq_6,Gq_7,
    show ((1:Int)==0)=false from rfl,show ((0:Int)==0)=true from rfl]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [nJ_A6_two d s hd (by omega)]
  rw [show ((1:Int)+1,(0:Int)+1)=((2:Int),(1:Int)) from by congr 1 <;> omega,
    show ((1:Int)+1,(-1:Int)+1)=((2:Int),(0:Int)) from by congr 1 <;> omega,
    show (1:Int)-0=1 from by omega,show (1:Int)-(-1)=2 from by omega]
  rw [show Trans.Recal.derp (Win 6 d 1)=[] from by
      show (Win 6 d 1).drop 1=[]
      rw [Win_drop1]
      rfl,
    show ((2:Int),(0:Int)) :: Trans.Recal.derp (Win 7 d (s-1))=Zr d (s-2) from by
      show ((2:Int),(0:Int)) :: (Win 7 d (s-1)).drop 1=_
      rw [Win_drop1,show s-1-1=s-2 by omega]
      rfl]

/-- `Q` の段。`A6` の答えから頭を落とす。 -/
theorem step_Q (e : Int) (s f : Nat) (he : 0 ≤ e) (hs : 1 ≤ s)
    (h : Trans.Recal.red f (A6 (e+1) s)=((0:Int),(0:Int)) :: Win 5 0 (s+1)) :
    Trans.Recal.red (f+1) (Q e s)=Win 5 0 (s+1) := by
  refine Rows.Ladder.red_head_one (Q e s) f (Win 5 0 (s+1))
    (by unfold Q; exact isZeroP_Hd _ 6 e s hs)
    (prin_Q e s he hs) (by unfold Q; rw [gp0_Hd_0]; rfl)
    (by unfold Q; rw [gp1_Hd_0]) ?_
    (by rw [length_Win]; omega)
    (by rw [show s+1=s+1 from rfl]; exact isPrincipalP_Win 5 0 s (by omega) (Or.inr rfl))
    (by rw [gp0_Win_0 5 0 (s+1) (by omega),gp1_Win_0 5 0 (s+1) (by omega),Gp_5,Gq_5]
        omega)
  unfold Q
  rw [incrFirst_Hd 1 1 6 e 1 s]
  exact h

/-- `Zr` の段。頭を 0 に正規化して降りるだけ。 -/
theorem step_Zr (d : Int) (t f : Nat) (hd : 0 ≤ d) (ht : 1 ≤ t) :
    Trans.Recal.red (f+1) (Zr d t)=Trans.Recal.red f (Cw d t) := by
  rw [Rows.Ladder.red_shift (Zr d t) f
    (by unfold Zr; exact isZeroP_Hd _ 8 d t ht)
    (prin_Zr d t hd ht) (by unfold Zr; rw [gp0_Hd_0]; rfl)
    (by unfold Zr; rw [gp1_Hd_0])]
  congr 1
  show Trans.Recal.incrFirst (Hd ((2:Int),(0:Int)) 8 d t) (-(2:Int))=Cw d t
  rw [incrFirst_Hd 2 0 8 d (-2) t]
  show Hd ((2:Int)+(-2),(0:Int)) 8 (d+(-2)) t=Hd ((0:Int),(0:Int)) 1 d t
  unfold Hd
  rw [show ((2:Int)+(-2))=(0:Int) from by omega,
    show Win 8 (d+(-2)) t=Win 1 d t from by
      rw [show (8:Nat)=1+7 from rfl,Win_add_seven]
      congr 1
      omega]

/-! ### Link 2, step 15: the small branches and the glue. -/

theorem red_X (f : Nat) : Trans.Recal.red (f+2) [((2:Int),(1:Int))]=[((1:Int),(1:Int))] :=
  G1.red_X1 f

theorem red_Z (f : Nat) : Trans.Recal.red (f+1) [((2:Int),(0:Int))]=[((0:Int),(0:Int))] :=
  G9.red_single_zero f

theorem Win005 : Win 0 0 5
    =([((0:Int),(0:Int)),((1:Int),(1:Int)),((2:Int),(1:Int)),((2:Int),(1:Int)),
      ((2:Int),(0:Int))] : Trans.Recal.PS) := by decide

theorem glue_Cw (t : Nat) (ht : 4 ≤ t) :
    (([((0:Int),(0:Int)),((1:Int),(1:Int))] : Trans.Recal.PS)
      ++[((2:Int),(1:Int))]++[((2:Int),(1:Int))]++[((2:Int),(0:Int))])
      ++Win 5 0 (t-4)=Win 0 0 (t+1) := by
  rw [show (([((0:Int),(0:Int)),((1:Int),(1:Int))] : Trans.Recal.PS)
      ++[((2:Int),(1:Int))]++[((2:Int),(1:Int))]++[((2:Int),(0:Int))])
      =Win 0 0 5 from by rw [Win005]; rfl]
  rw [show (5:Nat)=0+5 from rfl,Win_append 0 0 5 (t-4)]
  congr 1
  omega

theorem glue_A6 (s : Nat) (hs : 1 ≤ s) :
    (([((0:Int),(0:Int)),((1:Int),(1:Int))] : Trans.Recal.PS)++[((2:Int),(1:Int))])
      ++Win 0 2 (s-1)=((0:Int),(0:Int)) :: Win 5 0 (s+1) := by
  rw [show Win 0 2 (s-1)=Win 7 0 (s-1) from by
      rw [show (7:Nat)=0+7 from rfl,Win_add_seven]
      congr 1
      try omega]
  rw [show ((0:Int),(0:Int)) :: Win 5 0 (s+1)
      =((0:Int),(0:Int)) :: (Gp 5+0,Gq 5) :: Win 6 0 s from by rw [Win_cons]]
  rw [show Win 6 0 s=(Gp 6+0,Gq 6) :: Win 7 0 (s-1) from by
      obtain ⟨u,rfl⟩ : ∃ u, s=u+1 := ⟨s-1,by omega⟩
      rw [Win_cons]
      congr 2
      try omega]
  rw [Gp_5,Gq_5,Gp_6,Gq_6]
  show _=([((0:Int),(0:Int)),((1:Int)+0,(1:Int)),((2:Int)+0,(1:Int))]
    : Trans.Recal.PS)++Win 7 0 (s-1)
  rw [show ((1:Int)+0)=(1:Int) from by omega,show ((2:Int)+0)=(2:Int) from by omega]
  rfl

/-! #### 底 -/

theorem trMax_Cw_one (e : Int) (he : 0 ≤ e) : Trans.Recal.trMax (Cw e 1)=1 := by
  have e1 : Trans.Recal.trMax (Cw e 1)=(((1:Nat)):Int) → Trans.Recal.trMax (Cw e 1)=1 :=
    fun hx => by rw [hx]; rfl
  apply e1
  refine Rows.Ladder.trMax_eq _ 1 (by unfold Cw; rw [length_Hd]; omega) ?_ ?_
  · intro j hj
    have hj0 : j=0 := by omega
    subst hj0
    refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega)
      (by unfold Cw; rw [lenI_Hd]; omega) ?_
    have hx : Trans.Recal.fpar (Cw e 1) 1 1 0=0 :=
      Rows.Ladder.fpar1_one _ (by unfold Cw; rw [length_Hd]; omega)
        (by unfold Cw; rw [gp0_Hd_0,gp0_Hd_1 _ 1 e 1 (by omega),Gp_1]
            show (0:Int)<1+e
            omega)
        (by unfold Cw; rw [gp1_Hd_0,gp1_Hd_1 _ 1 e 1 (by omega),Gq_1]
            omega)
    simpa using hx
  · refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
    have hx : Trans.Recal.fpar (Cw e 1) 1 2 1=-1 :=
      Rows.Ladder.fpar_out _ 1 2 1 (by unfold Cw; rw [lenI_Hd]; omega)
    simpa using hx

theorem base_Cw_zero (e : Int) (f : Nat) : Trans.Recal.red (f+1) (Cw e 0)=Win 0 0 1 := by
  rw [Rows.Ladder.red_zeroP _ f (by rfl)]
  decide

theorem base_Cw_one (e : Int) (f : Nat) (he : 0 ≤ e) :
    Trans.Recal.red (f+1) (Cw e 1)=Win 0 0 2 := by
  have h := Rows.Ladder.red_jj (Cw e 1) f
    (by unfold Cw; exact isZeroP_Hd _ 1 e 1 (by omega))
    (prin_Cw e 1 he (by omega))
    (by unfold Cw; exact gp0_Hd_0 _ 1 e 1) (by unfold Cw; exact gp1_Hd_0 _ 1 e 1)
    (by rw [trMax_Cw_one e he]; unfold Cw; rw [lenI_Hd]; omega)
  rw [h,show Trans.Recal.lenI (Cw e 1)=2 from by unfold Cw; rw [lenI_Hd]; omega,
    show (2:Int)-1=1 from by omega]
  decide

theorem trMax_A6_zero (d : Int) (hd : 1 ≤ d) : Trans.Recal.trMax (A6 d 0)=1 := by
  have e1 : Trans.Recal.trMax (A6 d 0)=(((1:Nat)):Int) → Trans.Recal.trMax (A6 d 0)=1 :=
    fun hx => by rw [hx]; rfl
  apply e1
  refine Rows.Ladder.trMax_eq _ 1 (by unfold A6; rw [length_A2]; omega) ?_ ?_
  · intro j hj
    have hj0 : j=0 := by omega
    subst hj0
    refine Rows.Ladder.isParentP_of_fpar _ _ _ _ (by omega)
      (by unfold A6; rw [lenI_A2]; omega) ?_
    have hx : Trans.Recal.fpar (A6 d 0) 1 1 0=0 :=
      Rows.Ladder.fpar1_one _ (by unfold A6; rw [length_A2]; omega)
        (by unfold A6; rw [gp0_A2_0,gp0_A2_1]; omega)
        (by unfold A6; rw [gp1_A2_0,gp1_A2_1]; omega)
    simpa using hx
  · refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
    have hx : Trans.Recal.fpar (A6 d 0) 1 2 1=-1 :=
      Rows.Ladder.fpar_out _ 1 2 1 (by unfold A6; rw [lenI_A2]; omega)
    simpa using hx

theorem base_A6_zero (d : Int) (f : Nat) (hd : 1 ≤ d) :
    Trans.Recal.red (f+1) (A6 d 0)=((0:Int),(0:Int)) :: Win 5 0 1 := by
  have h := Rows.Ladder.red_jj (A6 d 0) f
    (by unfold A6; exact isZeroP_A2 2 6 d 0)
    (prin_A6 d 0 hd)
    (by unfold A6; exact gp0_A2_0 2 6 d 0) (by unfold A6; exact gp1_A2_0 2 6 d 0)
    (by rw [trMax_A6_zero d hd]; unfold A6; rw [lenI_A2]; omega)
  rw [h,show Trans.Recal.lenI (A6 d 0)=2 from by unfold A6; rw [lenI_A2]; omega,
    show (2:Int)-1=1 from by omega]
  decide

theorem base_Q_zero (e : Int) (f : Nat) (he : 0 ≤ e) :
    Trans.Recal.red (f+2) (Q e 0)=Win 5 0 1 := by
  refine Rows.Ladder.red_head_one (Q e 0) (f+1) (Win 5 0 1)
    (by unfold Q; unfold Trans.Recal.isZeroP
        rw [show Trans.Recal.gp1 (Hd ((1:Int),(1:Int)) 6 e 0) 0=1 from rfl]
        simp)
    (by unfold Q; exact Rows.Ladder.isPrincipalP_single 1 1 (by decide))
    (by unfold Q; rw [gp0_Hd_0]; rfl) (by unfold Q; rw [gp1_Hd_0])
    ?_ (by rw [length_Win]; omega)
    (by rw [show Win 5 0 1=[((1:Int),(1:Int))] from by decide]
        exact Rows.Ladder.isPrincipalP_single 1 1 (by decide))
    (by rw [gp0_Win_0 5 0 1 (by omega),gp1_Win_0 5 0 1 (by omega),Gp_5,Gq_5]
        omega)
  unfold Q
  rw [incrFirst_Hd 1 1 6 e 1 0]
  have h := base_A6_zero (e+1) f (by omega)
  exact h

/-! #### 短い `Cw` と `A6` の畳み込み -/

theorem brF_Cw_short (e : Int) (t : Nat) (he : 0 ≤ e) (ht : 2 ≤ t) (ht4 : t ≤ 4) :
    Trans.Recal.brF (Cw e t)
      =(List.range (t-1)).map (fun j => Win (2+j) e 1) := by
  unfold Trans.Recal.brF Cw
  rw [trMax_Hd ((0:Int),(0:Int)) 1 e t (by omega)
      (by rw [Gp_1]; omega) (by rw [Gq_1]; omega)
      (by rw [show (1+1)=2 from rfl,Gp_1,Gp_2]; omega)
      (by rw [show (1+1)=2 from rfl,Gq_1,Gq_2]; omega),
    show ((1:Int)+1).toNat=2 from by rfl,drop_Hd_two,show (1+1)=2 from rfl]
  refine ppair_Win_roots 2 e (t-1) (by omega) ?_
  intro a b hab hbt
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := Gp_r 0
  rcases (show b=1 ∨ b=2 by omega) with rfl|rfl
  · have ha : a=0 := by omega
    subst ha
    rw [show (1+2)=7*0+3 by omega,show (0+2)=7*0+2 by omega,e2,e3]
    omega
  · rcases (show a=0 ∨ a=1 by omega) with rfl|rfl
    · rw [show (2+2)=7*0+4 by omega,show (0+2)=7*0+2 by omega,e2,e4]
      omega
    · rw [show (2+2)=7*0+4 by omega,show (1+2)=7*0+3 by omega,e3,e4]
      omega

theorem base_Cw_two (e : Int) (f : Nat) (he : 0 ≤ e) :
    Trans.Recal.red (f+3) (Cw e 2)=Win 0 0 3 := by
  have hbr : Trans.Recal.brF (Cw e 2)=[Win 2 e 1] := by
    rw [brF_Cw_short e 2 he (by omega) (by omega)]
    rfl
  rw [show f+3=(f+2)+1 by omega,Rows.Ladder.red_fold_open (Cw e 2) (f+2) 1
    (by unfold Cw; exact isZeroP_Hd _ 1 e 2 (by omega))
    (prin_Cw e 2 he (by omega))
    (by unfold Cw; exact gp0_Hd_0 _ 1 e 2) (by unfold Cw; exact gp1_Hd_0 _ 1 e 2)
    (trMax_Cw e 2 he (by omega))
    (by unfold Cw; rw [lenI_Hd]; exact beq_eq_false_iff_ne.mpr (by omega))]
  rw [hbr,Rows.Ladder.firstNodes_one _ _ hbr,Rows.Ladder.joints_one _ _ hbr,
    trMax_Cw e 2 he (by omega)]
  simp only [List.length_cons,List.length_nil,show (List.range 1)=[0] from rfl,
    List.foldl_cons,List.foldl_nil,List.getD_cons_zero,length_Win]
  rw [gp1_Win_0 2 e 1 (by omega),Gq_2,show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show ((1:Int)+1+0)=2 from by omega]
  have hj : Trans.Recal.fpar (Cw e 2) 0 2 0=1 := by
    have := joint_Cw e 2 he 2 (by omega) (by omega)
    rw [parHd_1_2] at this
    simpa using this
  rw [hj,nJ_Cw_two e 2 he (by omega),
    show ((1:Int)+1,(0:Int)+1)=((2:Int),(1:Int)) from by congr 1 <;> omega,
    show (1:Int)-0=1 from by omega,
    show Trans.Recal.derp (Win 2 e 1)=[] from by
      show (Win 2 e 1).drop 1=[]
      rw [Win_drop1]
      rfl,
    red_X f]
  decide

theorem base_Cw_three (e : Int) (f : Nat) (he : 0 ≤ e) :
    Trans.Recal.red (f+3) (Cw e 3)=Win 0 0 4 := by
  have hbr : Trans.Recal.brF (Cw e 3)=[Win 2 e 1,Win 3 e 1] := by
    rw [brF_Cw_short e 3 he (by omega) (by omega)]
    rfl
  rw [show f+3=(f+2)+1 by omega,Rows.Ladder.red_fold_open (Cw e 3) (f+2) 1
    (by unfold Cw; exact isZeroP_Hd _ 1 e 3 (by omega))
    (prin_Cw e 3 he (by omega))
    (by unfold Cw; exact gp0_Hd_0 _ 1 e 3) (by unfold Cw; exact gp1_Hd_0 _ 1 e 3)
    (trMax_Cw e 3 he (by omega))
    (by unfold Cw; rw [lenI_Hd]; exact beq_eq_false_iff_ne.mpr (by omega))]
  rw [hbr,Rows.Ladder.firstNodes_two _ _ _ hbr,Rows.Ladder.joints_two _ _ _ hbr,
    trMax_Cw e 3 he (by omega)]
  simp only [List.length_cons,List.length_nil,show (List.range 2)=[0,1] from rfl,
    List.foldl_cons,List.foldl_nil,List.getD_cons_zero,List.getD_cons_succ,length_Win]
  rw [gp1_Win_0 2 e 1 (by omega),gp1_Win_0 3 e 1 (by omega),Gq_2,Gq_3,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show ((1:Int)+1+0)=2 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)))=3 from by omega]
  have hj2 : Trans.Recal.fpar (Cw e 3) 0 2 0=1 := by
    have := joint_Cw e 3 he 2 (by omega) (by omega)
    rw [parHd_1_2] at this
    simpa using this
  have hj3 : Trans.Recal.fpar (Cw e 3) 0 3 0=1 := by
    have := joint_Cw e 3 he 3 (by omega) (by omega)
    rw [parHd_1_3] at this
    simpa using this
  rw [hj2,hj3,nJ_Cw_two e 3 he (by omega),nJ_Cw_three e 3 he (by omega),
    show ((1:Int)+1,(0:Int)+1)=((2:Int),(1:Int)) from by congr 1 <;> omega,
    show (1:Int)-0=1 from by omega,
    show Trans.Recal.derp (Win 2 e 1)=[] from by
      show (Win 2 e 1).drop 1=[]
      rw [Win_drop1]; rfl,
    show Trans.Recal.derp (Win 3 e 1)=[] from by
      show (Win 3 e 1).drop 1=[]
      rw [Win_drop1]; rfl,
    red_X f]
  decide

theorem base_Cw_four (e : Int) (f : Nat) (he : 0 ≤ e) :
    Trans.Recal.red (f+3) (Cw e 4)=Win 0 0 5 := by
  have hbr : Trans.Recal.brF (Cw e 4)=[Win 2 e 1,Win 3 e 1,Win 4 e 1] := by
    rw [brF_Cw_short e 4 he (by omega) (by omega)]
    rfl
  rw [show f+3=(f+2)+1 by omega,Rows.Ladder.red_fold_open (Cw e 4) (f+2) 1
    (by unfold Cw; exact isZeroP_Hd _ 1 e 4 (by omega))
    (prin_Cw e 4 he (by omega))
    (by unfold Cw; exact gp0_Hd_0 _ 1 e 4) (by unfold Cw; exact gp1_Hd_0 _ 1 e 4)
    (trMax_Cw e 4 he (by omega))
    (by unfold Cw; rw [lenI_Hd]; exact beq_eq_false_iff_ne.mpr (by omega))]
  rw [hbr,Rows.Ladder.firstNodes_three _ _ _ _ hbr,Rows.Ladder.joints_three _ _ _ _ hbr,
    trMax_Cw e 4 he (by omega)]
  simp only [List.length_cons,List.length_nil,show (List.range 3)=[0,1,2] from rfl,
    List.foldl_cons,List.foldl_nil,List.getD_cons_zero,List.getD_cons_succ,length_Win]
  rw [gp1_Win_0 2 e 1 (by omega),gp1_Win_0 3 e 1 (by omega),gp1_Win_0 4 e 1 (by omega),
    Gq_2,Gq_3,Gq_4,show ((1:Int)==0)=false from rfl,show ((0:Int)==0)=true from rfl]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show ((1:Int)+1+0)=2 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)))=3 from by omega,
    show ((1:Int)+1+(0+((1:Nat):Int)+((1:Nat):Int)))=4 from by omega]
  have hj2 : Trans.Recal.fpar (Cw e 4) 0 2 0=1 := by
    have := joint_Cw e 4 he 2 (by omega) (by omega)
    rw [parHd_1_2] at this
    simpa using this
  have hj3 : Trans.Recal.fpar (Cw e 4) 0 3 0=1 := by
    have := joint_Cw e 4 he 3 (by omega) (by omega)
    rw [parHd_1_3] at this
    simpa using this
  have hj4 : Trans.Recal.fpar (Cw e 4) 0 4 0=1 := by
    have := joint_Cw e 4 he 4 (by omega) (by omega)
    rw [parHd_1_4] at this
    simpa using this
  rw [hj2,hj3,hj4,nJ_Cw_two e 4 he (by omega),nJ_Cw_three e 4 he (by omega),
    show ((1:Int)+1,(0:Int)+1)=((2:Int),(1:Int)) from by congr 1 <;> omega,
    show ((1:Int)+1,(-1:Int)+1)=((2:Int),(0:Int)) from by congr 1 <;> omega,
    show (1:Int)-0=1 from by omega,show (1:Int)-(-1)=2 from by omega,
    show Trans.Recal.derp (Win 2 e 1)=[] from by
      show (Win 2 e 1).drop 1=[]
      rw [Win_drop1]; rfl,
    show Trans.Recal.derp (Win 3 e 1)=[] from by
      show (Win 3 e 1).drop 1=[]
      rw [Win_drop1]; rfl,
    show Trans.Recal.derp (Win 4 e 1)=[] from by
      show (Win 4 e 1).drop 1=[]
      rw [Win_drop1]; rfl,
    red_X f,red_Z (f+1)]
  decide

theorem base_A6_one (d : Int) (f : Nat) (hd : 1 ≤ d) :
    Trans.Recal.red (f+3) (A6 d 1)=((0:Int),(0:Int)) :: Win 5 0 2 := by
  have hbr : Trans.Recal.brF (A6 d 1)=[Win 6 d 1] := by
    unfold Trans.Recal.brF A6
    rw [trMax_A2 2 6 d 1 (by omega) (by omega) (by rw [Gp_6]; omega)
        (by rw [Gq_6]; omega),
      show ((1:Int)+1).toNat=2 from by rfl,drop_A2_two]
    exact ppair_Win_roots 6 d 1 (by omega) (fun a b _ hb => absurd hb (by omega))
  rw [show f+3=(f+2)+1 by omega,Rows.Ladder.red_fold_open (A6 d 1) (f+2) 1
    (by unfold A6; exact isZeroP_A2 2 6 d 1)
    (prin_A6 d 1 hd)
    (by unfold A6; exact gp0_A2_0 2 6 d 1) (by unfold A6; exact gp1_A2_0 2 6 d 1)
    (trMax_A6 d 1 hd (by omega))
    (by unfold A6; rw [lenI_A2]; exact beq_eq_false_iff_ne.mpr (by omega))]
  rw [hbr,Rows.Ladder.firstNodes_one _ _ hbr,Rows.Ladder.joints_one _ _ hbr,
    trMax_A6 d 1 hd (by omega)]
  simp only [List.length_cons,List.length_nil,show (List.range 1)=[0] from rfl,
    List.foldl_cons,List.foldl_nil,List.getD_cons_zero,length_Win]
  rw [gp1_Win_0 6 d 1 (by omega),Gq_6,show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show ((1:Int)+1+0)=2 from by omega]
  have hj : Trans.Recal.fpar (A6 d 1) 0 2 0=1 := by
    have := joint_A6 d 1 hd 2 (by omega) (by omega)
    rw [parA_6_2] at this
    simpa using this
  rw [hj,nJ_A6_two d 1 hd (by omega),
    show ((1:Int)+1,(0:Int)+1)=((2:Int),(1:Int)) from by congr 1 <;> omega,
    show (1:Int)-0=1 from by omega,
    show Trans.Recal.derp (Win 6 d 1)=[] from by
      show (Win 6 d 1).drop 1=[]
      rw [Win_drop1]; rfl,
    red_X f]
  decide

/-! ### Link 2, step 16: the cycle closes. -/

theorem jj_one : Trans.Recal.jjSeq 0 1
    =([((0:Int),(0:Int)),((1:Int),(1:Int))] : Trans.Recal.PS) := rfl

theorem red_Cw_of_Q (e : Int) (t f : Nat) (he : 0 ≤ e) (ht : 5 ≤ t)
    (h : Trans.Recal.red (f+2) (Q e (t-5))=Win 5 0 (t-4)) :
    Trans.Recal.red (f+3) (Cw e t)=Win 0 0 (t+1) := by
  rw [show f+3=(f+2)+1 by omega,fold_Cw e t (f+2) he ht,red_X f,
    show f+2=(f+1)+1 by omega,red_Z (f+1),h,jj_one,
    show Trans.Recal.incrFirst [((1:Int),(1:Int))] 1=[((2:Int),(1:Int))] from by decide,
    show Trans.Recal.incrFirst [((0:Int),(0:Int))] 2=[((2:Int),(0:Int))] from by decide,
    show Trans.Recal.incrFirst (Win 5 0 (t-4)) 0=Win 5 0 (t-4) from by
      rw [incrFirst_Win]
      congr 1
      try omega]
  exact glue_Cw t (by omega)

theorem red_A6_of_Zr (d : Int) (s f : Nat) (hd : 1 ≤ d) (hs : 2 ≤ s)
    (h : Trans.Recal.red (f+2) (Zr d (s-2))=Win 0 0 (s-1)) :
    Trans.Recal.red (f+3) (A6 d s)=((0:Int),(0:Int)) :: Win 5 0 (s+1) := by
  rw [show f+3=(f+2)+1 by omega,fold_A6 d s (f+2) hd hs,red_X f,h,jj_one,
    show Trans.Recal.incrFirst [((1:Int),(1:Int))] 1=[((2:Int),(1:Int))] from by decide,
    show Trans.Recal.incrFirst (Win 0 0 (s-1)) 2=Win 0 2 (s-1) from by
      rw [incrFirst_Win]
      congr 1
      try omega]
  exact glue_A6 s (by omega)

theorem base_Zr_zero (d : Int) (f : Nat) : Trans.Recal.red (f+1) (Zr d 0)=Win 0 0 1 := by
  rw [Rows.Ladder.red_zeroP _ f (by rfl)]
  decide

theorem red_Zr_of_Cw (d : Int) (t f : Nat) (hd : 0 ≤ d)
    (h : Trans.Recal.red f (Cw d t)=Win 0 0 (t+1)) :
    Trans.Recal.red (f+1) (Zr d t)=Win 0 0 (t+1) := by
  cases t with
  | zero => exact base_Zr_zero d f
  | succ u => rw [step_Zr d (u+1) f hd (by omega)]; exact h

/-- **輪が閉じる。** `Cw e t` の答えはずらしに依らない。 -/
theorem red_Cw (t : Nat) : ∀ (e : Int) (f : Nat), 0 ≤ e →
    Trans.Recal.red (2*t+f+11) (Cw e t)=Win 0 0 (t+1) := by
  refine Nat.strongRecOn t ?_
  intro t ih e f he
  rcases (show t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ 7 ≤ t by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl|h7
  · rw [show 2*0+f+11=(f+10)+1 by omega]
    exact base_Cw_zero e (f+10)
  · rw [show 2*1+f+11=(f+12)+1 by omega]
    exact base_Cw_one e (f+12) he
  · rw [show 2*2+f+11=(f+12)+3 by omega]
    exact base_Cw_two e (f+12) he
  · rw [show 2*3+f+11=(f+14)+3 by omega]
    exact base_Cw_three e (f+14) he
  · rw [show 2*4+f+11=(f+16)+3 by omega]
    exact base_Cw_four e (f+16) he
  · rw [show 2*5+f+11=(f+18)+3 by omega]
    refine red_Cw_of_Q e 5 (f+18) he (by omega) ?_
    rw [show 5-5=0 from rfl,show 5-4=1 from rfl]
    exact base_Q_zero e (f+18) he
  · rw [show 2*6+f+11=(f+20)+3 by omega]
    refine red_Cw_of_Q e 6 (f+20) he (by omega) ?_
    rw [show 6-5=1 from rfl,show 6-4=2 from rfl,show f+20+2=(f+21)+1 by omega]
    refine step_Q e 1 (f+21) he (by omega) ?_
    rw [show f+21=(f+18)+3 by omega]
    exact base_A6_one (e+1) (f+18) (by omega)
  · obtain ⟨r,rfl⟩ : ∃ r, t=r+7 := ⟨t-7,by omega⟩
    have hIH : Trans.Recal.red (2*r+f+21) (Cw (e+1) r)=Win 0 0 (r+1) := by
      have := ih r (by omega) (e+1) (f+10) (by omega)
      rw [show 2*r+(f+10)+11=2*r+f+21 by omega] at this
      exact this
    have hZr : Trans.Recal.red (2*r+f+22) (Zr (e+1) r)=Win 0 0 (r+1) := by
      have := red_Zr_of_Cw (e+1) r (2*r+f+21) (by omega) hIH
      rw [show 2*r+f+21+1=2*r+f+22 by omega] at this
      exact this
    have hA6 : Trans.Recal.red ((2*r+f+20)+3) (A6 (e+1) (r+2))
        =((0:Int),(0:Int)) :: Win 5 0 (r+2+1) := by
      refine red_A6_of_Zr (e+1) (r+2) (2*r+f+20) (by omega) (by omega) ?_
      rw [show r+2-2=r from rfl,show r+2-1=r+1 from rfl,
        show 2*r+f+20+2=2*r+f+22 by omega]
      exact hZr
    rw [show 2*(r+7)+f+11=(2*r+f+22)+3 by omega]
    refine red_Cw_of_Q e (r+7) (2*r+f+22) he (by omega) ?_
    rw [show r+7-5=r+2 from rfl,show r+7-4=r+3 from rfl,
      show 2*r+f+22+2=(2*r+f+23)+1 by omega]
    refine step_Q e (r+2) (2*r+f+23) he (by omega) ?_
    rw [show 2*r+f+23=(2*r+f+20)+3 by omega]
    exact hA6


/-- 梯子そのものが輪の形。 -/
theorem L_eq_Cw (m : Nat) : L m=Cw 0 (m+6) := by
  rw [L_eq_Win,show m+7=(m+6)+1 from rfl,Win_eq_Hd]
  unfold Cw
  rw [show (Gp 0+(0:Int),Gq 0)=((0:Int),(0:Int)) from by
    rw [Gp_0,Gq_0]
    congr 1
    try omega]

theorem red_L (m f : Nat) : Trans.Recal.red (2*m+f+23) (L m)=L m := by
  have h := red_Cw (m+6) 0 f (by omega)
  have hL : L m=Cw 0 (m+6) := L_eq_Cw m
  have hW : Win 0 0 (m+6+1)=L m := by rw [show m+6+1=m+7 from rfl,← L_eq_Win]
  rw [show 2*m+f+23=2*(m+6)+f+11 by omega,hL,h,hW]
  exact hL

/-- **リンク 2 の前半: 梯子は既約。** -/
theorem redP_L (m : Nat) : Trans.Recal.redP (L m)=L m := by
  unfold Trans.Recal.redP
  obtain ⟨f,hf⟩ : ∃ f, Trans.Recal.redFuel (L m)=2*m+f+23 := by
    refine ⟨Trans.Recal.redFuel (L m)-(2*m+23),?_⟩
    have h : 40+4*((L m).length+Trans.Recal.maxE (L m)) ≤ Trans.Recal.redFuel (L m) := by
      unfold Trans.Recal.redFuel
      omega
    rw [length_L] at h
    omega
  rw [hf]
  exact red_L m f

theorem isReducedP_L (m : Nat) : Trans.Recal.isReducedP (L m)=true := by
  unfold Trans.Recal.isReducedP
  rw [redP_L]
  exact G1.beq_PS_self _

#guard (List.range 12).all fun m => Trans.Recal.isReducedP (L m)

/-! ### Link 2, step 17: every index of this ladder is admitted.

`fpar (L m) 1 j (j-1)` hits only at `j ≡ 1 (mod 7)`, and then the successor's
residue is 2, so the two `isParentP` tests are never both true. -/

theorem fpar0_L_prev_hit (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+7) (h0 : Gp (j-1)<Gp j) :
    Trans.Recal.fpar0 (L m) ((j:Nat):Int) ((j-1:Nat):Int)=((j-1:Nat):Int) := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L,gp0_L m j hjm,
    show ((j:Nat):Int)-1=((j-1:Nat):Int) from by omega,
    Rows.Ladder.fpar0Aux_step,if_neg (by omega),gp0_L m (j-1) (by omega),if_pos h0]

theorem fpar0_L_prev_miss (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+7)
    (h0 : ¬(Gp (j-1)<Gp j)) :
    Trans.Recal.fpar0 (L m) ((j:Nat):Int) ((j-1:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L,gp0_L m j hjm,
    show ((j:Nat):Int)-1=((j-1:Nat):Int) from by omega,
    show m+7+1=(m+7)+1 from rfl,
    Rows.Ladder.fpar0Aux_step,if_neg (by omega),gp0_L m (j-1) (by omega),if_neg h0]
  obtain ⟨g,hg⟩ : ∃ g, m+7=g+1 := ⟨m+6,by omega⟩
  rw [hg,Rows.Ladder.fpar0Aux_step,if_pos (by omega)]

theorem fpar0_L_self_stop (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+7) :
    Trans.Recal.fpar0 (L m) ((j-1:Nat):Int) ((j-1:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L,show m+7+1=(m+7)+1 from rfl,
    Rows.Ladder.fpar0Aux_step,if_pos (by omega)]

theorem fpar1_L_prev_hit (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+7)
    (h0 : Gp (j-1)<Gp j) (h1 : Gq (j-1)<Gq j) :
    Trans.Recal.fpar (L m) 1 ((j:Nat):Int) ((j-1:Nat):Int)=((j-1:Nat):Int) := by
  rw [Rows.Ladder.fpar1_unfold (L m) _ _ (by rw [lenI_L]; omega),length_L,
    show m+7+1=(m+7)+1 from rfl,
    Rows.Ladder.fpar1Aux_step,fpar0_L_prev_hit m j hj hjm h0,if_neg (by omega),
    gp1_L m (j-1) (by omega),gp1_L m j hjm,if_pos h1]

theorem fpar1_L_prev_miss (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+7)
    (h0 : Gp (j-1)<Gp j) (h1 : ¬(Gq (j-1)<Gq j)) :
    Trans.Recal.fpar (L m) 1 ((j:Nat):Int) ((j-1:Nat):Int)=-1 := by
  rw [Rows.Ladder.fpar1_unfold (L m) _ _ (by rw [lenI_L]; omega),length_L,
    show m+7+1=(m+7)+1 from rfl,
    Rows.Ladder.fpar1Aux_step,fpar0_L_prev_hit m j hj hjm h0,if_neg (by omega),
    gp1_L m (j-1) (by omega),gp1_L m j hjm,if_neg h1]
  obtain ⟨g,hg⟩ : ∃ g, m+7=g+1 := ⟨m+6,by omega⟩
  rw [hg,Rows.Ladder.fpar1Aux_step,fpar0_L_self_stop m j hj hjm,if_pos (by omega)]

theorem fpar1_L_prev_nodrop (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+7)
    (h0 : ¬(Gp (j-1)<Gp j)) :
    Trans.Recal.fpar (L m) 1 ((j:Nat):Int) ((j-1:Nat):Int)=-1 := by
  rw [Rows.Ladder.fpar1_unfold (L m) _ _ (by rw [lenI_L]; omega),length_L,
    show m+7+1=(m+7)+1 from rfl,
    Rows.Ladder.fpar1Aux_step,fpar0_L_prev_miss m j hj hjm h0,if_pos (by omega)]

/-- 行 1 の親は残余 1 のときだけ当たる。 -/
theorem fpar1_L_prev (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+7) :
    Trans.Recal.fpar (L m) 1 ((j:Nat):Int) ((j-1:Nat):Int)
      = if j%7=1 then ((j-1:Nat):Int) else -1 := by
  obtain ⟨a,r,hr,rfl⟩ : ∃ a r, r<7 ∧ j=7*a+r := ⟨j/7,j%7,by omega,by omega⟩
  rw [show (7*a+r)%7=r by omega]
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := Gp_r a
  rcases (show r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · rw [if_neg (by omega)]
    obtain ⟨b,rfl⟩ : ∃ b, a=b+1 := ⟨a-1,by omega⟩
    obtain ⟨f0,f1,f2,f3,f4,f5,f6⟩ := Gp_r b
    refine fpar1_L_prev_nodrop m (7*(b+1)+0) (by omega) (by omega) ?_
    rw [show 7*(b+1)+0-1=7*b+6 by omega,f6]
    rw [show 7*(b+1)+0=7*(b+1)+0 from rfl] at e0
    rw [e0]
    push_cast
    omega
  · rw [if_pos rfl]
    refine fpar1_L_prev_hit m (7*a+1) (by omega) (by omega) ?_ ?_
    · rw [show 7*a+1-1=7*a+0 by omega,e0,e1]; omega
    · rw [show 7*a+1-1=7*a+0 by omega]
      unfold Gq
      rw [if_pos (by omega),if_neg (by omega)]
      omega
  · rw [if_neg (by omega)]
    refine fpar1_L_prev_miss m (7*a+2) (by omega) (by omega) ?_ ?_
    · rw [show 7*a+2-1=7*a+1 by omega,e1,e2]; omega
    · rw [show 7*a+2-1=7*a+1 by omega]
      unfold Gq
      rw [if_neg (by omega),if_neg (by omega)]
      omega
  · rw [if_neg (by omega)]
    refine fpar1_L_prev_nodrop m (7*a+3) (by omega) (by omega) ?_
    rw [show 7*a+3-1=7*a+2 by omega,e2,e3]; omega
  · rw [if_neg (by omega)]
    refine fpar1_L_prev_nodrop m (7*a+4) (by omega) (by omega) ?_
    rw [show 7*a+4-1=7*a+3 by omega,e3,e4]; omega
  · rw [if_neg (by omega)]
    refine fpar1_L_prev_nodrop m (7*a+5) (by omega) (by omega) ?_
    rw [show 7*a+5-1=7*a+4 by omega,e4,e5]; omega
  · rw [if_neg (by omega)]
    refine fpar1_L_prev_miss m (7*a+6) (by omega) (by omega) ?_ ?_
    · rw [show 7*a+6-1=7*a+5 by omega,e5,e6]; omega
    · rw [show 7*a+6-1=7*a+5 by omega]
      unfold Gq
      rw [if_neg (by omega),if_neg (by omega)]
      omega

#guard (List.range 10).all fun m => (List.range (m+7)).all fun j =>
  (j==0) || (Trans.Recal.fpar (L m) 1 ((j:Nat):Int) ((j-1:Nat):Int)
    == (if j%7=1 then ((j-1:Nat):Int) else -1))

theorem isParentP_L_prev_false (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+7) (h : j%7 ≠ 1) :
    Trans.Recal.isParentP (L m) 1 ((j:Nat):Int) (((j:Nat):Int)-1)=false := by
  rw [show ((j:Nat):Int)-1=((j-1:Nat):Int) from by omega]
  refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
  rw [fpar1_L_prev m j hj hjm,if_neg h]

/-- **どの添字も入場可能。** -/
theorem isAdm_L (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+7) :
    Trans.Recal.isAdm (L m) ((j:Nat):Int)=true := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((j:Nat):Int)>Trans.Recal.lenI (L m))=false from
    decide_eq_false (by rw [lenI_L]; omega)]
  simp only [Bool.false_or]
  by_cases h1 : j%7=1
  · rw [show Trans.Recal.isParentP (L m) 1 (((j:Nat):Int)+1) ((j:Nat):Int)=false from by
      by_cases hlt : j+1<m+7
      · rw [show ((j:Nat):Int)+1=(((j+1:Nat)):Int) from by omega,
          show ((j:Nat):Int)=(((j+1:Nat)):Int)-1 from by omega]
        exact isParentP_L_prev_false m (j+1) (by omega) hlt (by omega)
      · refine Rows.Ladder.isParentP_of_ne _ _ _ _ (-1) ?_ (by omega)
        exact Rows.Ladder.fpar_out _ 1 _ _ (by rw [lenI_L]; omega)]
    rw [Bool.and_false]
    rfl
  · rw [isParentP_L_prev_false m j hj hjm h1,Bool.false_and]
    rfl

theorem adm_L (m j : Nat) (hj : 1 ≤ j) (hjm : j<m+7) :
    Trans.Recal.adm (L m) ((j:Nat):Int)=((j:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L,show m+7+2=(m+7+1)+1 from rfl,Rows.Ladder.admAux_step,if_neg (by omega),
    isAdm_L m j hj hjm,if_pos rfl]

#guard (List.range 10).all fun m => (List.range (m+7)).all fun j =>
  Trans.Recal.isAdm (L m) ((j:Nat):Int)
#guard (List.range 10).all fun m => (List.range (m+7)).all fun j =>
  Trans.Recal.adm (L m) ((j:Nat):Int)==((j:Nat):Int)

/-! ### Link 2, step 18: the row-zero parent of the ladder, and the seven phases. -/

theorem parHd_one_eq (k : Nat) (hk : 1 ≤ k) : parHd 1 k=parN k := by
  unfold parHd
  rw [show k-1+1=k by omega]
  by_cases h : 1 ≤ parN k
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

theorem fpar_L_zero (m k : Nat) (hk : 1 ≤ k) (hkm : k<m+7) :
    Trans.Recal.fpar (L m) 0 ((k:Nat):Int) 0=((parN k : Nat):Int) := by
  rw [L_eq_Cw]
  have h := joint_Cw 0 (m+6) (by omega) k hk (by omega)
  rw [parHd_one_eq k hk] at h
  exact h

theorem Gq_zero (j : Nat) (h : j%7=0 ∨ j%7=4) : Gq j=0 := by
  unfold Gq
  rw [if_pos h]

theorem Gq_one (j : Nat) (h : ¬(j%7=0 ∨ j%7=4)) : Gq j=1 := by
  unfold Gq
  rw [if_neg h]

theorem parN_val (k : Nat) (r : Nat) (h : k%7=r) (hr : r<7) :
    parN k=(if r=0 ∨ r=3 then k-2 else if r=4 then k-3 else if r=5 then k-5 else k-1) := by
  unfold parN
  rw [h]

theorem j0_L (k : Nat) : Trans.Recal.fpar (L k) 0 ((k+6:Nat):Int) 0
    = ((parN (k+6) : Nat):Int) := fpar_L_zero k (k+6) (by omega) (by omega)

theorem parN_k6_r0 (k : Nat) (h : k%7=0) : parN (k+6)=k+5 := by
  rw [parN_val (k+6) 6 (by omega) (by omega),if_neg (by omega),if_neg (by omega),
    if_neg (by omega)]
  omega
theorem parN_k6_r1 (k : Nat) (h : k%7=1) : parN (k+6)=k+4 := by
  rw [parN_val (k+6) 0 (by omega) (by omega),if_pos (by omega)]
  omega
theorem parN_k6_r2 (k : Nat) (h : k%7=2) : parN (k+6)=k+5 := by
  rw [parN_val (k+6) 1 (by omega) (by omega),if_neg (by omega),if_neg (by omega),
    if_neg (by omega)]
  omega
theorem parN_k6_r3 (k : Nat) (h : k%7=3) : parN (k+6)=k+5 := by
  rw [parN_val (k+6) 2 (by omega) (by omega),if_neg (by omega),if_neg (by omega),
    if_neg (by omega)]
  omega
theorem parN_k6_r4 (k : Nat) (h : k%7=4) : parN (k+6)=k+4 := by
  rw [parN_val (k+6) 3 (by omega) (by omega),if_pos (by omega)]
  omega
theorem parN_k6_r5 (k : Nat) (h : k%7=5) : parN (k+6)=k+3 := by
  rw [parN_val (k+6) 4 (by omega) (by omega),if_neg (by omega),if_pos (by omega)]
  omega
theorem parN_k6_r6 (k : Nat) (h : k%7=6) : parN (k+6)=k+1 := by
  rw [parN_val (k+6) 5 (by omega) (by omega),if_neg (by omega),if_neg (by omega),
    if_pos (by omega)]
  omega

#guard (List.range 20).all fun k =>
  Trans.Recal.fpar (L k) 0 ((k+6:Nat):Int) 0
    == ((if k%7=0 then k+5 else if k%7=1 then k+4 else if k%7=2 then k+5
         else if k%7=3 then k+5 else if k%7=4 then k+4 else if k%7=5 then k+3
         else k+1 : Nat):Int)

/-! #### 相ごとの遷移型と `c2`

    r   j0     ty   c1            c2
    0   k+5    3    D1 0          D1 (D1 0)
    1   k+4    1    D1 (D1 0)     D1 (D1 0 + D0 0)
    2   k+5    6    D0 0          D0 (D1 0)
    3   k+5    3    D1 0          D1 (D1 0)
    4   k+4    3    D1 (D1 0)     D1 (D1 0 + D1 0)
    5   k+3    1    D1 (D1 0+D1 0) A0
    6   k+1    5    D0 A0         D0 (A0 + D1 0)
-/

theorem transType_L_r0 (k : Nat) (h : k%7=0) :
    Trans.Recal.transTypeMain (L k) ((k+5:Nat):Int) ((k+6:Nat):Int)=3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+6) (by omega),gp1_L k (k+5) (by omega),
    Gq_one (k+6) (by omega),Gq_one (k+5) (by omega),show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [if_pos (by omega),isAdm_L k (k+5) (by omega) (by omega),if_pos rfl]

theorem transType_L_r1 (k : Nat) (h : k%7=1) :
    Trans.Recal.transTypeMain (L k) ((k+4:Nat):Int) ((k+6:Nat):Int)=1 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+6) (by omega),Gq_zero (k+6) (by omega),
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  rw [isAdm_L k (k+4) (by omega) (by omega),if_pos rfl]

theorem transType_L_r2 (k : Nat) (h : k%7=2) :
    Trans.Recal.transTypeMain (L k) ((k+5:Nat):Int) ((k+6:Nat):Int)=6 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+6) (by omega),gp1_L k (k+5) (by omega),
    Gq_one (k+6) (by omega),Gq_zero (k+5) (by omega),show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [if_neg (by omega),if_neg (by omega)]

theorem transType_L_r3 (k : Nat) (h : k%7=3) :
    Trans.Recal.transTypeMain (L k) ((k+5:Nat):Int) ((k+6:Nat):Int)=3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+6) (by omega),gp1_L k (k+5) (by omega),
    Gq_one (k+6) (by omega),Gq_one (k+5) (by omega),show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [if_pos (by omega),isAdm_L k (k+5) (by omega) (by omega),if_pos rfl]

theorem transType_L_r4 (k : Nat) (h : k%7=4) :
    Trans.Recal.transTypeMain (L k) ((k+4:Nat):Int) ((k+6:Nat):Int)=3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+6) (by omega),gp1_L k (k+4) (by omega),
    Gq_one (k+6) (by omega),Gq_one (k+4) (by omega),show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [if_pos (by omega),isAdm_L k (k+4) (by omega) (by omega),if_pos rfl]

theorem transType_L_r5 (k : Nat) (h : k%7=5) :
    Trans.Recal.transTypeMain (L k) ((k+3:Nat):Int) ((k+6:Nat):Int)=1 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+6) (by omega),Gq_zero (k+6) (by omega),
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  rw [isAdm_L k (k+3) (by omega) (by omega),if_pos rfl]

theorem transType_L_r6 (k : Nat) (h : k%7=6) :
    Trans.Recal.transTypeMain (L k) ((k+1:Nat):Int) ((k+6:Nat):Int)=5 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L k (k+6) (by omega),gp1_L k (k+1) (by omega),
    Gq_one (k+6) (by omega),Gq_zero (k+1) (by omega),show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [if_neg (by omega),if_pos (by omega)]

theorem mkC2_L_r0 (k : Nat) (h : k%7=0) :
    Trans.Recal.mkC2 (L k) ((k+5:Nat):Int) ((k+6:Nat):Int) 3 D1z=D11z := by
  unfold Trans.Recal.mkC2
  rw [gp1_L k (k+6) (by omega),Gq_one (k+6) (by omega)]
  rfl

theorem mkC2_L_r1 (k : Nat) (h : k%7=1) :
    Trans.Recal.mkC2 (L k) ((k+4:Nat):Int) ((k+6:Nat):Int) 1 D11z
      =Trans.Dict.BT.D 1 (.sum D1z D0z) := by
  unfold Trans.Recal.mkC2
  rw [gp1_L k (k+6) (by omega),Gq_zero (k+6) (by omega)]
  rfl

theorem mkC2_L_r2 (k : Nat) (h : k%7=2) :
    Trans.Recal.mkC2 (L k) ((k+5:Nat):Int) ((k+6:Nat):Int) 6 D0z
      =Trans.Dict.BT.D 0 D1z := by
  unfold Trans.Recal.mkC2
  rw [gp1_L k (k+6) (by omega),Gq_one (k+6) (by omega)]
  rfl

theorem mkC2_L_r3 (k : Nat) (h : k%7=3) :
    Trans.Recal.mkC2 (L k) ((k+5:Nat):Int) ((k+6:Nat):Int) 3 D1z=D11z := by
  unfold Trans.Recal.mkC2
  rw [gp1_L k (k+6) (by omega),Gq_one (k+6) (by omega)]
  rfl

theorem mkC2_L_r4 (k : Nat) (h : k%7=4) :
    Trans.Recal.mkC2 (L k) ((k+4:Nat):Int) ((k+6:Nat):Int) 3 D11z=D1ss := by
  unfold Trans.Recal.mkC2
  rw [gp1_L k (k+6) (by omega),Gq_one (k+6) (by omega)]
  rfl

theorem mkC2_L_r5 (k : Nat) (h : k%7=5) :
    Trans.Recal.mkC2 (L k) ((k+3:Nat):Int) ((k+6:Nat):Int) 1 D1ss=A0 := by
  unfold Trans.Recal.mkC2
  rw [gp1_L k (k+6) (by omega),Gq_zero (k+6) (by omega)]
  rfl

theorem mkC2_L_r6 (k : Nat) (h : k%7=6) :
    Trans.Recal.mkC2 (L k) ((k+1:Nat):Int) ((k+6:Nat):Int) 5 (Trans.Dict.BT.D 0 A0)
      =Trans.Dict.BT.D 0 B0 := by
  unfold Trans.Recal.mkC2
  rw [gp1_L k (k+6) (by omega),Gq_one (k+6) (by omega)]
  rfl

/-! ### Link 2, step 19: the replacement inside the reader output.

`W`'s rightmost spine descends four constructors per complete block — one more
than `G10`'s, which is the extra column. -/

theorem repl_D0W : ∀ (a f r : Nat) (b bb c cc : Trans.Dict.BT),
    (∀ g : Nat, r ≤ g → Trans.Recal.replMark g (.D 0 b) c cc=some (.D 0 bb)) →
    (∀ n : Nat, ((Trans.Dict.BT.D 0 (W (n+1) b))==c)=false
      ∧ ((Trans.Dict.BT.D 1 (.sum D1z (.D 0 (W n b))))==c)=false) →
    4*a+r ≤ f →
    Trans.Recal.replMark f (.D 0 (W a b)) c cc=some (.D 0 (W a bb))
  | 0,f,r,b,bb,c,cc,hbase,_,hf => hbase f (by simpa using hf)
  | a+1,f,r,b,bb,c,cc,hbase,hne,hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+4 := ⟨f-4,by omega⟩
    change Trans.Recal.replMark (g+4)
      (.D 0 (.sum A0 (.D 1 (.sum D1z (.D 0 (W a b)))))) c cc=
      some (.D 0 (.sum A0 (.D 1 (.sum D1z (.D 0 (W a bb))))))
    rw [show g+4=(g+3)+1 by omega,Trans.Recal.replMark]
    have hn:=(hne a).1
    change ((Trans.Dict.BT.D 0 (.sum A0 (.D 1 (.sum D1z (.D 0 (W a b))))))==c)=false at hn
    rw [hn]
    simp only [Bool.false_eq_true,if_false]
    rw [show g+3=(g+2)+1 by omega,Trans.Recal.replMark]
    rw [show Trans.Dict.BT.toL (.sum A0 (.D 1 (.sum D1z (.D 0 (W a b)))))
      =[A0,.D 1 (.sum D1z (.D 0 (W a b)))] from rfl]
    change ((Trans.Recal.replMark (g+2) (.D 1 (.sum D1z (.D 0 (W a b)))) c cc).map
      (fun x=>Trans.Dict.BT.sum A0 x)).map (fun x=>Trans.Dict.BT.D 0 x)=_
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.replMark,(hne a).2]
    simp only [Bool.false_eq_true,if_false]
    change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
      (Option.map (fun x=>Trans.Dict.BT.sum A0 x)
        (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
          (Option.map (fun ll=>Trans.Dict.BT.ofL
              (([D1z,(Trans.Dict.BT.D 0 (W a b))] : List Trans.Dict.BT).dropLast++[ll]))
            (Trans.Recal.replMark g (.D 0 (W a b)) c cc)))))=_
    rw [repl_D0W a g r b bb c cc hbase hne (by omega)]
    rfl

theorem W_add (a b : Nat) (c : Trans.Dict.BT) : W a (W b c)=W (a+b) c := by
  induction a with
  | zero => simp [W]
  | succ a ih =>
    simp only [W,ih]
    rw [show a+1+b=(a+b)+1 by omega,W]

theorem LBT_r (a r : Nat) (hr : r<7) : LBT (7*a+r)=.D 0 (W a (Part r)) := by
  unfold LBT
  rw [show (7*a+r)/7=a by omega,show (7*a+r)%7=r by omega]

theorem repl_LBT_r1 (a f : Nat) (hf : 4*a+3 ≤ f) :
    Trans.Recal.replMark f (LBT (7*a+0)) D11z (.D 1 (.sum D1z D0z))
      =some (LBT (7*a+1)) := by
  rw [LBT_r a 0 (by omega),LBT_r a 1 (by omega)]
  refine repl_D0W a f 3 (Part 0) (Part 1) D11z (.D 1 (.sum D1z D0z)) ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+3 := ⟨g-3,by omega⟩
    change Trans.Recal.replMark (h+3) (.D 0 (.sum A0 D11z)) D11z
      (.D 1 (.sum D1z D0z))=some (.D 0 (.sum A0 (.D 1 (.sum D1z D0z))))
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 0 (.sum A0 D11z))==D11z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark,
      show Trans.Dict.BT.toL (.sum A0 D11z)=[A0,D11z] from rfl]
    change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
      (Option.map (fun ll=>Trans.Dict.BT.ofL
          (([A0,D11z] : List Trans.Dict.BT).dropLast++[ll]))
        (Trans.Recal.replMark (h+1) D11z D11z (.D 1 (.sum D1z D0z)))))=_
    rw [G1.replMark_self (h+1) 1 D1z (.D 1 (.sum D1z D0z)) (by omega)]
    rfl
  · intro n
    exact ⟨rfl,rfl⟩

theorem repl_LBT_r2 (a f : Nat) (hf : 4*a+5 ≤ f) :
    Trans.Recal.replMark f (LBT (7*a+1)) D0z (.D 0 D1z)=some (LBT (7*a+2)) := by
  rw [LBT_r a 1 (by omega),LBT_r a 2 (by omega)]
  refine repl_D0W a f 5 (Part 1) (Part 2) D0z (.D 0 D1z) ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+5 := ⟨g-5,by omega⟩
    change Trans.Recal.replMark (h+5) (.D 0 (.sum A0 (.D 1 (.sum D1z D0z)))) D0z
      (.D 0 D1z)=some (.D 0 (.sum A0 (.D 1 (.sum D1z (.D 0 D1z)))))
    rw [show h+5=(h+4)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 0 (.sum A0 (.D 1 (.sum D1z D0z))))==D0z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark,
      show Trans.Dict.BT.toL (.sum A0 (.D 1 (.sum D1z D0z)))
        =[A0,.D 1 (.sum D1z D0z)] from rfl]
    change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
      (Option.map (fun ll=>Trans.Dict.BT.ofL
          (([A0,(Trans.Dict.BT.D 1 (.sum D1z D0z))] : List Trans.Dict.BT).dropLast++[ll]))
        (Trans.Recal.replMark (h+3) (.D 1 (.sum D1z D0z)) D0z (.D 0 D1z))))=_
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark,
      show ((Trans.Dict.BT.D 1 (.sum D1z D0z))==D0z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
      (Option.map (fun ll=>Trans.Dict.BT.ofL
          (([A0,(Trans.Dict.BT.D 1 (.sum D1z D0z))] : List Trans.Dict.BT).dropLast++[ll]))
        (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
          (Trans.Recal.replMark (h+2) (.sum D1z D0z) D0z (.D 0 D1z)))))=_
    rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark,
      show Trans.Dict.BT.toL (.sum D1z D0z)=[D1z,D0z] from rfl]
    change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
      (Option.map (fun ll=>Trans.Dict.BT.ofL
          (([A0,(Trans.Dict.BT.D 1 (.sum D1z D0z))] : List Trans.Dict.BT).dropLast++[ll]))
        (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
          (Option.map (fun ll=>Trans.Dict.BT.ofL
              (([D1z,D0z] : List Trans.Dict.BT).dropLast++[ll]))
            (Trans.Recal.replMark (h+1) D0z D0z (.D 0 D1z))))))=_
    rw [G1.replMark_self (h+1) 0 .zero (.D 0 D1z) (by omega)]
    rfl
  · intro n
    exact ⟨rfl,rfl⟩

#guard (List.range 5).all fun a =>
  Trans.Recal.replMark 60 (LBT (7*a+0)) D11z (.D 1 (.sum D1z D0z))==some (LBT (7*a+1))
#guard (List.range 5).all fun a =>
  Trans.Recal.replMark 60 (LBT (7*a+1)) D0z (.D 0 D1z)==some (LBT (7*a+2))

/-- `Part` の中を 1 段深く降りる形。相 3・4・5 が共有する。 -/
theorem repl_base_deep (h u : Nat) (y cc : Trans.Dict.BT)
    (hn1 : ((Trans.Dict.BT.D 0 (.sum A0 (.D 1 (.sum D1z (.D 0 (.D u y))))))
            ==(Trans.Dict.BT.D u y))=false)
    (hn2 : ((Trans.Dict.BT.D 1 (.sum D1z (.D 0 (.D u y))))==(Trans.Dict.BT.D u y))=false)
    (hn3 : ((Trans.Dict.BT.D 0 (.D u y))==(Trans.Dict.BT.D u y))=false) :
    Trans.Recal.replMark (h+6) (.D 0 (.sum A0 (.D 1 (.sum D1z (.D 0 (.D u y))))))
      (.D u y) cc
      = some (.D 0 (.sum A0 (.D 1 (.sum D1z (.D 0 cc))))) := by
  rw [show h+6=(h+5)+1 by omega,Trans.Recal.replMark,hn1]
  simp only [Bool.false_eq_true,if_false]
  rw [show h+5=(h+4)+1 by omega,Trans.Recal.replMark,
    show Trans.Dict.BT.toL (.sum A0 (.D 1 (.sum D1z (.D 0 (.D u y)))))
      =[A0,.D 1 (.sum D1z (.D 0 (.D u y)))] from rfl]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D 0 (.D u y))))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Trans.Recal.replMark (h+4) (.D 1 (.sum D1z (.D 0 (.D u y))))
        (.D u y) cc)))=_
  rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark,hn2]
  simp only [Bool.false_eq_true,if_false]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D 0 (.D u y))))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
        (Trans.Recal.replMark (h+3) (.sum D1z (.D 0 (.D u y))) (.D u y) cc))))=_
  rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark,
    show Trans.Dict.BT.toL (.sum D1z (.D 0 (.D u y)))
      =[D1z,.D 0 (.D u y)] from rfl]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D 0 (.D u y))))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
        (Option.map (fun ll=>Trans.Dict.BT.ofL
            (([D1z,(Trans.Dict.BT.D 0 (.D u y))] : List Trans.Dict.BT).dropLast++[ll]))
          (Trans.Recal.replMark (h+2) (.D 0 (.D u y)) (.D u y) cc)))))=_
  rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark,hn3]
  simp only [Bool.false_eq_true,if_false]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D 0 (.D u y))))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
        (Option.map (fun ll=>Trans.Dict.BT.ofL
            (([D1z,(Trans.Dict.BT.D 0 (.D u y))] : List Trans.Dict.BT).dropLast++[ll]))
          (Option.map (fun aa=>Trans.Dict.BT.D 0 aa)
            (Trans.Recal.replMark (h+1) (.D u y) (.D u y) cc))))))=_
  rw [G1.replMark_self (h+1) u y cc (by omega)]
  rfl

/-- `Part` の中の浅い側。相 6 が使う。 -/
theorem repl_base_shallow (h u : Nat) (y cc : Trans.Dict.BT)
    (hn1 : ((Trans.Dict.BT.D 0 (.sum A0 (.D 1 (.sum D1z (.D u y)))))
            ==(Trans.Dict.BT.D u y))=false)
    (hn2 : ((Trans.Dict.BT.D 1 (.sum D1z (.D u y)))==(Trans.Dict.BT.D u y))=false) :
    Trans.Recal.replMark (h+5) (.D 0 (.sum A0 (.D 1 (.sum D1z (.D u y)))))
      (.D u y) cc
      = some (.D 0 (.sum A0 (.D 1 (.sum D1z cc)))) := by
  rw [show h+5=(h+4)+1 by omega,Trans.Recal.replMark,hn1]
  simp only [Bool.false_eq_true,if_false]
  rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark,
    show Trans.Dict.BT.toL (.sum A0 (.D 1 (.sum D1z (.D u y))))
      =[A0,.D 1 (.sum D1z (.D u y))] from rfl]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D u y)))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Trans.Recal.replMark (h+3) (.D 1 (.sum D1z (.D u y))) (.D u y) cc)))=_
  rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark,hn2]
  simp only [Bool.false_eq_true,if_false]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D u y)))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
        (Trans.Recal.replMark (h+2) (.sum D1z (.D u y)) (.D u y) cc))))=_
  rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark,
    show Trans.Dict.BT.toL (.sum D1z (.D u y))=[D1z,.D u y] from rfl]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D u y)))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
        (Option.map (fun ll=>Trans.Dict.BT.ofL
            (([D1z,(Trans.Dict.BT.D u y)] : List Trans.Dict.BT).dropLast++[ll]))
          (Trans.Recal.replMark (h+1) (.D u y) (.D u y) cc)))))=_
  rw [G1.replMark_self (h+1) u y cc (by omega)]
  rfl

theorem repl_LBT_r3 (a f : Nat) (hf : 4*a+6 ≤ f) :
    Trans.Recal.replMark f (LBT (7*a+2)) D1z D11z=some (LBT (7*a+3)) := by
  rw [LBT_r a 2 (by omega),LBT_r a 3 (by omega)]
  refine repl_D0W a f 6 (Part 2) (Part 3) D1z D11z ?_ (fun n => ⟨rfl,rfl⟩) hf
  intro g hg
  obtain ⟨h,rfl⟩ : ∃ h,g=h+6 := ⟨g-6,by omega⟩
  exact repl_base_deep h 1 .zero D11z rfl rfl rfl

theorem repl_LBT_r4 (a f : Nat) (hf : 4*a+6 ≤ f) :
    Trans.Recal.replMark f (LBT (7*a+3)) D11z D1ss=some (LBT (7*a+4)) := by
  rw [LBT_r a 3 (by omega),LBT_r a 4 (by omega)]
  refine repl_D0W a f 6 (Part 3) (Part 4) D11z D1ss ?_ (fun n => ⟨rfl,rfl⟩) hf
  intro g hg
  obtain ⟨h,rfl⟩ : ∃ h,g=h+6 := ⟨g-6,by omega⟩
  exact repl_base_deep h 1 D1z D1ss rfl rfl rfl

theorem repl_LBT_r5 (a f : Nat) (hf : 4*a+6 ≤ f) :
    Trans.Recal.replMark f (LBT (7*a+4)) D1ss A0=some (LBT (7*a+5)) := by
  rw [LBT_r a 4 (by omega),LBT_r a 5 (by omega)]
  refine repl_D0W a f 6 (Part 4) (Part 5) D1ss A0 ?_ (fun n => ⟨rfl,rfl⟩) hf
  intro g hg
  obtain ⟨h,rfl⟩ : ∃ h,g=h+6 := ⟨g-6,by omega⟩
  exact repl_base_deep h 1 (.sum D1z D1z) A0 rfl rfl rfl

theorem repl_LBT_r6 (a f : Nat) (hf : 4*a+5 ≤ f) :
    Trans.Recal.replMark f (LBT (7*a+5)) (.D 0 A0) (.D 0 B0)=some (LBT (7*a+6)) := by
  rw [LBT_r a 5 (by omega),LBT_r a 6 (by omega)]
  refine repl_D0W a f 5 (Part 5) (Part 6) (.D 0 A0) (.D 0 B0) ?_ (fun n => ⟨rfl,rfl⟩) hf
  intro g hg
  obtain ⟨h,rfl⟩ : ∃ h,g=h+5 := ⟨g-5,by omega⟩
  exact repl_base_shallow h 0 A0 (.D 0 B0) rfl rfl

theorem repl_LBT_r0 (a f : Nat) (hf : 4*a+7 ≤ f) :
    Trans.Recal.replMark f (LBT (7*a+6)) D1z D11z=some (LBT (7*a+7)) := by
  rw [LBT_r a 6 (by omega),show 7*a+7=7*(a+1)+0 by omega,LBT_r (a+1) 0 (by omega),
    ← W_add a 1 (Part 0)]
  refine repl_D0W a f 7 (Part 6) (W 1 (Part 0)) D1z D11z ?_ (fun n => ⟨rfl,rfl⟩) hf
  intro g hg
  obtain ⟨h,rfl⟩ : ∃ h,g=h+7 := ⟨g-7,by omega⟩
  change Trans.Recal.replMark (h+7)
    (.D 0 (.sum A0 (.D 1 (.sum D1z (.D 0 (.sum A0 D1z)))))) D1z D11z
    =some (.D 0 (.sum A0 (.D 1 (.sum D1z (.D 0 (.sum A0 D11z))))))
  rw [show h+7=(h+6)+1 by omega,Trans.Recal.replMark,
    show ((Trans.Dict.BT.D 0 (.sum A0 (.D 1 (.sum D1z (.D 0 (.sum A0 D1z))))))==D1z)
      =false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show h+6=(h+5)+1 by omega,Trans.Recal.replMark,
    show Trans.Dict.BT.toL (.sum A0 (.D 1 (.sum D1z (.D 0 (.sum A0 D1z)))))
      =[A0,.D 1 (.sum D1z (.D 0 (.sum A0 D1z)))] from rfl]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D 0 (.sum A0 D1z))))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Trans.Recal.replMark (h+5) (.D 1 (.sum D1z (.D 0 (.sum A0 D1z)))) D1z D11z)))=_
  rw [show h+5=(h+4)+1 by omega,Trans.Recal.replMark,
    show ((Trans.Dict.BT.D 1 (.sum D1z (.D 0 (.sum A0 D1z))))==D1z)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D 0 (.sum A0 D1z))))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
        (Trans.Recal.replMark (h+4) (.sum D1z (.D 0 (.sum A0 D1z))) D1z D11z))))=_
  rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark,
    show Trans.Dict.BT.toL (.sum D1z (.D 0 (.sum A0 D1z)))
      =[D1z,.D 0 (.sum A0 D1z)] from rfl]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D 0 (.sum A0 D1z))))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
        (Option.map (fun ll=>Trans.Dict.BT.ofL
            (([D1z,(Trans.Dict.BT.D 0 (.sum A0 D1z))]
              : List Trans.Dict.BT).dropLast++[ll]))
          (Trans.Recal.replMark (h+3) (.D 0 (.sum A0 D1z)) D1z D11z)))))=_
  rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark,
    show ((Trans.Dict.BT.D 0 (.sum A0 D1z))==D1z)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D 0 (.sum A0 D1z))))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
        (Option.map (fun ll=>Trans.Dict.BT.ofL
            (([D1z,(Trans.Dict.BT.D 0 (.sum A0 D1z))]
              : List Trans.Dict.BT).dropLast++[ll]))
          (Option.map (fun aa=>Trans.Dict.BT.D 0 aa)
            (Trans.Recal.replMark (h+2) (.sum A0 D1z) D1z D11z))))))=_
  rw [show h+2=(h+1)+1 by omega,Trans.Recal.replMark,
    show Trans.Dict.BT.toL (.sum A0 D1z)=[A0,D1z] from rfl]
  change (Option.map (fun x=>Trans.Dict.BT.D 0 x)
    (Option.map (fun ll=>Trans.Dict.BT.ofL
        (([A0,(Trans.Dict.BT.D 1 (.sum D1z (.D 0 (.sum A0 D1z))))]
          : List Trans.Dict.BT).dropLast++[ll]))
      (Option.map (fun aa=>Trans.Dict.BT.D 1 aa)
        (Option.map (fun ll=>Trans.Dict.BT.ofL
            (([D1z,(Trans.Dict.BT.D 0 (.sum A0 D1z))]
              : List Trans.Dict.BT).dropLast++[ll]))
          (Option.map (fun aa=>Trans.Dict.BT.D 0 aa)
            (Option.map (fun ll=>Trans.Dict.BT.ofL
                (([A0,D1z] : List Trans.Dict.BT).dropLast++[ll]))
              (Trans.Recal.replMark (h+1) D1z D1z D11z)))))))=_
  rw [G1.replMark_self (h+1) 1 .zero D11z (by omega)]
  rfl

#guard (List.range 5).all fun a =>
  Trans.Recal.replMark 60 (LBT (7*a+2)) D1z D11z==some (LBT (7*a+3))
#guard (List.range 5).all fun a =>
  Trans.Recal.replMark 60 (LBT (7*a+3)) D11z D1ss==some (LBT (7*a+4))
#guard (List.range 5).all fun a =>
  Trans.Recal.replMark 60 (LBT (7*a+4)) D1ss A0==some (LBT (7*a+5))
#guard (List.range 5).all fun a =>
  Trans.Recal.replMark 60 (LBT (7*a+5)) (.D 0 A0) (.D 0 B0)==some (LBT (7*a+6))
#guard (List.range 5).all fun a =>
  Trans.Recal.replMark 60 (LBT (7*a+6)) D1z D11z==some (LBT (7*a+7))

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
