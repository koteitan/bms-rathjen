import Rows.G10

/-!
# G12 — Γ_{ψ₀(Ω₂)+1} の行 `(0,0)(1,1)(2,2)(1,1)(2,1)(3,1)`

`oR` が要る 12 行の最後の 1 行。展開の値の列は標準基本列ではなく閉じた形 `fD`
(`Rows/Selected.lean`) で、`Certified` の極限節はそれで構わない。

**リンク 1 が定理になっている。残るのはリンク 2 と 3 である。**

    展開 --ofMatrix--> 梯子 --transPort--> BT --dict--> 値
            ✅ ofMatrix_M      🚧 未着手      🚧 未着手

この行の読み出し出力は高さ 3 の族の中では**最も単純**で、`W` は 1 つの構成子の
繰り返しになる (`G10` は 6 相、`G11` は 7 相)。周期は 5 列、行 0 の値はブロックごとに
3 ずつ増える。

リンク 3 の測定 (定理ではない):

    dict (D 0 (W n Base))                    = fD n
    dict D2z = Z 1,  dict D1z = Ω,  dict D11z = φ̄(0, Ω+Ω)
    collapse 1 (fD n)                        = φ̄(0, Ω + fD n)
    collapse 1 (collapse 1 (fD n))           = φ̄(0, φ̄(0, Ω + fD n))   -- Ω は増えない

2 段目で `Ω` が増えないのは、1 段目の値が既に `Ω` より大きく `plus` の filter が
`Ω` を落とすためである。`G11` の逆で、そこが `G10`/`G11` との違いになる。
-/

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected
namespace G12

def M : BMS.Matrix := [[0,0],[1,1],[2,2],[1,1],[2,1],[3,1]]
def t : Term := psi (Z zero) (add (Z (phi zero zero)) (phi zero zero))

/-- Row-zero value of the `0,1,2,1,1` five-column tail; the block steps by 3. -/
def p (k : Nat) : Int :=
  if k%5=0 then ((3*(k/5)+3:Nat):Int)
  else if k%5=1 ∨ k%5=3 then ((3*(k/5)+4:Nat):Int)
  else ((3*(k/5)+5:Nat):Int)

/-- Row-one value of the five-column tail. -/
def q (k : Nat) : Int := if k%5=0 then 0 else if k%5=2 then 2 else 1

def T (m : Nat) : Trans.Recal.PS := (List.range m).map fun k => (p k,q k)

/-- The parsed expansion after `m` individual tail columns. -/
def L (m : Nat) : Trans.Recal.PS := [(0,0),(1,1),(2,2),(1,1),(2,1)]++T m

abbrev D0z : Trans.Dict.BT := .D 0 .zero
abbrev D1z : Trans.Dict.BT := .D 1 .zero
abbrev D2z : Trans.Dict.BT := .D 2 .zero
abbrev D11z : Trans.Dict.BT := .D 1 D1z
abbrev Base : Trans.Dict.BT := .sum D2z D11z

/-- A complete block wraps the unfinished suffix in the reader output. -/
def W : Nat → Trans.Dict.BT → Trans.Dict.BT
  | 0,b => b
  | n+1,b => .sum D2z (.D 1 (.D 1 (.D 0 (W n b))))

def Part : Nat → Trans.Dict.BT
  | 0 => Base
  | 1 => .sum D2z (.D 1 (.D 1 D0z))
  | 2 => .sum D2z (.D 1 (.D 1 (.D 0 D1z)))
  | 3 => .sum D2z (.D 1 (.D 1 (.D 0 D2z)))
  | _ => .sum D2z (.D 1 (.D 1 (.D 0 (.sum D2z D1z))))

/-- Reader output on every one-column prefix of the five-phase ladder. -/
def LBT (m : Nat) : Trans.Dict.BT := .D 0 (W (m/5) (Part (m%5)))

theorem T_succ (m : Nat) : T (m+1)=T m++[(p m,q m)] := by
  unfold T
  rw [List.range_succ,List.map_append]
  rfl

theorem L_succ (m : Nat) : L (m+1)=L m++[(p m,q m)] := by
  unfold L
  rw [T_succ,List.append_assoc]

theorem length_T (m : Nat) : (T m).length=m := by simp [T]

theorem length_L (m : Nat) : (L m).length=m+5 := by simp [L,length_T]

theorem lenI_L (m : Nat) : Trans.Recal.lenI (L m)=(m:Int)+5 := by
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
      ([[0+a*3*1,0+a*0*1],[1+a*3*1,1+a*0*1],
        [2+a*3*1,2+a*0*1],[1+a*3*1,1+a*0*1],
        [2+a*3*1,1+a*0*1]] : BMS.Matrix))=
      fun a => [[3*a,0],[1+3*a,1],[2+3*a,2],[1+3*a,1],[2+3*a,1]] := by
  funext a
  simp [Nat.mul_comm]

theorem expand_block_succ : ((fun a : Nat =>
      ([[3*a,0],[1+3*a,1],[2+3*a,2],[1+3*a,1],[2+3*a,1]]:BMS.Matrix)) ∘ Nat.succ)=
      fun a => [[3+3*a,0],[4+3*a,1],[5+3*a,2],[4+3*a,1],[5+3*a,1]] := by
  funext a
  simp only [Function.comp_apply]
  rw [show 3*(a+1)=3+3*a by omega,
    show 1+(3+3*a)=4+3*a by omega,
    show 2+(3+3*a)=5+3*a by omega]

theorem expand_M (n : Nat) :
    BMS.expand M n=[[0,0],[1,1],[2,2],[1,1],[2,1]]++
      ((List.range n).map fun a =>
        ([[3+3*a,0],[4+3*a,1],[5+3*a,2],[4+3*a,1],[5+3*a,1]] : BMS.Matrix)).flatten := by
  show (BMS.expand? M n).getD []=_
  have h : BMS.expand? M n=some (M.take 0++
      ((List.range (n+1)).map fun a =>
        ([[0+a*3*1,0+a*0*1],[1+a*3*1,1+a*0*1],
          [2+a*3*1,2+a*0*1],[1+a*3*1,1+a*0*1],
          [2+a*3*1,1+a*0*1]] : BMS.Matrix)).flatten) := rfl
  rw [h,expand_block_first,List.range_succ_eq_map]
  simp only [Option.getD_some,List.take,List.map_cons,List.flatten_cons,
    List.map_map,List.nil_append]
  rw [expand_block_succ]

theorem p_phase0 (a : Nat) : p (5*a)=((3*a+3:Nat):Int) := by simp [p]
theorem p_phase1 (a : Nat) : p (5*a+1)=((3*a+4:Nat):Int) := by simp [p]; omega
theorem p_phase2 (a : Nat) : p (5*a+2)=((3*a+5:Nat):Int) := by simp [p]; omega
theorem p_phase3 (a : Nat) : p (5*a+3)=((3*a+4:Nat):Int) := by simp [p]; omega
theorem p_phase4 (a : Nat) : p (5*a+4)=((3*a+5:Nat):Int) := by simp [p]; omega
theorem q_phase0 (a : Nat) : q (5*a)=0 := by simp [q]
theorem q_phase1 (a : Nat) : q (5*a+1)=1 := by simp [q]
theorem q_phase2 (a : Nat) : q (5*a+2)=2 := by simp [q]
theorem q_phase3 (a : Nat) : q (5*a+3)=1 := by simp [q]
theorem q_phase4 (a : Nat) : q (5*a+4)=1 := by simp [q]

theorem T_five_mul (n : Nat) :
    T (5*n)=((List.range n).map fun a =>
      ([(((3*a+3:Nat):Int),(0:Int)),(((3*a+4:Nat):Int),(1:Int)),
        (((3*a+5:Nat):Int),(2:Int)),(((3*a+4:Nat):Int),(1:Int)),
        (((3*a+5:Nat):Int),(1:Int))]
        : Trans.Recal.PS)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 5*(n+1)=5*n+5 by omega,T_succ,T_succ,T_succ,T_succ,T_succ,ih,
      List.range_succ,List.map_append,List.flatten_append]
    simp only [List.map_singleton,List.flatten_singleton,List.append_assoc,
      List.singleton_append]
    rw [p_phase0 n,q_phase0 n,p_phase1 n,q_phase1 n,p_phase2 n,q_phase2 n,
      p_phase3 n,q_phase3 n,p_phase4 n,q_phase4 n]
    simp only [List.cons_append,List.nil_append]

theorem map_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[3+3*a,0],[4+3*a,1],[5+3*a,2],[4+3*a,1],[5+3*a,1]] : BMS.Matrix)).flatten).map
        (fun c => ((c.getD 0 0:Int),(c.getD 1 0:Int)))=T (5*n) := by
  rw [T_five_mul,List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  change [(((3+3*a:Nat):Int),0),(((4+3*a:Nat):Int),1),
    (((5+3*a:Nat):Int),2),(((4+3*a:Nat):Int),1),
    (((5+3*a:Nat):Int),1)]=_
  rw [show 3+3*a=3*a+3 by omega,show 4+3*a=3*a+4 by omega,
    show 5+3*a=3*a+5 by omega]

theorem all_len_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[3+3*a,0],[4+3*a,1],[5+3*a,2],[4+3*a,1],[5+3*a,1]] : BMS.Matrix)).flatten).all
        (fun c => decide (c.length≤2))=true := by simp

/-- Link 1: each expansion lands on a five-column-complete prefix. -/
theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n)=some (L (5*n)) := by
  rw [expand_M]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1],[2,2],[1,1],[2,1]]:BMS.Matrix)++
      ((List.range n).map fun a =>
        ([[3+3*a,0],[4+3*a,1],[5+3*a,2],[4+3*a,1],[5+3*a,1]]:BMS.Matrix)).flatten).isEmpty=false
      from by rfl]
  rw [List.all_append,all_len_blocks]
  simp only [List.all_cons,List.length_cons,List.length_nil,Bool.and_true,
    Bool.not_false,Bool.true_and,List.map_append,List.map_cons,List.map_nil]
  rw [map_blocks]
  rfl

#guard (List.range 8).all fun n =>
  Trans.Recal.ofMatrix (BMS.expand M n)==some (L (5*n))
#guard (List.range 20).all fun m => Trans.Recal.predP (L (m+1))==L m
#guard (List.range 20).all fun m => Trans.Recal.transPort (L m)==LBT m
#guard (List.range 20).all fun m => Trans.Recal.redP (L m)==L m
#guard rest12.any fun r => r.m==M && r.t==t
#guard (List.range 6).all fun n => Trans.oR (BMS.expand M n)==some (fD n)

#print axioms ofMatrix_M

end G12
end Rows.Selected
